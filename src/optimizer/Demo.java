import ir.*;
import ir.datatype.IRArrayType;
import ir.datatype.IRIntType;
import ir.datatype.IRType;
import ir.operand.IRConstantOperand;
import ir.operand.IROperand;
import ir.operand.IRVariableOperand;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import middle_end.CFG;
import middle_end.DeadCodeElimination;
import middle_end.GlobalReassociation;
import middle_end.GlobalValueNumbering;
import middle_end.LazyCodeMotion;
import middle_end.LoopAnalysis;
import middle_end.RemoveEmptyBlocks;
import middle_end.SSABuilder;

/**
 * Entry point for the Tiger-IR optimizer.
 *
 * Pipeline (in order):
 *   1. Parse Tiger-IR                            (IRReader)
 *   2. CFG construction                          (per-function)
 *   3. Loop nesting depths                       (LoopAnalysis)        -- pass id "loop"
 *   4. SSA construction                          (SSABuilder.buildSSA) -- pass id "ssa"
 *   5. Global Reassociation                      (GlobalReassociation) -- pass id "reassoc"
 *   6. Global Value Numbering                    (GlobalValueNumbering)-- pass id "gvn"
 *   7. Leave SSA                                 (SSABuilder.leavingSSA, paired with "ssa")
 *   8. Lazy Code Motion                          (LazyCodeMotion)      -- pass id "lcm"
 *   9. Dead code elimination                     (DeadCodeElimination) -- pass id "dce"
 *  10. Remove empty/forwarder/unreachable blocks (RemoveEmptyBlocks)   -- pass id "empty"
 *  11. Write out.ir                              (IRPrinter)
 *
 * Note on ordering: any future multiply-by-constant strength-reduction pass that lowers
 * {@code mul} to bit shifts MUST run AFTER step 8 (LCM), never before step 5
 * (GlobalReassociation), because shifts are not associative and would break reassociation's
 * tree-rebuild assumptions. The pipeline reserves the slot between LCM and DCE for this.
 *
 * Flags:
 *   -debug         Verbose IR / dataflow dumps between passes (stderr only — never to out.ir).
 *   -passes LIST   Comma-separated subset of pass ids to run; others are skipped. Example:
 *                  java -cp build/optimizer Demo -passes ssa,reassoc,gvn,lcm,dce input.ir out.ir
 *                  When omitted, all passes run.
 */
public class Demo {

    /** Pass ids accepted by {@code -passes}. Order matches the pipeline. */
    private static final List<String> KNOWN_PASSES = Arrays.asList(
            "loop", "ssa", "reassoc", "gvn", "lcm", "dce", "empty");

    public static void main(String[] args) throws Exception {
        boolean debug = false;
        Set<String> enabled = null; // null sentinel = all passes on
        List<String> files = new ArrayList<>();
        for (int i = 0; i < args.length; i++) {
            String a = args[i];
            if ("-debug".equals(a)) {
                debug = true;
            } else if (a.startsWith("-passes=")) {
                enabled = parsePassList(a.substring("-passes=".length()));
            } else if ("-passes".equals(a)) {
                if (i + 1 >= args.length) {
                    usage();
                    return;
                }
                enabled = parsePassList(args[++i]);
            } else if (a.startsWith("-")) {
                System.err.println("[Demo] Unknown flag '" + a + "'");
                usage();
                return;
            } else {
                files.add(a);
            }
        }
        if (files.size() < 2) {
            usage();
            return;
        }

        IRReader irReader = new IRReader();
        IRProgram program = irReader.parseIRFile(files.get(0));

        if (debug) {
            System.err.println("[Demo] pipeline passes: " + (enabled == null ? KNOWN_PASSES : enabled));
        }

        for (IRFunction function : program.functions) {
            runPipeline(function, debug, enabled);
        }

        // Write the optimized IR to the output file.
        try (PrintStream out = new PrintStream(files.get(1))) {
            new IRPrinter(out).printProgram(program);
        }

        // Existing diagnostics — run AFTER the full pipeline so they reflect the optimized IR.
        printDiagnostics(program);
    }

    /**
     * Run the full pipeline on one function. Each pass honors {@code enabled}: if not in the
     * set (and {@code enabled != null}), it is skipped. SSA-dependent passes ({@code reassoc},
     * {@code gvn}) are silently no-ops when {@code ssa} is disabled. When {@code ssa} runs,
     * {@code leavingSSA} is paired with it unconditionally so the IR ends up flat for the
     * downstream flat-IR passes.
     */
    private static void runPipeline(IRFunction function, boolean debug, Set<String> enabled) {
        if (debug) {
            System.err.println();
            System.err.println("==== BEGIN function " + function.name + " ====");
            dumpFlat(function, "INITIAL");
        }

        CFG cfg = new CFG(function);

        if (isOn(enabled, "loop")) {
            LoopAnalysis.analyze(cfg);
            if (debug) {
                LoopAnalysis.printLoopInfoToStderr(function, cfg);
            }
        }

        boolean ssaBuilt = false;
        if (isOn(enabled, "ssa")) {
            SSABuilder.buildSSA(cfg);
            ssaBuilt = true;
            if (debug) {
                System.err.println("---- AFTER buildSSA (" + function.name + ") ----");
                SSABuilder.printSSAFormToStderr(function, cfg);
            }
        }

        if (isOn(enabled, "reassoc")) {
            if (ssaBuilt) {
                GlobalReassociation.run(cfg, debug);
                if (debug) {
                    System.err.println("---- AFTER reassoc (" + function.name + ") ----");
                }
            } else if (debug) {
                System.err.println("[Demo] 'reassoc' skipped — requires 'ssa'");
            }
        }

        if (isOn(enabled, "gvn")) {
            if (ssaBuilt) {
                GlobalValueNumbering.run(cfg, debug);
                if (debug) {
                    System.err.println("---- AFTER gvn (" + function.name + ") ----");
                }
            } else if (debug) {
                System.err.println("[Demo] 'gvn' skipped — requires 'ssa'");
            }
        }

        if (ssaBuilt) {
            SSABuilder.leavingSSA(cfg, debug);
            if (debug) {
                dumpFlat(function, "AFTER leavingSSA");
            }
        }

        // RESERVED SLOT: any future multiply-by-constant strength-reduction pass goes here,
        // AFTER lcm but BEFORE dce. Shift rewrites are non-associative and must not happen
        // before reassoc/gvn.

        if (isOn(enabled, "lcm")) {
            LazyCodeMotion.run(cfg, debug);
            if (debug) {
                dumpFlat(function, "AFTER lcm");
            }
        }

        if (isOn(enabled, "dce")) {
            DeadCodeElimination.run(cfg, debug);
            if (debug) {
                dumpFlat(function, "AFTER dce");
            }
        }

        if (isOn(enabled, "empty")) {
            RemoveEmptyBlocks.run(cfg, debug);
            if (debug) {
                dumpFlat(function, "AFTER empty");
            }
        }

        if (debug) {
            System.err.println("==== END function " + function.name + " ====");
        }
    }

    private static boolean isOn(Set<String> enabled, String name) {
        return enabled == null || enabled.contains(name);
    }

    private static Set<String> parsePassList(String spec) {
        Set<String> r = new LinkedHashSet<>();
        for (String t : spec.split(",")) {
            String name = t.trim().toLowerCase();
            if (name.isEmpty()) continue;
            if (!KNOWN_PASSES.contains(name)) {
                System.err.println("[Demo] Unknown pass id '" + name + "' in -passes; known: " + KNOWN_PASSES);
                System.exit(1);
            }
            r.add(name);
        }
        return r;
    }

    private static void dumpFlat(IRFunction fn, String tag) {
        System.err.println("---- " + tag + " (" + fn.name + ") ----");
        for (IRInstruction inst : fn.instructions) {
            System.err.println("  " + inst);
        }
    }

    private static void usage() {
        System.err.println("Usage: java Demo [-debug] [-passes LIST] <input.ir> <output.ir>");
        System.err.println("  -debug         verbose stderr dumps between passes");
        System.err.println("  -passes LIST   comma-separated subset of: " + KNOWN_PASSES);
        System.err.println("                 omitted = all passes on");
        System.exit(1);
    }

    /**
     * Existing diagnostic reports (preserved from the original Demo). Reflect the fully
     * optimized IR, not any intermediate stage.
     */
    private static void printDiagnostics(IRProgram program) {
        IRPrinter stdoutPrinter = new IRPrinter(new PrintStream(System.out));

        System.out.println("Instructions that stores a constant to an array:");
        for (IRFunction function : program.functions) {
            for (IRInstruction instruction : function.instructions) {
                if (instruction.opCode == IRInstruction.OpCode.ARRAY_STORE) {
                    if (instruction.operands[0] instanceof IRConstantOperand) {
                        System.out.print(String.format("Line %d:", instruction.irLineNumber));
                        stdoutPrinter.printInstruction(instruction);
                    }
                }
            }
        }
        System.out.println();

        System.out.println("Int scalars and 1-sized arrays:");
        for (IRFunction function : program.functions) {
            List<String> vars = new ArrayList<>();
            for (IRVariableOperand v : function.variables) {
                IRType type = v.type;
                if (type == IRIntType.get() || type == IRArrayType.get(IRIntType.get(), 1)) {
                    vars.add(v.getName());
                }
            }
            if (!vars.isEmpty()) {
                System.out.println(function.name + ": " + String.join(", ", vars));
            }
        }
        System.out.println();

        System.out.println("Unused variables/parameters:");
        for (IRFunction function : program.functions) {
            Set<String> vars = new HashSet<>();
            for (IRVariableOperand v : function.parameters) vars.add(v.getName());
            for (IRVariableOperand v : function.variables) vars.add(v.getName());
            for (IRInstruction instruction : function.instructions) {
                for (IROperand operand : instruction.operands) {
                    if (operand instanceof IRVariableOperand) {
                        vars.remove(((IRVariableOperand) operand).getName());
                    }
                }
            }
            if (!vars.isEmpty()) {
                System.out.println(function.name + ": " + String.join(", ", vars));
            }
        }
        System.out.println();
    }
}
