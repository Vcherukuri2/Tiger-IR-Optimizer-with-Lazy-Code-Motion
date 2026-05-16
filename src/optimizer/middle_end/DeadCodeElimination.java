package middle_end;

import ir.IRFunction;
import ir.IRInstruction;
import ir.operand.IROperand;
import ir.operand.IRVariableOperand;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

// SCOPE: Mark-and-sweep dead code elimination on flat Tiger-IR. Runs after LCM so that
// LCM's hoisted _lcm_t temps whose original sites no longer feed any critical instruction
// (and any GR-introduced _ra temps that ended up unused after GVN renaming) get removed.
//
// PACKAGING: middle_end. Public entry is run(cfg [, debug]). Reuses the existing
// (package-private) per-function logic spirit of {@link Optimizer} but exposed as a clean
// CFG-driven facade so Demo.java doesn't need to instantiate the legacy Optimizer.
//
// ALGORITHM:
//   1. Mark every "critical" instruction (any branch/goto/return/label/call/array_store —
//      i.e., anything with observable side effects or required for control flow).
//   2. Worklist: pop a marked instruction, walk its read-operand variables, and mark every
//      instruction that defines that variable as a destination. Repeat until empty.
//   3. Sweep: keep only marked instructions.
//
// LIMITATIONS:
//   - Marks ALL defs of a used variable, not just the reaching definition. This is correct
//     but conservative (post-leavingSSA flat IR allows multiple defs per name).
//   - Calls / array_stores stay because they're critical, even if their result/destination
//     is never read.
//
public final class DeadCodeElimination {

    private DeadCodeElimination() {}

    public static void run(CFG cfg) {
        run(cfg, false);
    }

    public static void run(CFG cfg, boolean debug) {
        IRFunction fn = cfg.function;
        List<IRInstruction> insts = fn.getInstructions();
        if (insts.isEmpty()) {
            return;
        }

        Map<String, List<IRInstruction>> defsOf = new HashMap<>();
        for (IRInstruction inst : insts) {
            String d = destVariableName(inst);
            if (d != null) {
                defsOf.computeIfAbsent(d, k -> new ArrayList<>()).add(inst);
            }
        }

        Set<IRInstruction> marked = new HashSet<>();
        Deque<IRInstruction> worklist = new ArrayDeque<>();
        for (IRInstruction inst : insts) {
            if (isCritical(inst)) {
                if (marked.add(inst)) {
                    worklist.add(inst);
                }
            }
        }

        while (!worklist.isEmpty()) {
            IRInstruction cur = worklist.removeFirst();
            for (String use : usedVariableNames(cur)) {
                List<IRInstruction> defs = defsOf.get(use);
                if (defs == null) continue;
                for (IRInstruction d : defs) {
                    if (marked.add(d)) {
                        worklist.add(d);
                    }
                }
            }
        }

        List<IRInstruction> kept = new ArrayList<>(insts.size());
        for (IRInstruction inst : insts) {
            if (marked.contains(inst)) {
                kept.add(inst);
            }
        }
        for (int i = 0; i < kept.size(); i++) {
            kept.get(i).irLineNumber = i;
        }
        int removed = insts.size() - kept.size();
        fn.setInstructions(kept);
        cfg.rebuildCFG();

        if (debug) {
            System.err.println("==== DCE (" + fn.name + "): removed " + removed + " of "
                    + insts.size() + " instructions ====");
        }
    }

    private static boolean isCritical(IRInstruction inst) {
        switch (inst.opCode) {
            case GOTO:
            case BREQ:
            case BRNEQ:
            case BRLT:
            case BRGT:
            case BRLEQ:
            case BRGEQ:
            case RETURN:
            case CALL:
            case CALLR:
            case LABEL:
            case ARRAY_STORE:
                return true;
            default:
                return false;
        }
    }

    private static String destVariableName(IRInstruction inst) {
        switch (inst.opCode) {
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
            case ASSIGN:
            case CALLR:
            case ARRAY_LOAD:
                if (inst.operands.length > 0 && inst.operands[0] instanceof IRVariableOperand) {
                    return ((IRVariableOperand) inst.operands[0]).getName();
                }
                return null;
            default:
                return null;
        }
    }

    private static List<String> usedVariableNames(IRInstruction inst) {
        List<String> r = new ArrayList<>();
        int[] idx = useIndices(inst);
        for (int i : idx) {
            if (i >= inst.operands.length) continue;
            IROperand op = inst.operands[i];
            if (op instanceof IRVariableOperand) {
                r.add(((IRVariableOperand) op).getName());
            }
        }
        return r;
    }

    private static int[] useIndices(IRInstruction inst) {
        switch (inst.opCode) {
            case ASSIGN:
                if (inst.operands.length == 2) return new int[]{1};
                if (inst.operands.length == 3) return new int[]{1, 2};
                return new int[]{};
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
                return new int[]{1, 2};
            case BREQ:
            case BRNEQ:
            case BRLT:
            case BRGT:
            case BRLEQ:
            case BRGEQ:
                return new int[]{1, 2};
            case RETURN:
                return new int[]{0};
            case CALL: {
                int[] r = new int[Math.max(0, inst.operands.length - 1)];
                for (int i = 0; i < r.length; i++) r[i] = i + 1;
                return r;
            }
            case CALLR: {
                int[] r = new int[Math.max(0, inst.operands.length - 2)];
                for (int i = 0; i < r.length; i++) r[i] = i + 2;
                return r;
            }
            case ARRAY_STORE:
                return new int[]{0, 1, 2};
            case ARRAY_LOAD:
                return new int[]{1, 2};
            default:
                return new int[]{};
        }
    }
}
