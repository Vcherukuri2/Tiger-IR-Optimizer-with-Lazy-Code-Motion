package middle_end;

import ir.IRFunction;
import ir.IRInstruction;
import ir.IRInstruction.OpCode;
import ir.operand.IRLabelOperand;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

// SCOPE: Final flat-IR cleanup pass. Runs after DCE so that any trivially empty / forwarder
// blocks (typically left behind after copy propagation or branch simplification) and any
// blocks made unreachable by upstream passes are removed.
//
// PACKAGING: middle_end. Public entry is run(cfg [, debug]).
//
// TWO TRANSFORMATIONS (applied in order, single pass):
//
//   1. Forwarder collapsing: a block whose body is exactly { label L; goto T } is a pure
//      forwarder. We rewrite every explicit branch/goto target that names L to name T
//      instead. The forwarder block is then removed UNLESS it has a fall-through predecessor
//      (in which case removing it would silently change semantics for that predecessor).
//      Chained forwarders (L → T1 → T2 → …) are collapsed via transitive closure of the
//      forwarding map before rewriting.
//
//   2. Unreachable-block removal: any block not reachable from the entry block (after the
//      forwarding rewrite) has all its instructions stripped.
//
// LIMITATIONS:
//   - Does NOT promote a label-only block ({ label L }) to a forwarder; that would require
//     inventing a goto and reasoning about fall-through, which is dependent on the next
//     block in the flat instruction order. The pass is intentionally conservative.
//   - Does NOT split critical edges or alter CFG structure beyond removing redundant blocks.
//
public final class RemoveEmptyBlocks {

    private RemoveEmptyBlocks() {}

    public static void run(CFG cfg) {
        run(cfg, false);
    }

    public static void run(CFG cfg, boolean debug) {
        IRFunction fn = cfg.function;
        if (cfg.basicBlocks.isEmpty()) {
            return;
        }

        int forwardersRemoved = collapseForwarders(cfg);
        int unreachableRemoved = removeUnreachable(cfg);

        if (debug) {
            System.err.println("==== RemoveEmptyBlocks (" + fn.name + "): forwarders=" + forwardersRemoved
                    + " unreachable=" + unreachableRemoved + " ====");
        }
    }

    /**
     * Phase 1: rewrite explicit branches whose target is a {@code label L; goto T} forwarder
     * to instead target {@code T}. Remove the forwarder blocks from the flat instruction list
     * unless a fall-through predecessor would be affected.
     */
    private static int collapseForwarders(CFG cfg) {
        IRFunction fn = cfg.function;
        List<IRInstruction> insts = fn.getInstructions();
        BasicBlock entry = cfg.basicBlocks.get(0);

        Map<String, String> forward = new HashMap<>();
        List<BasicBlock> candidates = new ArrayList<>();
        for (BasicBlock b : cfg.basicBlocks) {
            if (b == entry) continue;
            List<IRInstruction> bi = b.getInstructions();
            if (bi.size() == 2
                    && bi.get(0).opCode == OpCode.LABEL
                    && bi.get(1).opCode == OpCode.GOTO) {
                String myLabel = ((IRLabelOperand) bi.get(0).operands[0]).getName();
                String target = ((IRLabelOperand) bi.get(1).operands[0]).getName();
                forward.put(myLabel, target);
                candidates.add(b);
            }
        }
        if (forward.isEmpty()) {
            return 0;
        }

        // Transitive closure with cycle protection.
        for (String key : new ArrayList<>(forward.keySet())) {
            Set<String> seen = new HashSet<>();
            String cur = forward.get(key);
            while (forward.containsKey(cur) && seen.add(cur)) {
                cur = forward.get(cur);
            }
            forward.put(key, cur);
        }

        for (IRInstruction inst : insts) {
            switch (inst.opCode) {
                case GOTO:
                case BREQ:
                case BRNEQ:
                case BRLT:
                case BRGT:
                case BRLEQ:
                case BRGEQ: {
                    IRLabelOperand op = (IRLabelOperand) inst.operands[0];
                    String fwd = forward.get(op.getName());
                    if (fwd != null && !fwd.equals(op.getName())) {
                        inst.operands[0] = new IRLabelOperand(fwd, inst);
                    }
                    break;
                }
                default:
                    break;
            }
        }

        Set<IRInstruction> toRemove = new HashSet<>();
        int removed = 0;
        for (BasicBlock b : candidates) {
            if (hasFallThroughPredecessor(cfg, b)) {
                continue;
            }
            for (IRInstruction inst : b.getInstructions()) {
                toRemove.add(inst);
            }
            removed++;
        }
        if (toRemove.isEmpty()) {
            // Branch rewrites were applied even though no block was removed — still need to
            // rebuild the CFG so labelToBlock and instrToBlock reflect the new branch targets.
            cfg.rebuildCFG();
            return 0;
        }

        List<IRInstruction> kept = new ArrayList<>(insts.size() - toRemove.size());
        for (IRInstruction inst : insts) {
            if (!toRemove.contains(inst)) {
                kept.add(inst);
            }
        }
        for (int i = 0; i < kept.size(); i++) {
            kept.get(i).irLineNumber = i;
        }
        fn.setInstructions(kept);
        cfg.rebuildCFG();
        return removed;
    }

    /**
     * Phase 2: walk forward from the entry block; remove every block that isn't reached.
     */
    private static int removeUnreachable(CFG cfg) {
        IRFunction fn = cfg.function;
        if (cfg.basicBlocks.isEmpty()) {
            return 0;
        }
        BasicBlock entry = cfg.basicBlocks.get(0);
        Set<BasicBlock> reached = new HashSet<>();
        Deque<BasicBlock> wl = new ArrayDeque<>();
        wl.add(entry);
        while (!wl.isEmpty()) {
            BasicBlock b = wl.removeFirst();
            if (!reached.add(b)) continue;
            for (BasicBlock s : b.getSuccessors()) {
                wl.add(s);
            }
        }
        int total = cfg.basicBlocks.size();
        if (reached.size() == total) {
            return 0;
        }

        Set<IRInstruction> toRemove = new HashSet<>();
        for (BasicBlock b : cfg.basicBlocks) {
            if (!reached.contains(b)) {
                for (IRInstruction inst : b.getInstructions()) {
                    toRemove.add(inst);
                }
            }
        }

        List<IRInstruction> insts = fn.getInstructions();
        List<IRInstruction> kept = new ArrayList<>(insts.size() - toRemove.size());
        for (IRInstruction inst : insts) {
            if (!toRemove.contains(inst)) {
                kept.add(inst);
            }
        }
        for (int i = 0; i < kept.size(); i++) {
            kept.get(i).irLineNumber = i;
        }
        fn.setInstructions(kept);
        cfg.rebuildCFG();
        return total - reached.size();
    }

    /**
     * @return {@code true} if some predecessor reaches {@code b} via implicit fall-through,
     *         i.e. predecessor's end line is exactly one less than b's start line AND that
     *         predecessor's last instruction is not a terminator.
     */
    private static boolean hasFallThroughPredecessor(CFG cfg, BasicBlock b) {
        IRFunction fn = cfg.function;
        List<IRInstruction> insts = fn.getInstructions();
        for (BasicBlock p : b.getPredecessors()) {
            int pEnd = p.getEndLine();
            if (pEnd + 1 != b.getStartLine()) continue;
            if (pEnd < 0 || pEnd >= insts.size()) continue;
            IRInstruction last = insts.get(pEnd);
            if (!isTerminator(last)) {
                return true;
            }
        }
        return false;
    }

    private static boolean isTerminator(IRInstruction inst) {
        switch (inst.opCode) {
            case GOTO:
            case BREQ:
            case BRNEQ:
            case BRLT:
            case BRGT:
            case BRLEQ:
            case BRGEQ:
            case RETURN:
                return true;
            default:
                return false;
        }
    }
}
