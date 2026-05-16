package middle_end;

import ir.IRFunction;
import ir.IRInstruction;
import ir.IRInstruction.OpCode;
import ir.datatype.IRIntType;
import ir.operand.IRConstantOperand;
import ir.operand.IROperand;
import ir.operand.IRVariableOperand;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

// SCOPE: Global reassociation + forward propagation (Briggs & Cooper 1994), adapted to Tiger-IR SSA.
// Operates on each BasicBlock.getSsaIRList() built by SSABuilder.buildSSA(CFG). Block ranks come
// from LoopAnalysis.computeBlockRank(CFG). The flat IR (function.instructions) is NOT touched;
// the rewritten SSA form is consumed by GVN, leavingSSA, LCM, and DCE downstream.
//
// PACKAGING: middle_end. New _ra* temporaries are added to function.variables as IRIntType so
// the printer emits them on the int-list after leavingSSA.
//
// LIMITATIONS / DESIGN CHOICES:
// - Reassociable opcodes: ADD, MULT, AND, OR are flattened and sorted by rank.
// - SUB is folded into a parent ADD chain (a - b inside (a - b) + c is rewritten so the operand
//   list of the ADD carries a sign vector). A SUB whose result does NOT feed an ADD stays as a
//   binary subtract.
// - DIV is never rewritten (non-associative, non-commutative). Stays binary.
// - Forward propagation only inlines defs whose dest has total use-count 1 and whose single use
//   is in a reassociable arith op. This matches the bound in Table 2 of Briggs & Cooper (no code
//   size explosion).
// - assign, array_load, array_store, call, callr, branches, return, label, goto: never inlined,
//   never treated as expression nodes. array_load and call/callr defs get rank = block rank.
// - Distribution: mul(low, add(...)) -> add(mul(low, hi1), mul(low, hi2)) one level deep only.
//
/**
 * Reassociation + forward propagation pass. See file header for scope and limitations.
 */
public final class GlobalReassociation {

    /** Reserved compiler-inserted temp prefix; see SSABuilder.checkOptimizerTempPrefix. */
    public static final String TEMP_PREFIX = "_ra";

    private GlobalReassociation() {}

    // --- Expression tree ---

    /** Abstract reassociation expression node. */
    public static abstract class Expr {
        public int rank;
        public abstract boolean isLeaf();
    }

    /** Leaf: variable or integer literal. {@code constValue} is non-null iff it is a constant. */
    public static final class Leaf extends Expr {
        public final String label;     // variable SSA name OR constant literal text
        public final boolean constant;

        Leaf(String label, boolean constant, int rank) {
            this.label = label;
            this.constant = constant;
            this.rank = rank;
        }

        @Override
        public boolean isLeaf() { return true; }

        @Override
        public String toString() {
            return label;
        }
    }

    /**
     * Internal node. {@code op} is one of {@code add, sub, mul, div, and, or}. For an ADD that
     * absorbed SUB children, {@code signs.get(i)} is +1 or -1 in parallel with
     * {@code operands.get(i)}. For all other ops {@code signs} is null.
     */
    public static final class Bin extends Expr {
        public String op;
        public List<Expr> operands;
        public List<Integer> signs;

        Bin(String op, List<Expr> operands, List<Integer> signs) {
            this.op = op;
            this.operands = operands;
            this.signs = signs;
        }

        @Override
        public boolean isLeaf() { return false; }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder("(").append(op);
            for (int i = 0; i < operands.size(); i++) {
                sb.append(' ');
                if (signs != null && signs.get(i) < 0) {
                    sb.append("-");
                }
                sb.append(operands.get(i).toString());
            }
            sb.append(")");
            return sb.toString();
        }
    }

    // --- Public API ---

    /** Run reassociation on SSA form of {@code cfg}; equivalent to {@code run(cfg, false)}. */
    public static void run(CFG cfg) {
        run(cfg, false);
    }

    /**
     * Run reassociation on SSA form. If {@code debug}, dumps the rewritten SSA via {@link #printIR(CFG)}.
     */
    public static void run(CFG cfg, boolean debug) {
        if (cfg.basicBlocks.isEmpty()) {
            return;
        }
        Map<BasicBlock, Integer> blockRanks = LoopAnalysis.computeBlockRank(cfg);
        Map<String, Integer> varRanks = assignRanks(cfg, blockRanks);

        Map<String, IRInstruction> defOf = buildDefMap(cfg);
        Map<String, Integer> useCount = buildUseCount(cfg);
        Set<IRInstruction> arithInsts = collectArithInsts(cfg);

        Set<IRInstruction> roots = new LinkedHashSet<>();
        Map<IRInstruction, BasicBlock> blockOf = mapInstrToBlock(cfg);
        for (IRInstruction inst : arithInsts) {
            String dest = ssaDestName(inst);
            if (dest == null) {
                continue;
            }
            if (!isInlineable(dest, defOf, useCount, arithInsts, cfg)) {
                roots.add(inst);
            }
        }

        Map<IRInstruction, BuildResult> built = new LinkedHashMap<>();
        for (IRInstruction r : roots) {
            BuildResult br = buildTreeForRoot(r, defOf, useCount, arithInsts, varRanks, cfg);
            built.put(r, br);
        }

        for (Map.Entry<IRInstruction, BuildResult> e : built.entrySet()) {
            BuildResult br = e.getValue();
            Expr t = br.expr;
            t = sortOperands(t, varRanks);
            t = distributeMultiply(t, varRanks);
            t = sortOperands(t, varRanks);
            // BuildResult.expr is final; rebuild and overwrite the map entry.
            e.setValue(new BuildResult(t, br.absorbed));
        }

        int seedCounter = scanExistingRaCounter(cfg.function);
        emit(cfg, built, blockOf, seedCounter);

        if (debug) {
            printIR(cfg);
        }
    }

    // STEP 1
    /**
     * Assign a rank to every SSA scalar name in {@code cfg}. Constants and parameters get rank 0.
     * Phi results, {@code array_load}, and {@code call} / {@code callr} results get the rank of their block.
     * All other arithmetic results get {@code max(operandRanks)}. Walks blocks in reverse postorder
     * so non-phi defs precede uses.
     */
    public static Map<String, Integer> assignRanks(CFG cfg, Map<BasicBlock, Integer> blockRanks) {
        Map<String, Integer> ranks = new HashMap<>();
        for (IRVariableOperand p : cfg.function.parameters) {
            ranks.put(p.getName(), 0);
        }
        if (cfg.basicBlocks.isEmpty()) {
            return ranks;
        }

        List<BasicBlock> rpo = reversePostorder(cfg);

        // Pre-assign phi result ranks so they are visible even if their block comes later in RPO
        // or some phi sources reference values defined further down (loop back edges).
        for (BasicBlock b : cfg.basicBlocks) {
            int br = blockRanks.getOrDefault(b, 0);
            for (String[] phi : b.getPhiNodes()) {
                ranks.put(phi[1], br);
            }
        }

        for (BasicBlock b : rpo) {
            int br = blockRanks.getOrDefault(b, 0);
            List<IRInstruction> list = b.getSsaIRList();
            if (list == null) {
                continue;
            }
            for (IRInstruction inst : list) {
                String dest = ssaDestName(inst);
                if (dest == null) {
                    continue;
                }
                int r;
                switch (inst.opCode) {
                    case ARRAY_LOAD:
                    case CALLR:
                        r = br;
                        break;
                    case ASSIGN:
                        r = rankOperand(inst.operands[1], ranks);
                        break;
                    case ADD:
                    case SUB:
                    case MULT:
                    case DIV:
                    case AND:
                    case OR:
                        int r1 = rankOperand(inst.operands[1], ranks);
                        int r2 = rankOperand(inst.operands[2], ranks);
                        r = Math.max(r1, r2);
                        break;
                    default:
                        r = br;
                }
                ranks.put(dest, r);
            }
        }
        return ranks;
    }

    // STEP 2
    /**
     * Build an expression tree rooted at every reassociation root. Leaves are SSA names or
     * integer literals; internal nodes are {@link Bin}s. A def is inlined into a use only when
     * the def is a reassociable arithmetic op AND its dest has total use-count 1 AND that single
     * use is itself a reassociable arith op (the "Table 2" bound from Briggs &amp; Cooper).
     */
    public static Map<IRInstruction, Expr> forwardPropagate(CFG cfg, Map<String, Integer> varRanks) {
        Map<String, IRInstruction> defOf = buildDefMap(cfg);
        Map<String, Integer> useCount = buildUseCount(cfg);
        Set<IRInstruction> arithInsts = collectArithInsts(cfg);
        Map<IRInstruction, Expr> out = new LinkedHashMap<>();
        for (IRInstruction inst : arithInsts) {
            String dest = ssaDestName(inst);
            if (dest == null) {
                continue;
            }
            if (!isInlineable(dest, defOf, useCount, arithInsts, cfg)) {
                BuildResult br = buildTreeForRoot(inst, defOf, useCount, arithInsts, varRanks, cfg);
                out.put(inst, br.expr);
            }
        }
        return out;
    }

    // STEP 3
    /**
     * Recursively normalize {@code tree}: flatten same-op associative children, fold SUB children
     * of ADD into the ADD's sign vector, then sort each associative node's operands by ascending
     * rank. DIV is left binary. SUB is left binary unless its parent is ADD (handled there).
     */
    public static Expr sortOperands(Expr tree, Map<String, Integer> varRanks) {
        if (tree.isLeaf()) {
            return tree;
        }
        Bin b = (Bin) tree;
        // Recurse first so children are already normalized.
        for (int i = 0; i < b.operands.size(); i++) {
            b.operands.set(i, sortOperands(b.operands.get(i), varRanks));
        }
        switch (b.op) {
            case "add":
                return flattenAndSortAdd(b);
            case "mul":
            case "and":
            case "or":
                return flattenAndSortAssoc(b);
            case "sub":
            case "div":
            default:
                recomputeBinRank(b);
                return b;
        }
    }

    // STEP 4
    /**
     * One-level multiply distribution: for any {@code mul} whose operands include a low-rank
     * scalar and an {@code add} subtree, rewrite to {@code add(mul(low, hi1), mul(low, hi2)...)}.
     * Does not recurse into the rewritten subtree.
     */
    public static Expr distributeMultiply(Expr tree, Map<String, Integer> varRanks) {
        if (tree.isLeaf()) {
            return tree;
        }
        Bin b = (Bin) tree;
        // Recurse into operands first, but per spec only one level of distribution at the top.
        for (int i = 0; i < b.operands.size(); i++) {
            b.operands.set(i, distributeChildrenButDoNotRedistribute(b.operands.get(i), varRanks));
        }
        if (!"mul".equals(b.op) || b.operands.size() < 2) {
            recomputeBinRank(b);
            return b;
        }
        Expr lowest = b.operands.get(0);
        Expr addChild = null;
        int addIdx = -1;
        for (int i = 1; i < b.operands.size(); i++) {
            Expr o = b.operands.get(i);
            if (!o.isLeaf() && "add".equals(((Bin) o).op)) {
                boolean lowerThanAllAddOperands = true;
                Bin innerAdd = (Bin) o;
                for (Expr a : innerAdd.operands) {
                    if (lowest.rank >= a.rank) {
                        lowerThanAllAddOperands = false;
                        break;
                    }
                }
                if (lowerThanAllAddOperands) {
                    addChild = o;
                    addIdx = i;
                    break;
                }
            }
        }
        if (addChild == null) {
            recomputeBinRank(b);
            return b;
        }

        Bin innerAdd = (Bin) addChild;
        List<Expr> newAddOperands = new ArrayList<>();
        List<Integer> newAddSigns = new ArrayList<>();
        for (int i = 0; i < innerAdd.operands.size(); i++) {
            Expr hi = innerAdd.operands.get(i);
            int sign = innerAdd.signs == null ? 1 : innerAdd.signs.get(i);
            List<Expr> mulOperands = new ArrayList<>();
            mulOperands.add(deepCopy(lowest));
            mulOperands.add(deepCopy(hi));
            Bin mulNode = new Bin("mul", mulOperands, null);
            mulNode.rank = Math.max(lowest.rank, hi.rank);
            newAddOperands.add(mulNode);
            newAddSigns.add(sign);
        }
        // Keep the remaining factors of the original mul as additional add operands by re-multiplying.
        // (Only matters when the mul had > 2 operands.)
        if (b.operands.size() > 2) {
            List<Expr> rest = new ArrayList<>();
            for (int i = 0; i < b.operands.size(); i++) {
                if (i == 0 || i == addIdx) continue;
                rest.add(b.operands.get(i));
            }
            for (int i = 0; i < newAddOperands.size(); i++) {
                Expr mulNode = newAddOperands.get(i);
                Bin asBin = (Bin) mulNode;
                asBin.operands.addAll(deepCopyList(rest));
                int mx = asBin.operands.get(0).rank;
                for (Expr o : asBin.operands) mx = Math.max(mx, o.rank);
                asBin.rank = mx;
            }
        }
        Bin newAdd = new Bin("add", newAddOperands, newAddSigns);
        recomputeBinRank(newAdd);
        return newAdd;
    }

    /** Distribute children but DO NOT redistribute the rewritten subtree at this level. */
    private static Expr distributeChildrenButDoNotRedistribute(Expr tree, Map<String, Integer> varRanks) {
        if (tree.isLeaf()) {
            return tree;
        }
        Bin b = (Bin) tree;
        for (int i = 0; i < b.operands.size(); i++) {
            b.operands.set(i, distributeMultiply(b.operands.get(i), varRanks));
        }
        recomputeBinRank(b);
        return b;
    }

    /** Dump the (possibly reassociated) SSA form of {@code cfg} to stderr. */
    public static void printIR(CFG cfg) {
        System.err.println("==== Reassociated SSA (" + cfg.function.name + ") ====");
        for (BasicBlock b : cfg.basicBlocks) {
            System.err.println("block [" + b.getStartLine() + ".." + b.getEndLine() + "]");
            for (String[] phi : b.getPhiNodes()) {
                StringBuilder sb = new StringBuilder("  phi ").append(phi[1]).append(" = (");
                for (int i = 2; i < phi.length; i++) {
                    if (i > 2) sb.append(", ");
                    sb.append(phi[i]);
                }
                sb.append(")");
                System.err.println(sb);
            }
            List<IRInstruction> list = b.getSsaIRList();
            if (list != null) {
                for (IRInstruction inst : list) {
                    System.err.println("  " + inst);
                }
            }
        }
        System.err.println("==== end ====");
    }

    // --- Sorting helpers ---

    private static Expr flattenAndSortAdd(Bin add) {
        List<Expr> flatOps = new ArrayList<>();
        List<Integer> flatSigns = new ArrayList<>();
        for (int i = 0; i < add.operands.size(); i++) {
            int parentSign = add.signs == null ? 1 : add.signs.get(i);
            absorbIntoAdd(add.operands.get(i), parentSign, flatOps, flatSigns);
        }
        // Stable sort by rank ascending, then put positives before negatives at equal rank to make
        // emission start from a positive accumulator when possible.
        Integer[] perm = new Integer[flatOps.size()];
        for (int i = 0; i < perm.length; i++) perm[i] = i;
        final List<Expr> ops = flatOps;
        final List<Integer> sgs = flatSigns;
        Arrays.sort(perm, new Comparator<Integer>() {
            @Override
            public int compare(Integer a, Integer b) {
                int cmp = Integer.compare(ops.get(a).rank, ops.get(b).rank);
                if (cmp != 0) return cmp;
                return Integer.compare(sgs.get(b), sgs.get(a)); // +1 first
            }
        });
        List<Expr> sortedOps = new ArrayList<>(flatOps.size());
        List<Integer> sortedSigns = new ArrayList<>(flatOps.size());
        for (int p : perm) {
            sortedOps.add(flatOps.get(p));
            sortedSigns.add(flatSigns.get(p));
        }
        Bin out = new Bin("add", sortedOps, sortedSigns);
        recomputeBinRank(out);
        return out;
    }

    private static void absorbIntoAdd(Expr e, int parentSign, List<Expr> outOps, List<Integer> outSigns) {
        if (!e.isLeaf()) {
            Bin b = (Bin) e;
            if ("add".equals(b.op)) {
                for (int i = 0; i < b.operands.size(); i++) {
                    int childSign = b.signs == null ? 1 : b.signs.get(i);
                    absorbIntoAdd(b.operands.get(i), parentSign * childSign, outOps, outSigns);
                }
                return;
            }
            if ("sub".equals(b.op) && b.operands.size() == 2) {
                absorbIntoAdd(b.operands.get(0), parentSign, outOps, outSigns);
                absorbIntoAdd(b.operands.get(1), -parentSign, outOps, outSigns);
                return;
            }
        }
        outOps.add(e);
        outSigns.add(parentSign);
    }

    private static Expr flattenAndSortAssoc(Bin node) {
        List<Expr> flat = new ArrayList<>();
        for (Expr o : node.operands) {
            absorbSameOp(o, node.op, flat);
        }
        flat.sort(Comparator.comparingInt(o -> o.rank));
        Bin out = new Bin(node.op, flat, null);
        recomputeBinRank(out);
        return out;
    }

    private static void absorbSameOp(Expr e, String op, List<Expr> out) {
        if (!e.isLeaf()) {
            Bin b = (Bin) e;
            if (op.equals(b.op) && b.signs == null) {
                for (Expr o : b.operands) {
                    absorbSameOp(o, op, out);
                }
                return;
            }
        }
        out.add(e);
    }

    private static void recomputeBinRank(Bin b) {
        int r = 0;
        for (Expr o : b.operands) {
            r = Math.max(r, o.rank);
        }
        b.rank = r;
    }

    // --- Tree building ---

    private static final class BuildResult {
        final Expr expr;
        final Set<IRInstruction> absorbed;

        BuildResult(Expr expr, Set<IRInstruction> absorbed) {
            this.expr = expr;
            this.absorbed = absorbed;
        }
    }

    private static BuildResult buildTreeForRoot(
            IRInstruction root,
            Map<String, IRInstruction> defOf,
            Map<String, Integer> useCount,
            Set<IRInstruction> arithInsts,
            Map<String, Integer> varRanks,
            CFG cfg) {
        Set<IRInstruction> absorbed = new LinkedHashSet<>();
        Expr e = buildExprFromInst(root, defOf, useCount, arithInsts, varRanks, absorbed, cfg);
        return new BuildResult(e, absorbed);
    }

    private static Expr buildExprFromInst(
            IRInstruction inst,
            Map<String, IRInstruction> defOf,
            Map<String, Integer> useCount,
            Set<IRInstruction> arithInsts,
            Map<String, Integer> varRanks,
            Set<IRInstruction> absorbed,
            CFG cfg) {
        switch (inst.opCode) {
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR: {
                Expr left = leafOrInlineExpr(inst.operands[1], defOf, useCount, arithInsts, varRanks, absorbed, cfg);
                Expr right = leafOrInlineExpr(inst.operands[2], defOf, useCount, arithInsts, varRanks, absorbed, cfg);
                List<Expr> ops = new ArrayList<>(2);
                ops.add(left);
                ops.add(right);
                Bin b = new Bin(opNameOf(inst.opCode), ops, null);
                recomputeBinRank(b);
                return b;
            }
            default:
                String dest = ssaDestName(inst);
                int r = dest == null ? 0 : varRanks.getOrDefault(dest, 0);
                return new Leaf(dest == null ? "?" : dest, false, r);
        }
    }

    private static Expr leafOrInlineExpr(
            IROperand op,
            Map<String, IRInstruction> defOf,
            Map<String, Integer> useCount,
            Set<IRInstruction> arithInsts,
            Map<String, Integer> varRanks,
            Set<IRInstruction> absorbed,
            CFG cfg) {
        if (op instanceof IRConstantOperand) {
            return new Leaf(((IRConstantOperand) op).getValueString(), true, 0);
        }
        if (op instanceof IRVariableOperand) {
            String name = ((IRVariableOperand) op).getName();
            IRInstruction def = defOf.get(name);
            if (def != null
                    && arithInsts.contains(def)
                    && useCount.getOrDefault(name, 0) == 1
                    && !absorbed.contains(def)) {
                absorbed.add(def);
                return buildExprFromInst(def, defOf, useCount, arithInsts, varRanks, absorbed, cfg);
            }
            return new Leaf(name, false, varRanks.getOrDefault(name, 0));
        }
        return new Leaf(op.toString(), false, 0);
    }

    // --- Use counting / def mapping ---

    private static Map<String, IRInstruction> buildDefMap(CFG cfg) {
        Map<String, IRInstruction> defs = new HashMap<>();
        for (BasicBlock b : cfg.basicBlocks) {
            List<IRInstruction> list = b.getSsaIRList();
            if (list == null) continue;
            for (IRInstruction inst : list) {
                String d = ssaDestName(inst);
                if (d != null) defs.put(d, inst);
            }
        }
        return defs;
    }

    private static Map<String, Integer> buildUseCount(CFG cfg) {
        Map<String, Integer> count = new HashMap<>();
        for (BasicBlock b : cfg.basicBlocks) {
            for (String[] phi : b.getPhiNodes()) {
                for (int i = 2; i < phi.length; i++) {
                    incIfVariableLikeName(count, phi[i]);
                }
            }
            List<IRInstruction> list = b.getSsaIRList();
            if (list == null) continue;
            for (IRInstruction inst : list) {
                for (int[] idxs : useIndices(inst)) {
                    int idx = idxs[0];
                    if (idx >= inst.operands.length) continue;
                    IROperand o = inst.operands[idx];
                    if (o instanceof IRVariableOperand) {
                        incName(count, ((IRVariableOperand) o).getName());
                    }
                }
            }
        }
        return count;
    }

    private static void incIfVariableLikeName(Map<String, Integer> count, String n) {
        if (n == null || n.isEmpty()) return;
        if (isLiteralIntegerText(n)) return;
        incName(count, n);
    }

    private static boolean isLiteralIntegerText(String n) {
        if (n.isEmpty()) return false;
        int i = 0;
        if (n.charAt(0) == '-') i = 1;
        if (i >= n.length()) return false;
        for (; i < n.length(); i++) {
            if (!Character.isDigit(n.charAt(i))) return false;
        }
        return true;
    }

    private static void incName(Map<String, Integer> count, String n) {
        count.merge(n, 1, Integer::sum);
    }

    /** Returns the indices into {@code inst.operands} that hold a "use" (read) of a value. */
    private static List<int[]> useIndices(IRInstruction inst) {
        List<int[]> out = new ArrayList<>();
        switch (inst.opCode) {
            case ASSIGN:
                if (inst.operands.length >= 2) out.add(new int[]{1});
                if (inst.operands.length >= 3) out.add(new int[]{2});
                break;
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
                out.add(new int[]{1});
                out.add(new int[]{2});
                break;
            case BREQ:
            case BRNEQ:
            case BRLT:
            case BRGT:
            case BRLEQ:
            case BRGEQ:
                out.add(new int[]{1});
                out.add(new int[]{2});
                break;
            case RETURN:
                out.add(new int[]{0});
                break;
            case CALL:
                for (int i = 1; i < inst.operands.length; i++) out.add(new int[]{i});
                break;
            case CALLR:
                for (int i = 2; i < inst.operands.length; i++) out.add(new int[]{i});
                break;
            case ARRAY_STORE:
                out.add(new int[]{0});
                out.add(new int[]{1});
                out.add(new int[]{2});
                break;
            case ARRAY_LOAD:
                out.add(new int[]{1});
                out.add(new int[]{2});
                break;
            default:
                break;
        }
        return out;
    }

    private static Set<IRInstruction> collectArithInsts(CFG cfg) {
        Set<IRInstruction> s = new LinkedHashSet<>();
        for (BasicBlock b : cfg.basicBlocks) {
            List<IRInstruction> list = b.getSsaIRList();
            if (list == null) continue;
            for (IRInstruction inst : list) {
                switch (inst.opCode) {
                    case ADD:
                    case SUB:
                    case MULT:
                    case DIV:
                    case AND:
                    case OR:
                        s.add(inst);
                        break;
                    default:
                        break;
                }
            }
        }
        return s;
    }

    private static Map<IRInstruction, BasicBlock> mapInstrToBlock(CFG cfg) {
        Map<IRInstruction, BasicBlock> m = new HashMap<>();
        for (BasicBlock b : cfg.basicBlocks) {
            List<IRInstruction> list = b.getSsaIRList();
            if (list == null) continue;
            for (IRInstruction inst : list) {
                m.put(inst, b);
            }
        }
        return m;
    }

    private static boolean isInlineable(
            String dest,
            Map<String, IRInstruction> defOf,
            Map<String, Integer> useCount,
            Set<IRInstruction> arithInsts,
            CFG cfg) {
        IRInstruction def = defOf.get(dest);
        if (def == null) return false;
        if (!arithInsts.contains(def)) return false;
        if (useCount.getOrDefault(dest, 0) != 1) return false;
        // The single use must be in a reassociable arith op. Walk to find the user.
        for (BasicBlock b : cfg.basicBlocks) {
            for (String[] phi : b.getPhiNodes()) {
                for (int i = 2; i < phi.length; i++) {
                    if (dest.equals(phi[i])) {
                        return false;
                    }
                }
            }
            List<IRInstruction> list = b.getSsaIRList();
            if (list == null) continue;
            for (IRInstruction inst : list) {
                for (int[] idxs : useIndices(inst)) {
                    int idx = idxs[0];
                    if (idx >= inst.operands.length) continue;
                    IROperand op = inst.operands[idx];
                    if (op instanceof IRVariableOperand
                            && dest.equals(((IRVariableOperand) op).getName())) {
                        return arithInsts.contains(inst);
                    }
                }
            }
        }
        return false;
    }

    // --- Rank helpers ---

    private static int rankOperand(IROperand op, Map<String, Integer> ranks) {
        if (op instanceof IRConstantOperand) return 0;
        if (op instanceof IRVariableOperand) return ranks.getOrDefault(((IRVariableOperand) op).getName(), 0);
        return 0;
    }

    private static String ssaDestName(IRInstruction inst) {
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

    private static List<BasicBlock> reversePostorder(CFG cfg) {
        List<BasicBlock> post = new ArrayList<>();
        Set<BasicBlock> seen = new HashSet<>();
        dfsPost(cfg.basicBlocks.get(0), seen, post);
        Collections.reverse(post);
        for (BasicBlock b : cfg.basicBlocks) {
            if (!seen.contains(b)) {
                post.add(b);
            }
        }
        return post;
    }

    private static void dfsPost(BasicBlock b, Set<BasicBlock> seen, List<BasicBlock> out) {
        if (!seen.add(b)) return;
        for (BasicBlock s : b.getSuccessors()) {
            dfsPost(s, seen, out);
        }
        out.add(b);
    }

    private static String opNameOf(OpCode op) {
        switch (op) {
            case ADD: return "add";
            case SUB: return "sub";
            case MULT: return "mul";
            case DIV: return "div";
            case AND: return "and";
            case OR: return "or";
            default: return op.toString();
        }
    }

    private static OpCode opCodeOf(String name) {
        switch (name) {
            case "add": return OpCode.ADD;
            case "sub": return OpCode.SUB;
            case "mul": return OpCode.MULT;
            case "div": return OpCode.DIV;
            case "and": return OpCode.AND;
            case "or": return OpCode.OR;
            default: throw new IllegalStateException("unknown op " + name);
        }
    }

    // --- Emission ---

    private static int scanExistingRaCounter(IRFunction fn) {
        int max = 0;
        for (IRVariableOperand v : fn.variables) {
            String n = v.getName();
            if (n.startsWith(TEMP_PREFIX)) {
                try {
                    int k = Integer.parseInt(n.substring(TEMP_PREFIX.length()));
                    if (k > max) max = k;
                } catch (NumberFormatException ignore) {}
            }
        }
        return max;
    }

    private static void emit(
            CFG cfg,
            Map<IRInstruction, BuildResult> built,
            Map<IRInstruction, BasicBlock> blockOf,
            int seedCounter) {
        int[] counter = new int[]{seedCounter};
        // Map: root -> (block, sequence of new instructions producing root.dest)
        Map<IRInstruction, List<IRInstruction>> emittedFor = new LinkedHashMap<>();
        Set<IRInstruction> toDelete = new HashSet<>();

        for (Map.Entry<IRInstruction, BuildResult> e : built.entrySet()) {
            IRInstruction root = e.getKey();
            String dest = ssaDestName(root);
            if (dest == null) continue;
            List<IRInstruction> seq = new ArrayList<>();
            emitTree(e.getValue().expr, cfg.function, dest, counter, seq);
            emittedFor.put(root, seq);
            toDelete.addAll(e.getValue().absorbed);
        }

        for (BasicBlock b : cfg.basicBlocks) {
            List<IRInstruction> list = b.getSsaIRList();
            if (list == null) continue;
            List<IRInstruction> rewritten = new ArrayList<>(list.size());
            for (IRInstruction inst : list) {
                if (toDelete.contains(inst)) {
                    continue;
                }
                if (emittedFor.containsKey(inst)) {
                    rewritten.addAll(emittedFor.get(inst));
                } else {
                    rewritten.add(inst);
                }
            }
            b.setSsaIRList(rewritten);
        }
    }

    /** Emit instructions for {@code tree} producing {@code finalDest}. Returns {@code finalDest}. */
    private static String emitTree(Expr tree, IRFunction fn, String finalDest, int[] counter, List<IRInstruction> out) {
        if (tree.isLeaf()) {
            Leaf lf = (Leaf) tree;
            IRInstruction in = newInstruction(OpCode.ASSIGN);
            in.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), finalDest, in),
                    leafOperand(lf, in)
            };
            out.add(in);
            return finalDest;
        }
        Bin b = (Bin) tree;
        // Emit each non-leaf operand to a fresh temp; leaves stay inline.
        List<String> labels = new ArrayList<>(b.operands.size());
        for (Expr o : b.operands) {
            if (o.isLeaf()) {
                labels.add(((Leaf) o).label);
            } else {
                String t = freshTemp(fn, counter);
                emitTree(o, fn, t, counter, out);
                labels.add(t);
            }
        }
        emitOp(b, labels, fn, finalDest, counter, out);
        return finalDest;
    }

    private static void emitOp(
            Bin b, List<String> labels, IRFunction fn, String finalDest, int[] counter, List<IRInstruction> out) {
        switch (b.op) {
            case "add":
                emitAddChain(b, labels, fn, finalDest, counter, out);
                break;
            case "mul":
            case "and":
            case "or":
                emitAssocChain(opCodeOf(b.op), labels, fn, finalDest, counter, out);
                break;
            case "sub":
            case "div":
                IRInstruction in = newInstruction(opCodeOf(b.op));
                in.operands = new IROperand[]{
                        new IRVariableOperand(IRIntType.get(), finalDest, in),
                        labelToOperand(labels.get(0), in),
                        labelToOperand(labels.get(1), in)
                };
                out.add(in);
                break;
            default:
                throw new IllegalStateException("unhandled emit op " + b.op);
        }
    }

    private static void emitAddChain(
            Bin add, List<String> labels, IRFunction fn, String finalDest, int[] counter, List<IRInstruction> out) {
        List<Integer> signs = add.signs;
        List<Integer> posIdx = new ArrayList<>();
        List<Integer> negIdx = new ArrayList<>();
        for (int i = 0; i < labels.size(); i++) {
            int s = (signs == null) ? 1 : signs.get(i);
            if (s >= 0) posIdx.add(i);
            else negIdx.add(i);
        }

        int totalOps;
        if (posIdx.isEmpty()) {
            // negIdx.size() subs total: one "0 - neg0" plus (negIdx.size() - 1) chained subs.
            totalOps = negIdx.size();
        } else {
            totalOps = (posIdx.size() - 1) + negIdx.size();
        }

        // Degenerate: zero operands.
        if (posIdx.isEmpty() && negIdx.isEmpty()) {
            IRInstruction asg = newInstruction(OpCode.ASSIGN);
            asg.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), finalDest, asg),
                    constZero(asg)
            };
            out.add(asg);
            return;
        }

        // Degenerate: single positive operand, no subs -> assign.
        if (totalOps == 0) {
            IRInstruction asg = newInstruction(OpCode.ASSIGN);
            asg.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), finalDest, asg),
                    labelToOperand(labels.get(posIdx.get(0)), asg)
            };
            out.add(asg);
            return;
        }

        String acc;
        int nextPos = 0;
        int nextNeg = 0;
        int emitted = 0;

        if (!posIdx.isEmpty()) {
            acc = labels.get(posIdx.get(0));
            nextPos = 1;
        } else {
            boolean isOnly = (totalOps == 1);
            String dst = isOnly ? finalDest : freshTemp(fn, counter);
            IRInstruction in = newInstruction(OpCode.SUB);
            in.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), dst, in),
                    constZero(in),
                    labelToOperand(labels.get(negIdx.get(0)), in)
            };
            out.add(in);
            acc = dst;
            nextNeg = 1;
            emitted = 1;
        }

        while (nextPos < posIdx.size()) {
            boolean isLast = (emitted == totalOps - 1);
            String dst = isLast ? finalDest : freshTemp(fn, counter);
            IRInstruction in = newInstruction(OpCode.ADD);
            in.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), dst, in),
                    nameOperand(acc, in),
                    labelToOperand(labels.get(posIdx.get(nextPos)), in)
            };
            out.add(in);
            acc = dst;
            nextPos++;
            emitted++;
        }
        while (nextNeg < negIdx.size()) {
            boolean isLast = (emitted == totalOps - 1);
            String dst = isLast ? finalDest : freshTemp(fn, counter);
            IRInstruction in = newInstruction(OpCode.SUB);
            in.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), dst, in),
                    nameOperand(acc, in),
                    labelToOperand(labels.get(negIdx.get(nextNeg)), in)
            };
            out.add(in);
            acc = dst;
            nextNeg++;
            emitted++;
        }

        if (!acc.equals(finalDest)) {
            // Should not occur given the isLast accounting, but stays as a safety net.
            IRInstruction asg = newInstruction(OpCode.ASSIGN);
            asg.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), finalDest, asg),
                    nameOperand(acc, asg)
            };
            out.add(asg);
        }
    }

    private static void emitAssocChain(
            OpCode op, List<String> labels, IRFunction fn, String finalDest, int[] counter, List<IRInstruction> out) {
        if (labels.size() == 1) {
            IRInstruction asg = newInstruction(OpCode.ASSIGN);
            asg.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), finalDest, asg),
                    labelToOperand(labels.get(0), asg)
            };
            out.add(asg);
            return;
        }
        String acc = labels.get(0);
        for (int i = 1; i < labels.size(); i++) {
            boolean last = (i == labels.size() - 1);
            String dst = last ? finalDest : freshTemp(fn, counter);
            IRInstruction in = newInstruction(op);
            in.operands = new IROperand[]{
                    new IRVariableOperand(IRIntType.get(), dst, in),
                    nameOperand(acc, in),
                    labelToOperand(labels.get(i), in)
            };
            out.add(in);
            acc = dst;
        }
    }

    private static IROperand leafOperand(Leaf l, IRInstruction parent) {
        if (l.constant) {
            return new IRConstantOperand(IRIntType.get(), l.label, parent);
        }
        return new IRVariableOperand(IRIntType.get(), l.label, parent);
    }

    private static IROperand labelToOperand(String label, IRInstruction parent) {
        if (isLiteralIntegerText(label)) {
            return new IRConstantOperand(IRIntType.get(), label, parent);
        }
        return new IRVariableOperand(IRIntType.get(), label, parent);
    }

    private static IROperand nameOperand(String name, IRInstruction parent) {
        return new IRVariableOperand(IRIntType.get(), name, parent);
    }

    private static IROperand constZero(IRInstruction parent) {
        return new IRConstantOperand(IRIntType.get(), "0", parent);
    }

    private static IRInstruction newInstruction(OpCode opCode) {
        IRInstruction in = new IRInstruction();
        in.opCode = opCode;
        in.irLineNumber = -1;
        in.operands = new IROperand[0];
        return in;
    }

    private static String freshTemp(IRFunction fn, int[] counter) {
        String name;
        do {
            counter[0]++;
            name = TEMP_PREFIX + counter[0];
        } while (nameExistsInFunction(fn, name));
        fn.variables.add(new IRVariableOperand(IRIntType.get(), name, null));
        return name;
    }

    private static boolean nameExistsInFunction(IRFunction fn, String n) {
        for (IRVariableOperand p : fn.parameters) {
            if (p.getName().equals(n)) return true;
        }
        for (IRVariableOperand v : fn.variables) {
            if (v.getName().equals(n)) return true;
        }
        return false;
    }

    // --- Deep copy ---

    private static Expr deepCopy(Expr e) {
        if (e.isLeaf()) {
            Leaf l = (Leaf) e;
            return new Leaf(l.label, l.constant, l.rank);
        }
        Bin b = (Bin) e;
        List<Expr> ops = new ArrayList<>(b.operands.size());
        for (Expr o : b.operands) ops.add(deepCopy(o));
        List<Integer> signs = b.signs == null ? null : new ArrayList<>(b.signs);
        Bin out = new Bin(b.op, ops, signs);
        out.rank = b.rank;
        return out;
    }

    private static List<Expr> deepCopyList(List<Expr> in) {
        List<Expr> out = new ArrayList<>(in.size());
        for (Expr e : in) out.add(deepCopy(e));
        return out;
    }
}
