package middle_end;

import ir.IRInstruction;
import ir.IRInstruction.OpCode;
import ir.operand.IRConstantOperand;
import ir.operand.IROperand;
import ir.operand.IRVariableOperand;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

// SCOPE: Global value numbering on SSA form (Alpern, Wegman, Zadeck 1988 — partition-based
// variant, not the SCC-based one). Operates on each BasicBlock.getSsaIRList()/getPhiNodes()
// after GlobalReassociation has normalized commutative operand order. Only renames operand
// occurrences in place; never adds, removes, or moves an instruction. Self-copies that result
// from merging (e.g. `assign, x, x`) are left for the downstream DCE pass.
//
// PACKAGING: middle_end. Runs before SSABuilder.leavingSSA. After this pass, every two value-
// producing defs (arith / phi) in the same value class have identical (op, operands) tuples
// when operand order is canonicalized for commutative ops.
//
// LIMITATIONS / DESIGN CHOICES:
// - Constants of the same text are merged into one class (e.g. `0` everywhere → one class).
// - Parameters get a unique class each (opaque inputs).
// - array_load and callr results each get their own unique class (no memory aliasing model).
// - 3-operand assign (`assign, arr, size, value` — array init) is treated as an opaque def.
// - 2-operand assign (scalar copy) merges the dest into the RHS's class.
// - Phi defs are compared as (phi, block-identity, operand-class-vector). Two phis in different
//   blocks never merge, matching the AWZ join-point semantics.
// - Refinement is iterate-to-fixed-point (split classes whose members have different
//   (op, operand-classes) signatures); a true worklist with reverse-use maps would be faster.
//
/**
 * AWZ partition-based GVN. See file header for scope and limitations.
 */
public final class GlobalValueNumbering {

    private GlobalValueNumbering() {}

    // --- Public API ---

    /** Run GVN. Equivalent to {@code run(cfg, false)}. */
    public static void run(CFG cfg) {
        run(cfg, false);
    }

    /**
     * Run GVN on SSA form of {@code cfg}. If {@code debug}, verifies the post-condition and dumps
     * the renamed SSA via {@link #printIR(CFG)}.
     */
    public static void run(CFG cfg, boolean debug) {
        if (cfg.basicBlocks.isEmpty()) {
            return;
        }
        Partition p = initPartitions(cfg);
        refinePartitions(p);
        renameToCanonical(p);
        if (debug) {
            verifyPostCondition(p);
            printIR(cfg);
        }
    }

    /**
     * STEP 1. Build the initial partition: one class per parameter, one class per distinct
     * constant value, one class for all phi dests, one class per arith opcode for arith dests,
     * unique class per opaque def ({@code array_load}, {@code callr}, 3-operand {@code assign}).
     * Scalar {@code assign} defs merge their dest into the RHS class.
     */
    public static Partition initPartitions(CFG cfg) {
        Partition p = new Partition(cfg);
        p.buildDefsAndRpo();
        p.assignInitialClasses();
        return p;
    }

    /**
     * STEP 2. Iterate-to-fixpoint partition refinement: split any class whose value-producing
     * members have different (op, operand-class) signatures.
     */
    public static void refinePartitions(Partition p) {
        boolean changed = true;
        while (changed) {
            changed = p.refineOnce();
        }
    }

    /**
     * STEP 3. Replace every variable use in instructions and phi nodes with the canonical name
     * (the first member of its value class in reverse-postorder).
     */
    public static void renameToCanonical(Partition p) {
        Map<Integer, String> canonical = new HashMap<>();
        for (String name : p.rpoNameOrder) {
            Integer c = p.nameToClass.get(name);
            if (c != null && !canonical.containsKey(c)) {
                canonical.put(c, name);
            }
        }
        p.canonicalByClass = canonical;
        p.applyRename();
    }

    /**
     * STEP 4. Verify the post-condition: for every pair of value-producing defs (arith or phi)
     * in the same value class, their (op, operand-names-after-rename) tuples match. Throws on
     * violation. Opaque defs (assign / array_load / callr / parameters) are excluded since they
     * have no comparable expression form.
     */
    public static void verifyPostCondition(Partition p) {
        for (Map.Entry<Integer, Set<String>> e : p.classToMembers.entrySet()) {
            Set<String> members = e.getValue();
            if (members.size() <= 1) {
                continue;
            }
            String firstSig = null;
            String firstSrc = null;
            for (String name : members) {
                String sig = p.valueProducingSignature(name);
                if (sig == null) {
                    continue;
                }
                if (firstSig == null) {
                    firstSig = sig;
                    firstSrc = name;
                } else if (!firstSig.equals(sig)) {
                    throw new IllegalStateException(
                            "GVN post-condition violated for class " + e.getKey()
                                    + ": " + firstSrc + " has sig '" + firstSig
                                    + "' but " + name + " has sig '" + sig + "'");
                }
            }
        }
    }

    /** Dump the renamed SSA form of {@code cfg} to stderr. */
    public static void printIR(CFG cfg) {
        System.err.println("==== GVN-renamed SSA (" + cfg.function.name + ") ====");
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

    // --- Partition state ---

    /**
     * Mutable partition state shared between the four steps. Public so callers can step through
     * the algorithm and inspect intermediate state.
     */
    public static final class Partition {
        public final CFG cfg;
        /** SSA name → class id. */
        public final Map<String, Integer> nameToClass = new HashMap<>();
        /** class id → its members. */
        public final Map<Integer, Set<String>> classToMembers = new LinkedHashMap<>();
        /** constant literal text → class id (constants of the same value share). */
        public final Map<String, Integer> constantClass = new HashMap<>();
        /** value-producing defs (arith / array_load / callr / scalar-assign / 3-op-assign). */
        public final Map<String, IRInstruction> defOf = new HashMap<>();
        /** phi defs keyed by dest name. */
        public final Map<String, String[]> phiOf = new HashMap<>();
        /** dest name → its block (for phi block-identity in signatures). */
        public final Map<String, BasicBlock> blockOfName = new HashMap<>();
        /** RPO order of all SSA dest names (parameters first, then RPO of blocks). */
        public final List<String> rpoNameOrder = new ArrayList<>();
        /** Canonical name per class id (set by renameToCanonical). */
        public Map<Integer, String> canonicalByClass;

        private int nextClassId = 0;

        Partition(CFG cfg) {
            this.cfg = cfg;
        }

        int newClass() {
            int id = nextClassId++;
            classToMembers.put(id, new LinkedHashSet<>());
            return id;
        }

        void assignNameToClass(String name, int classId) {
            Integer prev = nameToClass.get(name);
            if (prev != null) {
                if (prev == classId) {
                    return;
                }
                Set<String> oldMembers = classToMembers.get(prev);
                if (oldMembers != null) {
                    oldMembers.remove(name);
                }
            }
            nameToClass.put(name, classId);
            classToMembers.computeIfAbsent(classId, k -> new LinkedHashSet<>()).add(name);
        }

        int classOfOperand(IROperand op) {
            if (op instanceof IRConstantOperand) {
                String val = ((IRConstantOperand) op).getValueString();
                Integer c = constantClass.get(val);
                if (c != null) {
                    return c;
                }
                int id = newClass();
                constantClass.put(val, id);
                return id;
            }
            if (op instanceof IRVariableOperand) {
                String name = ((IRVariableOperand) op).getName();
                Integer c = nameToClass.get(name);
                return c == null ? -1 : c;
            }
            return -1;
        }

        int classOfPhiSource(String s) {
            if (isLiteralIntegerText(s)) {
                Integer c = constantClass.get(s);
                if (c != null) {
                    return c;
                }
                int id = newClass();
                constantClass.put(s, id);
                return id;
            }
            Integer c = nameToClass.get(s);
            return c == null ? -1 : c;
        }

        // --- init helpers ---

        void buildDefsAndRpo() {
            // Parameters first.
            for (IROperand p : cfg.function.parameters) {
                if (p instanceof IRVariableOperand) {
                    rpoNameOrder.add(((IRVariableOperand) p).getName());
                }
            }
            // Then RPO of blocks.
            List<BasicBlock> rpo = reversePostorder(cfg);
            for (BasicBlock b : rpo) {
                for (String[] phi : b.getPhiNodes()) {
                    phiOf.put(phi[1], phi);
                    blockOfName.put(phi[1], b);
                    rpoNameOrder.add(phi[1]);
                }
                List<IRInstruction> list = b.getSsaIRList();
                if (list == null) {
                    continue;
                }
                for (IRInstruction inst : list) {
                    String d = ssaDestName(inst);
                    if (d != null) {
                        defOf.put(d, inst);
                        blockOfName.put(d, b);
                        rpoNameOrder.add(d);
                    }
                }
            }
        }

        void assignInitialClasses() {
            // Each parameter gets its own class.
            for (IROperand p : cfg.function.parameters) {
                if (p instanceof IRVariableOperand) {
                    assignNameToClass(((IRVariableOperand) p).getName(), newClass());
                }
            }

            // Pre-seed constant classes by scanning all operands so refinement sees them.
            for (BasicBlock b : cfg.basicBlocks) {
                for (String[] phi : b.getPhiNodes()) {
                    for (int i = 2; i < phi.length; i++) {
                        if (isLiteralIntegerText(phi[i])) {
                            constantClass.computeIfAbsent(phi[i], k -> newClass());
                        }
                    }
                }
                List<IRInstruction> list = b.getSsaIRList();
                if (list == null) {
                    continue;
                }
                for (IRInstruction inst : list) {
                    for (IROperand op : inst.operands) {
                        if (op instanceof IRConstantOperand) {
                            String v = ((IRConstantOperand) op).getValueString();
                            constantClass.computeIfAbsent(v, k -> newClass());
                        }
                    }
                }
            }

            // Coarse initial class per kind: one for all phi dests, one per arith opcode.
            int phiClass = newClass();
            Map<OpCode, Integer> arithClass = new HashMap<>();
            arithClass.put(OpCode.ADD, newClass());
            arithClass.put(OpCode.SUB, newClass());
            arithClass.put(OpCode.MULT, newClass());
            arithClass.put(OpCode.DIV, newClass());
            arithClass.put(OpCode.AND, newClass());
            arithClass.put(OpCode.OR, newClass());

            // Walk in RPO order so non-phi defs precede their uses (assigns can see their RHS).
            for (String name : rpoNameOrder) {
                if (nameToClass.containsKey(name)) {
                    continue; // already classified (parameter)
                }
                String[] phi = phiOf.get(name);
                if (phi != null) {
                    assignNameToClass(name, phiClass);
                    continue;
                }
                IRInstruction inst = defOf.get(name);
                if (inst == null) {
                    continue;
                }
                switch (inst.opCode) {
                    case ADD:
                    case SUB:
                    case MULT:
                    case DIV:
                    case AND:
                    case OR:
                        assignNameToClass(name, arithClass.get(inst.opCode));
                        break;
                    case ASSIGN:
                        if (inst.operands.length == 2) {
                            // Scalar copy: dest joins RHS's class.
                            int c = classOfOperand(inst.operands[1]);
                            if (c < 0) {
                                c = newClass();
                            }
                            assignNameToClass(name, c);
                        } else {
                            // 3-operand assign (array init): opaque, unique class.
                            assignNameToClass(name, newClass());
                        }
                        break;
                    case ARRAY_LOAD:
                    case CALLR:
                    default:
                        assignNameToClass(name, newClass());
                        break;
                }
            }
        }

        // --- refinement ---

        boolean refineOnce() {
            boolean splitHappened = false;
            // Snapshot the list of class ids; we'll mutate classToMembers during iteration.
            List<Integer> classIds = new ArrayList<>(classToMembers.keySet());
            for (Integer cid : classIds) {
                Set<String> members = classToMembers.get(cid);
                if (members == null || members.size() <= 1) {
                    continue;
                }
                Map<String, Set<String>> bySig = new LinkedHashMap<>();
                for (String name : new ArrayList<>(members)) {
                    String sig = refinementSignature(name);
                    if (sig == null) {
                        // Member without a comparable signature (parameter, opaque). Treat each
                        // such member as its own group ("LEAF:<name>" already returned).
                        sig = "LEAF:" + name;
                    }
                    bySig.computeIfAbsent(sig, k -> new LinkedHashSet<>()).add(name);
                }
                if (bySig.size() <= 1) {
                    continue;
                }
                // Keep the first/largest group in the original class; move the rest to new classes.
                int largestSize = -1;
                String largestKey = null;
                for (Map.Entry<String, Set<String>> e : bySig.entrySet()) {
                    if (e.getValue().size() > largestSize) {
                        largestSize = e.getValue().size();
                        largestKey = e.getKey();
                    }
                }
                for (Map.Entry<String, Set<String>> e : bySig.entrySet()) {
                    if (e.getKey().equals(largestKey)) {
                        continue;
                    }
                    int newId = newClass();
                    for (String n : e.getValue()) {
                        assignNameToClass(n, newId);
                    }
                    splitHappened = true;
                }
            }
            return splitHappened;
        }

        String refinementSignature(String name) {
            String[] phi = phiOf.get(name);
            if (phi != null) {
                BasicBlock bb = blockOfName.get(name);
                StringBuilder sb = new StringBuilder("PHI:");
                sb.append(System.identityHashCode(bb)).append(':');
                for (int i = 2; i < phi.length; i++) {
                    sb.append(classOfPhiSource(phi[i])).append(',');
                }
                return sb.toString();
            }
            IRInstruction def = defOf.get(name);
            if (def == null) {
                // Parameter: leaf, unique signature by name so it never merges with another.
                return null;
            }
            switch (def.opCode) {
                case ADD:
                case SUB:
                case MULT:
                case DIV:
                case AND:
                case OR: {
                    int c1 = classOfOperand(def.operands[1]);
                    int c2 = classOfOperand(def.operands[2]);
                    if (isCommutative(def.opCode)) {
                        if (c1 > c2) {
                            int t = c1;
                            c1 = c2;
                            c2 = t;
                        }
                    }
                    return def.opCode.toString() + ":" + c1 + "," + c2;
                }
                default:
                    // Opaque defs are singletons; signature does not need to compare equal.
                    return null;
            }
        }

        String valueProducingSignature(String name) {
            String[] phi = phiOf.get(name);
            if (phi != null) {
                BasicBlock bb = blockOfName.get(name);
                StringBuilder sb = new StringBuilder("PHI:");
                sb.append(System.identityHashCode(bb)).append(':');
                for (int i = 2; i < phi.length; i++) {
                    sb.append(phi[i]).append(',');
                }
                return sb.toString();
            }
            IRInstruction def = defOf.get(name);
            if (def == null) {
                return null;
            }
            switch (def.opCode) {
                case ADD:
                case SUB:
                case MULT:
                case DIV:
                case AND:
                case OR: {
                    String n1 = operandText(def.operands[1]);
                    String n2 = operandText(def.operands[2]);
                    if (isCommutative(def.opCode) && n1.compareTo(n2) > 0) {
                        String t = n1;
                        n1 = n2;
                        n2 = t;
                    }
                    return def.opCode.toString() + ":" + n1 + "," + n2;
                }
                default:
                    return null;
            }
        }

        // --- rename ---

        void applyRename() {
            for (BasicBlock b : cfg.basicBlocks) {
                for (String[] phi : b.getPhiNodes()) {
                    for (int i = 2; i < phi.length; i++) {
                        String s = phi[i];
                        if (isLiteralIntegerText(s)) {
                            continue;
                        }
                        Integer c = nameToClass.get(s);
                        if (c == null) {
                            continue;
                        }
                        String canon = canonicalByClass.get(c);
                        if (canon != null) {
                            phi[i] = canon;
                        }
                    }
                }
                List<IRInstruction> list = b.getSsaIRList();
                if (list == null) {
                    continue;
                }
                for (IRInstruction inst : list) {
                    int[] uses = useIndices(inst);
                    for (int idx : uses) {
                        if (idx >= inst.operands.length) {
                            continue;
                        }
                        IROperand op = inst.operands[idx];
                        if (!(op instanceof IRVariableOperand)) {
                            continue;
                        }
                        IRVariableOperand v = (IRVariableOperand) op;
                        Integer c = nameToClass.get(v.getName());
                        if (c == null) {
                            continue;
                        }
                        String canon = canonicalByClass.get(c);
                        if (canon != null && !canon.equals(v.getName())) {
                            inst.operands[idx] = new IRVariableOperand(v.type, canon, inst);
                        }
                    }
                }
            }
        }
    }

    // --- statics ---

    private static String operandText(IROperand op) {
        if (op instanceof IRConstantOperand) {
            return ((IRConstantOperand) op).getValueString();
        }
        if (op instanceof IRVariableOperand) {
            return ((IRVariableOperand) op).getName();
        }
        return op == null ? "null" : op.toString();
    }

    private static boolean isCommutative(OpCode op) {
        switch (op) {
            case ADD:
            case MULT:
            case AND:
            case OR:
                return true;
            default:
                return false;
        }
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

    /** Indices into {@code inst.operands} that are read uses (renamable). */
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
                int[] r = new int[inst.operands.length - 1];
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

    private static boolean isLiteralIntegerText(String n) {
        if (n == null || n.isEmpty()) return false;
        int i = 0;
        if (n.charAt(0) == '-') i = 1;
        if (i >= n.length()) return false;
        for (; i < n.length(); i++) {
            if (!Character.isDigit(n.charAt(i))) return false;
        }
        return true;
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
}
