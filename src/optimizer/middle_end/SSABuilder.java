package middle_end;

import ir.*;
import ir.IRInstruction.OpCode;
import ir.datatype.*;
import ir.operand.*;

import java.util.*;
import java.util.regex.Pattern;

// SCOPE: SSA renaming covers int scalar variables only.
// Array variables (used in array_store/array_load as the array operand)
// are not renamed. The scalar result of array_load IS renamed.
// call/callr result variables ARE renamed (treated as fresh defs).
// This means array aliasing is NOT modeled in SSA form; any pass
// that needs array alias information must be conservative (kill all
// array_load expressions on any array_store).
//
// PACKAGING: New optimizer passes (LoopAnalysis, GlobalReassociation, GlobalValueNumbering,
// LazyCodeMotion, …) belong in this package under src/optimizer/middle_end/ with
// {@code package middle_end;}. Do not add top-level facades or wrappers under src/optimizer/.
//
/**
 * Pruned SSA construction (Cytron et al.) with internal phi rows
 * {@code ["phi", destBaseOrSsa, srcForPred0, ...]} per {@link BasicBlock}.
 */
public final class SSABuilder {

    private static final Pattern SSA_SUFFIX = Pattern.compile("#[0-9]+$");

    private SSABuilder() {}

    /** Build SSA form on {@code cfg}: dominators, DF, phis, renamed per-block {@link BasicBlock#setSsaIRList}. */
    public static void buildSSA(CFG cfg) {
        assertNoIllegalSSANames(cfg.function);
        assertReservedOptimizerPrefixes(cfg.function);
        for (BasicBlock bb : cfg.basicBlocks) {
            bb.getPhiNodes().clear();
            bb.setSsaIRList(null);
        }

        List<BasicBlock> blocks = cfg.basicBlocks;
        if (blocks.isEmpty()) {
            return;
        }
        BasicBlock entry = blocks.get(0);

        Map<BasicBlock, Set<BasicBlock>> dom = computeDominators(cfg, entry);
        Map<BasicBlock, BasicBlock> idom = computeImmediateDominators(cfg, entry, dom);
        Map<BasicBlock, Set<BasicBlock>> df = computeDominanceFrontiers(cfg, idom);

        Set<String> intScalars = collectIntScalarNames(cfg.function);
        Map<BasicBlock, Set<String>> gen = new HashMap<>();
        Map<BasicBlock, Set<String>> kill = new HashMap<>();
        computeGenKillIntScalars(cfg, intScalars, gen, kill);
        Map<BasicBlock, Set<String>> liveIn = new HashMap<>();
        Map<BasicBlock, Set<String>> liveOut = new HashMap<>();
        computeLiveVariables(blocks, gen, kill, liveIn, liveOut);

        Map<String, Set<BasicBlock>> defBlocks = collectDefBlocks(cfg, intScalars);
        insertPhiNodes(cfg, intScalars, defBlocks, df, liveIn);

        Map<BasicBlock, List<BasicBlock>> domChildren = buildDomTree(blocks, entry, idom);
        Map<String, Deque<String>> stacks = new HashMap<>();
        Map<String, Integer> versions = new HashMap<>();
        for (String v : intScalars) {
            stacks.put(v, new ArrayDeque<>());
            versions.put(v, 0);
        }

        for (IRVariableOperand p : cfg.function.parameters) {
            if (p.type != IRIntType.get()) {
                continue;
            }
            String s = p.getName();
            if (!intScalars.contains(s)) {
                continue;
            }
            String v0 = freshVersion(versions, s);
            stacks.get(s).push(v0);
        }

        for (BasicBlock bb : blocks) {
            List<IRInstruction> cloned = new ArrayList<>();
            for (IRInstruction inst : bb.getInstructions()) {
                cloned.add(cloneInstruction(inst));
            }
            bb.setSsaIRList(cloned);
        }

        renameBlock(entry, domChildren, stacks, versions, intScalars, cfg.function);
    }

    /** Lower internal phis to flat Tiger-IR {@code assign}s and strip {@code #n} suffixes; rebuild CFG. */
    public static void leavingSSA(CFG cfg) {
        leavingSSA(cfg, false);
    }

    /**
     * Same as {@link #leavingSSA(CFG)}; if {@code debug}, runs {@link CFG#assertFlatInvariants()} after
     * {@link CFG#rebuildCFG()}.
     */
    public static void leavingSSA(CFG cfg, boolean debug) {
        if (cfg.basicBlocks.isEmpty()) {
            return;
        }
        List<BasicBlock> order = new ArrayList<>(cfg.basicBlocks);
        int[] ssaTmpCounter = new int[]{0};

        for (BasicBlock b : order) {
            if (b.getPhiNodes().isEmpty()) {
                continue;
            }
            List<BasicBlock> preds = b.getPredecessors();
            for (int pi = 0; pi < preds.size(); pi++) {
                BasicBlock pred = preds.get(pi);
                insertPhiCopiesForPredecessor(cfg.function, b, pred, pi, ssaTmpCounter);
            }
        }

        List<IRInstruction> flat = new ArrayList<>();
        for (BasicBlock b : order) {
            List<IRInstruction> list = b.getSsaIRList();
            if (list != null) {
                flat.addAll(list);
            }
        }
        for (IRInstruction inst : flat) {
            stripSSAOperands(inst, cfg.function);
        }
        cfg.function.setInstructions(flat);
        for (BasicBlock b : cfg.basicBlocks) {
            b.getPhiNodes().clear();
            b.setSsaIRList(null);
        }
        cfg.rebuildCFG();
        if (debug) {
            cfg.assertFlatInvariants();
        }
    }

    /** Human-readable SSA dump (stderr only). */
    public static void printSSAFormToStderr(IRFunction fn, CFG cfg) {
        System.err.println("==== SSA (" + fn.name + ") ====");
        for (BasicBlock bb : cfg.basicBlocks) {
            System.err.println("block [" + bb.getStartLine() + ".." + bb.getEndLine() + "]");
            for (String[] phi : bb.getPhiNodes()) {
                System.err.println("  " + Arrays.toString(phi));
            }
            List<IRInstruction> list = bb.getSsaIRList();
            if (list != null) {
                for (IRInstruction inst : list) {
                    System.err.println("  " + inst);
                }
            }
        }
        System.err.println("==== end SSA ====");
    }

    // --- assertions ---

    private static void assertNoIllegalSSANames(IRFunction fn) {
        for (IRVariableOperand v : fn.parameters) {
            if (v.getName().indexOf('#') >= 0) {
                throw new IllegalStateException("Illegal '#' in parameter name: " + v.getName());
            }
        }
        for (IRVariableOperand v : fn.variables) {
            if (v.getName().indexOf('#') >= 0) {
                throw new IllegalStateException("Illegal '#' in variable name: " + v.getName());
            }
        }
        for (IRInstruction inst : fn.getInstructions()) {
            for (IROperand op : inst.operands) {
                if (op instanceof IRVariableOperand && ((IRVariableOperand) op).getName().indexOf('#') >= 0) {
                    throw new IllegalStateException("Illegal '#' in IR before SSA: " + inst);
                }
            }
        }
    }

    private static void assertReservedOptimizerPrefixes(IRFunction fn) {
        for (IRVariableOperand v : fn.parameters) {
            checkOptimizerTempPrefix(v.getName());
        }
        for (IRVariableOperand v : fn.variables) {
            checkOptimizerTempPrefix(v.getName());
        }
        for (IRInstruction inst : fn.getInstructions()) {
            for (IROperand op : inst.operands) {
                if (op instanceof IRVariableOperand) {
                    checkOptimizerTempPrefix(((IRVariableOperand) op).getName());
                }
            }
        }
    }

    /**
     * Reserved for lowering / later passes: {@code _ssa_tmp*}, {@code _ra*}, {@code _lcm*} must not
     * appear in user IR so compiler-inserted names never collide.
     */
    private static void checkOptimizerTempPrefix(String name) {
        if (name.startsWith("_ssa_tmp")
                || name.startsWith("_ra")
                || name.startsWith("_lcm")) {
            throw new IllegalStateException(
                    "Reserved optimizer prefix in identifier '" + name + "' (forbidden in input IR)");
        }
    }

    private static final class PhiEdge {
        final String destFlat;
        final String srcSsa;
        final IRType destType;

        PhiEdge(String destFlat, String srcSsa, IRType destType) {
            this.destFlat = destFlat;
            this.srcSsa = srcSsa;
            this.destType = destType;
        }
    }

    /**
     * Inserts all phi copies for one predecessor edge, breaking true 2-cycles (swap) with {@code _ssa_tmpN}.
     */
    private static void insertPhiCopiesForPredecessor(
            IRFunction fn, BasicBlock join, BasicBlock pred, int predIdx, int[] ssaTmpCounter) {
        List<String[]> phis = join.getPhiNodes();
        int nPred = join.getPredecessors().size();
        List<PhiEdge> edges = new ArrayList<>();
        for (String[] phi : phis) {
            if (phi.length < 2 + nPred) {
                throw new IllegalStateException("Phi arity mismatch for join block " + join.getStartLine());
            }
            String destSsa = phi[1];
            String src = phi[2 + predIdx];
            if (src == null || src.isEmpty()) {
                throw new IllegalStateException("Missing phi input for predecessor index " + predIdx);
            }
            String destFlat = stripSSASuffix(destSsa);
            IRType t = lookupIntScalarType(fn, baseName(destSsa));
            edges.add(new PhiEdge(destFlat, src, t));
        }

        Set<Integer> handled = new HashSet<>();
        List<IRInstruction> batch = new ArrayList<>();

        boolean progress = true;
        while (progress) {
            progress = false;
            outer:
            for (int i = 0; i < edges.size(); i++) {
                if (handled.contains(i)) {
                    continue;
                }
                for (int j = i + 1; j < edges.size(); j++) {
                    if (handled.contains(j)) {
                        continue;
                    }
                    PhiEdge a = edges.get(i);
                    PhiEdge b = edges.get(j);
                    if (isPhiSwap(a, b)) {
                        String tmp = freshSsaTmpName(ssaTmpCounter);
                        declareIntTempIfAbsent(fn, tmp);
                        // tmp = incoming for a's RHS (uses b); a = a_in; b = tmp  (incoming for b was a_in)
                        batch.add(makeAssignInstruction(tmp, IRIntType.get(), a.srcSsa, fn));
                        batch.add(makeAssignInstruction(a.destFlat, a.destType, b.srcSsa, fn));
                        batch.add(makeAssignInstruction(b.destFlat, b.destType, tmp, fn));
                        handled.add(i);
                        handled.add(j);
                        progress = true;
                        continue outer;
                    }
                }
            }
        }

        for (int i = 0; i < edges.size(); i++) {
            if (!handled.contains(i)) {
                PhiEdge e = edges.get(i);
                batch.add(makeAssignInstruction(e.destFlat, e.destType, e.srcSsa, fn));
            }
        }

        insertSequenceBeforeTerminator(pred, batch);
    }

    private static boolean isPhiSwap(PhiEdge x, PhiEdge y) {
        String srcBaseX = baseName(x.srcSsa);
        String srcBaseY = baseName(y.srcSsa);
        return srcBaseX.equals(y.destFlat) && srcBaseY.equals(x.destFlat);
    }

    private static String freshSsaTmpName(int[] counter) {
        return "_ssa_tmp" + (++counter[0]);
    }

    private static void declareIntTempIfAbsent(IRFunction fn, String name) {
        if (nameExistsInFunction(fn, name)) {
            return;
        }
        fn.variables.add(new IRVariableOperand(IRIntType.get(), name, null));
    }

    private static boolean nameExistsInFunction(IRFunction fn, String n) {
        for (IRVariableOperand p : fn.parameters) {
            if (p.getName().equals(n)) {
                return true;
            }
        }
        for (IRVariableOperand v : fn.variables) {
            if (v.getName().equals(n)) {
                return true;
            }
        }
        return false;
    }

    private static IRInstruction makeAssignInstruction(String destFlat, IRType destType, String rhs, IRFunction fn) {
        IRInstruction in = new IRInstruction();
        in.opCode = OpCode.ASSIGN;
        in.irLineNumber = -1;
        IROperand rhsOp = makeOperandFromSsaName(fn, rhs, in);
        in.operands = new IROperand[]{new IRVariableOperand(destType, destFlat, in), rhsOp};
        return in;
    }

    private static int terminatorIndex(List<IRInstruction> list) {
        int n = list.size();
        if (n == 0) {
            return 0;
        }
        IRInstruction last = list.get(n - 1);
        if (isTerminator(last)) {
            return n - 1;
        }
        return n;
    }

    private static void insertSequenceBeforeTerminator(BasicBlock pred, List<IRInstruction> copies) {
        if (copies.isEmpty()) {
            return;
        }
        List<IRInstruction> list = pred.getSsaIRList();
        if (list == null) {
            throw new IllegalStateException("predecessor missing ssaIRList");
        }
        int pos = terminatorIndex(list);
        for (IRInstruction c : copies) {
            list.add(pos, c);
            pos++;
        }
    }

    // --- dominators (Cooper, Harvey, Kennedy iterative) ---

    static Map<BasicBlock, Set<BasicBlock>> computeDominators(CFG cfg, BasicBlock entry) {
        List<BasicBlock> blocks = cfg.basicBlocks;
        Set<BasicBlock> all = new HashSet<>(blocks);
        Map<BasicBlock, Set<BasicBlock>> dom = new HashMap<>();
        for (BasicBlock b : blocks) {
            dom.put(b, new HashSet<>(all));
        }
        dom.put(entry, new HashSet<>(Collections.singleton(entry)));

        boolean changed = true;
        while (changed) {
            changed = false;
            for (BasicBlock b : blocks) {
                if (b == entry) {
                    continue;
                }
                List<BasicBlock> preds = b.getPredecessors();
                if (preds.isEmpty()) {
                    Set<BasicBlock> nb = new HashSet<>();
                    nb.add(b);
                    if (!dom.get(b).equals(nb)) {
                        dom.put(b, nb);
                        changed = true;
                    }
                    continue;
                }
                Set<BasicBlock> newDom = null;
                for (BasicBlock p : preds) {
                    Set<BasicBlock> dp = dom.get(p);
                    if (newDom == null) {
                        newDom = new HashSet<>(dp);
                    } else {
                        newDom.retainAll(dp);
                    }
                }
                newDom.add(b);
                if (!newDom.equals(dom.get(b))) {
                    dom.put(b, newDom);
                    changed = true;
                }
            }
        }
        return dom;
    }

    /**
     * Immediate dominator: unique strict dominator m of b such that m does not strictly dominate
     * any other strict dominator of b (Appel).
     */
    static Map<BasicBlock, BasicBlock> computeImmediateDominators(
            CFG cfg, BasicBlock entry, Map<BasicBlock, Set<BasicBlock>> dom) {
        Map<BasicBlock, BasicBlock> idom = new HashMap<>();
        idom.put(entry, null);
        for (BasicBlock b : cfg.basicBlocks) {
            if (b == entry) {
                continue;
            }
            Set<BasicBlock> s = new HashSet<>(dom.get(b));
            s.remove(b);
            BasicBlock chosen = null;
            for (BasicBlock m : s) {
                boolean mStrictlyDominatesAnotherInS = false;
                for (BasicBlock n : s) {
                    if (n == m) {
                        continue;
                    }
                    if (dom.get(n).contains(m)) {
                        mStrictlyDominatesAnotherInS = true;
                        break;
                    }
                }
                if (!mStrictlyDominatesAnotherInS) {
                    if (chosen == null || m.getStartLine() > chosen.getStartLine()) {
                        chosen = m;
                    }
                }
            }
            idom.put(b, chosen);
        }
        return idom;
    }

    static Map<BasicBlock, Set<BasicBlock>> computeDominanceFrontiers(
            CFG cfg, Map<BasicBlock, BasicBlock> idom) {
        Map<BasicBlock, Set<BasicBlock>> df = new HashMap<>();
        for (BasicBlock b : cfg.basicBlocks) {
            df.put(b, new HashSet<>());
        }
        for (BasicBlock b : cfg.basicBlocks) {
            for (BasicBlock y : b.getSuccessors()) {
                BasicBlock runner = b;
                BasicBlock idomY = idom.get(y);
                while (runner != null && idomY != null && runner != idomY) {
                    df.get(runner).add(y);
                    runner = idom.get(runner);
                }
            }
        }
        return df;
    }

    // --- liveness (int scalars) ---

    private static void computeGenKillIntScalars(
            CFG cfg,
            Set<String> intScalars,
            Map<BasicBlock, Set<String>> gen,
            Map<BasicBlock, Set<String>> kill) {
        for (BasicBlock bb : cfg.basicBlocks) {
            Set<String> k = new HashSet<>();
            for (IRInstruction inst : bb.getInstructions()) {
                for (String d : definedIntScalars(inst, intScalars)) {
                    k.add(d);
                }
            }
            Set<String> g = new HashSet<>();
            Set<String> defSoFar = new HashSet<>();
            for (IRInstruction inst : bb.getInstructions()) {
                for (String u : usedIntScalars(inst, intScalars)) {
                    if (!defSoFar.contains(u)) {
                        g.add(u);
                    }
                }
                defSoFar.addAll(definedIntScalars(inst, intScalars));
            }
            gen.put(bb, g);
            kill.put(bb, k);
        }
    }

    private static void computeLiveVariables(
            List<BasicBlock> blocks,
            Map<BasicBlock, Set<String>> gen,
            Map<BasicBlock, Set<String>> kill,
            Map<BasicBlock, Set<String>> liveIn,
            Map<BasicBlock, Set<String>> liveOut) {
        for (BasicBlock b : blocks) {
            liveIn.put(b, new HashSet<>());
            liveOut.put(b, new HashSet<>());
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (BasicBlock b : blocks) {
                Set<String> newOut = new HashSet<>();
                for (BasicBlock s : b.getSuccessors()) {
                    newOut.addAll(liveIn.get(s));
                }
                Set<String> newIn = new HashSet<>(gen.get(b));
                for (String x : liveOut.get(b)) {
                    if (!kill.get(b).contains(x)) {
                        newIn.add(x);
                    }
                }
                if (!newIn.equals(liveIn.get(b)) || !newOut.equals(liveOut.get(b))) {
                    liveIn.put(b, newIn);
                    liveOut.put(b, newOut);
                    changed = true;
                }
            }
        }
    }

    // --- def blocks & phi insertion ---

    private static Map<String, Set<BasicBlock>> collectDefBlocks(CFG cfg, Set<String> intScalars) {
        Map<String, Set<BasicBlock>> map = new HashMap<>();
        for (String v : intScalars) {
            map.put(v, new HashSet<>());
        }
        BasicBlock entry = cfg.basicBlocks.get(0);
        for (String v : intScalars) {
            if (isParameter(cfg.function, v)) {
                map.get(v).add(entry);
            }
        }
        for (BasicBlock bb : cfg.basicBlocks) {
            for (IRInstruction inst : bb.getInstructions()) {
                for (String d : definedIntScalars(inst, intScalars)) {
                    map.get(d).add(bb);
                }
            }
        }
        return map;
    }

    private static void insertPhiNodes(
            CFG cfg,
            Set<String> intScalars,
            Map<String, Set<BasicBlock>> defBlocks,
            Map<BasicBlock, Set<BasicBlock>> df,
            Map<BasicBlock, Set<String>> liveIn) {
        for (String v : intScalars) {
            Set<BasicBlock> work = new HashSet<>(defBlocks.get(v));
            Set<BasicBlock> hasPhi = new HashSet<>();
            while (!work.isEmpty()) {
                Iterator<BasicBlock> it = work.iterator();
                BasicBlock x = it.next();
                it.remove();
                for (BasicBlock y : df.getOrDefault(x, Collections.emptySet())) {
                    if (!liveIn.getOrDefault(y, Collections.emptySet()).contains(v)) {
                        continue; // pruned
                    }
                    if (hasPhi.contains(y)) {
                        continue;
                    }
                    int np = y.getPredecessors().size();
                    if (np < 2) {
                        continue;
                    }
                    String[] row = new String[2 + np];
                    row[0] = "phi";
                    row[1] = v;
                    for (int i = 0; i < np; i++) {
                        row[2 + i] = v;
                    }
                    y.getPhiNodes().add(row);
                    hasPhi.add(y);
                    if (!defBlocks.get(v).contains(y)) {
                        work.add(y);
                    }
                }
            }
        }
    }

    // --- renaming ---

    private static Map<BasicBlock, List<BasicBlock>> buildDomTree(
            List<BasicBlock> blocks, BasicBlock entry, Map<BasicBlock, BasicBlock> idom) {
        Map<BasicBlock, List<BasicBlock>> children = new HashMap<>();
        for (BasicBlock b : blocks) {
            children.put(b, new ArrayList<>());
        }
        for (BasicBlock b : blocks) {
            if (b == entry) {
                continue;
            }
            BasicBlock p = idom.get(b);
            if (p != null) {
                children.get(p).add(b);
            }
        }
        return children;
    }

    private static void renameBlock(
            BasicBlock B,
            Map<BasicBlock, List<BasicBlock>> domChildren,
            Map<String, Deque<String>> stacks,
            Map<String, Integer> versions,
            Set<String> intScalars,
            IRFunction fn) {

        List<String> pushedHere = new ArrayList<>();

        for (String[] phi : B.getPhiNodes()) {
            String base = phi[1];
            if (!intScalars.contains(base)) {
                continue;
            }
            String fresh = freshVersion(versions, base);
            phi[1] = fresh;
            stacks.get(base).push(fresh);
            pushedHere.add(base);
        }

        List<IRInstruction> list = B.getSsaIRList();
        if (list != null) {
            for (IRInstruction inst : list) {
                renameUsesInPlace(inst, stacks, intScalars, fn);
                List<String> defs = definedIntScalars(inst, intScalars);
                for (String base : defs) {
                    String fresh = freshVersion(versions, base);
                    renameDefInPlace(inst, base, fresh, fn);
                    stacks.get(base).push(fresh);
                    pushedHere.add(base);
                }
            }
        }

        for (BasicBlock s : B.getSuccessors()) {
            int idx = s.getPredecessors().indexOf(B);
            if (idx < 0) {
                continue;
            }
            for (String[] phi : s.getPhiNodes()) {
                if (phi.length < 2 + s.getPredecessors().size()) {
                    continue;
                }
                String base = baseName(phi[1]);
                if (!intScalars.contains(base)) {
                    continue;
                }
                Deque<String> st = stacks.get(base);
                String top = st.isEmpty() ? base : st.peek();
                phi[2 + idx] = top;
            }
        }

        for (BasicBlock c : domChildren.getOrDefault(B, Collections.emptyList())) {
            renameBlock(c, domChildren, stacks, versions, intScalars, fn);
        }

        for (int i = pushedHere.size() - 1; i >= 0; i--) {
            String base = pushedHere.get(i);
            if (!stacks.get(base).isEmpty()) {
                stacks.get(base).pop();
            }
        }
    }

    // --- helpers ---

    private static String baseName(String ssaName) {
        int h = ssaName.indexOf('#');
        return h < 0 ? ssaName : ssaName.substring(0, h);
    }

    private static String freshVersion(Map<String, Integer> versions, String base) {
        int c = versions.getOrDefault(base, 0);
        versions.put(base, c + 1);
        return base + "#" + c;
    }

    private static Set<String> collectIntScalarNames(IRFunction fn) {
        Set<String> s = new HashSet<>();
        for (IRVariableOperand v : fn.parameters) {
            if (v.type == IRIntType.get()) {
                s.add(v.getName());
            }
        }
        for (IRVariableOperand v : fn.variables) {
            if (v.type == IRIntType.get()) {
                s.add(v.getName());
            }
        }
        return s;
    }

    private static boolean isParameter(IRFunction fn, String name) {
        for (IRVariableOperand p : fn.parameters) {
            if (p.getName().equals(name)) {
                return true;
            }
        }
        return false;
    }

    private static IRType lookupIntScalarType(IRFunction fn, String base) {
        for (IRVariableOperand p : fn.parameters) {
            if (p.getName().equals(base) && p.type == IRIntType.get()) {
                return IRIntType.get();
            }
        }
        for (IRVariableOperand v : fn.variables) {
            if (v.getName().equals(base) && v.type == IRIntType.get()) {
                return IRIntType.get();
            }
        }
        return IRIntType.get();
    }

    private static IROperand makeOperandFromSsaName(IRFunction fn, String name, IRInstruction parent) {
        IRType t = IRIntType.get();
        if (isConstantName(name)) {
            return new IRConstantOperand(IRIntType.get(), name, parent);
        }
        return new IRVariableOperand(t, name, parent);
    }

    private static boolean isConstantName(String s) {
        return s.matches("^-?\\d+$");
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

    private static void stripSSAOperands(IRInstruction inst, IRFunction fn) {
        for (int i = 0; i < inst.operands.length; i++) {
            IROperand op = inst.operands[i];
            if (op instanceof IRVariableOperand) {
                IRVariableOperand v = (IRVariableOperand) op;
                String n = stripSSASuffix(v.getName());
                inst.operands[i] = new IRVariableOperand(v.type, n, inst);
            }
        }
    }

    static String stripSSASuffix(String name) {
        return SSA_SUFFIX.matcher(name).replaceAll("");
    }

    private static IRInstruction cloneInstruction(IRInstruction src) {
        IRInstruction c = new IRInstruction();
        c.opCode = src.opCode;
        c.irLineNumber = src.irLineNumber;
        c.operands = new IROperand[src.operands.length];
        for (int i = 0; i < src.operands.length; i++) {
            c.operands[i] = cloneOperand(src.operands[i], c);
        }
        return c;
    }

    private static IROperand cloneOperand(IROperand op, IRInstruction parent) {
        if (op instanceof IRVariableOperand) {
            IRVariableOperand v = (IRVariableOperand) op;
            return new IRVariableOperand(v.type, v.getName(), parent);
        }
        if (op instanceof IRConstantOperand) {
            IRConstantOperand c = (IRConstantOperand) op;
            return new IRConstantOperand(c.type, c.getValueString(), parent);
        }
        if (op instanceof IRLabelOperand) {
            return new IRLabelOperand(((IRLabelOperand) op).getName(), parent);
        }
        if (op instanceof IRFunctionOperand) {
            return new IRFunctionOperand(((IRFunctionOperand) op).getName(), parent);
        }
        throw new IllegalStateException("unknown operand");
    }

    private static void renameUsesInPlace(
            IRInstruction inst,
            Map<String, Deque<String>> stacks,
            Set<String> intScalars,
            IRFunction fn) {
        switch (inst.opCode) {
            case ASSIGN:
                if (inst.operands.length == 2) {
                    renameIfVar(inst, 1, stacks, intScalars, fn);
                } else {
                    renameIfVar(inst, 1, stacks, intScalars, fn);
                    renameIfVar(inst, 2, stacks, intScalars, fn);
                }
                break;
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
                renameIfVar(inst, 1, stacks, intScalars, fn);
                renameIfVar(inst, 2, stacks, intScalars, fn);
                break;
            case BREQ:
            case BRNEQ:
            case BRLT:
            case BRGT:
            case BRLEQ:
            case BRGEQ:
                renameIfVar(inst, 1, stacks, intScalars, fn);
                renameIfVar(inst, 2, stacks, intScalars, fn);
                break;
            case RETURN:
                renameIfVar(inst, 0, stacks, intScalars, fn);
                break;
            case CALL:
                for (int i = 1; i < inst.operands.length; i++) {
                    renameIfVar(inst, i, stacks, intScalars, fn);
                }
                break;
            case CALLR:
                for (int i = 2; i < inst.operands.length; i++) {
                    renameIfVar(inst, i, stacks, intScalars, fn);
                }
                break;
            case ARRAY_STORE:
                renameIfVar(inst, 0, stacks, intScalars, fn);
                renameIfVar(inst, 1, stacks, intScalars, fn);
                renameIfVar(inst, 2, stacks, intScalars, fn);
                break;
            case ARRAY_LOAD:
                renameIfVar(inst, 1, stacks, intScalars, fn);
                renameIfVar(inst, 2, stacks, intScalars, fn);
                break;
            default:
                break;
        }
    }

    private static void renameIfVar(
            IRInstruction inst,
            int idx,
            Map<String, Deque<String>> stacks,
            Set<String> intScalars,
            IRFunction fn) {
        IROperand op = inst.operands[idx];
        if (!(op instanceof IRVariableOperand)) {
            return;
        }
        IRVariableOperand v = (IRVariableOperand) op;
        String plain = baseName(v.getName());
        if (!intScalars.contains(plain)) {
            return;
        }
        Deque<String> st = stacks.get(plain);
        String top = st.isEmpty() ? plain : st.peek();
        inst.operands[idx] = new IRVariableOperand(v.type, top, inst);
    }

    private static void renameDefInPlace(IRInstruction inst, String base, String fresh, IRFunction fn) {
        if (inst.operands.length == 0) {
            return;
        }
        IROperand d0 = inst.operands[0];
        if (d0 instanceof IRVariableOperand) {
            IRVariableOperand v = (IRVariableOperand) d0;
            if (v.getName().equals(base)) {
                inst.operands[0] = new IRVariableOperand(v.type, fresh, inst);
            }
        }
    }

    private static List<String> usedIntScalars(IRInstruction inst, Set<String> intScalars) {
        List<String> u = new ArrayList<>();
        switch (inst.opCode) {
            case ASSIGN:
                if (inst.operands.length == 2) {
                    addIfIntScalar(u, inst.operands[1], intScalars);
                } else {
                    addIfIntScalar(u, inst.operands[1], intScalars);
                    addIfIntScalar(u, inst.operands[2], intScalars);
                }
                break;
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
                addIfIntScalar(u, inst.operands[1], intScalars);
                addIfIntScalar(u, inst.operands[2], intScalars);
                break;
            case BREQ:
            case BRNEQ:
            case BRLT:
            case BRGT:
            case BRLEQ:
            case BRGEQ:
                addIfIntScalar(u, inst.operands[1], intScalars);
                addIfIntScalar(u, inst.operands[2], intScalars);
                break;
            case RETURN:
                addIfIntScalar(u, inst.operands[0], intScalars);
                break;
            case CALL:
                for (int i = 1; i < inst.operands.length; i++) {
                    addIfIntScalar(u, inst.operands[i], intScalars);
                }
                break;
            case CALLR:
                for (int i = 2; i < inst.operands.length; i++) {
                    addIfIntScalar(u, inst.operands[i], intScalars);
                }
                break;
            case ARRAY_STORE:
                addIfIntScalar(u, inst.operands[0], intScalars);
                addIfIntScalar(u, inst.operands[1], intScalars);
                addIfIntScalar(u, inst.operands[2], intScalars);
                break;
            case ARRAY_LOAD:
                addIfIntScalar(u, inst.operands[1], intScalars);
                addIfIntScalar(u, inst.operands[2], intScalars);
                break;
            default:
                break;
        }
        return u;
    }

    private static void addIfIntScalar(List<String> u, IROperand op, Set<String> intScalars) {
        if (op instanceof IRVariableOperand) {
            String n = ((IRVariableOperand) op).getName();
            if (intScalars.contains(n)) {
                u.add(n);
            }
        }
    }

    private static List<String> definedIntScalars(IRInstruction inst, Set<String> intScalars) {
        List<String> d = new ArrayList<>();
        switch (inst.opCode) {
            case ASSIGN:
                if (inst.operands.length >= 2 && inst.operands[0] instanceof IRVariableOperand) {
                    String n = ((IRVariableOperand) inst.operands[0]).getName();
                    if (intScalars.contains(n)) {
                        d.add(n);
                    }
                }
                break;
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
                if (inst.operands[0] instanceof IRVariableOperand) {
                    String n = ((IRVariableOperand) inst.operands[0]).getName();
                    if (intScalars.contains(n)) {
                        d.add(n);
                    }
                }
                break;
            case CALLR:
                if (inst.operands[0] instanceof IRVariableOperand) {
                    String n = ((IRVariableOperand) inst.operands[0]).getName();
                    if (intScalars.contains(n)) {
                        d.add(n);
                    }
                }
                break;
            case ARRAY_LOAD:
                if (inst.operands[0] instanceof IRVariableOperand) {
                    String n = ((IRVariableOperand) inst.operands[0]).getName();
                    if (intScalars.contains(n)) {
                        d.add(n);
                    }
                }
                break;
            default:
                break;
        }
        return d;
    }
}
