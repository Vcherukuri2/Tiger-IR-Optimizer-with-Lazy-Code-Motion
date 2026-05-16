package middle_end;

import ir.IRFunction;
import ir.IRInstruction;
import ir.IRInstruction.OpCode;
import ir.datatype.IRIntType;
import ir.operand.IRConstantOperand;
import ir.operand.IRFunctionOperand;
import ir.operand.IRLabelOperand;
import ir.operand.IROperand;
import ir.operand.IRVariableOperand;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

// SCOPE: Lazy Code Motion (Knoop, Rüthing, Steffen 1992) — the 6-equation bitvector
// formulation. Runs AFTER SSABuilder.leavingSSA on flat Tiger-IR (no '#' suffixes, no
// internal phi rows). Expressions are tuples (op, op1, op2) keyed by canonical text from
// upstream GVN renaming. Each distinct triple gets its own bit. Operates per IRFunction.
//
// PACKAGING: middle_end. Public entry is run(cfg [, debug]). DCE / RemoveEmptyBlocks follow.
//
// CORRECTNESS ARGUMENT (no path-length increase):
//   For every block b with e ∈ INSERT(b), the equations guarantee e ∈ antOut(b), meaning
//   e is downsafe at b's exit — every path leaving b was going to compute e anyway. Hoisting
//   to b's exit therefore never adds a computation to any path. assertDownsafeInserts()
//   re-checks this in -debug mode as a guard against equation bugs.
//
// LIMITATIONS / DESIGN CHOICES:
//   - Critical edges are NOT pre-split. The KRS equations still produce correct (path-safe)
//     placements with end-of-block insertion; only optimality (fewer redundant computations
//     on uncritical edges) is sacrificed. SPLIT_LABEL_PREFIX is reserved for a future pass.
//   - call / callr instructions are full barriers: kill ALL expressions in their block.
//   - array_store, a, arr, i kills every array_load expression of `arr` (conservatively
//     all array_load expressions if the array name is unknown — matches the SSABuilder
//     scope note that array aliasing isn't modeled).
//   - assign copies are treated as expressions with op = ASSIGN (per user spec). LCM may
//     therefore introduce redundant temp-then-assign sequences that DCE folds afterward.
//   - Non-arith ops (goto, br*, return, label, array_store, call) don't define expressions.
//   - 3-operand assign (array initializer) is opaque: not an LCM expression.
//   - The "used" backward equation follows the standard Knoop form
//        usedIn(b) = (use(b) ∪ usedOut(b)) \ latest(b)
//
// TRANSFORMATION (Knoop / Engineer's-Compiler style, applied per block on the FIRST
// occurrence of each expression):
//   KEEP_SITE     = use(b) ∩ latest(b) ∩ usedOut(b)
//                   → split `x = compute(e)` into `t_e = compute(e); x = t_e`
//                     (the original site IS the insertion point — no duplicate emit at end)
//   REPLACE_SITE  = use(b) ∩ ¬latest(b)
//                   → `x = compute(e)`  becomes  `x = t_e`   (t_e set by upstream KEEP/PURE)
//   PURE_INSERT   = latest(b) ∩ usedOut(b) ∩ ¬use(b)
//                   → emit `t_e = compute(e)` before b's terminator (no existing site to merge)
//   DO_NOTHING    = use(b) ∩ latest(b) ∩ ¬usedOut(b)
//                   → leave the original site untouched (value not needed downstream)
// This is the placement decomposition that gives the textbook LCM result (no insertion is
// ever co-located with an unaltered original computation) and is what makes the no-
// regression claim hold on simple diamond and loop-invariant patterns.
//
/**
 * Lazy Code Motion (Knoop–Rüthing–Steffen 1992), bitvector formulation. See file header
 * for scope, correctness argument, and limitations.
 */
public final class LazyCodeMotion {

    /** Fresh-temp prefix for hoisted expression computations. */
    public static final String TEMP_PREFIX = "_lcm_t";
    /** Reserved for future critical-edge splitting (not used in this implementation). */
    public static final String SPLIT_LABEL_PREFIX = "_lcm_split_";

    private LazyCodeMotion() {}

    // --- public API ---

    public static void run(CFG cfg) {
        run(cfg, false);
    }

    public static void run(CFG cfg, boolean debug) {
        if (cfg.basicBlocks.isEmpty()) {
            return;
        }
        assertReservedPrefixesUnused(cfg.function);

        Context c = new Context(cfg);
        c.buildExpressionIndex();
        if (c.M == 0) {
            return;
        }
        computeLocalUseKill(c);
        computeAnticipated(c);
        computeAvailable(c);
        computeEarliest(c);
        computePostponable(c);
        computeLatest(c);
        computeUsed(c);

        if (debug) {
            c.printDataflow();
        }

        applyTransformations(c);

        if (debug) {
            assertDownsafeInserts(c);
        }

        cfg.rebuildCFG();
        if (debug) {
            cfg.assertFlatInvariants();
        }
    }

    /** Dump every bitvector for diagnostic purposes. */
    public static void printIR(CFG cfg) {
        System.err.println("==== LCM IR (" + cfg.function.name + ") ====");
        for (BasicBlock b : cfg.basicBlocks) {
            System.err.println("block [" + b.getStartLine() + ".." + b.getEndLine() + "]");
            for (IRInstruction inst : b.getInstructions()) {
                System.err.println("  " + inst);
            }
        }
        System.err.println("==== end ====");
    }

    // --- equation methods (each KRS equation gets its own static method) ---

    /**
     * Local sets: {@code use(b)} (upward-exposed expression computations) and
     * {@code kill(b)} (expressions killed by some instruction in b — either an operand is
     * redefined, a call/callr executes, or an array_store invalidates array_load expressions
     * of the same array).
     */
    static void computeLocalUseKill(Context c) {
        c.use = newBitSetArr(c.N);
        c.kill = newBitSetArr(c.N);
        for (int bi = 0; bi < c.N; bi++) {
            BasicBlock b = c.blocks.get(bi);
            BitSet killedSoFar = new BitSet();
            BitSet useB = new BitSet();
            for (IRInstruction inst : b.getInstructions()) {
                Integer eid = c.expressionIdOf(inst);
                if (eid != null && !killedSoFar.get(eid)) {
                    useB.set(eid);
                }
                c.applyInstructionKills(inst, killedSoFar);
            }
            c.use[bi] = useB;
            c.kill[bi] = killedSoFar;
        }
    }

    /**
     * anticipatedIn / anticipatedOut. Backward dataflow:
     *   antIn(b)  = use(b) ∪ (antOut(b) \ kill(b))
     *   antOut(b) = ∩ over s ∈ succ(b) of antIn(s),  ∅ if no successors
     * Initialized to ALL on the inside (greatest fixed point); ∅ at exit blocks.
     */
    static void computeAnticipated(Context c) {
        c.antIn = newBitSetArr(c.N);
        c.antOut = newBitSetArr(c.N);
        for (int i = 0; i < c.N; i++) {
            c.antIn[i] = c.allBits();
            c.antOut[i] = c.allBits();
        }
        for (int i = 0; i < c.N; i++) {
            if (c.blocks.get(i).getSuccessors().isEmpty()) {
                c.antOut[i] = new BitSet();
            }
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = c.N - 1; i >= 0; i--) {
                BasicBlock b = c.blocks.get(i);
                List<BasicBlock> succs = b.getSuccessors();
                BitSet newOut;
                if (succs.isEmpty()) {
                    newOut = new BitSet();
                } else {
                    newOut = c.allBits();
                    for (BasicBlock s : succs) {
                        int si = c.indexOf(s);
                        if (si < 0) continue;
                        newOut.and(c.antIn[si]);
                    }
                }
                BitSet newIn = (BitSet) newOut.clone();
                newIn.andNot(c.kill[i]);
                newIn.or(c.use[i]);
                if (!newIn.equals(c.antIn[i]) || !newOut.equals(c.antOut[i])) {
                    c.antIn[i] = newIn;
                    c.antOut[i] = newOut;
                    changed = true;
                }
            }
        }
    }

    /**
     * availableIn / availableOut. Forward dataflow:
     *   availIn(b)  = ∩ over p ∈ pred(b) of availOut(p),  ∅ at entry
     *   availOut(b) = (antIn(b) ∪ availIn(b)) \ kill(b)
     */
    static void computeAvailable(Context c) {
        c.availIn = newBitSetArr(c.N);
        c.availOut = newBitSetArr(c.N);
        for (int i = 0; i < c.N; i++) {
            c.availIn[i] = c.allBits();
            c.availOut[i] = c.allBits();
        }
        c.availIn[0] = new BitSet();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < c.N; i++) {
                BasicBlock b = c.blocks.get(i);
                List<BasicBlock> preds = b.getPredecessors();
                BitSet newIn;
                if (i == 0 || preds.isEmpty()) {
                    newIn = new BitSet();
                } else {
                    newIn = c.allBits();
                    for (BasicBlock p : preds) {
                        int pi = c.indexOf(p);
                        if (pi < 0) continue;
                        newIn.and(c.availOut[pi]);
                    }
                }
                BitSet newOut = (BitSet) c.antIn[i].clone();
                newOut.or(newIn);
                newOut.andNot(c.kill[i]);
                if (!newIn.equals(c.availIn[i]) || !newOut.equals(c.availOut[i])) {
                    c.availIn[i] = newIn;
                    c.availOut[i] = newOut;
                    changed = true;
                }
            }
        }
    }

    /**
     * earliest(b) = ∪ over p ∈ pred(b) of (antIn(b) \ availOut(p)).
     * For the entry block, treats the (absent) virtual pred as having availOut = ∅, so
     *   earliest(entry) = antIn(entry).
     */
    static void computeEarliest(Context c) {
        c.earliest = newBitSetArr(c.N);
        for (int i = 0; i < c.N; i++) {
            BasicBlock b = c.blocks.get(i);
            List<BasicBlock> preds = b.getPredecessors();
            BitSet e = new BitSet();
            if (i == 0 || preds.isEmpty()) {
                e.or(c.antIn[i]);
            } else {
                for (BasicBlock p : preds) {
                    int pi = c.indexOf(p);
                    if (pi < 0) continue;
                    BitSet edge = (BitSet) c.antIn[i].clone();
                    edge.andNot(c.availOut[pi]);
                    e.or(edge);
                }
            }
            c.earliest[i] = e;
        }
    }

    /**
     * postponableIn / postponableOut. Forward dataflow:
     *   postIn(b)  = ∩ over p ∈ pred(b) of postOut(p),  ∅ at entry
     *   postOut(b) = (earliest(b) ∪ postIn(b)) \ use(b)
     */
    static void computePostponable(Context c) {
        c.postIn = newBitSetArr(c.N);
        c.postOut = newBitSetArr(c.N);
        for (int i = 0; i < c.N; i++) {
            c.postIn[i] = c.allBits();
            c.postOut[i] = c.allBits();
        }
        c.postIn[0] = new BitSet();
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < c.N; i++) {
                BasicBlock b = c.blocks.get(i);
                List<BasicBlock> preds = b.getPredecessors();
                BitSet newIn;
                if (i == 0 || preds.isEmpty()) {
                    newIn = new BitSet();
                } else {
                    newIn = c.allBits();
                    for (BasicBlock p : preds) {
                        int pi = c.indexOf(p);
                        if (pi < 0) continue;
                        newIn.and(c.postOut[pi]);
                    }
                }
                BitSet newOut = (BitSet) c.earliest[i].clone();
                newOut.or(newIn);
                newOut.andNot(c.use[i]);
                if (!newIn.equals(c.postIn[i]) || !newOut.equals(c.postOut[i])) {
                    c.postIn[i] = newIn;
                    c.postOut[i] = newOut;
                    changed = true;
                }
            }
        }
    }

    /**
     * latest(b) = (earliest(b) ∪ postIn(b))
     *           ∩ (use(b) ∪ ¬(∩ over s ∈ succ(b) of (earliest(s) ∪ postIn(s)))).
     * For terminal blocks the inner ∩ over an empty successor set is treated as ∅, so the
     * "cannot defer further" predicate is universally true and latest(b) collapses to
     * (earliest(b) ∪ postIn(b)).
     */
    static void computeLatest(Context c) {
        c.latest = newBitSetArr(c.N);
        for (int i = 0; i < c.N; i++) {
            BasicBlock b = c.blocks.get(i);
            BitSet left = (BitSet) c.earliest[i].clone();
            left.or(c.postIn[i]);

            List<BasicBlock> succs = b.getSuccessors();
            BitSet succInter;
            if (succs.isEmpty()) {
                succInter = new BitSet();
            } else {
                succInter = c.allBits();
                for (BasicBlock s : succs) {
                    int si = c.indexOf(s);
                    if (si < 0) continue;
                    BitSet sset = (BitSet) c.earliest[si].clone();
                    sset.or(c.postIn[si]);
                    succInter.and(sset);
                }
            }
            BitSet notSuccInter = c.allBits();
            notSuccInter.andNot(succInter);

            BitSet right = (BitSet) c.use[i].clone();
            right.or(notSuccInter);

            BitSet lat = (BitSet) left.clone();
            lat.and(right);
            c.latest[i] = lat;
        }
    }

    /**
     * usedIn / usedOut. Backward dataflow:
     *   usedOut(b) = ∪ over s ∈ succ(b) of usedIn(s)
     *   usedIn(b)  = (use(b) ∪ usedOut(b)) \ latest(b)
     *
     * This is the standard Knoop form. Combined with the user-spec DELETE rule
     *   DELETE(b) = use(b) ∩ ¬(latest(b) ∪ usedIn(b))
     * it simplifies to the equivalent and well-known
     *   DELETE(b) = use(b) ∩ ¬latest(b) ∩ ¬usedOut(b)
     * which we apply directly in {@link #applyTransformations(Context)}.
     */
    static void computeUsed(Context c) {
        c.usedIn = newBitSetArr(c.N);
        c.usedOut = newBitSetArr(c.N);
        for (int i = 0; i < c.N; i++) {
            c.usedIn[i] = new BitSet();
            c.usedOut[i] = new BitSet();
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = c.N - 1; i >= 0; i--) {
                BasicBlock b = c.blocks.get(i);
                BitSet newOut = new BitSet();
                for (BasicBlock s : b.getSuccessors()) {
                    int si = c.indexOf(s);
                    if (si < 0) continue;
                    newOut.or(c.usedIn[si]);
                }
                BitSet newIn = (BitSet) c.use[i].clone();
                newIn.or(newOut);
                newIn.andNot(c.latest[i]);
                if (!newIn.equals(c.usedIn[i]) || !newOut.equals(c.usedOut[i])) {
                    c.usedIn[i] = newIn;
                    c.usedOut[i] = newOut;
                    changed = true;
                }
            }
        }
    }

    // --- transformation ---

    /**
     * Per-block transformation routing the FIRST occurrence of each expression in {@code b}
     * into one of {KEEP_SITE, REPLACE_SITE, DO_NOTHING}, and emitting PURE_INSERTs at the end.
     * See the file header for the decomposition; this is the Knoop / Engineer's-Compiler
     * formulation that avoids any duplicate-computation regression on diamond / loop-invariant
     * patterns. Subsequent occurrences of the same expression within the same block are left
     * untouched (treating them conservatively as potential re-evaluations after operand kills
     * that a simple block-level analysis can't disambiguate).
     */
    static void applyTransformations(Context c) {
        // Pass 1: pre-allocate one fresh temp per expression that will be inserted, kept,
        // or replaced. All sites for the same expression share one _lcm_t name.
        for (int bi = 0; bi < c.N; bi++) {
            BitSet ensureTemp = (BitSet) c.use[bi].clone();
            BitSet latestUsedOut = (BitSet) c.latest[bi].clone();
            latestUsedOut.and(c.usedOut[bi]);
            ensureTemp.or(latestUsedOut);
            for (int e = ensureTemp.nextSetBit(0); e >= 0; e = ensureTemp.nextSetBit(e + 1)) {
                c.ensureTempForExpr(e);
            }
        }

        // Pass 2: emit the new flat instruction list per block.
        List<IRInstruction> newFlat = new ArrayList<>();
        for (int bi = 0; bi < c.N; bi++) {
            BasicBlock b = c.blocks.get(bi);

            BitSet placeHere = (BitSet) c.latest[bi].clone();
            placeHere.and(c.usedOut[bi]);                       // latest ∩ usedOut

            BitSet keepSet = (BitSet) c.use[bi].clone();
            keepSet.and(placeHere);                              // use ∩ latest ∩ usedOut

            BitSet replaceSet = (BitSet) c.use[bi].clone();
            replaceSet.andNot(c.latest[bi]);                     // use ∩ ¬latest

            BitSet pureInsertSet = (BitSet) placeHere.clone();
            pureInsertSet.andNot(c.use[bi]);                     // (latest ∩ usedOut) ∩ ¬use

            List<IRInstruction> blockInsts = new ArrayList<>(b.getInstructions());
            List<IRInstruction> out = new ArrayList<>(blockInsts.size());
            BitSet handledHere = new BitSet();

            for (IRInstruction inst : blockInsts) {
                Integer eid = c.expressionIdOf(inst);
                if (eid == null) {
                    out.add(inst);
                    continue;
                }
                String tName = c.tempNameForExpr.get(eid);
                String dest = destVariableName(inst);
                if (handledHere.get(eid) || tName == null || dest == null) {
                    out.add(inst);
                    continue;
                }
                if (keepSet.get(eid)) {
                    // KEEP_SITE: split `dest = compute(e)` into `t_e = compute(e); dest = t_e`.
                    out.add(cloneInstructionWithDest(inst, tName));
                    out.add(makeAssign(dest, tName, c.fn));
                    handledHere.set(eid);
                    continue;
                }
                if (replaceSet.get(eid)) {
                    // REPLACE_SITE: original computation is redundant; t_e comes from upstream.
                    out.add(makeAssign(dest, tName, c.fn));
                    handledHere.set(eid);
                    continue;
                }
                // DO_NOTHING_SITE: use ∩ latest ∩ ¬usedOut → leave untouched.
                out.add(inst);
            }

            if (!pureInsertSet.isEmpty()) {
                int insertPos = terminatorIndex(out);
                List<IRInstruction> toInsert = new ArrayList<>();
                for (int e = pureInsertSet.nextSetBit(0); e >= 0; e = pureInsertSet.nextSetBit(e + 1)) {
                    String tName = c.tempNameForExpr.get(e);
                    IRInstruction template = c.templateInstForExpr.get(e);
                    toInsert.add(cloneInstructionWithDest(template, tName));
                }
                out.addAll(insertPos, toInsert);
            }

            newFlat.addAll(out);
        }

        c.fn.instructions.clear();
        c.fn.instructions.addAll(newFlat);
        // Renumber so the new flat IR has consecutive lines for CFG.buildCFG()'s leader logic.
        for (int i = 0; i < c.fn.instructions.size(); i++) {
            c.fn.instructions.get(i).irLineNumber = i;
        }
    }

    /**
     * Sanity check: every PURE_INSERT site has e ∈ antOut(b). Anticipation downward means
     * every path leaving b was already going to compute e in the unoptimized program, so
     * hoisting to b's exit cannot lengthen any execution path. KEEP_SITE / REPLACE_SITE
     * locations don't need a separate check — they only rewrite ORIGINAL computation sites.
     * Throws if violated.
     */
    static void assertDownsafeInserts(Context c) {
        for (int bi = 0; bi < c.N; bi++) {
            BitSet pureInsert = (BitSet) c.latest[bi].clone();
            pureInsert.and(c.usedOut[bi]);
            pureInsert.andNot(c.use[bi]);
            for (int e = pureInsert.nextSetBit(0); e >= 0; e = pureInsert.nextSetBit(e + 1)) {
                if (!c.antOut[bi].get(e)) {
                    throw new IllegalStateException(
                            "LCM path-length invariant violated: expr " + c.exprList.get(e).key
                                    + " inserted at end of block #" + bi
                                    + " is not in antOut(b) (would compute on a non-anticipated path)");
                }
            }
        }
    }

    // --- helpers ---

    private static BitSet[] newBitSetArr(int n) {
        BitSet[] a = new BitSet[n];
        for (int i = 0; i < n; i++) a[i] = new BitSet();
        return a;
    }

    private static int terminatorIndex(List<IRInstruction> list) {
        if (list.isEmpty()) return 0;
        IRInstruction last = list.get(list.size() - 1);
        if (isTerminator(last)) return list.size() - 1;
        return list.size();
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

    private static IRInstruction makeAssign(String destName, String rhsName, IRFunction fn) {
        IRInstruction in = new IRInstruction();
        in.opCode = OpCode.ASSIGN;
        in.irLineNumber = -1;
        IRVariableOperand dest = new IRVariableOperand(IRIntType.get(), destName, in);
        IROperand rhs;
        if (isLiteralIntegerText(rhsName)) {
            rhs = new IRConstantOperand(IRIntType.get(), rhsName, in);
        } else {
            rhs = new IRVariableOperand(IRIntType.get(), rhsName, in);
        }
        in.operands = new IROperand[]{dest, rhs};
        return in;
    }

    private static IRInstruction cloneInstructionWithDest(IRInstruction template, String newDest) {
        IRInstruction c = new IRInstruction();
        c.opCode = template.opCode;
        c.irLineNumber = -1;
        c.operands = new IROperand[template.operands.length];
        c.operands[0] = new IRVariableOperand(IRIntType.get(), newDest, c);
        for (int i = 1; i < template.operands.length; i++) {
            c.operands[i] = cloneOperand(template.operands[i], c);
        }
        return c;
    }

    private static IROperand cloneOperand(IROperand op, IRInstruction parent) {
        if (op instanceof IRVariableOperand) {
            IRVariableOperand v = (IRVariableOperand) op;
            return new IRVariableOperand(v.type, v.getName(), parent);
        }
        if (op instanceof IRConstantOperand) {
            IRConstantOperand k = (IRConstantOperand) op;
            return new IRConstantOperand(k.type, k.getValueString(), parent);
        }
        if (op instanceof IRLabelOperand) {
            return new IRLabelOperand(((IRLabelOperand) op).getName(), parent);
        }
        if (op instanceof IRFunctionOperand) {
            return new IRFunctionOperand(((IRFunctionOperand) op).getName(), parent);
        }
        throw new IllegalStateException("LCM: unknown operand kind in template instruction");
    }

    private static boolean isLiteralIntegerText(String n) {
        if (n == null || n.isEmpty()) return false;
        int i = (n.charAt(0) == '-') ? 1 : 0;
        if (i >= n.length()) return false;
        for (; i < n.length(); i++) {
            if (!Character.isDigit(n.charAt(i))) return false;
        }
        return true;
    }

    private static String operandText(IROperand op) {
        if (op instanceof IRConstantOperand) return ((IRConstantOperand) op).getValueString();
        if (op instanceof IRVariableOperand) return ((IRVariableOperand) op).getName();
        return op == null ? "null" : op.toString();
    }

    private static void assertReservedPrefixesUnused(IRFunction fn) {
        for (IRVariableOperand v : fn.variables) {
            String n = v.getName();
            if (n.startsWith(TEMP_PREFIX)) {
                throw new IllegalStateException(
                        "LCM reserved prefix '" + TEMP_PREFIX + "' is already used by variable '" + n
                                + "' in function " + fn.name);
            }
        }
        for (IRVariableOperand p : fn.parameters) {
            if (p.getName().startsWith(TEMP_PREFIX)) {
                throw new IllegalStateException(
                        "LCM reserved prefix '" + TEMP_PREFIX + "' is already used by parameter '" + p.getName()
                                + "' in function " + fn.name);
            }
        }
    }

    private static void addIntVariableIfAbsent(IRFunction fn, String name) {
        for (IRVariableOperand v : fn.variables) {
            if (v.getName().equals(name)) return;
        }
        for (IRVariableOperand p : fn.parameters) {
            if (p.getName().equals(name)) return;
        }
        fn.variables.add(new IRVariableOperand(IRIntType.get(), name, null));
    }

    // --- expression key ---

    static final class ExprKey {
        final OpCode op;
        final String a;
        final String b;
        final String key;

        ExprKey(OpCode op, String a, String b) {
            this.op = op;
            this.a = a;
            this.b = b;
            this.key = op + ":" + (a == null ? "" : a) + ":" + (b == null ? "" : b);
        }
    }

    static ExprKey expressionKey(IRInstruction inst) {
        switch (inst.opCode) {
            case ADD:
            case SUB:
            case MULT:
            case DIV:
            case AND:
            case OR:
                return new ExprKey(inst.opCode,
                        operandText(inst.operands[1]),
                        operandText(inst.operands[2]));
            case ASSIGN:
                if (inst.operands.length == 2) {
                    return new ExprKey(inst.opCode, operandText(inst.operands[1]), null);
                }
                return null; // 3-operand array initializer is opaque
            case ARRAY_LOAD:
                return new ExprKey(inst.opCode,
                        operandText(inst.operands[1]),
                        operandText(inst.operands[2]));
            default:
                return null;
        }
    }

    // --- context ---

    /** Per-function LCM state: expression universe, kill maps, per-block bitvectors. */
    public static final class Context {
        public final CFG cfg;
        public final IRFunction fn;
        public final List<BasicBlock> blocks;
        public final int N;
        public int M;

        public final Map<String, Integer> exprIndex = new LinkedHashMap<>();
        public final List<ExprKey> exprList = new ArrayList<>();
        final Map<Integer, IRInstruction> templateInstForExpr = new HashMap<>();
        final Map<String, BitSet> exprsUsingVar = new HashMap<>();
        final Map<String, BitSet> arrayLoadByArray = new HashMap<>();
        final BitSet allArrayLoadExprs = new BitSet();

        public BitSet[] use, kill;
        public BitSet[] antIn, antOut;
        public BitSet[] availIn, availOut;
        public BitSet[] earliest;
        public BitSet[] postIn, postOut;
        public BitSet[] latest;
        public BitSet[] usedIn, usedOut;

        final Map<Integer, String> tempNameForExpr = new HashMap<>();
        int tempCounter = 0;

        private final Map<BasicBlock, Integer> blockIdx = new HashMap<>();

        Context(CFG cfg) {
            this.cfg = cfg;
            this.fn = cfg.function;
            this.blocks = cfg.basicBlocks;
            this.N = blocks.size();
            for (int i = 0; i < N; i++) {
                blockIdx.put(blocks.get(i), i);
            }
        }

        int indexOf(BasicBlock b) {
            Integer i = blockIdx.get(b);
            return i == null ? -1 : i;
        }

        BitSet allBits() {
            BitSet s = new BitSet(M);
            s.set(0, M);
            return s;
        }

        Integer expressionIdOf(IRInstruction inst) {
            ExprKey k = expressionKey(inst);
            if (k == null) return null;
            return exprIndex.get(k.key);
        }

        /**
         * Scan every instruction in every block, assigning a stable bit index to each
         * distinct expression triple. Also builds the kill-side maps:
         *   {@code exprsUsingVar}: variable name → expressions referencing it as an operand
         *   {@code arrayLoadByArray}: array variable name → array_load expressions of that array
         *   {@code allArrayLoadExprs}: every array_load expression (for unknown-array conservatism)
         */
        void buildExpressionIndex() {
            for (BasicBlock b : blocks) {
                for (IRInstruction inst : b.getInstructions()) {
                    ExprKey k = expressionKey(inst);
                    if (k == null) continue;
                    Integer eid = exprIndex.get(k.key);
                    if (eid == null) {
                        eid = exprList.size();
                        exprIndex.put(k.key, eid);
                        exprList.add(k);
                        templateInstForExpr.put(eid, inst);
                        if (k.a != null && !isLiteralIntegerText(k.a)) {
                            exprsUsingVar.computeIfAbsent(k.a, kk -> new BitSet()).set(eid);
                        }
                        if (k.b != null && !isLiteralIntegerText(k.b)) {
                            exprsUsingVar.computeIfAbsent(k.b, kk -> new BitSet()).set(eid);
                        }
                        if (inst.opCode == OpCode.ARRAY_LOAD) {
                            arrayLoadByArray.computeIfAbsent(k.a, kk -> new BitSet()).set(eid);
                            allArrayLoadExprs.set(eid);
                        }
                    }
                }
            }
            M = exprList.size();
        }

        void applyInstructionKills(IRInstruction inst, BitSet killed) {
            switch (inst.opCode) {
                case CALL:
                case CALLR:
                    killed.set(0, M);
                    return;
                case ARRAY_STORE: {
                    String arr = operandText(inst.operands[1]);
                    BitSet arrLoads = arrayLoadByArray.get(arr);
                    if (arrLoads != null) {
                        killed.or(arrLoads);
                    } else {
                        killed.or(allArrayLoadExprs);
                    }
                    return;
                }
                default:
                    break;
            }
            String dest = destVariableName(inst);
            if (dest != null) {
                BitSet uses = exprsUsingVar.get(dest);
                if (uses != null) {
                    killed.or(uses);
                }
            }
        }

        void ensureTempForExpr(int eid) {
            if (tempNameForExpr.containsKey(eid)) return;
            String t = TEMP_PREFIX + (tempCounter++);
            tempNameForExpr.put(eid, t);
            addIntVariableIfAbsent(fn, t);
        }

        void printDataflow() {
            System.err.println("==== LCM dataflow (" + fn.name + ") ====");
            System.err.println("expressions:");
            for (int i = 0; i < M; i++) {
                System.err.println("  e" + i + " = " + exprList.get(i).key);
            }
            for (int i = 0; i < N; i++) {
                BasicBlock b = blocks.get(i);
                System.err.println("block #" + i + " [" + b.getStartLine() + ".." + b.getEndLine() + "]");
                System.err.println("  use      = " + use[i]);
                System.err.println("  kill     = " + kill[i]);
                System.err.println("  antIn    = " + antIn[i]);
                System.err.println("  antOut   = " + antOut[i]);
                System.err.println("  availIn  = " + availIn[i]);
                System.err.println("  availOut = " + availOut[i]);
                System.err.println("  earliest = " + earliest[i]);
                System.err.println("  postIn   = " + postIn[i]);
                System.err.println("  postOut  = " + postOut[i]);
                System.err.println("  latest   = " + latest[i]);
                System.err.println("  usedIn   = " + usedIn[i]);
                System.err.println("  usedOut  = " + usedOut[i]);
            }
            System.err.println("==== end ====");
        }
    }

}
