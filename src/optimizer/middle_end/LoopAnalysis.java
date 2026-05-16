package middle_end;

import ir.IRFunction;

import java.util.*;

// SCOPE: Identifies loops in the CFG via back edges (B -> H where H dominates B),
// then derives the natural loop of each back edge using a reverse-reachability walk
// on the CFG predecessors, stopping at the header H.
//
// PACKAGING: Lives in middle_end alongside CFG and SSABuilder. Consumed by
// GlobalReassociation (block rank == nesting depth).
//
// CACHING: analyze(cfg) caches a LoopInfo on the CFG; CFG.rebuildCFG() clears it
// because back edges and loop sets depend on the predecessor/successor sets.
//
// LIMITATIONS:
// - Only natural loops are detected. Irreducible CFGs would expose their back edges
//   here but the "natural loop" of an irreducible back edge can be ambiguous; the
//   reverse-reachability definition used here still produces a well-defined set per
//   back edge, but two back edges into the same header are merged at the consumer
//   side if desired. This pass does NOT merge them.
// - Unreachable blocks (predecessors empty, not the entry) are treated as standalone
//   with depth 0 by default. SSABuilder gives such blocks an idom of null; we treat
//   them similarly.
//
/**
 * Natural-loop analysis. Reports back edges, the natural-loop body of each back edge,
 * and the per-block nesting depth (which serves as the reassociation rank).
 */
public final class LoopAnalysis {

    private LoopAnalysis() {}

    /** Directed CFG edge {@code from -> to}. Equality is structural on both endpoints. */
    public static final class Edge {
        public final BasicBlock from;
        public final BasicBlock to;

        Edge(BasicBlock from, BasicBlock to) {
            this.from = from;
            this.to = to;
        }

        @Override
        public boolean equals(Object o) {
            if (o == this) {
                return true;
            }
            if (!(o instanceof Edge)) {
                return false;
            }
            Edge e = (Edge) o;
            return e.from == from && e.to == to;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(from) * 31 + System.identityHashCode(to);
        }

        @Override
        public String toString() {
            return "(" + from.getStartLine() + "->" + to.getStartLine() + ")";
        }
    }

    /**
     * All loop-analysis results for one CFG.
     */
    public static final class LoopInfo {
        public final Set<Edge> backEdges;
        public final Map<Edge, Set<BasicBlock>> naturalLoops;
        public final Map<BasicBlock, Integer> nestingDepth;

        LoopInfo(Set<Edge> backEdges,
                 Map<Edge, Set<BasicBlock>> naturalLoops,
                 Map<BasicBlock, Integer> nestingDepth) {
            this.backEdges = Collections.unmodifiableSet(backEdges);
            this.naturalLoops = Collections.unmodifiableMap(naturalLoops);
            this.nestingDepth = Collections.unmodifiableMap(nestingDepth);
        }
    }

    /**
     * Compute back edges, natural loops, and per-block nesting depth, and cache them on {@code cfg}.
     * Idempotent: returns the cached result on subsequent calls until the CFG is rebuilt.
     */
    public static LoopInfo analyze(CFG cfg) {
        LoopInfo cached = cfg.getLoopInfo();
        if (cached != null) {
            return cached;
        }
        if (cfg.basicBlocks.isEmpty()) {
            LoopInfo empty = new LoopInfo(
                    new LinkedHashSet<>(),
                    new LinkedHashMap<>(),
                    new HashMap<>());
            cfg.setLoopInfo(empty);
            return empty;
        }

        BasicBlock entry = cfg.basicBlocks.get(0);
        Map<BasicBlock, Set<BasicBlock>> dom = SSABuilder.computeDominators(cfg, entry);
        Set<Edge> backEdges = findBackEdgesUsingDom(cfg, dom);
        Map<Edge, Set<BasicBlock>> naturalLoops = computeNaturalLoops(backEdges);
        Map<BasicBlock, Integer> depths = computeDepths(cfg, naturalLoops);

        LoopInfo info = new LoopInfo(backEdges, naturalLoops, depths);
        cfg.setLoopInfo(info);
        return info;
    }

    /** Set of back edges {@code B -> H} (H dominates B). */
    public static Set<Edge> findBackEdges(CFG cfg) {
        return analyze(cfg).backEdges;
    }

    /** Per-block natural-loop nesting depth (entry = 0, body of one loop = 1, etc.). */
    public static Map<BasicBlock, Integer> computeLoopNestingDepth(CFG cfg) {
        return analyze(cfg).nestingDepth;
    }

    /** Block rank for reassociation. Currently identical to {@link #computeLoopNestingDepth(CFG)}. */
    public static Map<BasicBlock, Integer> computeBlockRank(CFG cfg) {
        return analyze(cfg).nestingDepth;
    }

    /** Diagnostic dump on stderr. */
    public static void printLoopInfoToStderr(IRFunction fn, CFG cfg) {
        LoopInfo info = analyze(cfg);
        System.err.println("==== Loops (" + fn.name + ") ====");
        if (info.backEdges.isEmpty()) {
            System.err.println("(no loops)");
        }
        for (Edge e : info.backEdges) {
            Set<BasicBlock> body = info.naturalLoops.get(e);
            System.err.print("back edge " + e + "  body={");
            boolean first = true;
            for (BasicBlock b : body) {
                if (!first) {
                    System.err.print(", ");
                }
                System.err.print(b.getStartLine());
                first = false;
            }
            System.err.println("}");
        }
        System.err.println("depths:");
        for (BasicBlock b : cfg.basicBlocks) {
            System.err.println("  [" + b.getStartLine() + ".." + b.getEndLine() + "] = "
                    + info.nestingDepth.get(b));
        }
        System.err.println("==== end Loops ====");
    }

    // --- internals ---

    private static Set<Edge> findBackEdgesUsingDom(CFG cfg, Map<BasicBlock, Set<BasicBlock>> dom) {
        Set<Edge> out = new LinkedHashSet<>();
        for (BasicBlock b : cfg.basicBlocks) {
            Set<BasicBlock> domB = dom.get(b);
            if (domB == null) {
                continue;
            }
            for (BasicBlock s : b.getSuccessors()) {
                if (domB.contains(s)) {
                    out.add(new Edge(b, s));
                }
            }
        }
        return out;
    }

    /**
     * For each back edge {@code n -> d}, the natural loop is {@code {d}} plus every block from which
     * {@code n} is reachable without passing through {@code d}. Implemented as a reverse walk on the
     * CFG predecessors stopping at {@code d}.
     */
    private static Map<Edge, Set<BasicBlock>> computeNaturalLoops(Set<Edge> backEdges) {
        Map<Edge, Set<BasicBlock>> map = new LinkedHashMap<>();
        for (Edge be : backEdges) {
            BasicBlock n = be.from;
            BasicBlock d = be.to;
            Set<BasicBlock> loop = new LinkedHashSet<>();
            loop.add(d);
            Deque<BasicBlock> work = new ArrayDeque<>();
            if (n != d && loop.add(n)) {
                work.push(n);
            }
            while (!work.isEmpty()) {
                BasicBlock m = work.pop();
                for (BasicBlock p : m.getPredecessors()) {
                    if (loop.add(p)) {
                        work.push(p);
                    }
                }
            }
            map.put(be, loop);
        }
        return map;
    }

    /**
     * Nesting depth counts distinct loop headers whose loop body contains a block. Multiple back
     * edges into the same header H collapse to a single loop {@code loop(H)} (the union of their
     * natural-loop bodies), so they do not double-count.
     */
    private static Map<BasicBlock, Integer> computeDepths(
            CFG cfg, Map<Edge, Set<BasicBlock>> naturalLoops) {
        Map<BasicBlock, Set<BasicBlock>> loopByHeader = new LinkedHashMap<>();
        for (Map.Entry<Edge, Set<BasicBlock>> entry : naturalLoops.entrySet()) {
            BasicBlock header = entry.getKey().to;
            Set<BasicBlock> body = entry.getValue();
            loopByHeader.computeIfAbsent(header, k -> new LinkedHashSet<>()).addAll(body);
        }

        Map<BasicBlock, Integer> depth = new HashMap<>();
        for (BasicBlock b : cfg.basicBlocks) {
            depth.put(b, 0);
        }
        for (Set<BasicBlock> body : loopByHeader.values()) {
            for (BasicBlock b : body) {
                depth.merge(b, 1, Integer::sum);
            }
        }
        return depth;
    }
}
