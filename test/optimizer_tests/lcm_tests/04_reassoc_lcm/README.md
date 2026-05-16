# TEST 4 — Reassociation exposes loop-invariant subexpression

Briggs & Cooper Figure 2 example translated to Tiger-IR. The source
computes `s = s + i + y + z` each iteration as the left-associative
chain

```
add, t1, s, i
add, t2, t1, y
add, s,  t2, z
```

Operand ranks: `y`, `z` have rank 0 (callr'd in the entry block); `s`
and `i` carry the loop header's rank. After reassociation the operands
of the flattened `add(s, i, y, z)` tree are sorted ascending by rank and
re-emitted as

```
_ra1 = y + z          ; rank-0 pair (loop-invariant)
_ra2 = _ra1 + i       ; +i (loop-variant)
s    = _ra2 + s       ; +s
```

The `EXIT` block also recomputes `y + z` (so LCM has anticipation on
both successors of the loop header). LCM hoists `_ra1 = y + z` into the
PREHEAD as `_lcm_t<n>` and replaces both the loop-body and the EXIT
sites with `assign _, _lcm_t<n>`. DCE then strips the dead reassociation
temps.

Pipeline: `-passes ssa,reassoc,lcm,dce,empty` — GVN is skipped because
the current canonical-name selection isn't dominance-aware (would
otherwise pick `_ra1` from inside the loop body as the canonical of the
`y+z` class, which doesn't dominate the EXIT use).

Expected: optimized total executed adds ≤ baseline, and the dynamic
count of `add` ops in the loop body falls by one per iteration.
