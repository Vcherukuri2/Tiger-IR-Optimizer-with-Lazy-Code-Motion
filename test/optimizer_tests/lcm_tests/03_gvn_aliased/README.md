# TEST 3 — GVN catches aliased names

The input mirrors the user's spec:

```
assign, a, x
add,    b, a, z
add,    c, x, z
```

Because the assign merges `a` into `x`'s value class, the AWZ partition
refinement converges with `b` and `c` in the same class. With `b`'s
definition dominating `c`'s use (single straight-line block), GVN
selects `b` as the canonical and rewrites every use of `c` accordingly.
The redundant `add, c, x, z` is then dead and is removed by DCE; the
`assign, a, x` becomes dead too once the `a` operand of `b`'s definition
is canonicalized to `x`.

`-passes ssa,gvn,dce,empty` — straight-line, so dominance is trivial and
the GVN renaming is unconditionally safe (no diamond-merge bug).

Sample run with `x=4 z=5`: both prints emit `9`; the optimized program
performs exactly one `add` instead of two.
