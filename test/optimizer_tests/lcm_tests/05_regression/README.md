# TEST 5 — Reassociation regression (Briggs & Cooper §4.2)

In the unoptimized source `r0 + r1` is an **explicit, textually
identical** common subexpression:

```
add, t1, r0, r1
add, b,  t1, a      ; b = (r0 + r1) + a
add, t3, r0, r1     ; t3 = r0 + r1     -- CSE with t1
add, c,  t3, d      ; c = (r0 + r1) + d
```

Naive reassociation flattens `b`'s expression tree to `add(r0, r1, a)`
and `c`'s to `add(r0, r1, d)`, sorts each by operand rank, and re-emits
them as a left-fold. Depending on how ties are broken (Briggs & Cooper
§4.2 documents this hazard), the freshly-emitted `_raN` temporary for
`r0 + r1` in `b`'s tree may not be textually identical to the one in
`c`'s tree, **breaking the manifest CSE** that the baseline expressed.

The pipeline must recover from this scenario: GlobalValueNumbering
should re-identify the `(add, r0, r1)` equivalence on the reassociated
SSA form, and the redundant `_raN` defs must be removed by LCM/DCE.
This test asserts:

  optimized_executed_instr_count ≤ baseline_executed_instr_count

i.e. however reassoc reorders operands, the *full* pipeline is at least
break-even on operation count.

Empty `passes.txt` means "run the full default pipeline" (no `-passes`
flag).

Sample inputs `a=1, d=10, r0=100, r1=1000`:
  b = (r0 + r1) + a = 1101
  c = (r0 + r1) + d = 1110
Both prints must emit those values regardless of optimization level.
