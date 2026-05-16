# TEST 1 — Basic Partial Redundancy (if-then-else)

`add, _, a, b` is computed in both branches of the breq/brneq AND in the
join block. The basic LCM equations should classify the THEN/ELSE sites
as KEEP_SITE (latest ∩ usedOut ∩ use) and the JOIN site as REPLACE_SITE
(use ∩ ¬latest), eliminating one of the adds in the dynamic trace.

`-passes lcm,dce,empty` so the test isolates LCM (GVN is intentionally
skipped — its current canonical-name selection doesn't rename across a
diamond when the canonical's def doesn't dominate the use).

## Expected effect

Three textual `add, _, a, b` occurrences in the source collapse to one
arithmetic add (in the merged temp), two assigns through the LCM temp,
and one `assign t3, _lcm_t<n>` at the join. The dynamic instruction count
for the `add` op falls by 1 vs the unoptimized baseline regardless of
which branch is taken at runtime.

Baseline-vs-optimized comparison (interpreter stats) is done by
`../run_tests.ps1` / `../run_tests.sh`; both must:

1. Produce identical stdout on every `*.in` file.
2. Have optimized total executed instructions ≤ baseline.
