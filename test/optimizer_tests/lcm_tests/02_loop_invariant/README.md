# TEST 2 — Loop-invariant expression

`add, t1, y, z` lives in the loop body but its operands `y` and `z` are
set only ONCE (via `getf`/`geti`) before the loop. Standard LCM cannot
speculatively hoist out of a loop, so the test makes the value
anticipated on the exit path as well by recomputing `y + z` in `EXIT`:
this forces `antOut(LOOP_HEADER) = {(add y z)}` and lets the equations
identify the preheader (which has only the loop header as successor) as
the unique placement point.

After LCM:
  - the preheader emits `_lcm_t0 = y + z` once;
  - the body's `add t1 y z` becomes `assign t1 _lcm_t0`;
  - the exit's `add t2 y z` becomes `assign t2 _lcm_t0`.

For the input `y=2 z=3` the loop runs 11 times (`i = 0..10`). Baseline
performs 1+1+1 = 3 arithmetic adds per body iteration plus 2 in EXIT,
i.e. 11·3 + 2 = 35 adds executed. Optimized: 1 (preheader) + 11·2
(body without the y+z add) + 1 (EXIT) = 24 adds. Saving: 11 adds /
execution.

Uses `-passes lcm,dce,empty` to isolate LCM behavior.
