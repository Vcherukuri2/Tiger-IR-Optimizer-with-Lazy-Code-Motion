# LCM test suite

End-to-end correctness + no-regression tests for the new middle-end
passes (`LoopAnalysis`, `SSABuilder`, `GlobalReassociation`,
`GlobalValueNumbering`, `LazyCodeMotion`, `DeadCodeElimination`,
`RemoveEmptyBlocks`). One test directory per scenario:

| Directory | Pattern | Pipeline subset |
|---|---|---|
| `01_basic_pre/`        | Diamond partial-redundancy (Knoop §2)   | `-passes lcm,dce,empty` |
| `02_loop_invariant/`   | Loop-invariant hoisted via preheader    | `-passes lcm,dce,empty` |
| `03_gvn_aliased/`      | `assign`-merge → b ≡ c                  | `-passes ssa,gvn,dce,empty` |
| `04_reassoc_lcm/`      | Briggs & Cooper Fig. 2 (reassoc + LCM)  | `-passes ssa,reassoc,lcm,dce,empty` |
| `05_regression/`       | r0+r1 CSE hidden by reassoc (§4.2)      | full pipeline |

Per-test files:

- `<name>.ir`          – the source program.
- `<name>.in`          – stdin fed to `IRInterpreter` (`geti` lines).
- `passes.txt`         – content of the `-passes` flag (empty = full pipeline).
- `<name>.expected.ir` – textual reference for the optimizer output
                          (informational; semantic + count checks are
                          authoritative).
- `README.md`          – what the test exercises.

## What the runner asserts

For every test directory `T`:

1. `IRInterpreter T.ir < T.in` produces stdout *S* and prints both
   `Number of non-label instructions executed: B_total` and
   `Operation count (excludes LABEL and ASSIGN): B_ops` on stderr,
   plus a per-opcode breakdown.
2. `Demo [-passes ...] T.ir T.opt.ir` succeeds.
3. `IRInterpreter T.opt.ir < T.in` produces stdout *S'* and the same
   two counters *O_total* and *O_ops*.
4. *S* == *S'* (semantic correctness — the optimizer must preserve
   observable behavior).
5. ***O_ops ≤ B_ops*** (no operation-count regression). PRE / LCM
   literature treats register copies as essentially free (the back-end
   coalesces them into MIPS register-to-register `move`s), so the
   regression metric uses the *operation* count — everything except
   `LABEL` and `ASSIGN`. For tests with a real optimization opportunity
   *O_ops* is strictly less than *B_ops*; *O_total* may rise slightly
   because LCM introduces explicit copies in place of the eliminated
   arithmetic, and a future copy-propagation / DCE pass would reclaim
   those.

On any failure the runner dumps the per-opcode breakdown for both
runs and leaves the optimizer's `T.opt.ir` in place for inspection.

## Running

Windows / PowerShell:

```powershell
pwsh -File test/optimizer_tests/lcm_tests/run_tests.ps1
pwsh -File test/optimizer_tests/lcm_tests/run_tests.ps1 -Build           # force rebuild
pwsh -File test/optimizer_tests/lcm_tests/run_tests.ps1 -KeepArtifacts   # keep .opt.ir files
```

Linux / macOS / Git-Bash:

```bash
./test/optimizer_tests/lcm_tests/run_tests.sh
./test/optimizer_tests/lcm_tests/run_tests.sh -b   # force rebuild
./test/optimizer_tests/lcm_tests/run_tests.sh -k   # keep .opt.ir files
```

Both runners exit 0 iff every test passes both the stdout-match and the
no-regression checks; otherwise they exit non-zero and print a per-test
summary listing the failure mode.
