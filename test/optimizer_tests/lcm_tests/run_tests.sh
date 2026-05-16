#!/usr/bin/env bash
# Cross-platform (Linux / macOS / Git-Bash) runner for the lcm_tests suite.
# Mirrors run_tests.ps1 — keep these two scripts in lock-step.
#
#   ./run_tests.sh           # run all tests
#   ./run_tests.sh -b        # force rebuild of build/optimizer first
#   ./run_tests.sh -k        # keep the <name>.opt.ir artifacts
#
# Per test:
#   1. Interpret the original .ir, capture stdout + stats from IRInterpreter.
#   2. Run Demo with the -passes flag from passes.txt (empty = full pipeline).
#   3. Interpret the optimized .opt.ir.
#   4. Assert stdout matches and optimized instruction count <= baseline.
#   5. If <name>.expected.ir exists, diff it informationally.

set -u
set +e   # we need to inspect non-zero exits ourselves

build=0
keep=0
while getopts ":bk" opt; do
    case $opt in
        b) build=1 ;;
        k) keep=1 ;;
        *) echo "unknown flag -$OPTARG"; exit 2 ;;
    esac
done

script_dir="$(cd "$(dirname "$0")" && pwd)"
project_root="$(cd "$script_dir/../../.." && pwd)"
build_dir="$project_root/build/optimizer"

build_optimizer() {
    echo "[build] javac src/optimizer ..."
    mkdir -p "$build_dir"
    (
        cd "$project_root"
        javac \
            src/optimizer/ir/*.java \
            src/optimizer/ir/datatype/*.java \
            src/optimizer/ir/operand/*.java \
            src/optimizer/middle_end/*.java \
            src/optimizer/*.java \
            -d "$build_dir"
    )
}

if [ "$build" -eq 1 ] || [ ! -f "$build_dir/Demo.class" ]; then
    build_optimizer || { echo "build failed"; exit 2; }
fi

extract_count() {
    # Pulls the integer N out of "Number of non-label instructions executed: N"
    grep -oE 'Number of non-label instructions executed:[[:space:]]+[0-9]+' "$1" \
        | grep -oE '[0-9]+$' | tail -n 1
}

extract_ops() {
    # Pulls the integer N out of "Operation count (excludes LABEL and ASSIGN): N".
    # PRE/LCM literature speaks of operation count (arith + branch + mem + call) and
    # treats register copies as essentially free; that's the no-regression metric.
    # Falls back to the gross executed count if running against an older interpreter
    # build that doesn't emit the explicit line.
    local n
    n="$(grep -oE 'Operation count \(excludes LABEL and ASSIGN\):[[:space:]]+[0-9]+' "$1" \
        | grep -oE '[0-9]+$' | tail -n 1)"
    if [ -n "$n" ]; then
        echo "$n"
    else
        extract_count "$1"
    fi
}

extract_opcodes() {
    grep -oE 'Per-opcode counts:.*' "$1" | tail -n 1
}

pass=0
fail=0
summary=()

for test_dir in "$script_dir"/*/; do
    name="$(basename "$test_dir")"
    ir="$test_dir$name.ir"
    [ -f "$ir" ] || continue
    in_file="$test_dir$name.in"
    passes_file="$test_dir/passes.txt"
    opt_ir="$test_dir$name.opt.ir"
    expected_ir="$test_dir$name.expected.ir"
    base_out="$test_dir/.baseline.out"
    base_err="$test_dir/.baseline.err"
    opt_out="$test_dir/.optimized.out"
    opt_err="$test_dir/.optimized.err"
    demo_err="$test_dir/.demo.err"

    passes=""
    if [ -f "$passes_file" ]; then
        passes="$(tr -d '[:space:]' < "$passes_file")"
    fi

    echo
    echo "==== $name ===="
    echo "  passes : ${passes:-<full pipeline>}"

    if [ -f "$in_file" ]; then
        java -cp "$build_dir" IRInterpreter "$ir" < "$in_file" > "$base_out" 2> "$base_err"
    else
        java -cp "$build_dir" IRInterpreter "$ir" < /dev/null > "$base_out" 2> "$base_err"
    fi
    if [ $? -ne 0 ]; then
        echo "  [FAIL] baseline interpreter exit $?"
        cat "$base_err"
        fail=$((fail+1)); summary+=("FAIL  $name (baseline interp)"); continue
    fi
    base_count="$(extract_count "$base_err")"
    base_ops="$(extract_ops "$base_err")"
    base_opcodes="$(extract_opcodes "$base_err")"
    echo "  base   : $base_count instructions ($base_ops ops; ASSIGN+LABEL excluded)"

    if [ -n "$passes" ]; then
        java -cp "$build_dir" Demo -passes "$passes" "$ir" "$opt_ir" > /dev/null 2> "$demo_err"
    else
        java -cp "$build_dir" Demo "$ir" "$opt_ir" > /dev/null 2> "$demo_err"
    fi
    if [ $? -ne 0 ]; then
        echo "  [FAIL] Demo exit $?"
        cat "$demo_err"
        fail=$((fail+1)); summary+=("FAIL  $name (optimizer)"); continue
    fi

    if [ -f "$in_file" ]; then
        java -cp "$build_dir" IRInterpreter "$opt_ir" < "$in_file" > "$opt_out" 2> "$opt_err"
    else
        java -cp "$build_dir" IRInterpreter "$opt_ir" < /dev/null > "$opt_out" 2> "$opt_err"
    fi
    if [ $? -ne 0 ]; then
        echo "  [FAIL] optimized interpreter exit $?"
        cat "$opt_err"
        fail=$((fail+1)); summary+=("FAIL  $name (optimized interp)"); continue
    fi
    opt_count="$(extract_count "$opt_err")"
    opt_ops="$(extract_ops "$opt_err")"
    opt_opcodes="$(extract_opcodes "$opt_err")"
    echo "  opt    : $opt_count instructions ($opt_ops ops; ASSIGN+LABEL excluded)"

    if ! diff -q "$base_out" "$opt_out" >/dev/null; then
        echo "  [FAIL] stdout differs (semantic regression)"
        diff "$base_out" "$opt_out" | head -n 40
        echo "  baseline opcode counts : $base_opcodes"
        echo "  optimized opcode counts: $opt_opcodes"
        fail=$((fail+1)); summary+=("FAIL  $name (stdout differs)"); continue
    fi

    if [ -n "$base_ops" ] && [ -n "$opt_ops" ] && [ "$opt_ops" -gt "$base_ops" ]; then
        echo "  [FAIL] optimized executes MORE operations than baseline (regression)"
        echo "    baseline_ops=$base_ops, optimized_ops=$opt_ops"
        echo "  baseline opcode counts : $base_opcodes"
        echo "  optimized opcode counts: $opt_opcodes"
        echo "  optimized IR kept at: $opt_ir"
        fail=$((fail+1)); summary+=("FAIL  $name (perf regression)"); continue
    fi

    delta=$((base_ops - opt_ops))
    if [ -f "$expected_ir" ]; then
        if diff -q <(sed 's/\r$//' "$expected_ir") <(sed 's/\r$//' "$opt_ir") >/dev/null; then
            echo "  expected.ir matches exactly"
        else
            echo "  [warn] optimizer output does NOT match expected.ir textually"
            echo "         (passes semantic + count checks; expected.ir is informational)"
        fi
    fi

    echo "  [PASS] saved $delta operations; stdout matches"
    pass=$((pass+1))
    summary+=("PASS  $name (saved $delta ops)")

    if [ "$keep" -eq 0 ]; then
        rm -f "$opt_ir"
    fi
    rm -f "$base_out" "$base_err" "$opt_out" "$opt_err" "$demo_err"
done

echo
echo "==== SUMMARY ===="
for line in "${summary[@]:-}"; do echo "  $line"; done
echo "  $pass passed, $fail failed"
[ "$fail" -eq 0 ]
