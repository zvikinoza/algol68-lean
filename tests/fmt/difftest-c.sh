#!/bin/bash
# Differential test of the C number formatter (csrc/fmt.c) against the Lean one
# (A68/Numfmt.lean): the generated case sets of gen.py are run through
# `a68lean fmttest` and csrc/fmt_test.c, the extended sets of gen_long.py through
# tests/fmt/fmtlong.lean (via `lean --run` on the built oleans) and the driver.
# Usage: tests/fmt/difftest-c.sh [COUNT] [SEEDS...]   (default: 1000 cases per seed, seeds 1 2 3 4 5)
set -u
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
BIN="$ROOT/.lake/build/bin/a68lean"
LEAN=${LEAN:-lean}
COUNT=${1:-1000}; shift || true
SEEDS=${*:-1 2 3 4 5}
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
cc -std=c99 -O2 -Wall -Wextra "$ROOT/csrc/fmt_test.c" "$ROOT/csrc/fmt.c" "$ROOT/csrc/bigint.c" -lm -o "$WORK/fmt_test" || exit 1
total=0; bad=0
for seed in $SEEDS; do
  ( cd "$WORK" && python3 "$ROOT/tests/fmt/gen.py" "$seed" "$COUNT" )
  "$BIN" fmttest "$WORK/cases.txt" > "$WORK/lean.txt"
  "$WORK/fmt_test" "$WORK/cases.txt" > "$WORK/c.txt"
  n=$(grep -c . "$WORK/cases.txt"); d=$(diff "$WORK/lean.txt" "$WORK/c.txt" | grep -c '^[<>]')
  echo "gen.py seed $seed: $n cases, $d differing lines"
  [ "$d" = 0 ] || diff "$WORK/lean.txt" "$WORK/c.txt" | head -20
  total=$((total + n)); bad=$((bad + d))
  python3 "$ROOT/tests/fmt/gen_long.py" "$seed" "$((COUNT / 4))" > "$WORK/cases_long.txt"
  ( cd "$ROOT" && LEAN_PATH="$ROOT/.lake/build/lib/lean" "$LEAN" --run tests/fmt/fmtlong.lean "$WORK/cases_long.txt" ) > "$WORK/lean_long.txt"
  "$WORK/fmt_test" "$WORK/cases_long.txt" > "$WORK/c_long.txt"
  n=$(grep -c . "$WORK/cases_long.txt"); d=$(diff "$WORK/lean_long.txt" "$WORK/c_long.txt" | grep -c '^[<>]')
  echo "gen_long.py seed $seed: $n cases, $d differing lines"
  [ "$d" = 0 ] || diff "$WORK/lean_long.txt" "$WORK/c_long.txt" | head -20
  total=$((total + n)); bad=$((bad + d))
done
echo "total: $total cases, $bad differing lines"
[ "$bad" = 0 ]
