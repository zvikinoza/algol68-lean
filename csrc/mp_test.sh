#!/bin/sh
# Differential test of csrc/mp.c, mpmath.c, mpfmt.c against the evaluator.
#
#   csrc/mp_test.sh [WORKDIR] [OPS_PER_SEED]
#
# Builds mp_test, generates random LONG / LONG LONG programs with mp_gen.py (ten seeds at
# the default precision and three `PR precision` variants), runs each program with
# `.lake/build/bin/a68lean run` and the same operations with mp_test, and diffs the outputs.
# Prints one line per program and the total number of differing lines; exits 1 on any.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
work=${1:-/tmp/mp_test_work}
n=${2:-3000}
mkdir -p "$work"
cc -std=c99 -Wall -Wextra -O2 -ffp-contract=off -o "$work/mp_test" \
   "$here/mp.c" "$here/mpmath.c" "$here/mpfmt.c" "$here/mp_test.c" -lm || exit 1

run_one() {   # name seed n precision lldigits
  name=$1; seed=$2; count=$3; prec=$4; lld=$5
  if [ -n "$prec" ]; then
    python3 "$here/mp_gen.py" "$seed" "$count" "$work/$name.a68" "$prec" > "$work/$name.ops"
  else
    python3 "$here/mp_gen.py" "$seed" "$count" "$work/$name.a68" > "$work/$name.ops"
  fi
  "$root/.lake/build/bin/a68lean" run "$work/$name.a68" > "$work/$name.a68.out" 2> "$work/$name.a68.err"
  echo "rc=$?" > "$work/$name.rc"
  "$work/mp_test" "$lld" < "$work/$name.ops" > "$work/$name.c.out"
}

rm -f "$work"/*.rc
for seed in 11 12 13 14 15 16 17 18 19 20; do
  run_one "s$seed" "$seed" "$n" "" 12 &
done
run_one "p30" 31 "$((n / 2))" 30 7 &
run_one "p100" 32 "$((n / 2))" 100 17 &
run_one "p200" 33 "$((n / 2))" 200 31 &
wait

total=0; ops=0
for f in "$work"/*.rc; do
  name=$(basename "$f" .rc)
  d=$(diff "$work/$name.a68.out" "$work/$name.c.out" | grep -c '^[<>]')
  lines=$(wc -l < "$work/$name.a68.out" | tr -d ' ')
  echo "$name: $(cat "$f") lines=$lines differing=$d $(head -c 120 "$work/$name.a68.err")"
  total=$((total + d)); ops=$((ops + lines))
done
echo "total operations: $ops, differing lines: $total"
[ "$total" -eq 0 ]
