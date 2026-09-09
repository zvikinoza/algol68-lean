#!/bin/bash
# Summarise a difftest report, separating expected divergences from real failures:
#   * programs using `random` without `first random` (a68g seeds from the clock: not reproducible)
#   * programs whose output depends on LONG REAL / LONG LONG REAL precision (multi-precision in a68g)
REPORT=$1
DIR=$(dirname "$REPORT")
pass=$(grep -c '^PASS' "$REPORT")
total=$(wc -l < "$REPORT")
rnd=0; lreal=0; other=0
for line in $(grep -v '^PASS' "$REPORT" | awk '{print $2}'); do
  src=$(find "$DIR" -path "*/$line/prog.a68" | head -1)
  if grep -q "random" "$src" && ! grep -q "first random" "$src"; then rnd=$((rnd+1))
  elif grep -qi "LONG REAL\|LONG LONG\|LONG COMPL\|long sqrt\|long pi\|LENG" "$src"; then lreal=$((lreal+1))
  else other=$((other+1)); echo "$(grep " $line " "$REPORT" | cut -c1-160)"
  fi
done
echo "total=$total pass=$pass random-seeded=$rnd long-real=$lreal other=$other"
