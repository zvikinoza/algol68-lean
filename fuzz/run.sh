#!/bin/bash
# Differential fuzzing: generate N programs from seed S onward, run a68g and a68lean, compare.
# Usage: run.sh START COUNT   -> summary on stdout; mismatching cases kept in fuzz/failures/
START=${1:-1}; COUNT=${2:-100}
DIR=$(cd "$(dirname "$0")" && pwd)
BIN=${A68LEAN:-$DIR/../.lake/build/bin/a68lean}
mkdir -p "$DIR/cases" "$DIR/failures"
same=0; diff=0; a68gerr=0
for ((s=START; s<START+COUNT; s++)); do
  f="$DIR/cases/f$s.a68"
  python3 "$DIR/gen.py" "$s" "$f"
  exp=$(mktemp); act=$(mktemp)
  ( cd "$DIR/cases" && gtimeout 20 a68g "f$s.a68" </dev/null >"$exp" 2>/dev/null ); erc=$?
  ( cd "$DIR/cases" && gtimeout 20 "$BIN" run "f$s.a68" </dev/null >"$act" 2>/dev/null ); arc=$?
  if [ $erc -ne 0 ]; then a68gerr=$((a68gerr+1)); fi
  if cmp -s "$exp" "$act" && { [ $erc -eq $arc ] || { [ $erc -ne 0 ] && [ $arc -ne 0 ]; }; }; then
    same=$((same+1))
  else
    diff=$((diff+1))
    cp "$f" "$DIR/failures/f$s.a68"; cp "$exp" "$DIR/failures/f$s.expected"; cp "$act" "$DIR/failures/f$s.actual"
    echo "MISMATCH f$s (a68g rc=$erc, a68lean rc=$arc): $(diff "$exp" "$act" | head -2 | tr '\n' '|' | cut -c1-150)"
  fi
  rm -f "$exp" "$act"
done
echo "agree=$same mismatch=$diff (a68g nonzero exit: $a68gerr) of $COUNT"
