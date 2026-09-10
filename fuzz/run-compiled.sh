#!/bin/bash
# Differential fuzzing of the C back end: generate programs, compile them to native
# binaries, and compare with a68g.  Usage: run-compiled.sh START COUNT [-O0|-O1|-O2]
START=${1:-1}; COUNT=${2:-50}; OPT=${3:--O1}
DIR=$(cd "$(dirname "$0")" && pwd)
BIN=${A68LEAN:-$DIR/../.lake/build/bin/a68lean}
mkdir -p "$DIR/cases" "$DIR/failures"
same=0; diff=0
for ((s=START; s<START+COUNT; s++)); do
  f="$DIR/cases/f$s.a68"
  python3 "$DIR/gen.py" "$s" "$f"
  exp=$(mktemp); act=$(mktemp); bin=$(mktemp -d)
  ( cd "$DIR/cases" && gtimeout 30 a68g "f$s.a68" </dev/null >"$exp" 2>/dev/null ); erc=$?
  if ( cd "$DIR/cases" && gtimeout 120 "$BIN" compile "f$s.a68" $OPT -o "$bin/p" >/dev/null 2>&1 ); then
    ( cd "$DIR/cases" && gtimeout 30 "$bin/p" </dev/null >"$act" 2>/dev/null ); arc=$?
  else
    arc=99; : > "$act"
  fi
  if cmp -s "$exp" "$act" && { [ $erc -eq $arc ] || { [ $erc -ne 0 ] && [ $arc -ne 0 ]; }; }; then
    same=$((same+1))
  else
    diff=$((diff+1))
    cp "$f" "$DIR/failures/"; cp "$exp" "$DIR/failures/f$s.expected"; cp "$act" "$DIR/failures/f$s.actual"
    echo "MISMATCH f$s (a68g rc=$erc, compiled rc=$arc): $(diff "$exp" "$act" | head -2 | tr '\n' '|' | cut -c1-140)"
  fi
  rm -f "$exp" "$act"; rm -rf "$bin"
done
echo "agree=$same mismatch=$diff of $COUNT"
