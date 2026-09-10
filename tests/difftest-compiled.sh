#!/bin/bash
# Differential test of the C backend: compile every golden program with
# `a68lean compile`, run the binary, and compare its stdout byte for byte with
# the recorded a68g output.  Usage: difftest-compiled.sh <golden-list> <report>
LIST=$1; REPORT=${2:-/dev/stdout}
ROOT=$(cd "$(dirname "$0")" && pwd)
BIN=${A68LEAN:-$ROOT/../.lake/build/bin/a68lean}
pass=0; diff=0; cerr=0; rerr=0; tmo=0
: > "$REPORT"
while read -r d; do
  d="${d%/}"; name=$(basename "$d")
  out=$(mktemp -d)
  if ! (cd "$d" && gtimeout 120 "$BIN" compile prog.a68 -o "$out/prog" >"$out/cc.log" 2>&1); then
    cerr=$((cerr+1)); echo "CCERR $name :: $(tail -2 "$out/cc.log" | tr '\n' ' ' | cut -c1-160)" >> "$REPORT"
    rm -rf "$out"; continue
  fi
  act=$(mktemp); errf=$(mktemp)
  ( cd "$d" && gtimeout 90 "$out/prog" </dev/null >"$act" 2>"$errf" ); rc=$?
  if [ $rc -eq 124 ]; then tmo=$((tmo+1)); echo "TIMEOUT $name" >> "$REPORT"
  elif [ $rc -ne 0 ]; then rerr=$((rerr+1)); echo "RTERR $name :: $(head -c 160 "$errf" | tr '\n' ' ')" >> "$REPORT"
  elif cmp -s "$d/out1.txt" "$act"; then pass=$((pass+1)); echo "PASS $name" >> "$REPORT"
  else diff=$((diff+1)); echo "DIFF $name :: $(diff "$d/out1.txt" "$act" | head -3 | tr '\n' '|' | cut -c1-160)" >> "$REPORT"
  fi
  rm -f "$act" "$errf"; rm -rf "$out"
done < "$LIST"
echo "pass=$pass diff=$diff compile-error=$cerr runtime-error=$rerr timeout=$tmo"
