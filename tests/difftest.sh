#!/bin/bash
# Differential test: run every golden program with a68lean and compare stdout byte-for-byte
# with a68g's recorded output. Usage: difftest.sh <golden-list> <outdir-root> [report]
LIST=$1; ROOT=$2; REPORT=${3:-/dev/stdout}
BIN=${A68LEAN:-$(cd "$(dirname "$0")" && pwd)/../.lake/build/bin/a68lean}
pass=0; fail=0; err=0; tmo=0
: > "$REPORT"
while read -r d; do
  d="${d%/}"
  name=$(basename "$d")
  exp="$d/out1.txt"
  act=$(mktemp); errf=$(mktemp)
  ( cd "$d" && gtimeout 90 "$BIN" run prog.a68 </dev/null >"$act" 2>"$errf" ); rc=$?
  if [ $rc -eq 124 ]; then tmo=$((tmo+1)); echo "TIMEOUT $name" >> "$REPORT"
  elif [ $rc -ne 0 ]; then err=$((err+1)); echo "ERROR $name :: $(head -c 200 "$errf" | tr '\n' ' ')" >> "$REPORT"
  elif cmp -s "$exp" "$act"; then pass=$((pass+1)); echo "PASS $name" >> "$REPORT"
  else fail=$((fail+1)); echo "DIFF $name :: $(diff "$exp" "$act" | head -3 | tr '\n' '|' | cut -c1-200)" >> "$REPORT"
  fi
  rm -f "$act" "$errf"
done < "$LIST"
echo "pass=$pass diff=$fail error=$err timeout=$tmo total=$((pass+fail+err+tmo))"
