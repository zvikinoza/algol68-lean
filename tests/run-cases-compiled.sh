#!/bin/bash
# In-repo regression suite for the C back end: every tests/cases/*.a68 is compiled to a
# native binary with a68lean, run, and compared byte-for-byte with the recorded a68g output
# tests/cases/*.expected and exit status tests/cases/*.rc, exactly as run-cases.sh does for
# the evaluator.  Usage: run-cases-compiled.sh [-O0|-O1|-O2]   (default -O2)
ROOT=$(cd "$(dirname "$0")" && pwd)
BIN=${A68LEAN:-$ROOT/../.lake/build/bin/a68lean}
OPT=${1:--O2}
pass=0; fail=0
work=$(mktemp -d)
for f in "$ROOT"/cases/*.a68; do
  base="${f%.a68}"; n=$(basename "$f")
  exe="$work/p"
  if ! ( cd "$ROOT/cases" && gtimeout 900 "$BIN" compile "$n" "$OPT" -o "$exe" >/dev/null 2>&1 ); then
    # a program a68g rejects is expected not to compile
    if [ "$(cat "$base.rc")" != "0" ] && [ ! -s "$base.expected" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "CCERR $n"; fi
    continue
  fi
  act="$work/out"
  ( cd "$ROOT/cases" && gtimeout 60 "$exe" </dev/null > "$act" 2>/dev/null ); rc=$?
  if cmp -s "$act" "$base.expected" && [ "$rc" = "$(cat "$base.rc")" ]; then pass=$((pass+1))
  else fail=$((fail+1)); echo "FAIL $n (rc=$rc, a68g rc=$(cat "$base.rc"))"; fi
  rm -f "$exe" "$exe.c" "$act"
done
rm -rf "$work"
echo "compiled $OPT: pass=$pass fail=$fail"
