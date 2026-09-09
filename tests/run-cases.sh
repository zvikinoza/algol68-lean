#!/bin/bash
# In-repo regression suite: every tests/cases/*.a68 is run with a68lean and compared
# byte-for-byte with the recorded a68g output tests/cases/*.expected (and exit status).
# Pass --record to (re)generate the expected outputs with a68g.
ROOT=$(cd "$(dirname "$0")" && pwd)
BIN="$ROOT/../.lake/build/bin/a68lean"
pass=0; fail=0
for f in "$ROOT"/cases/*.a68; do
  base="${f%.a68}"
  if [ "$1" = "--record" ]; then
    ( cd "$ROOT/cases" && a68g "$(basename "$f")" </dev/null > "$base.expected" 2>/dev/null; echo $? > "$base.rc" )
    continue
  fi
  act=$(mktemp)
  ( cd "$ROOT/cases" && gtimeout 60 "$BIN" run "$(basename "$f")" </dev/null > "$act" 2>/dev/null ); rc=$?
  if cmp -s "$act" "$base.expected" && [ "$rc" = "$(cat "$base.rc")" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $(basename "$f")"; fi
  rm -f "$act"
done
[ "$1" = "--record" ] || echo "pass=$pass fail=$fail"
