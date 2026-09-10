#!/bin/bash
# Optimiser regression: for every tests/opt/*.a68, check that
#   a68lean run            (no optimiser)
#   a68lean compile -O0    (no optimiser, C back end)
#   a68lean compile -O1    (the cheap passes)
#   a68lean compile -O2    (all passes)
# produce the same bytes, and that they equal the recorded a68g output.
# Pass --record to (re)generate the expected outputs with a68g.
ROOT=$(cd "$(dirname "$0")" && pwd)
BIN=${A68LEAN:-$ROOT/../../.lake/build/bin/a68lean}
pass=0; fail=0
for f in "$ROOT"/*.a68; do
  base="${f%.a68}"; name=$(basename "$f")
  if [ "$1" = "--record" ]; then
    ( cd "$ROOT" && a68g "$name" </dev/null > "$base.expected" 2>/dev/null )
    continue
  fi
  w=$(mktemp -d); ok=1; why=""
  ( cd "$ROOT" && "$BIN" run "$name" </dev/null > "$w/interp" 2>/dev/null )
  for lvl in O0 O1 O2; do
    if ! ( cd "$ROOT" && "$BIN" compile "$name" "-$lvl" -o "$w/p$lvl" > "$w/cc$lvl.log" 2>&1 ); then
      ok=0; why="$why compile-$lvl"; continue
    fi
    ( cd "$ROOT" && "$w/p$lvl" </dev/null > "$w/$lvl" 2>/dev/null )
    cmp -s "$w/$lvl" "$w/interp" || { ok=0; why="$why $lvl-vs-interpreter"; }
  done
  cmp -s "$w/interp" "$base.expected" || { ok=0; why="$why interpreter-vs-a68g"; }
  if [ $ok = 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $name ::$why"; fi
  rm -rf "$w"
done
[ "$1" = "--record" ] || echo "pass=$pass fail=$fail"
