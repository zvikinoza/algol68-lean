#!/bin/bash
# Fetch the two external test corpora and record Algol 68 Genie's reference output.
#
#   * Rosetta Code ALGOL 68 solutions (github.com/acmeism/RosettaCodeData, sparse clone)
#   * the test set shipped in the Algol 68 Genie source distribution
#
# Every program is run twice with a68g; programs that a68g rejects, that fail at run time,
# or whose output differs between the two runs are excluded from tests/corpus/golden.txt.
# Requires: git, a68g (brew install algol68g), gtimeout (brew install coreutils).
set -e
ROOT=$(cd "$(dirname "$0")" && pwd)
CORPUS="$ROOT/corpus"
mkdir -p "$CORPUS"
cd "$CORPUS"

if [ ! -d rc ]; then
  git clone --filter=blob:none --no-checkout --depth 1 https://github.com/acmeism/RosettaCodeData.git rc
  ( cd rc && git sparse-checkout init --no-cone && git sparse-checkout set '/Task/*/ALGOL-68/*' && git checkout )
fi
if [ ! -d a68g-src ]; then
  curl -sL -o algol68g.tar.gz https://algol68genie.nl/algol68g-3.13.3.tar.gz
  mkdir -p a68g-src && tar xzf algol68g.tar.gz -C a68g-src
fi

record() {  # record <dir> <source>
  local d="$1" src="$2"
  # already recorded: skip, so that an interrupted sweep resumes where it stopped
  [ -s "$d/rc1.txt" ] && [ -f "$d/out2.txt" ] && return 0
  mkdir -p "$d"; cp "$src" "$d/prog.a68"
  # a68g exits nonzero on the many programs it rejects, and that is data, not a failure:
  # swallow the status so `set -e` does not stop the sweep on the first rejected program.
  ( cd "$d" && gtimeout 60 a68g prog.a68 </dev/null >out1.txt 2>err1.txt; echo $? > rc1.txt
             gtimeout 60 a68g prog.a68 </dev/null >out2.txt 2>/dev/null ) || true
}

: > golden.txt
find rc/Task -path '*ALGOL-68*' -name '*.alg' | sort | while read -r f; do
  name=$(echo "$f" | sed 's#.*/Task/\([^/]*\)/ALGOL-68/\(.*\)\.alg#\1__\2#')
  record "out/$name" "$f"
done
for f in a68g-src/*/src/test-set/*.a68; do
  record "a68gset/$(basename "$f" .a68)" "$f"
done
for d in out/*/ a68gset/*/; do
  d=${d%/}
  errs=$(grep -v '^\[.*\]$' "$d/err1.txt" | wc -c | tr -d ' ')
  if [ "$(cat "$d/rc1.txt")" = "0" ] && [ "$errs" -eq 0 ] && cmp -s "$d/out1.txt" "$d/out2.txt" \
     && ! grep -q "exiting graciously" "$d/out1.txt"; then
    echo "$CORPUS/$d" >> golden.txt
  fi
done
echo "golden programs: $(wc -l < golden.txt)"
