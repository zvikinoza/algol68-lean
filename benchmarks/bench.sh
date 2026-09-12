#!/bin/bash
# Benchmark harness.
#
# For every program in progs/ it runs, in order:
#   native   the hand-written C equivalent in native/ (the roofline ceiling)
#   a68g     Algol 68 Genie, interpreted
#   a68gO    Algol 68 Genie with --compile (skipped where the platform cannot link it)
#   interp   a68lean's evaluator
#   llvm0/1/2  a68lean compiled at -O0, -O1, -O2 (the LLVM back end, the default)
#   comp0/1/2  the C back end (`--c`) at -O0, -O1, -O2
#
# Every run is checked against the native program's output, so a benchmark that
# computes the wrong thing cannot post a good time.  Results go to
# results/bench.csv as: program,variant,seconds,ops,ns_per_op,status
#
# Usage: bench.sh [name ...]      (default: every program in progs/)
#
# Environment:
#   REPS=n        repetitions per measurement, best taken (default 3)
#   VARIANTS=...  space-separated subset of: native a68g a68gO interp comp0 comp1 comp2 llvm0 llvm1 llvm2
#                 (default: all).  `interp` and `comp0` are the slow ones; when you are
#                 measuring the emitted binary, VARIANTS="native a68g comp1 comp2" is
#                 several times quicker and measures the same thing.
set -u
DIR=$(cd "$(dirname "$0")" && pwd)
BIN=${A68LEAN:-$DIR/../.lake/build/bin/a68lean}
OUT=$DIR/results
mkdir -p "$OUT" "$DIR/build"
CSV=$OUT/bench.csv
REPS=${REPS:-3}
VARIANTS=${VARIANTS:-"native a68g a68gO interp comp0 comp1 comp2"}
want() { case " $VARIANTS " in *" $1 "*) return 0;; *) return 1;; esac; }

# Record what else the machine was doing.  CPU time is far steadier than wall clock, but
# it is not immune to contention, so a reader should be able to see the conditions.
LOAD=$(uptime | sed 's/.*averages*: *//')
echo "# load averages at start: $LOAD" > "$CSV.meta"
echo "# variants: $VARIANTS, reps: $REPS" >> "$CSV.meta"
echo "program,variant,seconds,ops,ns_per_op,status" > "$CSV"

# Best-of-N CPU time (user+sys) of a command, in seconds.  CPU time rather than wall
# clock, so that a benchmark run stays meaningful when other work shares the machine.
timeit() {
  local best=999999 t
  for _ in $(seq "$REPS"); do
    local s=$( { /usr/bin/time -p "$@" >/dev/null; } 2>&1 |
               awk '/^user/{u=$2} /^sys/{s=$2} END{printf "%.3f", u+s}' )
    [ -z "$s" ] && s=999999
    t=$(python3 -c "print(min($best,$s))")
    best=$t
  done
  echo "$best"
}

record() {  # record <prog> <variant> <seconds> <ops> <status>
  local ns
  ns=$(python3 -c "
s=$3; ops=$4
print('%.2f' % (s*1e9/ops) if ops>0 and s<999999 else 'NA')")
  echo "$1,$2,$3,$4,$ns,$5" >> "$CSV"
  printf "  %-8s %8ss  %10s ns/op  %s\n" "$2" "$3" "$ns" "$5"
}

progs=${*:-$(cd "$DIR/progs" && ls *.a68 | sed 's/\.a68//')}
for name in $progs; do
  src=$DIR/progs/$name.a68
  [ -f "$src" ] || continue
  # the operation count is declared in the source as "# ops: <n> ... #"
  ops=$(grep -o 'ops: *[0-9.e+]*' "$src" | head -1 | sed 's/ops: *//')
  ops=${ops:-1}
  ops=$(python3 -c "print(int(float('$ops')))")
  echo "$name (ops=$ops)"

  # reference output from the native C program
  ref=$DIR/build/$name.ref
  if [ -f "$DIR/native/$name.c" ]; then
    cc -O2 -w "$DIR/native/$name.c" -o "$DIR/build/$name.native" 2>/dev/null
    "$DIR/build/$name.native" > "$ref" 2>/dev/null
    if want native; then
      t=$(timeit "$DIR/build/$name.native")
      record "$name" native "$t" "$ops" ok
    fi
  else
    a68g "$src" > "$ref" 2>/dev/null
  fi

  # Algol prints integers right-aligned with a sign; compare on the digits only
  norm() { tr -d ' +\t' < "$1"; }
  check() {  # check <file> -> ok|WRONG
    if diff -q <(norm "$1") <(norm "$ref") >/dev/null 2>&1; then echo ok; else echo WRONG; fi
  }

  o=$DIR/build/$name.out
  if want a68g; then
  if gtimeout 300 a68g "$src" > "$o" 2>/dev/null; then
    t=$(timeit a68g "$src"); record "$name" a68g "$t" "$ops" "$(check "$o")"
  else
    record "$name" a68g 999999 "$ops" failed
  fi
  fi

  # a68g --compile writes prog.c/prog.o next to the source; keep progs/ clean
  if want a68gO; then
  if gtimeout 300 a68g -O "$src" > "$o" 2>/dev/null; then
    t=$(timeit a68g -O "$src"); record "$name" a68gO "$t" "$ops" "$(check "$o")"
  else
    record "$name" a68gO 999999 "$ops" unsupported
  fi
  fi
  rm -f "$DIR/progs/$name.c" "$DIR/progs/$name.o" "$DIR/progs/$name.so"

  if want interp; then
  if gtimeout 300 "$BIN" run "$src" > "$o" 2>/dev/null; then
    t=$(timeit "$BIN" run "$src"); record "$name" interp "$t" "$ops" "$(check "$o")"
  else
    record "$name" interp 999999 "$ops" failed
  fi
  fi

  # llvm<n>: the compiler (LLVM back end); comp<n>: the C back end (`--c`)
  for v in comp0 comp1 comp2 llvm0 llvm1 llvm2; do
    want "$v" || continue
    lvl=${v: -1}
    extra=""; case "$v" in comp*) extra="--c";; esac
    exe=$DIR/build/$name.$v
    if "$BIN" compile "$src" -O$lvl $extra -o "$exe" >/dev/null 2>&1; then
      if gtimeout 300 "$exe" > "$o" 2>/dev/null; then
        t=$(timeit "$exe"); record "$name" "$v" "$t" "$ops" "$(check "$o")"
      else
        record "$name" "$v" 999999 "$ops" failed
      fi
    else
      record "$name" "$v" 999999 "$ops" compile-error
    fi
  done
done
echo
echo "wrote $CSV"
