# Testing

The correctness target is *byte-for-byte equality of standard output with
Algol 68 Genie 3.13.3* plus agreement on success/failure. Four layers of tests
serve that goal.

## 1. In-repo regression suite (`tests/cases`)

Small programs covering every construct area (formats, loops and cases,
procedures and operators, modes, names into rows, transput, long arithmetic).
Their expected outputs and exit statuses were recorded from a68g and are checked
with `tests/run-cases.sh` through the evaluator and `tests/run-cases-compiled.sh`
through the C back end, at `-O0`, `-O1` and `-O2`. All 62 pass on every one.

Many of them are regression cases for defects the corpus or the fuzzer found, and
for each optimisation of the emitted code: rows kept as C arrays (of primitive
elements, of structures, of unions), `STRING` buffers, conditional and case clauses
computed natively, blocks with labels, calls through procedure parameters, heap
cells given back after boxed calls, a `GO TO` out of a routine into a loop body.
Others pin a68g behaviours: `LONG` and `LONG LONG` arithmetic, `COMPL` to the last
bit, library extensions (`format-items`, `stdenv-strings`, `stdenv-processes`),
unions that were never given a value.

## 2. Number-formatting differential test (`tests/fmt`)

`gen.py` produces thousands of `whole`/`fixed`/`float`/`print` cases (edge
values, random doubles, random widths); the same cases are run through a68g
and through `a68lean fmttest`. Result: 3,437 of 3,441 cases identical; the 4
exceptions are `fixed` of values ≥ 10⁷⁰ (documented in COMPATIBILITY.md).

## 3. External corpora (`tests/fetch-corpus.sh`, `tests/run-corpus.sh`)

Two corpora of real programs are fetched and run twice under a68g. A program
is *golden* if a68g accepts it, it exits successfully with nothing on stderr,
and both runs produce the same output. Every golden program is then run with
an empty standard input, a 90-second limit and its own directory as working
directory, through the evaluator and compiled at `-O2`, and its bytes and exit
status are compared with a68g's.

| corpus | golden programs | evaluator | compiled `-O2` |
|---|---:|---:|---:|
| Rosetta Code, ALGOL 68 solutions | 744 | 726 | 735 |
| Algol 68 Genie bundled test set | 29 | 28 | 28 |
| **total** | **773** | **754** | **763** |

A program that calls `random` without `first random` is not golden, even when
its two reference runs agree: a68g seeds its generator from the clock, so such a
program is only reproducible by accident. Programs that seed with `first random`
are reproduced exactly: a68lean implements a68g's taus113 generator.

The ten programs that do not match when compiled:

* **The clock and the machine** (4): `Date-format`, `System-time`, `Hostname` and the
  test set's `end-of-time` print the date, the host name or a speed measured while
  running (`end-of-time` now overflows an `INT` with the speed the compiled program
  reaches). Their recorded output cannot be reproduced by a68g itself either.
* **`PAR`** (1): `Concurrent-computing` prints in whatever order a68g's threads ran.
* **Unsupported extensions** (2): `HTTP` fetches a web page with `http content`, and
  `Metered-concurrency` uses semaphores (`DOWN`, `UP`) between parallel units.
* **`evaluate`** (3): the `Runtime-evaluation` programs compile Algol 68 text while
  they run, which needs the evaluator; `a68lean compile` refuses them and `a68lean
  run` reproduces them.

The evaluator additionally exceeds the limit on 12 programs that pass compiled
(Erdős–Nicolas numbers, Ulam numbers, Square-form factorization and others): it is
a direct interpreter of the core representation, and those programs run for minutes
in it.

## 3a. The C back end

A compiled program runs on a C runtime that transcribes the evaluator (`csrc/`), so
running the corpus compiled checks both the compiled structure — frames, control
flow, jumps, promoted variables — and the transcription. Two parts of the runtime
have differential tests of their own against the Lean they transcribe: the number
formatting (`tests/fmt/difftest-c.sh`, 171,112 cases with no difference) and the
multi-precision arithmetic (`csrc/mp_test.sh`, 37,700 operations at several
precisions with no difference). The corpus found defects only compiled programs had,
each now fixed and covered by a case: a subscript through a `REF STRING`
parameter sliced the cell holding the name instead of the row; values of declared
modes could not be printed; a `GO TO` from a routine to a label outside it hung; an
event routine leaving with a `GO TO` was taken to have returned; a routine leaving by a
jump had the top of its caller's operand stack taken as its result, which emptied the
stack when the label was in a loop body; and compiled programs saw their own path as
`argv (1)` where a68g gives `a68g` and the source file.

## 3b. The collector

Compiled programs collect their heap (docs/GC-DESIGN.md). `A68LEAN_GC=stress` makes the
collector run at every safe point, so any value the runtime failed to keep in a root
is freed while still in use; `A68LEAN_GC=verify` poisons freed objects instead of
reusing them, keeps each for four collections, and after every collection walks
everything reachable and stops the program if it finds a poisoned object. The compiled case suite is run under `stress,verify` as well as plainly, and
the fuzzer too. Two cases exercise the collector directly: `gc-churn` allocates
tens of megabytes of short-lived lists, rows and strings while keeping a small live
set, and `gc-roots` uses values that are reachable only through roots the collector
must know — a routine's frame, a file's associated string and event routine, a name
of a sub-row, a united row, a procedure parameter — after heavy allocation. A case
that uses `evaluate` is marked `evaluator only` on its first line and skipped by
`run-cases-compiled.sh`, since compiled programs do not have it.
`A68LEAN_GC=stats` reports the collections, the bytes freed, the peak live size and
the time spent.

## 3c. The LLVM back end

`a68lean compile --llvm` (docs/LLVM-DESIGN.md) emits LLVM IR instead of C, through the
same runtime. Every suite above runs through it by setting `A68LEAN_OPTS=--llvm`:
`A68LEAN_OPTS=--llvm tests/run-cases-compiled.sh -O2` (also at `-O0`, and under
`A68LEAN_GC=stress,verify`), `A68LEAN_OPTS=--llvm fuzz/run-compiled.sh START COUNT -O2`,
and the corpus runner. The MIR the back end lowers to can be inspected with
`a68lean dump-mir prog.a68 -O2`; the verified MIR passes (`A68/Verified/MIR.lean`) are
applied unless `-O0` is given. What is proved and what is tested is stated in
docs/LLVM-DESIGN.md §4.

## 4. Differential fuzzing (`fuzz/`)

`fuzz/gen.py` is a grammar-based generator of random Algol 68 programs over
the implemented subset: variable and identity declarations of every basic
mode, rows, nested conditionals, `FOR`/`WHILE` loops, case clauses, procedure
declarations with parameters and calls, integer/real/boolean/string/character
expressions, `whole`/`fixed`/`float`, and `printf` with numeric and general
patterns. Programs are generated so that a68g accepts them (declarations
scoped correctly, integers kept in range, divisors non-zero, subscripts in
bounds), so that mismatches point at the implementation rather than at the
generator. `fuzz/run.sh START COUNT` runs both implementations on each program
and keeps any mismatch in `fuzz/failures/`.

Result on the final binary: 300 of 300 fresh programs (seeds 103000–103299) produce
identical output and exit status through the evaluator, and 300 of 300 (seeds
102000–102149 at `-O2`, 102500–102649 at `-O1`) through the C back end. Earlier
builds agreed on seeds 1–2500. Fuzzing found real defects during development: a
missing uninitialised-value check on identity declarations, a format bug, and, at
seeds 9535 and 101236, a `printf` item that failed after part of it had been written,
whose partial text a68g loses and this implementation used to keep.

`fuzz/run-compiled.sh START COUNT -O1|-O2` does the same through the C back end: it
compiles each program, runs the binary, and compares with a68g. Every change to the
back end was fuzzed with 300 fresh programs, 150 at each level, before it was merged;
the C runtime was fuzzed with 500 more (seeds 5000–5149 and 7000–7149 under
`A68LEAN_GC=stress,verify`, 6000–6199 at `-O2`), all agreeing.
This caught two defects. `x +:= e` with a non-trivial right operand wrote through a
reference to a variable that had been promoted to a C variable and had no cell (seed
12102). And `REAL` division checked its quotient, which a68g does not: `exp(769.9) /
1000.0` is an infinity a68g carries on with, and only a later operation that checks,
such as `*` or printing, reports it (seed 60083).

One generated program is not reproduced and is not counted as a mismatch by design:
a string tripled 36 times exhausts a68g's fixed-size heap, which stops the program with
*not enough memory*, while here memory grows until the system refuses it (see
COMPATIBILITY.md).

## Reproducing

```bash
brew install algol68g coreutils        # a68g 3.13.3 and gtimeout
lake build
tests/run-cases.sh
tests/run-cases-compiled.sh -O2
A68LEAN_OPTS=--llvm tests/run-cases-compiled.sh -O2
( cd tests/fmt && python3 gen.py 1 300 && a68g cases.a68 > expected.txt \
  && ../../.lake/build/bin/a68lean fmttest cases.txt > actual.txt && diff expected.txt actual.txt )
tests/fetch-corpus.sh                  # ~20 minutes: clones, records a68g output
tests/run-corpus.sh                    # ~30 minutes
fuzz/run.sh 1 1000
fuzz/run-compiled.sh 1 150 -O2
```
