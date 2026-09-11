# Testing

The correctness target is *byte-for-byte equality of standard output with
Algol 68 Genie 3.13.3* plus agreement on success/failure. Four layers of tests
serve that goal.

## 1. In-repo regression suite (`tests/cases`)

Small programs covering every construct area (formats, loops and cases,
procedures and operators, modes, names into rows). Their expected outputs were
recorded from a68g (`tests/run-cases.sh --record`) and are checked with
`tests/run-cases.sh` through the evaluator and `tests/run-cases-compiled.sh`
through the C back end. All 16 pass on both. Six of them are regression cases for
defects the external corpus and the fuzzer found in compiled programs: a
`GO TO` out of a routine that hung, values of declared modes that could not be
printed, subscripts through a `REF` row parameter, an event routine that leaves
with a `GO TO`, the evaluation order of direct calls, and `REAL` division.  Three
cover a68g's library extensions: `format-items` (bits, `h` and C-style patterns),
`stdenv-strings` (regular expressions, string transput, `evaluate`, `BYTES`, associated
strings) and `stdenv-processes` (`system`, `fork`, the `execve` family).

## 2. Number-formatting differential test (`tests/fmt`)

`gen.py` produces thousands of `whole`/`fixed`/`float`/`print` cases (edge
values, random doubles, random widths); the same cases are run through a68g
and through `a68lean fmttest`. Result: 3,437 of 3,441 cases identical; the 4
exceptions are `fixed` of values ≥ 10⁷⁰ (documented in COMPATIBILITY.md).

## 3. External corpora (`tests/fetch-corpus.sh`, `tests/run-corpus.sh`)

Two corpora of real programs are fetched and run twice under a68g. A program
is *golden* if a68g accepts it, it exits successfully with nothing on stderr,
and both runs produce the same output. The `difftest.sh` driver then runs
`a68lean` on every golden program (with an empty standard input, a timeout,
and the program's own directory as working directory) and compares the bytes.

| corpus | golden programs | byte-identical |
|---|---|---|
| Rosetta Code, ALGOL 68 solutions | 744 | 645 |
| Algol 68 Genie bundled test set (39 files) | 29 | 16 |

A program that calls `random` without `first random` is not golden, even when
its two reference runs agree: a68g seeds its generator from the clock, so such a
program is only reproducible by accident, when both runs land in the same second.
Earlier versions of this table counted those, which is why its totals differ.
Programs that seed with `first random` are reproduced exactly: a68lean
implements a68g's taus113 generator.

The 112 programs that do not match fall into these groups:

* **Unsupported a68g extensions** (about 30): library procedures such as
  `evaluate`, `system`, `get directory`, `grep in string` and `local time`, and
  the `r`, `n`, `h` and `%` format items.
* **Parser gaps** (about 30): syntax a68g accepts and a68lean does not, most of
  them a68g extensions to the Revised Report such as `DOUBLE`, refinements and
  partial parametrisation.
* **Multi-precision `LONG REAL`** (about 12 of the 17 output differences):
  output that depends on a68g's 42- and 70-digit reals, which are IEEE doubles
  here. The rest are `PAR`, printing infinities, and a few layout corner cases.
* **Time** (15): programs that exceed the 90-second limit under the evaluator.
  13 of them pass when compiled; see below.
* **Genuine gaps** (the remainder): a scalar rowed into a multi-dimensional row,
  `BYTES`, and a handful of single-program cases listed by `tests/classify.sh`.

The a68g test set relies heavily on optional libraries (GSL, MPFR, plotutils,
R, the network) and on `LONG LONG REAL`; the 29 programs that run
deterministically on a plain a68g were used, of which 16 are reproduced exactly.

## 3a. The C back end

Everything above runs the interpreter. `tests/difftest-compiled.sh` runs the
same corpus through `a68lean compile`, executes the resulting native binaries
and compares their bytes with a68g's recorded output. Because both back ends
share `A68.Runtime`, a difference between them can only come from the compiled
*structure* — frames, control flow, jumps — which is what this test exercises.
The same script with `-O0` versus `-O2` checks that the optimiser changes no
observable behaviour.

A random 60 of the golden programs, compiled at `-O2`: 52 match a68g byte for
byte, and each of the other 8 also fails under the evaluator: five are front-end
errors, two depend on multi-precision `LONG REAL`, and one on `LONG INT`
overflow behaviour. Of the 15 programs that exceed the time limit
under the evaluator, 13 match when compiled; Erdős–Nicolas numbers and the
test set's rationals program exceed it compiled as well.

Running the corpus this way found four defects that only compiled programs had,
each now fixed and covered by an in-repo case: a subscript through a
`REF STRING` or `REF [] INT` parameter sliced the cell holding the name instead of
the row; values of declared modes such as `MODE YEAR = INT` could not be printed,
because the compiled runtime had no table of mode declarations; a `GO TO` from a
routine to a label outside it hung, because landing never cleared the pending
jump; and an event routine leaving with a `GO TO` was taken to have returned,
because the runtime did not look at the pending jump after calling compiled
code.

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

Result: 1,000 of 1,000 generated programs (seeds 1–1000) produce
identical output and exit status with the final binary; a further 1,500
programs (seeds 1001–2500) agreed with earlier builds. Fuzzing found two real defects during
development (a missing uninitialised-value check on identity declarations and
a generator-independent format bug), both fixed.

`fuzz/run-compiled.sh START COUNT -O1|-O2` does the same through the C back end:
it compiles each program, runs the binary, and compares with a68g. Every change to
the back end was fuzzed with 300 fresh programs, 150 at each level, before it was
merged. This caught two defects. `x +:= e` with a non-trivial right operand wrote
through a reference to a variable that had been promoted to a C variable and had
no cell (seed 12102). And `REAL` division checked its quotient, which a68g does
not: `exp(769.9) / 1000.0` is an infinity a68g carries on with, and only a later
operation that checks, such as `*` or printing, reports it (seed 60083).

## Reproducing

```bash
brew install algol68g coreutils        # a68g 3.13.3 and gtimeout
lake build
tests/run-cases.sh
tests/run-cases-compiled.sh -O2
( cd tests/fmt && python3 gen.py 1 300 && a68g cases.a68 > expected.txt \
  && ../../.lake/build/bin/a68lean fmttest cases.txt > actual.txt && diff expected.txt actual.txt )
tests/fetch-corpus.sh                  # ~20 minutes: clones, records a68g output
tests/run-corpus.sh                    # ~30 minutes
fuzz/run.sh 1 1000
fuzz/run-compiled.sh 1 150 -O2
```
