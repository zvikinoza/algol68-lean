# Testing

The correctness target is *byte-for-byte equality of standard output with
Algol 68 Genie 3.13.3* plus agreement on success/failure. Four layers of tests
serve that goal.

## 1. In-repo regression suite (`tests/cases`)

Small programs covering every construct area (formats, loops and cases,
procedures and operators, modes, names into rows). Their expected outputs were
recorded from a68g (`tests/run-cases.sh --record`) and are checked with
`tests/run-cases.sh`. All 7 pass.

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
| Rosetta Code, ALGOL 68 solutions (1,328 files) | 729 | 651 |
| Algol 68 Genie bundled test set (39 files) | 31 | 17 |

Non-passing programs are classified by `tests/classify.sh`:

* **random-seeded** (27 programs): they call `random` without
  `first random`. a68g seeds its generator from the wall clock, so the recorded
  reference output is a snapshot of one second; it cannot be reproduced by a68g
  itself either. (Programs that seed with `first random` are reproduced
  exactly: a68lean implements a68g's taus113 generator.)
* **LONG REAL** (18 programs): output depends on a68g's 42/70-digit
  multi-precision reals, which a68lean does not implement.
* **other** (33 programs): mostly a68g-specific extensions that are out of
  scope — `evaluate` (run-time evaluation of source text), `system`, `fork`,
  `execve child pipe`, `getenv`, `local time`, `get directory`,
  `file is directory`, `grep in string`, `rewind`, `reset possible`, and
  `BYTES` — plus a few genuine gaps: rowing a scalar into a
  multi-dimensional row (2 programs), reading into a `UNION`, one
  format-purge corner case, one `COMPL` printing layout, two programs whose
  expected output relies on `INT`/`LONG INT` overflow behaviour that differs,
  and 4 programs that exceed the 90-second time limit (a68lean interprets
  roughly ten times slower than a68g on tight numeric loops).

The a68g test set relies heavily on optional libraries (GSL, MPFR, plotutils,
R, the network) and on `LONG LONG REAL`; the 31 programs that run on a plain
a68g were used, of which 17 are reproduced exactly.

## 3a. The C back end

Everything above runs the interpreter. `tests/difftest-compiled.sh` runs the
same corpus through `a68lean compile`, executes the resulting native binaries
and compares their bytes with a68g's recorded output. Because both back ends
share `A68.Runtime`, a difference between them can only come from the compiled
*structure* — frames, control flow, jumps — which is what this test exercises.
The same script with `-O0` versus `-O2` checks that the optimiser changes no
observable behaviour.

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

## Reproducing

```bash
brew install algol68g coreutils        # a68g 3.13.3 and gtimeout
lake build
tests/run-cases.sh
( cd tests/fmt && python3 gen.py 1 300 && a68g cases.a68 > expected.txt \
  && ../../.lake/build/bin/a68lean fmttest cases.txt > actual.txt && diff expected.txt actual.txt )
tests/fetch-corpus.sh                  # ~20 minutes: clones, records a68g output
tests/run-corpus.sh                    # ~30 minutes
fuzz/run.sh 1 1000
```
