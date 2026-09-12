# a68lean — an Algol 68 compiler written in Lean 4

`a68lean` is an implementation of Algol 68 written from scratch in Lean 4. It
compiles Algol 68 source into an explicitly typed, coercion-resolved core
representation and executes it, reproducing the observable behaviour of
[Algol 68 Genie](https://jmvdveer.home.xs4all.nl/en/algol.html) (a68g), the
reference implementation, **byte for byte** on its standard output.

Lean was chosen so that the implementation is verifiable: every function is
total unless marked `partial`, the type checker rules out whole classes of
bugs, and the parts of the design most prone to subtle errors are backed by
machine-checked theorems (see [docs/VERIFICATION.md](docs/VERIFICATION.md)).

## Status

| Test | Programs | Byte-identical to a68g |
|---|---:|---:|
| Rosetta Code ALGOL 68 solutions (a68g-runnable, deterministic), compiled `-O2` | 744 | 735 |
| Algol 68 Genie bundled test set (a68g-runnable, deterministic), compiled `-O2` | 29 | 28 |
| The same 773 programs through the evaluator | 773 | 754 |
| In-repo regression cases, evaluator and C back end at `-O0`, `-O1`, `-O2` | 67 | 67 |
| Random programs through the C back end, `-O1` and `-O2`, also under the collector's stress and verify modes | 500 | 500 |
| Random programs through the evaluator | 300 | 300 |

Of the ten corpus programs that differ when compiled, four print the date, the
host name or a speed measured while running (one of them overflows an `INT` with
the speed the compiled program reaches), one depends on the order in which a68g's
threads ran a `PAR` clause, two use extensions not implemented here (a web page
fetched with `http content`, semaphores between parallel units), and three use
`evaluate`, which compiles Algol 68 text at run time and is available under
`a68lean run` only. The evaluator additionally runs out of time on 12 programs that
pass compiled. See [docs/TESTING.md](docs/TESTING.md).

## Speed of the compiled program

`a68lean compile` produces a native binary through LLVM (`docs/LLVM-DESIGN.md`): the
elaborated core is lowered to MIR, a typed register-machine IR with a semantics in Lean
and optimisation passes each proved to preserve it, printed as LLVM IR and compiled by
clang against the C runtime. Values of primitive mode are native, locals that cannot
escape are registers, routines with primitive signatures are plain functions called
directly, and rows, structures, unions, strings and names are reached inline through
the runtime's own object layout, with the runtime as the fallback whenever a value is
not as expected. Every benchmark in `benchmarks/` ships with a C twin computing the same
answer, which is the ceiling the emitted code is measured against.

| benchmark | LLVM back end vs hand-written C |
|---|---:|
| `intloop`, integer arithmetic in a loop | 1.3x |
| `num_real`, `num_divmod`, real and integer arithmetic | 1.0x |
| `ctl_fib`, 18 million recursive calls | 1.5x |
| `ctl_mutual`, three mutually recursive routines | 1.3x |
| `calls`, `ctl_hof`, procedure calls and procedures as parameters | 1.5x–2x |
| `arraysum`, 40 million row element accesses | 1.7x |
| `data_matmul`, matrix multiplication | 1.8x |
| `data_list`, walking a linked list of `HEAP` nodes | 1.7x |
| `data_slice`, a sliding window taken by slicing | 1.8x |
| `sieve`, a sieve over 2 million `BOOL`s | ~1x (at the timer's resolution) |
| `data_struct`, `data_union` | 2x–3x |
| `data_string`, building and comparing strings | 6x |

The C back end (`--c`) was the proof of concept for the compiled structure — frames,
control flow, jumps, promoted variables — and stays as a second implementation the
test suites run for comparison; the evaluator (`a68lean run`) is the specification both
are checked against. See [benchmarks/ROOFLINE.md](benchmarks/ROOFLINE.md) for all 22
programs and for what is left.

## Quick start

```bash
# toolchain: Lean 4 via elan (https://github.com/leanprover/elan)
lake build                                    # builds the compiler and checks all proofs
.lake/build/bin/a68lean run hello.a68         # compile and run in one step
.lake/build/bin/a68lean compile hello.a68     # compile to LLVM IR and link a native binary
./hello                                       # …then run it
.lake/build/bin/a68lean compile hello.a68 -c  # keep the generated LLVM IR only
.lake/build/bin/a68lean compile hello.a68 --c # the C back end instead
.lake/build/bin/a68lean dump-mir hello.a68 -O2   # print the MIR the back end optimises
.lake/build/bin/a68lean check hello.a68       # parse + mode check only
.lake/build/bin/a68lean dump hello.a68        # print the elaborated core representation
```

`compile` accepts `-o <file>`, `-O0`/`-O1`/`-O2` (optimiser level, default
`-O1`) and `-v` (report how many core nodes the optimiser removed).

```algol68
BEGIN
  PROC fact = (INT n) INT: IF n <= 1 THEN 1 ELSE n * fact(n - 1) FI;
  FOR i TO 5 DO printf(($g(0)"! = "g(0)l$, i, fact(i))) OD
END
```

To reproduce the differential tests you need a68g (`brew install algol68g`)
and GNU coreutils (`gtimeout`):

```bash
tests/run-cases.sh          # in-repo regression suite
tests/fetch-corpus.sh       # sparse-clone Rosetta Code + a68g test set, record a68g output
tests/run-corpus.sh         # run a68lean on every golden program, compare byte for byte
fuzz/run.sh 1 200           # differential fuzzing: 200 random programs from seed 1
```

## What is implemented

* **Lexing** of upper-stropped Algol 68 as accepted by a68g: bold words, tags
  with insignificant spaces (`new line`), numerals with embedded spaces
  (`10 000`), radix denotations (`16rff`), `#`/`CO`/`COMMENT` comments,
  pragmats (`PR precision 100 PR`, `PR echo "…" PR`, `PR regression PR`),
  format texts, the exact operator-symbol rule of a68g's scanner.
* **Parsing**: declarations (`MODE`, `PRIO`, `OP`, `PROC`, identity and
  variable declarations with actual bounds, collateral declarations), all
  clauses (serial, closed, collateral, conditional, case, conformity case,
  loops, brief forms `(…|…|…)` and `|:`), routine texts, casts, slices with
  trims and `AT`, selections, jumps and labels, `EXIT` completers, formats.
  User-defined operators and priorities are discovered by a pre-scan.
* **Modes**: `INT REAL BOOL CHAR BITS BYTES COMPL STRING VOID`, `LONG` and
  `LONG LONG` versions of the numeric modes as a68g's multi-precision numbers
  (42- and 70-digit reals, 49- and 84-digit integers, `PR precision`), `REF`,
  multi-dimensional and `FLEX` rows, `PROC`, `STRUCT`, `UNION`, recursive
  mode declarations, structural mode equivalence.
* **Elaboration**: the Algol 68 coercion system with its five strengths
  (strong, firm, meek, weak, soft): deproceduring, dereferencing, uniting,
  widening (with a68g's chained widening), rowing and voiding; balancing of
  conditional and case clauses; operator identification with user overloading;
  scope resolution to frames and slots; enquiry-clause scoping.
* **Execution**: 32-bit `INT` with overflow detection, IEEE `REAL` with
  a68g's checks for infinities and NaNs, a68g's square-and-multiply `**`,
  a68g's multi-precision arithmetic re-implemented digit for digit (`A68/MP*.lean`),
  `COMPL` arithmetic to the last bit, uninitialised-value detection, names into
  rows and structs (slices, trims, fields), flexible rows with bounds checks,
  closures, jumps, `stop`.
* **Transput**: `print`/`write`, `printf` with the a68g picture language
  (integral, real, string, boolean, choice and general patterns, replicators,
  insertions, `k` alignment, embedded formats `f(…)`), `read`/`readf`,
  files (`open`, `establish`, `associate`, `get`, `put`, `getf`, `reset`,
  `close`, `on logical file end`, `on value error`, `make term`), and
  byte-exact `whole`, `fixed`, `float` reproducing a68g's multi-precision
  formatting including its double-to-decimal conversion quirks.
* **Standard prelude**: arithmetic, string and bits operators, the
  mathematical and complex functions at every length, `char in string`,
  `string in string`, character classification, a68g's taus113 random generator
  (`random`, `first random`), environment enquiries, and a68g's extensions:
  regular expressions, `evaluate`, `system`, `fork` and the `execve` family,
  directories and file enquiries, `getenv`, local and UTC time.
* **Two back ends**: a direct evaluator, and a C back end that emits a C
  program linked against a C runtime that transcribes the evaluator routine for
  routine (`csrc/`), so both produce identical bytes; the binary depends on the
  C library alone. The emitted code computes primitive values in C types, keeps
  locals that cannot escape in C variables, rows of primitive elements,
  structures and unions in C arrays and strings in C buffers, and calls routines
  with primitive signatures as plain C functions, falling back to the runtime
  wherever the analysis cannot prove that safe. The runtime collects its heap
  with a precise mark–sweep collector whose model is proved in Lean
  ([docs/GC-DESIGN.md](docs/GC-DESIGN.md)). `evaluate`, which compiles Algol 68
  text at run time, is available under `a68lean run` only.
* **Optimiser**: constant folding by evaluation, coercion simplification,
  constant control flow and frameless-block flattening, mirroring a68g's
  optimiser passes; the same rewrites are proved correct over the formal core.

## Project layout

```
A68/Syntax.lean      abstract syntax
A68/Lexer.lean       tokeniser
A68/Parser.lean      recursive-descent parser with pre-scan
A68/Mode.lean        modes and mode equivalence
A68/Core.lean        runtime values and the core representation
A68/Builtins.lean    modes of the standard prelude
A68/Numfmt.lean      byte-exact number formatting (whole/fixed/float)
A68/MP.lean          a68g's multi-precision arithmetic (mp.c), digit for digit
A68/MPMath.lean      multi-precision functions, π and complex (mp-math.c, mp-pi.c, mp-complex.c)
A68/MPFmt.lean       formatting of LONG and LONG LONG values
A68/Elab.lean        elaborator: mode checking, coercions, operator identification
A68/Interp.lean      evaluator, standard prelude, formatted transput, files
A68/Opt.lean         optimisation passes over the core representation
A68/CodeGen.lean     C back end
A68/Serial.lean      mode and format tables carried by compiled programs
A68/Pretty.lean      readable rendering of the core representation (dump)
A68/Verified/        machine-checked theorems
csrc/rt.c            C runtime of compiled programs: values, frames, operand stack, collector
csrc/io.c            transput: files, formatted and unformatted reading and writing
csrc/prelude.c       the standard prelude
csrc/ops.c           operators, coercions, SKIP values, conformity
csrc/tables.c        the mode and format tables of a compiled program
csrc/fmt.c bigint.c  byte-exact number formatting, arbitrary-precision integers
csrc/mp*.c           a68g's multi-precision arithmetic and its formatting
csrc/os.c            operating-system services (processes, files, time, regex)
csrc/sys.c stubs.c   the evaluator's @[extern] wrappers and dispatch stubs
Main.lean            command line driver
tests/               regression suite and differential-test scripts
fuzz/                grammar-based program generator and fuzz driver
docs/                architecture, compatibility notes, testing, verification
```

## Documentation

* [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) — the compilation pipeline and runtime model
* [docs/COMPATIBILITY.md](docs/COMPATIBILITY.md) — how a68g's behaviour was reproduced, and known differences
* [docs/TESTING.md](docs/TESTING.md) — corpora, methodology, results, fuzzing
* [docs/VERIFICATION.md](docs/VERIFICATION.md) — what is proved and what is not

## License

MIT. Algol 68 Genie, whose behaviour this implementation reproduces and whose
test programs are used as a test corpus, is © Marcel van der Veer (GPL-3).
The Rosetta Code programs used as a test corpus are © their authors (GFDL).
No code from Algol 68 Genie or from any other Algol 68 implementation is
included here.
