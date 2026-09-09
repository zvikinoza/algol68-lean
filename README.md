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

| Test suite | Programs | Byte-identical to a68g |
|---|---|---|
| Rosetta Code ALGOL 68 solutions (a68g-runnable, deterministic) | 729 | 651 |
| Algol 68 Genie bundled test set (a68g-runnable) | 31 | 17 |
| In-repo regression cases | 7 | 7 |
| Random programs (grammar-based fuzzing, seeds 1–1000) | 1,000 | 1,000 |

The corpus failures fall into three groups (see [docs/TESTING.md](docs/TESTING.md)):
programs that use `random` without seeding it (a68g seeds from the clock, so the
reference output is not reproducible by any implementation), programs whose
output depends on a68g's multi-precision `LONG REAL` arithmetic (not
implemented: `LONG REAL` is IEEE double here), and a small remainder of
unsupported a68g extensions or genuine gaps listed in the testing document.

## Quick start

```bash
# toolchain: Lean 4 via elan (https://github.com/leanprover/elan)
lake build                                  # builds the compiler and checks all proofs
.lake/build/bin/a68lean run hello.a68       # compile and run a program
.lake/build/bin/a68lean check hello.a68     # parse + mode check only
.lake/build/bin/a68lean dump hello.a68      # print the elaborated core representation
```

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
* **Modes**: `INT REAL BOOL CHAR BITS COMPL STRING VOID`, `LONG`/`LONG LONG`
  (`LONG INT` with a68g's 49/84-digit limits and `PR precision`), `REF`,
  multi-dimensional and `FLEX` rows, `PROC`, `STRUCT`, `UNION`, recursive
  mode declarations, structural mode equivalence.
* **Elaboration**: the Algol 68 coercion system with its five strengths
  (strong, firm, meek, weak, soft): deproceduring, dereferencing, uniting,
  widening (with a68g's chained widening), rowing and voiding; balancing of
  conditional and case clauses; operator identification with user overloading;
  scope resolution to frames and slots; enquiry-clause scoping.
* **Execution**: 32-bit `INT` with overflow detection, IEEE `REAL` with
  a68g's checks for infinities and NaNs, a68g's square-and-multiply `**`,
  uninitialised-value detection, names into rows and structs (slices, trims,
  fields), flexible rows with bounds checks, closures, jumps, `stop`.
* **Transput**: `print`/`write`, `printf` with the a68g picture language
  (integral, real, string, boolean, choice and general patterns, replicators,
  insertions, `k` alignment, embedded formats `f(…)`), `read`/`readf`,
  files (`open`, `establish`, `associate`, `get`, `put`, `getf`, `reset`,
  `close`, `on logical file end`, `on value error`, `make term`), and
  byte-exact `whole`, `fixed`, `float` reproducing a68g's multi-precision
  formatting including its double-to-decimal conversion quirks.
* **Standard prelude**: arithmetic, string and bits operators, the
  mathematical functions, `char in string`, `string in string`, character
  classification, a68g's taus113 random generator (`random`, `first random`),
  environment enquiries.

## Project layout

```
A68/Syntax.lean      abstract syntax
A68/Lexer.lean       tokeniser
A68/Parser.lean      recursive-descent parser with pre-scan
A68/Mode.lean        modes and mode equivalence
A68/Core.lean        runtime values and the core representation
A68/Builtins.lean    modes of the standard prelude
A68/Numfmt.lean      byte-exact number formatting (whole/fixed/float)
A68/Elab.lean        elaborator: mode checking, coercions, operator identification
A68/Interp.lean      evaluator, standard prelude, formatted transput, files
A68/Verified/        machine-checked theorems
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
