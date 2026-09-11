# Compatibility with Algol 68 Genie

The goal of `a68lean` is that a program produces the *same bytes on standard
output and the same exit status* as Algol 68 Genie 3.13.3 (the Homebrew build
on macOS/arm64, a "level 2" build with 32-bit `INT` and double `REAL`). This
document records the behaviours that had to be reproduced deliberately and the
differences that remain.

Everything here was established by running a68g on probe programs and, where
the observable behaviour alone was ambiguous, by reading a68g's C source to
learn the exact algorithm. No a68g code was copied; the algorithms were
re-implemented in Lean.

## Numbers

* `INT` is 32-bit: `max int = 2147483647`; any result outside
  `[-max int, max int]` is the runtime error *INT value overflow*
  (so `-max int - 1` is an error, as in a68g).
* `LONG` and `LONG LONG` modes use a68g's own multi-precision arithmetic,
  reproduced digit for digit in `A68.MP` (see below): `LONG INT` has 49 decimal
  digits and `LONG LONG INT` 84 (radix 10⁷ with 7 and 12 digit blocks);
  `PR precision N PR` sets `LONG LONG` to `2 + ⌈N/7⌉` blocks.
* `REAL` is IEEE double. Every arithmetic operation and mathematical function
  checks its result: an infinity is *infinite REAL value*, a NaN is
  *REAL value is not a number*, and division by zero is an error.
* `**`: `INT ** INT` and `REAL ** INT` use square-and-multiply in a68g's exact
  order of multiplications (which matters for the last bits of `REAL` results);
  `REAL ** REAL` is `exp(y * ln x)`, not `pow`, again to match a68g bit for bit.
* `ROUND` rounds half away from zero; `ENTIER` is floor; both are range-checked.
* `%`/`OVER` truncates toward zero; `%*`/`MOD` is always non-negative.
* Widening: a68g accepts chains such as `INT → REAL → COMPL` and
  `INT → LONG INT → LONG REAL` in strong positions, and widens mixed operands
  of the standard operators (`LONG 1 + 1`, `1.5 + LONG 1`). User-defined
  operators receive only firm coercions (no widening), exactly as in a68g.
* `SHORT` modes are identical to the base modes.

## LONG and LONG LONG arithmetic

This a68g build is "level 2" (clang, no 128-bit integer or floating types, no
MPFR), so `LONG REAL`, `LONG LONG REAL`, `LONG INT`, `LONG LONG INT` and the
`COMPLEX` modes built on them are all a68g's multi-precision numbers (`mp.c`):
a status word, an exponent and digits in radix 10⁷, of which `LONG` modes have 7
and `LONG LONG` modes 12 (`2 + ⌈p/7⌉` after `PR precision p PR`). `long real
width` is 42, `long long real width` 70, `long max real` is `1e+999999`,
`long small real` is `1e-42`, and exponents beyond ±142857 radix digits are the
error *multiprecision value out of bounds*.

`A68.MP`, `A68.MPMath` and `A68.MPFmt` re-implement a68g's routines step by
step rather than computing correctly rounded results, because a68g's are not:

* every operation works on a scratch number two digits longer, normalises, and
  rounds back with the "Gaussian" rounding as `mp.c` writes it (a half-way digit
  adds one to an odd digit and two to an even one);
* guard digits beyond the precision an operation is asked to use are left in
  place, and later operations read them (e.g. `sqrt_mp` rounds with the guard
  digits of an earlier `rec_mp`);
* digits are C doubles; the only inexact double arithmetic, the quotient-digit
  estimates of `div_mp` and `div_mp_digit` (which clang compiled to `fmadd`), is
  reproduced exactly with integer arithmetic;
* the elementary functions follow `mp-math.c` and `mp-pi.c`: Newton iterations
  seeded with the C library's `sqrt`, `cbrt`, `log`, `atan`, Taylor series with
  a68g's stopping rule, argument reduction by halving (`exp`) and thirds (`sin`),
  and a68g's caches, which make results depend on history: π and its derived
  constants are kept at the precision of the request that needed most digits and
  truncated for later requests, ln 10⁷ and ln 10 are kept and rounded on each use;
* formatting of long values (`print`, `whole`, `fixed`, `float`, general
  patterns) is done with multi-precision arithmetic at the value's own precision,
  as `transput-formatting.c` does, so digits are rounded where a68g rounds them;
* `LONG INT` values are exact integers here: their sums, differences and
  products are exact in a68g too and checked against the same range, while
  `OVER`, `MOD` and `**` go through a68g's real division and power;
* conversions: `LENG` and the widening of a `REAL` use `real_to_mp` (21
  significant digits from a floating-point loop), an `INT` widens exactly,
  `SHORTEN` of a `LONG INT` wraps as `mp_to_int`'s 32-bit weights do
  (`SHORTEN LONG 100000000000000` is `276447232`), and a REAL denotation that is
  widened — in a strong position, or as the operand of a standard operator —
  is read again at the longer precision (`LONG 1.0 + 1.1` is exactly 2.1, while
  `-1.1` widened is not, being a formula);
* `LONG INT ** LONG INT` has no operator of its own in a68g, so both operands
  widen to `LONG REAL`.

Differential testing of about 12,000 random `LONG`/`LONG LONG` operations,
functions, conversions and formatting calls agrees with a68g on every output.

## Printing numbers

The layouts of `print` and of `whole`, `fixed` and `float` are those of a68g:

| value | layout |
|---|---|
| `INT` | `whole (x, 11)`: sign plus 10 digits, right aligned |
| `LONG INT` / `LONG LONG INT` | width 50 / 85 |
| `REAL` | `float (x, 22, 14, 4)`: `+d.dddddddddddddde  +e` |
| `BOOL` | `T` / `F` |
| `BITS` | 32 flip/flop characters |
| rows, structs | elements back to back, no separators |

`fixed` and `float` are re-implementations of a68g's `fixed`, `real`,
`sub_fixed_mp` and `standardize_mp`, including their quirks: the recursion
that drops decimals when a value does not fit (`fixed (123.456, 5, 1)` is
` +123`), the missing leading zero when there is no room (`fixed (0.5, 4, 2)`
is `+.50`), error characters `*` when nothing fits, and `float`'s retry with a
wider exponent field. All of this is done in exact decimal arithmetic.

The one inexact step in a68g is converting a `double` to its multi-precision
representation (`real_to_mp` in the generic build): it takes `⌊log10 x⌋`,
divides by a power of ten built from a table of `10^(2^k)`, and extracts three
7-digit blocks with `modf (a * 10^7)` in double arithmetic. `Numfmt.realToDec`
performs the same floating-point steps so the same 21 digits come out, which
is why a68lean prints `123456789012345671.653` for
`fixed (123456789012345678.0, 0, 3)` just as a68g does, rather than the exact
value. A differential test of 3,441 formatting cases (`tests/fmt`) agrees with
a68g on all but four, which involve `fixed` of values ≥ 10⁷⁰ where a68g's
84-digit window swallows the rounding term.

## Formatted transput

`printf` follows a68g's picture machinery: a format is a sequence of
pictures (insertions, patterns, replicated collections); values consume
patterns in order, insertions are emitted as they are passed, trailing
insertions are emitted when the format is exhausted, after which the format
restarts. Details reproduced from a68g:

* Numeric patterns are *moulds*: the sign of an integral pattern floats only
  through the `z` frames *before* the sign frame; in a real pattern a68g shifts
  it through the whole integral part (so `$-zd.ddddd$` prints ` -0.00000`).
* `z` frames print blanks until the first non-zero digit; insertions inside a
  suppressed zone are printed as blanks; a negative value with no sign frame is
  a runtime error; too many digits is *error transputting INT value*.
* `g` alone prints with the standard layout; `g(w)`, `g(w,a)`, `g(w,a,e)`
  are `whole`, `fixed`, `float`.
* `n(k)a` reads/writes exactly `k` characters; `b`, `b("t","f")`, `c(…)`.
* A comma separates pictures; a literal `","` inside a numeric pattern is an
  insertion (`$3d","3d$` is one six-digit pattern).
* `n k` aligns to column `n` of the current `printf` line.
* `f(fmt)` enters an embedded format that is left when exhausted.
* Strings are one value each (not straightened into characters).
* A `COMPL` is written and read as two `REAL` values, each taking a pattern of its
  own, so `$gl$` puts its parts on two lines.
* Bits patterns `16r8d`, `n(base)r4z` write and read `BITS` through a mould in any
  radix from 2 to 16; `z` frames blank leading zeros and read a blank as a zero.
* `h`, `h(a)`, `h(a,m)`, `h(w,a,m)`, `h(w,a,e,m)` write a number with a68g's `real`,
  whose exponent is a multiple of `m` (3 by default); `h` alone writes other modes as
  `g` does.
* C-style patterns `%[-][+][w][.a]d i f e g b o x s c` follow a68g's
  `write_c_pattern`: the conversion's leading blanks are dropped and the text aligned
  right in the width, or left for `-`; `%g` chooses fixed notation when the exponent is
  from -3 to the number of decimals.  On input a width reads exactly that many
  characters.  `%c` cannot write, as in a68g.

## Reading

`read`/`get` items receive names: `INT` reads an optional sign and digits
(so `1-3` yields 1 and leaves `-3`), `REAL` also a fraction and exponent,
`STRING` reads to the end of the line or a `make term` terminator, a fixed
`[n]CHAR` reads exactly `n` characters, structs and rows are read element
by element, and a `UNION` is read with the mode of the value it currently holds. End
of file calls the `on logical file end` mender; if it returns
`TRUE` the rest of the transput call is abandoned.

## Files

`open` returns 0 for an existing regular file and otherwise the error number `stat`
gives (`ENOENT` for a directory), and sets the file up either way, as a68g opens files
when they are first used; `establish` creates a file; `associate` connects a file with
a `STRING` variable.  The string is emptied when the file turns to writing, and each
write appends to what the string then holds; reading continues at the position reached,
in the string's current value.  `close` writes disk files; `reset` and `rewind` rewind,
and like `set` are refused unless the channel allows them (`stand back channel` and
associated files do, `stand in channel` and `stand out channel` do not, which is also
what `reset possible` and its relatives say). `scratch` and `erase` remove a file
that has been used. Standard files are `stand in`, `stand out`, `stand error`.

a68g collects transput in C strings, so a NUL character ends the text that reaches
standard output until the buffer is next purged: after each item of `print`, and at a
new line, a new page or the end of a `printf`.  `print (("a" + REPR 0 + "b", "c"))`
writes `ac`.

`BYTES` and `LONG BYTES` are rows of 32 and 256 characters, padded with NUL; `bytes pack`,
`ELEM`, the comparisons and the widening to `[] CHAR` and `STRING` are provided.

## Operating-system procedures

`system`, `fork`, `wait pid`, `execve`, `execve child`, `execve child pipe`,
`execve output`, `get directory` (in `readdir` order), the `file is ...` enquiries and
`file mode` (from `stat`, so `file is link` is never true, as in a68g), `grep in string`,
`grep in substring` and `sub in string` (POSIX extended regular expressions, taking the
widest of the first `re_nsub` matches as a68g does), `getenv`, `local time`, `utc time`,
`strerror`, `errno`, `get pwd`, `set pwd`, `realpath` and `sleep` call the C library
routines a68g calls (`csrc/sys.c`), and so do `gamma`, `ln gamma`, `erf`, `erfc` and
`ln1p`.  Standard output is flushed before a process is forked or a command run, so the
child's output follows what the program printed before.  `rows` and `columns` are 24 and
500, a68g's values when standard output is not a terminal.

`evaluate` parses and elaborates its text in the environment of the call, sees the
names visible there, and gives the value as `print` writes it.  The names reach it as a
format text holding a name of each cell (`Elab.evaluateScope`), which both back ends
keep alive.

## Random numbers

a68g uses the taus113 generator (from GSL). `first random (n)` seeds it and
`random` draws from it; a68lean implements the same generator, so seeded
programs produce identical sequences. Without `first random`, a68g seeds from
the clock, and no implementation can reproduce a given run; those programs are
reported separately by the test scripts.

## Miscellaneous a68g behaviours reproduced

* Uninitialised `INT`, `REAL`, `BOOL`, `CHAR` values raise a runtime error
  when used; uninitialised `STRING`s are empty; copying a struct with
  uninitialised fields is allowed.
* `p IS NIL` never dereferences the variable `p` (a name is never `NIL`).
* Row assignment to a non-`FLEX` name requires identical bounds.
* `~` is `NOT` before an operand and `SKIP` otherwise; `~=` is `/=`;
  `ANDF`/`ANDTH`/`THEF` and `OREL`/`ORF` short-circuit; `DOWNTO`; `END.`
  with a trailing period; backslash-newline continues a string.
* `PR echo "text" PR` prints the text at start-up; `PR regression PR` makes
  a final unterminated output line end with a newline; `PR precision N PR`.
* `program idf` is the source file name; `argv (1)` is `a68g`.
* Subscripting with parentheses (`a(i)`) is accepted for rows.

## Known differences

* **`LONG INT` division by zero** gives an infinite `LONG INT` in a68g, which
  a68g then cannot print (it loops); here it is a run-time error. Likewise
  `ENTIER` of an infinite `LONG REAL` hangs a68g and is an error here.
* **Long values in numeric patterns** (`$-d.3d$` and the like) are formatted
  from their exact decimal value; a68g lengthens them to `LONG LONG` precision
  first, which agrees except where rounding at 84 digits would carry.
* **`long erf`, `long gamma`** and the `pi`-scaled functions (`long sinpi`, …) are
  not provided. The `LONG COMPLEX` functions are, following `mp-complex.c`.
* **Unsupported a68g extensions**: `UP` and `DOWN` on semaphores, `sound`, curses,
  plotutils, GSL, MPFR, R mathlib, sockets, `http content`, and the `PIPE` mode
  indicant (the values `execve child pipe` yields can be used, but `PIPE` cannot be
  written as a declarer).  Refinements, partial parametrisation (`f (x, )`),
  `DO … UNTIL … OD`, `NEW`, the environ modes `ZAHL`, `DOUBLE` and `QUAD`, and `LEVEL`
  are supported.
* **`PAR` clauses** run their units one after another, left to right.  a68g
  runs them on threads, and its output then depends on scheduling: six runs of
  Rosetta Code's concurrent-computing program give three different orders, so
  no implementation can reproduce a given run.
* **`evaluate`** accepts any unit here.  a68g evaluates the text with its monitor, which
  only knows expressions over the standard environment: it refuses calls of the
  program's own procedures and operands that need widening (`1.5 * 2`), prints a
  monitor error and returns the text.  Programs a68g evaluates successfully get the
  same result; where a68g reports a monitor error the texts of the errors differ.
* **`open` followed by writing** appends to the file's contents here; a68g writes over
  them from the start without truncating.
* **Output already written when formatted transput fails.** When a `printf`
  picture cannot accept the value it is given, a68g discards the characters it
  had produced for that item and this implementation keeps them. Both fail on
  the same line with a non-zero status, but the bytes before the failure differ:
  a68g emits nothing for the item, and `a68lean` emits the part it had already
  converted. The evaluator and the compiled program agree with each other; it is
  a68g they differ from. Found by differential fuzzing at seed 9535.
* **A display coerced to a union** is accepted here and rejected by a68g, which
  is right: a display has no a priori mode, so it cannot be the operand of a
  union coercion. This can only affect programs a68g refuses outright, so it
  cannot change the output of a program a68g accepts.
* **`COMPL` division** has no reference behaviour to match: a68g 3.13.3 stops
  with a memory access violation on `z / w` and `z /:= w` for complex `z` and
  `w`, whatever their values. a68lean divides, and reports a zero divisor.
* **Runtime error messages** are not byte-identical; only standard output
  and the non-zero exit status are.
