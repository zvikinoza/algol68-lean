# `num_*` benchmarks: scalar numeric computation

Six benchmarks stressing scalar arithmetic — REAL floating point, INT/REAL
widening, integer division and remainder, exponentiation, a branchy REAL
kernel, and the standard-prelude maths functions.  Each has a hand-written C
twin in `native/` performing the identical operation sequence, so the C timing
is a genuine roofline rather than a rewrite.

All six produce **identical output** under `a68g`, `a68lean run`,
`a68lean compile`, and the native C twin.

## Conventions

* Every program prints exactly one integer.  Where the kernel is floating
  point the printed value is `ROUND (x * <scale>)`, so no float formatting is
  involved and the two sides agree exactly.
* The printed value always fits in a 32-bit `INT`: a68g's `max int` is
  `2147483647`, i.e. **`INT` is 32-bit**, so every intermediate is kept inside
  that range.
* The C twins carry `#pragma STDC FP_CONTRACT OFF`.  Without it `cc -O2` is
  free to contract `x*x - y*y + x0` into an FMA, which changes the last bits
  and makes the Mandelbrot escape counts disagree.
* No `random`, no input, no files.

## The six benchmarks

| benchmark | what it stresses | declared ops | output |
|---|---|---|---|
| `num_real` | pure REAL arithmetic: a 2-D rotation recurrence plus an accumulator, 5e6 iterations at 8 flops each | 4e7 | `500000` |
| `num_horner` | mixed INT/REAL: Horner evaluation of a degree-15 polynomial with INT coefficients; `INT / INT` and `REAL + INT` both force widening | 2.0e7 | `11107158` |
| `num_divmod` | integer `OVER` and `MOD`: four division/remainder ops per iteration, 8e6 iterations | 3.2e7 | `999983` |
| `num_power` | `**` with both constant and varying INT exponents, 5e6 iterations | 1.5e7 | `453713` |
| `num_mandel` | branchy REAL kernel: Mandelbrot escape counts over a 400x300 grid, cap 200.  A single differing bit flips an escape decision, so this is a strong bit-exactness test | 5.4e6 | `5435527` |
| `num_math` | standard-prelude `sqrt`, `sin`, `exp`, `ln` over 6e6 points | 2.4e7 | `1298798` |

## Measured times (seconds)

The development machine had other benchmark jobs running for much of this
session, so wall-clock numbers vary by up to 3x between runs.  The `a68g`
column is a best-of-5 CPU time (user+sys) taken during a quiet window and is
the reliable one; the `run` / `compile` columns are single wall-clock samples
and should be treated as indicative only.  `native` is `cc -O2` on the twin.

| benchmark | native | a68g | a68lean run | a68lean compile |
|---|---|---|---|---|
| `num_real`   | 0.03 | 2.14 | 12.5 | 16.0 |
| `num_horner` | 0.01 | 2.26 | 33.7 | 45.3 |
| `num_divmod` | 0.03 | 1.34 | 14.0 | 26.8 |
| `num_power`  | 0.03 | 1.31 | 60.7 | 31.0 |
| `num_mandel` | 0.02 | 2.95 | 28.4 | 43.2 |
| `num_math`   | 0.06 | 1.58 | 19.2 | 25.5 |

Every a68g time sits inside the requested 1-5 s window.

### Performance observation (not a correctness bug)

**`a68lean compile` is consistently slower than `a68lean run`, and both are an
order of magnitude slower than a68g interpreted, on scalar numeric code.**
`num_real`: native 0.03 s, a68g 2.1 s, a68lean compiled 16.0 s — roughly 500x
off the C roofline and 8x slower than the reference interpreter.  Inspecting
the emitted C shows why: every REAL value goes through

```c
a68_v(a68rt_push_real(<literal>, W));
```

i.e. values are boxed onto a Lean-object stack rather than held in registers.
Unboxing scalars is the obvious first target for the C back end; until then
the `comp*` variants will not beat `a68g` on any of these six.

## Compiler bug found

### REAL literals lose precision in the C back end (`compile` only)

The C emitter formats REAL constants with 6 decimal places, so any literal
needing more precision — or any literal smaller than 5e-7 — is emitted wrong.
Small literals become exactly `0.0`.

`a68g` and `a68lean run` are both correct; only `a68lean compile` is affected.

**Reproducer A — small literal becomes zero**

```algol68
BEGIN
  REAL z := 1.0e-7;
  print((ROUND (z * 1.0e9), newline))
END
```

| | output |
|---|---|
| `a68g` | `+100` |
| `a68lean run` | `+100` |
| `a68lean compile` | `+0` |

**Reproducer B — precision truncated to 6 decimals**

```algol68
BEGIN
  REAL z := 0.1234567891;
  print((ROUND (z * 1.0e10), newline))
END
```

| | output |
|---|---|
| `a68g` | `+1234567891` |
| `a68lean run` | `+1234567891` |
| `a68lean compile` | `+1234570000` |

The generated C for reproducer B makes the cause plain:

```c
    a68_v(a68rt_push_real(0.123457, W));
```

`0.1234567891` has been printed as `0.123457`.  The fix is to emit REAL
constants in a round-trip-exact format (`%.17g`, or a C99 hex float literal)
rather than a fixed 6-decimal format.

Note that constant *folding* hides the bug in some expressions: writing
`ROUND (1.0e-7 * 1.0e9)` directly yields the correct `+100`, because the
multiply is folded before the constant reaches the emitter.  The bug only
shows once a literal survives into the generated C as its own constant.

### Benchmark dropped because of this bug

The originally planned mixed INT/REAL benchmark, `num_mixed`, accumulated
`s + k / (i + 1) + i * 1.0e-7` over 3e6 iterations.  Under `a68lean compile`
the `i * 1.0e-7` term vanished entirely, the literal having been emitted as
`0.000000`:

* expected (a68g, `a68lean run`, native C): `47764125`
* `a68lean compile`: `2764110` — exactly the sum with the `1.0e-7` term missing

Rather than reword the benchmark around the bug, `num_mixed` was **removed**
and `num_horner` written in its place to keep mixed INT/REAL widening covered.
`num_horner` uses no exponent-notation literals and agrees under all four
implementations.  `num_mixed` is worth restoring once the bug is fixed: a
widening-heavy loop with a wide dynamic range is exactly the case that caught
this.

## Checked and correct

Confirmed identical across `a68g`, `a68lean run` and `a68lean compile`:

* `OVER` / `MOD` / `%` / `%*`, including the Algol 68 sign rule
  (`(-7) %* 3` is `+2`, unlike C's `-1`).  The benchmarks keep operands
  non-negative so the C twins can use plain `/` and `%`.
* `INT ** INT` (exact), `REAL ** INT`, `REAL ** REAL`.
* `INT / INT` yielding REAL, and INT-to-REAL widening in mixed expressions.
* `ROUND`, `ENTIER`, `SHORTEN`, `ABS`, `BIN`.
* `sqrt`, `sin`, `cos`, `tan`, `arctan`, `exp`, `ln` — bit-identical to the C
  twins' libm calls, which is why `num_math` can compare exactly.
* `BITS`: `AND`, `OR`, `XOR`, `SHL`, `SHR`, `ABS`.
* `LONG INT` arbitrary-precision arithmetic (`long max int` is 49 nines under
  both a68g and a68lean).

One parser note, identical in both implementations and not a bug: a bold-tag
declaration whose identifier is the single letter `L` (`LONG INT L := ...`) is
rejected by a68g *and* a68lean alike.  Any other name works.
