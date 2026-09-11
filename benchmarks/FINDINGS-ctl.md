# Control-flow and procedure benchmarks (`ctl_*`)

> **Status.** The times and emitted C below are those of the back end when these
> benchmarks were written, and observation 1 no longer holds. Primitive values
> are now native C, and a routine with a primitive signature is a plain C
> function called directly. Re-measured, best of three CPU seconds:
> `ctl_fib` 0.05 s, `ctl_mutual` 0.09 s, `calls` 0.04 s, all within a few times
> their C twins and well ahead of a68g. `ctl_hof` is unchanged at 10.98 s,
> because its call is through a procedure parameter and cannot be resolved
> statically. See ROOFLINE.md for the current picture.

Six benchmarks that stress control flow and procedure machinery rather than
straight-line arithmetic, each with a hand-written C twin in `native/`.

All six agree, character for character (after the harness's whitespace/`+`
stripping), across the native C twin, `a68g`, `a68lean run`, and
`a68lean compile` at `-O0`, `-O1` and `-O2`.
**No correctness bugs were found in `a68lean`.**

## The benchmarks

| name | what it stresses | ops | result |
|---|---|---|---|
| `ctl_fib` | Deep self-recursion. Naive Fibonacci for n = 25..32: two recursive calls plus a comparison per node, max depth 32. | 1.8e7 calls | 581479 |
| `ctl_mutual` | Mutual recursion. A three-way `f -> g -> h -> f` cycle run 40 000 times at depths 200..300, so the call chain never settles into one function. | 1e7 calls | 31403 |
| `ctl_hof` | Higher order. `reduce` takes a `PROC (INT, INT) INT` as a parameter and calls it in a tight inner loop; two different operators are passed in, so the call site is genuinely indirect. | 1.2e7 indirect calls | 725720 |
| `ctl_ops` | User-defined operators. Two dyadic `OP`s (`ROT`, `MASH`, both `PRIO 7`) and one monadic `OP` (`INV`) applied in an 8 M-iteration loop. | 1.76e7 operator applications | 164985 |
| `ctl_case` | Multi-way dispatch. A `CASE` clause with twelve alternatives plus an `OUT`, selected by `i MOD 12 + 1` so every arm is taken equally often. | 8e6 dispatches | 885262 |
| `ctl_goto` | Hot-path control flow. A `WHILE` whose *condition* short-circuits (`x /= 1 ANDF x < 100000000`) and whose body does real work (Collatz), guarded by a nested `OREL`/`ANDF` test that fires a `GO TO` out of the loop to a label in the procedure body. | 9.7e6 Collatz steps | 669339 |

## Measured times

Best of 2, CPU seconds (user + sys), same convention as `bench.sh`.
`comp2` is `a68lean compile -O2`.

| program | native | a68g | a68lean run | a68lean -O2 |
|---|---|---|---|---|
| `ctl_fib`    | 0.02 | 2.74 | 18.46 | 25.41 |
| `ctl_mutual` | 0.04 | 2.37 | 17.71 | 19.12 |
| `ctl_hof`    | 0.06 | 2.70 | 20.49 | 23.55 |
| `ctl_ops`    | 0.07 | 2.66 | 36.05 | 46.06 |
| `ctl_case`   | 0.03 | 1.69 | 10.51 | 10.93 |
| `ctl_goto`   | 0.01 | 3.70 | 35.30 | 28.98 |

Every `a68g` time lands in the requested 1.7 - 3.7 s band.

The native times are very small because clang inlines and strength-reduces these
kernels aggressively - that is the point of the roofline, not a sign the
benchmark is degenerate: the C twin performs exactly the same arithmetic and
prints the same value.

## Observations

### 1. The C back end is slower than a68lean's own evaluator

In five of six benchmarks `a68lean compile -O2` is *slower* than `a68lean run`,
by 4 % to 38 %. This is not specific to the new benchmarks - the pre-existing
`calls.a68` behaves the same way (7.27 s compiled at `-O2`, against 0.63 s for
`a68g`).

The cause is visible in the emitted C. `a68lean compile -c` on

```algol68
BEGIN
  PROC f = (INT x, INT y) INT: (x + y) MOD 1000003;
  INT s := 0;
  FOR i TO 10 DO s := f(s, i) OD;
  print((s, newline))
END
```

emits, for the loop body:

```c
a68_v(a68rt_enter(1, W));
a68_v(a68rt_set_int(0, 0, i1, W));
a68_v(a68rt_push_ref(1, 1, W));
a68_v(a68rt_push_cell(1, 0, W));
a68_v(a68rt_push_cell(1, 1, W));
a68_v(a68rt_push_cell(0, 0, W));
a68_v(a68rt_call(2, W));
if (a68_jump()) return;
a68_v(a68rt_assign(0, W));
a68_v(a68rt_voiding(W));
a68_v(a68rt_pop(W));
a68_v(a68rt_leave(W));
```

and the procedure itself:

```c
static void a68_fn1(void) {
  a68_v(a68rt_enter_args(2, 2, W));
  a68_v(a68rt_push_cell(0, 0, W));
  a68_v(a68rt_push_cell(0, 1, W));
  a68_v(a68rt_dyop(0, 1, 1, W));
  a68_v(a68rt_push_int(1000003LL, W));
  a68_v(a68rt_dyop(2, 1, 1, W));
  a68_v(a68rt_leave(W));
}
```

So the back end is not compiling Algol 68 to C arithmetic; it is unrolling the
evaluator's bytecode into straight-line calls to a `lean_object*`-based stack
machine (`a68rt_push_*`, `a68rt_pop_*`, `a68rt_dyop`, `a68rt_enter` /
`a68rt_leave`). Values stay boxed, every operand goes through a heap-allocated
stack, and calls go through `a68_dispatch_proc`'s `switch`. Only the `FOR`
control variable is unboxed (`int64_t i1`). The extra cost over the tree-walking
evaluator is the per-node runtime-call overhead with none of the evaluator's
locality, which is why `-O2` can end up behind `run`.

`-O0`, `-O1` and `-O2` produce nearly identical times, consistent with the
optimisation levels affecting the emitted stack-machine program only marginally.

This is a performance characterisation, not a correctness bug; it is recorded
here because it is the headline number these benchmarks exist to measure.

### 2. `INT` is 32-bit in all three implementations

`max int` reports `2147483647` under `a68g`, `a68lean run` and
`a68lean compile` alike. Two first drafts of these benchmarks had to be reworked
because of it; both `a68g` and `a68lean` agree on trapping:

```algol68
# a68g: runtime error: INT value overflow, result too large #
BEGIN
  INT s := 0;
  FOR i TO 8000000 DO s := (s + i * i) MOD 1000003 OD;
  print((s, newline))
END
```

The C twins use `long long`, which is safe only because every benchmark is sized
so no intermediate exceeds 2^31 - 1. In particular `ctl_goto` carries the
explicit `x < 100000000` guard in its `WHILE` condition so that `3 * x + 1`
cannot overflow; without it, Collatz peaks for larger n ranges (~1.6e10) would
trap in Algol and silently succeed in C, making the two disagree.

### 3. Recursion depth limits differ sharply

`a68g` overflows its stack between 1 000 and 2 000 frames for a one-argument
`INT` procedure; `a68lean run` and `a68lean compile` reach 20 000 frames and
overflow somewhere before 40 000. Reproducer:

```algol68
BEGIN
  PROC dep = (INT n) INT: IF n = 0 THEN 0 ELSE 1 + dep(n - 1) FI;
  print((dep(2000), newline))   # a68g: stack overflow; a68lean: +2000 #
END
```

`a68g` is the binding constraint, so `ctl_mutual` (the deepest benchmark) is
capped at 300 frames and `ctl_fib` at 32 - both with a wide margin. Anyone
adding a recursion benchmark here should stay under roughly 600 frames.

## Language features exercised and confirmed working in a68lean

All of the following were probed against `a68g`, `a68lean run` and
`a68lean compile` and agreed on all three:

- `PROC` as a formal parameter, called indirectly (`PROC (INT, INT) INT f`)
- dyadic `OP` with `PRIO`, and monadic `OP`
- `CASE ... IN ... OUT ... ESAC` with many alternatives
- `ANDF` / `OREL` short-circuit operators, nested
- mutual recursion via a single multi-part `PROC a = ..., b = ..., c = ...;`
  declaration, including forward references within it
- `GO TO` to a label in an enclosing block, to a label inside a loop body, and
  to a label preceding the value-yielding final unit of a procedure body
- identity declarations (`INT k = ...`) inside a loop body
