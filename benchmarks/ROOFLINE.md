# Roofline analysis of the emitted code

The classical roofline bounds achieved performance by machine peaks. For a
compiler the binding ceiling is not the silicon but **the same algorithm written
by hand in C**: that is what the emitted code could reach, since it runs the same
algorithm on the same machine with the same memory traffic. Every benchmark
therefore ships with a C twin, and the gap to it is the budget an optimisation
has to spend.

Machine: Apple M2, 8 cores. Times are CPU time, best of N.

A note on reading the tables. Absolute nanoseconds per operation depend on what
else the machine is doing, so where a run was made under load the **slowdown
against the C twin** is the number to trust: both the twin and the compiled
binary are stretched by the same factor, and the ratio survives.

## Where this started

`intloop` — 20 million iterations of `s := (s + i * 3) MOD 1000003`, counted as
three arithmetic operations per iteration.

| variant | ns/op | vs native C |
|---|---:|---:|
| hand-written C (`cc -O2`) | 1.00 | 1x |
| a68g, interpreted | 26.0 | 26x |
| a68lean evaluator | 269.2 | 269x |
| a68lean compiled `-O1` | 350.3 | 350x |

Compiled code was slower than the evaluator it replaced. Compiling the control
flow to C had removed the interpreter's dispatch, but every value operation still
crossed into the runtime — several calls per Algol operation, each allocating a
Lean `IO` result — and that cost more than the dispatch it replaced.

Sampling confirmed it: `mi_malloc_small` and `mi_free` dominated, because
computing `s + i * 3` allocated a `Value.int` for the product and another for the
sum and then freed them.

## Where it is now

Three benchmarks, each timed back to back against its own C twin on the same
machine in the same minute, best of three, CPU time:

| benchmark | what it is | hand-written C | a68lean `-O2` | vs C |
|---|---|---:|---:|---:|
| `intloop` | integer arithmetic in a loop | 0.10 s | 0.19 s | **1.9x** |
| `arraysum` | fill and sum a row, 40 M element accesses | 0.10 s | 5.79 s | 58x |
| `sieve` | sieve of Eratosthenes over two million | 0.02 s | 4.91 s | ~250x |

Scalar code is essentially at C speed. Array code is not, and the reason is
visible in one line of the emitted C: every element access is still a call into
the runtime.

The loop body `intloop` emits has nothing in it at all:

```c
for (int64_t i1 = from1; ; i1 += by1) {
  if (has1 && ((by1 > 0 && i1 > to1) || (by1 < 0 && i1 < to1))) break;
  a68_line(6);
  p0_0 = a68_mod_i(a68_add_i(p0_0, a68_mul_i(i1, 3LL)), 1000003LL);
}
```

No frame is pushed, nothing is boxed, the operand stack is not touched, and
reaching a statement is a store to a C variable rather than a call. A `WHILE`
loop with `+:=` in its body compiles the same way, with no run-time calls
whatsoever.

The changes that got there, in the order the profile called for:

1. **Primitive values are computed in native C types.** `INT`, `REAL`, `BOOL`,
   `CHAR` and `BITS` at their unwidened length become `int64_t`, `double`,
   `uint8_t`, `uint32_t` and `uint64_t`. Each helper reproduces the check its
   interpreted counterpart performs, so an overflow, a division by zero or a
   non-finite real still fails in the same place with the same message.
2. **Locals that cannot escape become C variables.** A slot qualifies when its
   declared mode is primitive, nothing takes a reference to it, and no routine
   text or format text inside the frame could reach it from another C function.
   When every slot qualifies, the run-time frame is not pushed at all. A `FOR`
   counter becomes the C induction variable.
3. **The assigning operators are updates, not references.** `x +:= e` used to
   take a reference to `x`, which cost four calls and, worse, made the analysis
   refuse to promote `x` at all. In statement position it is now a native
   update, and the analysis knows it.
4. **Statement position is modelled.** Sequencing pops the value of its
   left-hand side, so that side is generated as a statement and nothing is
   pushed. A frame with no slots is not pushed. A condition that needs
   statements to compute it goes into a C variable rather than onto the stack,
   which is what a `WHILE` clause needs, since the elaborator puts the whole
   loop body inside it.
5. **Row elements are read and written in one call**, and written in place. The
   bounds check used to sit in a `try`, which kept the row alive across the
   update and made every write copy the whole element array.

`-O0` gains almost none of this, and that is the design: promotion needs the
block structure flattened first, so that an assignment is a statement rather
than the value of its own block. The optimiser earns the native code.

## What is left

The profile has moved, so the ordering has too:

1. **Row and structure access.** `arraysum` and `sieve` spend nearly all their
   time in one runtime call per element. The call resolves the frame, reads the
   cell, matches the row, checks the subscript and boxes the result, every time.
   Getting array code near C means keeping rows of primitive mode in memory the
   emitted C can address directly, rather than as a Lean array of boxed values.
2. **Procedure calls.** A call still pushes the procedure and its arguments onto
   the operand stack, goes through `a68rt_call`, builds a Lean array of
   arguments, and dispatches back into compiled code with a full save and
   restore of the environment. The bodies themselves are already native.
3. **Strings.** `+:=` on a `STRING` allocates a fresh row each time.
4. **Frame cells are never reclaimed.** Three million procedure calls reach
   232 MB resident, because each frame allocates cells that are never freed.
   a68g reclaims them with a frame stack.

One thing that was tried and abandoned: making the hot accessors return their
value directly instead of an `IO` result, to save the result object. Converting
the action out of `IO` allocates an `Except` in its place, and an A/B on the
sieve made it slower, 4.46 s to 6.04 s. Avoiding that allocation means changing
the monad the runtime is written in, not the signature of its entry points.
