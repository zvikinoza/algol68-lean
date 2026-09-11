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

Each benchmark timed against its own C twin on the same machine, the variants
interleaved so that load falls on all of them alike, best of three, CPU time.
a68g is best of two.

| benchmark | what it is | hand-written C | a68g interpreted | a68lean `-O2` | vs C |
|---|---|---:|---:|---:|---:|
| `intloop` | integer arithmetic in a loop | 0.11 s | – | 0.16 s | **1.5x** |
| `calls` | five million calls of a two-parameter procedure | 0.02 s | 0.96 s | 0.04 s | **2.0x** |
| `ctl_fib` | naive Fibonacci, 18 million recursive calls | 0.02 s | 2.82 s | 0.05 s | **2.5x** |
| `ctl_mutual` | three-way mutual recursion, 10 million calls | 0.06 s | 3.05 s | 0.09 s | **1.5x** |
| `ctl_hof` | a procedure passed as a parameter, called 12 million times | 0.06 s | 2.60 s | 10.98 s | 183x |
| `arraysum` | fill and sum a row, 40 million element accesses | 0.11 s | – | 3.62 s | 33x |

The C twins of `calls` and `ctl_fib` run close to the timer's 10 ms resolution,
so those two ratios are approximate. Before the last two changes below, `calls`
took 5.55 s and `ctl_fib` 16.66 s.

Scalar code and procedure calls with primitive signatures are now essentially at
C speed, and 24 to 56 times faster than a68g's interpreter. Two shapes are not:
an indirect call through a procedure parameter, and row access, where every
element is still a call into the runtime.

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
6. **Declaring a procedure no longer costs a block its C variables.** A block
   containing a routine text used to keep every slot in a cell, because the
   routine is a separate C function that reaches the frame through the run-time
   environment. Only the slots such a text actually reads or names need that, and
   the analysis now asks exactly that question.
7. **Routines with primitive signatures are plain C functions.** A routine whose
   parameters and result are primitive gets a second entry point that takes its
   arguments as C arguments and returns its result, and a call whose callee is
   certain, reachable without an environment switch, goes straight to it. Calls
   inside expressions are hoisted in the evaluator's order, so C's unspecified
   operand order never reorders side effects. `fib` compiles to

   ```c
   static int64_t a68_nf0(int64_t a0_0) {
     int64_t rv0 = 0;
     if ((uint8_t)((a0_0) < (2LL))) {
       rv0 = a0_0;
     } else {
       int64_t t1 = a68_nf0(a68_sub_i(a0_0, 1LL));
       if (a68_jump()) return 0;
       int64_t t2 = t1;
       int64_t t3 = a68_nf0(a68_sub_i(a0_0, 2LL));
       if (a68_jump()) return 0;
       rv0 = a68_add_i(t2, t3);
     }
     return rv0;
   }
   ```

   which is the C one would write by hand, plus a jump check that is one load.

`-O0` gains almost none of this, and that is the design: promotion needs the
block structure flattened first, so that an assignment is a statement rather
than the value of its own block. The optimiser earns the native code.

## What is left

The profile has moved again, so the ordering has too:

1. **Row access.** `arraysum` and the sieve spend nearly all their time in one
   runtime call per element. The call resolves the frame, reads the cell,
   matches the row, checks the subscript and boxes the result, every time.
   Getting array code near C means keeping rows of primitive mode in memory the
   emitted C can address directly, rather than as a Lean array of boxed values.
2. **Indirect calls.** A procedure parameter, a `PROC` variable, or a routine
   called from somewhere its captured environment is not already in effect still
   goes through the operand stack, `a68rt_call`, a Lean array of arguments and
   the dispatcher, with a full save and restore of the environment. `ctl_hof` is
   that case, at 183 times its C twin.
3. **Frame cells are never reclaimed.** Three million boxed procedure calls
   reach 232 MB resident, because each frame allocates cells that are never
   freed. a68g reclaims them with a frame stack. Direct calls push no frame, so
   they sidestep this, but every other call does not.

One thing that was tried and abandoned: making the hot accessors return their
value directly instead of an `IO` result, to save the result object. Converting
the action out of `IO` allocates an `Except` in its place, and an A/B on the
sieve made it slower, 4.46 s to 6.04 s. Avoiding that allocation means changing
the monad the runtime is written in, not the signature of its entry points.
