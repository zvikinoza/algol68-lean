# Roofline analysis of the emitted code

The classical roofline bounds achieved performance by machine peaks. For a
compiler the binding ceiling is not the silicon but **the same algorithm written
by hand in C**: that is what the emitted code could reach, since it runs the same
algorithm on the same machine with the same memory traffic. Every benchmark
therefore ships with a C twin, and the gap to it is the budget an optimisation
has to spend.

Machine: Apple M2, 8 cores. Times are CPU time (user + sys).

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
Lean `IO` result — and that cost more than the dispatch it replaced. Sampling
confirmed it: `mi_malloc_small` and `mi_free` dominated, because computing
`s + i * 3` allocated a `Value.int` for the product and another for the sum and
then freed them.

## Where it is now

Every benchmark against its C twin and against a68g's interpreter. The C twin and
the compiled program are each the best of three interleaved runs, a68g one run.

| benchmark | what it is | C twin | a68g | a68lean `-O2` | vs C | faster than a68g |
|---|---|---:|---:|---:|---:|---:|
| `intloop` | integer arithmetic in a loop | 0.06 s | 1.44 s | 0.09 s | 1.5x | 16x |
| `arraysum` | fill and sum a row, 40 million accesses | 0.06 s | 2.79 s | 0.09 s | 1.5x | 31x |
| `sieve` | sieve of Eratosthenes on a `[] BOOL` | 0.01 s | 1.85 s | 0.02 s | 2.0x | 92x |
| `data_matmul` | matrix multiplication on `[,] REAL` | 0.05 s | 2.89 s | 0.09 s | 1.8x | 32x |
| `data_struct` | a row of structures, field by field | <0.01 s | 2.06 s | 0.02 s | ~4x | 103x |
| `data_union` | a row of a union, dispatched by conformity | 0.02 s | 1.29 s | 0.04 s | 2.0x | 32x |
| `data_string` | building and comparing strings | <0.01 s | 1.44 s | 0.01 s | ~2x | 144x |
| `calls` | five million calls of a two-parameter procedure | 0.01 s | 0.57 s | 0.02 s | ~2x | 28x |
| `ctl_fib` | naive Fibonacci, 18 million recursive calls | 0.01 s | 2.09 s | 0.03 s | ~3x | 70x |
| `ctl_mutual` | three-way mutual recursion | 0.04 s | 2.31 s | 0.07 s | 1.8x | 33x |
| `ctl_ops` | user-defined operators | 0.07 s | 2.53 s | 0.09 s | 1.3x | 28x |
| `ctl_case` | a twelve-way case clause in a hot loop | 0.02 s | 1.32 s | 0.04 s | 2.0x | 33x |
| `ctl_goto` | Collatz steps with `ANDF`, `OREL` and a `GO TO` out | 0.01 s | 4.12 s | 0.07 s | ~7x | 59x |
| `ctl_hof` | a procedure passed as a parameter | 0.06 s | 2.92 s | 0.30 s | 5.0x | 10x |
| `num_divmod` | `OVER` and `MOD` | 0.02 s | 1.12 s | 0.05 s | 2.5x | 22x |
| `num_horner` | polynomial evaluation in `REAL` | <0.01 s | 1.03 s | 0.01 s | ~2x | 103x |
| `num_mandel` | Mandelbrot iteration | 0.01 s | 2.11 s | 0.03 s | ~3x | 70x |
| `num_math` | `sqrt`, `exp`, `ln`, `sin` in a loop | 0.04 s | 1.20 s | 0.06 s | 1.5x | 20x |
| `num_power` | `**` on `INT` and `REAL` | 0.02 s | 1.10 s | 0.07 s | 3.5x | 16x |
| `num_real` | `REAL` arithmetic | 0.01 s | 1.30 s | 0.02 s | 2.0x | 65x |
| `data_slice` | a sliding window taken with a slice | 0.07 s | 2.02 s | 1.53 s | 22x | 1.3x |
| `data_list` | walking a linked list of `HEAP` nodes | 0.03 s | 1.84 s | 2.84 s | 95x | 0.6x |

Several C twins run close to the timer's 10 ms resolution, so ratios marked `~`
are approximate.

Twenty of the twenty-two benchmarks are within about 1.3x to 7x of hand-written C
and 10 to 144 times faster than a68g. Two are not: heap structures reached
through `REF`, and slices. Both are discussed at the end.

## How it got there

In the order the profile called for:

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
3. **The assigning operators are updates, not references**, and statement
   position is modelled, so `x +:= e` and sequencing push nothing.
4. **Routines with primitive signatures are plain C functions**, called directly
   when the callee is certain, with calls inside expressions hoisted in the
   evaluator's order so C's unspecified operand order never reorders side effects.
   Naive Fibonacci compiles to the recursive C one would write, plus a jump check.
5. **Rows live in C memory.** A fixed row of primitive elements used only through
   subscripts, bounds enquiries and element updates is a C array with a flag per
   element for the undefined test. `arraysum` went from 5.85 s to 0.09 s and the
   sieve from 5.15 s to 0.02 s. A row of structures of primitive fields is one C
   array per field (`data_struct`, 13.6 s to 0.02 s).
6. **Unions in a row are a tag array and a payload array**, and a conformity clause
   on an element is a `switch` on the tag, with the bound value a C variable
   (`data_union`, 14.5 s to 0.04 s).
7. **Strings are C buffers.** A `STRING` variable declared with a denotation and used
   through reads, subscripts, comparisons, assignments and `+:=` is a growable byte
   buffer, turned back into a runtime value only where a whole-string value is
   needed (`data_string`, 1.26 s to 0.01 s).
8. **Choices are C.** Conditional and case clauses of primitive mode are C
   conditional expressions and `switch`es written into a C variable, and `ANDF` and
   `OREL` are `&&` and `||` (`ctl_case`, 1.58 s to 0.04 s).
9. **Blocks with labels keep their C variables.** With labels every unit used to count
   as a possible value of the block, so every assignment in it was an escape; now a
   unit followed by another before any `EXIT` is a statement (`ctl_goto`, 12.5 s to
   0.07 s together with 8).
10. **Calls through procedure parameters go to C.** A routine with a plain entry point
    and no captured environment is recorded in a table; a call through a procedure
    parameter looks the entry point up once per invocation of the caller and calls it
    directly (`ctl_hof`, 16.4 s to 0.30 s).
11. **Heap cells are given back** after a boxed call whose result holds no names and
    whose body lets no reference escape: three million such calls went from 134 MB to
    9 MB resident.
12. **Numbers.** `**`, the mathematical functions and `REAL` division compute natively
    with a68g's checks (`num_power`, 31.8 s to 0.07 s; `num_math`, 27.6 s to 0.06 s).

`-O0` gains little of this, by design: promotion needs the block structure
flattened first, so that an assignment is a statement rather than the value of its
own block. The optimiser earns the native code.

## What is left

1. **Heap structures.** `data_list` walks 40,000 `HEAP` nodes 250 times. Testing a
   `REF` against `NIL`, reading a field through it and moving along a link are one
   runtime call each now (they were nine), but each call still resolves a frame,
   reads a cell of the Lean heap and matches a `Value`, about 150 ns, where C loads a
   pointer. Closing this gap means keeping structures that are reached through names
   in memory the emitted C can address, with the runtime's heap as the fallback.
2. **Slices.** `data_slice` takes a 500-element window of a row 40,000 times. Building
   the slice is done by the runtime in Lean and costs about 30 ns an element, and so
   does each read of the window. Copying the window into a C array was tried and made
   the benchmark slower, because converting the row out of Lean cost more than the
   reads it saved; the real fix is slicing C arrays natively, which needs the analysis
   to reason about a `REF` slice aliasing the row it came from.
3. **Boxed callers.** In `ctl_hof` the procedure taking the parameter is itself boxed,
   because its signature contains a `PROC`; each of its 120,000 invocations enters and
   leaves a run-time frame.

One thing that was tried and abandoned early: making the hot accessors return their
value directly instead of an `IO` result. Converting the action out of `IO`
allocates an `Except` in its place, and an A/B on the sieve made it slower, 4.46 s
to 6.04 s. Avoiding that allocation means changing the monad the runtime is written
in, not the signature of its entry points.
