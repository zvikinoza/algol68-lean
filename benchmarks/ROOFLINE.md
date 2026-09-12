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
the compiled program are each the best of five interleaved runs, a68g one run.

| benchmark | what it is | C twin | a68g | a68lean `-O2` | vs C | faster than a68g |
|---|---|---:|---:|---:|---:|---:|
| `intloop` | integer arithmetic in a loop | 0.07 s | 1.45 s | 0.09 s | 1.3x | 16x |
| `arraysum` | fill and sum a row, 40 million accesses | 0.06 s | 2.66 s | 0.09 s | 1.5x | 30x |
| `sieve` | sieve of Eratosthenes on a `[] BOOL` | <0.01 s | 1.55 s | 0.01 s | ~2x | 155x |
| `data_matmul` | matrix multiplication on `[,] REAL` | 0.04 s | 2.18 s | 0.07 s | 1.8x | 31x |
| `data_struct` | a row of structures, field by field | <0.01 s | 2.06 s | 0.01 s | ~2x | 206x |
| `data_union` | a row of a union, dispatched by conformity | 0.02 s | 1.30 s | 0.03 s | 1.5x | 43x |
| `data_string` | building and comparing strings | <0.01 s | 1.46 s | 0.01 s | ~2x | 146x |
| `calls` | five million calls of a two-parameter procedure | 0.01 s | 0.55 s | 0.02 s | 2.0x | 28x |
| `ctl_fib` | naive Fibonacci, 18 million recursive calls | 0.01 s | 1.63 s | 0.02 s | 2.0x | 82x |
| `ctl_mutual` | three-way mutual recursion | 0.03 s | 1.76 s | 0.05 s | 1.7x | 35x |
| `ctl_ops` | user-defined operators | 0.07 s | 2.11 s | 0.08 s | 1.1x | 26x |
| `ctl_case` | a twelve-way case clause in a hot loop | 0.02 s | 1.25 s | 0.04 s | 2.0x | 31x |
| `ctl_goto` | Collatz steps with `ANDF`, `OREL` and a `GO TO` out | 0.01 s | 2.25 s | 0.02 s | 2.0x | 112x |
| `ctl_hof` | a procedure passed as a parameter | 0.04 s | 1.51 s | 0.06 s | 1.5x | 25x |
| `num_divmod` | `OVER` and `MOD` | 0.03 s | 1.13 s | 0.04 s | 1.3x | 28x |
| `num_horner` | polynomial evaluation in `REAL` | <0.01 s | 1.04 s | 0.01 s | ~2x | 104x |
| `num_mandel` | Mandelbrot iteration | 0.01 s | 2.13 s | 0.03 s | 3.0x | 71x |
| `num_math` | `sqrt`, `exp`, `ln`, `sin` in a loop | 0.04 s | 1.20 s | 0.06 s | 1.5x | 20x |
| `num_power` | `**` on `INT` and `REAL` | 0.02 s | 1.10 s | 0.03 s | 1.5x | 37x |
| `num_real` | `REAL` arithmetic | 0.01 s | 1.20 s | 0.02 s | 2.0x | 60x |
| `data_slice` | a sliding window taken with a slice | 0.06 s | 1.79 s | 0.16 s | 2.7x | 11x |
| `data_list` | walking a linked list of `HEAP` nodes | 0.03 s | 1.51 s | 0.72 s | 24x | 2x |

Several C twins run close to the timer's 10 ms resolution, so ratios marked `~`
are approximate.

Twenty-one of the twenty-two benchmarks are within about 1.1x to 3x of hand-written C
and 11 to 200 times faster than a68g. One is not: heap structures reached
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
   runtime call each, and the runtime is now C over C objects (`csrc/rt.c`), which
   took the benchmark from 2.84 s to 0.72 s; what remains is the call itself and the
   tag dispatch on the cell, about 40 ns where C loads a pointer. Closing the rest of
   the gap means emitting the field access and the link following inline.
2. **Slices.** `data_slice` takes a 500-element window of a row 40,000 times. A slice
   is a descriptor over the row's store, built in C, and each read of the window goes
   through it: 1.53 s to 0.16 s with the C runtime, 2.7x from the C twin. Slicing C
   arrays natively needs the analysis to reason about a `REF` slice aliasing the row
   it came from.

The runtime these numbers were measured against is the C one: every entry point the
emitted code calls is C over C memory, and a compiled program links the C library
only. The earlier runtime, Lean values behind the same entry points, allocated a
Lean `IO` result per call and a `Value` per intermediate, which is where the
remaining factor of 2 to 8 on the runtime-bound benchmarks (`data_slice`,
`data_list`, `ctl_hof`, `num_power`, `ctl_goto`) went.
