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

Same benchmark, same machine, measured with other work running:

| variant | ns/op | vs native C |
|---|---:|---:|
| hand-written C (`cc -O2`) | 2.00 | 1x |
| a68g, interpreted | 59.2 | 30x |
| a68lean evaluator | 613.2 | 307x |
| a68lean compiled `-O0` | 389.2 | 195x |
| a68lean compiled `-O1` | 4.17 | 2.1x |
| a68lean compiled `-O2` | 3.67 | **1.8x** |

The compiled binary is now within a factor of two of hand-written C, and about
sixteen times faster than a68g interpreted. The loop body it emits is one
statement:

```c
for (int64_t i1 = from1; ; i1 += by1) {
  if (has1 && ((by1 > 0 && i1 > to1) || (by1 < 0 && i1 < to1))) break;
  a68_line(6);
  p0_0 = a68_mod_i(a68_add_i(p0_0, a68_mul_i(i1, 3LL)), 1000003LL);
}
```

No frame is pushed, nothing is boxed, and the operand stack is not touched. The
three changes that got there, in the order the profile called for:

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
3. **Row elements are read and written natively.** `a[i]` was four calls — build
   a reference, push the subscript, slice, dereference — and yielded a boxed
   value. A row held directly in a cell is now reached in one call that carries a
   native value; any other shape falls back to the general slicing machinery.

`-O0` gains almost nothing, and that is the design: promotion needs the block
structure flattened first, so that an assignment is a statement rather than the
value of its own block. The optimiser earns the native code.

## What is left

The profile has moved, so the ordering has too:

1. **Procedure calls.** A call still pushes the procedure and its arguments onto
   the operand stack, goes through `a68rt_call`, builds a Lean array of
   arguments, and dispatches back into compiled code with a full save and
   restore of the environment. The bodies themselves are already native.
   `calls`, `ctl_fib`, `ctl_mutual` and `ctl_hof` are all made of this.
2. **Structure fields and strings.** `p OF s` builds a reference on the operand
   stack; `+:=` on a `STRING` allocates a fresh row each time. `data_struct` and
   `data_string` are dominated by these.
3. **Frame cells are never reclaimed.** Three million procedure calls reach
   232 MB resident, because each frame allocates cells that are never freed.
   a68g reclaims them with a frame stack.
4. **The remaining runtime calls for everything still boxed** — unions,
   transput, heap generators.
