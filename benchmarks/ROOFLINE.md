# Roofline analysis of the emitted code

The classical roofline bounds achieved performance by machine peaks. For a
compiler the binding ceiling is not the silicon but **the same algorithm written
by hand in C**: that is what the emitted code could reach, since it runs the same
algorithm on the same machine with the same memory traffic. Every benchmark
therefore ships with a C twin, and the gap to it is the budget an optimisation
has to spend.

Machine: Apple M2, 8 cores. Times are CPU time, best of N.

## Baseline, before optimisation work

`intloop` — 20 million iterations of `s := (s + i * 3) MOD 1000003`, counted as
three arithmetic operations per iteration (6e7 ops).

| variant | ns/op | vs native C | overhead ns/op |
|---|---:|---:|---:|
| hand-written C (`cc -O2`) | 1.00 | 1x | — |
| a68g, interpreted | 26.0 | 26x | 25.0 |
| a68lean evaluator | 269.2 | 269x | 268.2 |
| a68lean compiled `-O0` | 436.0 | 436x | 435.0 |
| a68lean compiled `-O1` | 350.3 | 350x | 349.3 |
| a68lean compiled `-O2` | 376.7 | 377x | 375.7 |

Two things stand out, and both are the point of the current work.

**Compiled code is slower than our own evaluator.** Compiling the control flow
to C removed the interpreter's dispatch, but every value operation still crosses
into the runtime — several calls per Algol operation, each allocating a Lean
`IO` result — and that costs more than the dispatch it replaced.

**Both are an order of magnitude behind a68g's interpreter**, which reaches
26 ns/op. a68g's own optimiser (`--compile`) would be the fairer comparison, but
it cannot link on this platform, so a68g interpreted is the practical target to
beat.

## Where the time goes

Sampling the evaluator on `intloop` puts the cost squarely in allocation:

```
mi_malloc_small   599
mi_free           529
eval              471
dyadic            217
lean_free_object  156
lean_dec_ref      271   (cold + known)
```

Every intermediate value is a heap-allocated constructor: computing `s + i * 3`
allocates a `Value.int` for the product and another for the sum, then frees them.
At roughly 60 ns of allocator traffic per operation, that alone accounts for most
of the gap, and it is why the compiled back end — which produces exactly the same
`Value` objects — did not improve on the evaluator.

A second, independent problem: **frame cells are never reclaimed**. Three million
procedure calls reach 232 MB resident in both back ends, because each frame
allocates cells that are never freed. a68g reclaims them with a frame stack.

## What follows from this

The ordering of work is set by the profile, not by taste:

1. **Unbox primitive values in compiled code.** Compute `INT`, `REAL`, `BOOL`,
   `CHAR` and `BITS` expressions in native C types, so that arithmetic allocates
   nothing and never touches the operand stack; box only at boundaries. This is
   what a68g's optimiser does for units of `primitive_mode`, and it is the only
   change that can move a 350 ns/op figure toward the 1 ns/op ceiling.
2. **Promote non-escaping primitive locals to C variables**, removing the cell
   access that remains after step 1.
3. **Reclaim frame cells** on block exit when nothing captured the frame.
4. **Fuse and cheapen the remaining runtime calls** for everything that stays
   boxed — rows, structs, strings, transput.

Steps 1 and 2 have no effect on programs dominated by transput or row copying,
which is why the benchmark set deliberately spans numeric kernels, data
structures and control flow rather than arithmetic alone.
