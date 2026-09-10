# Benchmarks

Every benchmark exists twice: as an Algol 68 program in `progs/` and as a
hand-written C program in `native/` that computes the same value. The C twin is
the ceiling — it is what the emitted code could reach in principle, since it
runs the same algorithm on the same machine with the same memory traffic.

```bash
cd benchmarks
REPS=3 ./bench.sh                 # all benchmarks, all implementations
REPS=3 ./bench.sh intloop calls   # a subset
python3 roofline.py               # analysis of results/bench.csv

# when you only care about the emitted binary, which is usually the case:
VARIANTS="native a68g comp1 comp2" REPS=3 ./bench.sh
```

`VARIANTS` selects which implementations to time. Leaving out `interp` and
`comp0`, which are one to two orders of magnitude slower than the rest, cuts a
full sweep from hours to minutes and measures the same thing. The machine's load
averages at the start of a run are written to `results/bench.csv.meta`, so a set
of numbers carries the conditions it was taken under.

For each program the harness runs, and checks the output of, seven variants:

| variant | what it is |
|---|---|
| `native` | the hand-written C twin, `cc -O2` — the ceiling |
| `a68g` | Algol 68 Genie, interpreted |
| `a68gO` | Algol 68 Genie with `--compile` (its optimiser; unsupported on this platform) |
| `interp` | `a68lean run` — this project's evaluator |
| `comp0` `comp1` `comp2` | `a68lean compile` at `-O0`, `-O1`, `-O2` |

## Conventions a benchmark must follow

* The Algol program and the C twin print **one value**, and it must be the same
  one. Outputs are compared with spaces and `+` stripped, so Algol's
  `print((x, newline))` matches C's `printf("%lld\n", x)`. Never print a raw
  float: the two implementations format reals differently, so derive an integer
  (for instance `ROUND (x * 1000000)`).
* The source declares the operation count in a comment, exactly as
  `# ops: 6e7  (three arithmetic operations per iteration) #`. The harness
  divides time by this to get nanoseconds per Algol operation, which is the
  number an optimisation has to move.
* Size it so a68g interpreted takes roughly one to five seconds.
* Deterministic: no input, no files, and no `random` without `first random`
  (a68g seeds from the clock, so unseeded runs are not reproducible).

## Measurement

Times are **CPU time (user + sys), best of `REPS` runs**, not wall clock, so
that numbers stay meaningful when something else is using the machine. Even so,
the authoritative numbers for a report should be taken on an otherwise idle
machine.

When a run was made under load, quote the **slowdown against the C twin** rather
than the absolute nanoseconds. Contention stretches the twin and the compiled
binary by roughly the same factor, so the ratio survives what the absolute
figure does not.

## What the numbers mean

`roofline.py` prints, per benchmark, nanoseconds per operation for each variant,
the slowdown against the C twin, and the **overhead per operation** — the
nanoseconds each implementation adds on top of native C. That last column is the
budget an optimisation is spending: to get from, say, 300 ns/op to 30 ns/op, the
work removed has to be worth 270 ns.

It also measures two machine peaks — the throughput of a dependent scalar
integer add chain, and streaming memory bandwidth — so it is visible whether a
benchmark is compute-bound or memory-bound and therefore which ceiling applies.
