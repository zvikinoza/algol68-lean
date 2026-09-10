# Data-structure benchmarks

Six programs covering the value shapes that are not scalars: rows, slices,
structures, heap-allocated links, strings and unions. Each has a hand-written C
twin in `native/` computing the same answer.

| benchmark | what it stresses | ops | answer |
|---|---|---|---|
| `data_matmul` | two-dimensional row indexing, 250x250 modular matrix multiply | 3.125e7 | 229194 |
| `data_slice` | slicing and trimming: a 500-element sliding window, `[@0]`, writing through a `REF []INT` slice | 2e7 | 429579 |
| `data_struct` | `STRUCT` field selection and update, 1000 particles over 8000 steps | 4.8e7 | 212524 |
| `data_list` | 40000 `HEAP` nodes chained through `REF NODE`, walked 250 times | 1e7 | 728645 |
| `data_string` | `STRING` built with `+:=`, compared with `=` and `<`, subscripted | 5.4e6 | 117544 |
| `data_union` | `UNION (INT, REAL, BOOL, CHAR)` row dispatched by a conformity `CASE`, 8000 passes | 8e6 | 849499 |

All six produce identical output under Algol 68 Genie, `a68lean run`, `a68lean
compile` at every optimisation level, and the C twin.

Algol 68 Genie interpreted takes between 2.1 and 3.2 seconds on each, which is
the band the harness asks for.

## What the numbers said at the time they were written

These were measured before scalars were unboxed, and they are the reason row and
structure access were taken up next. On composite values the compiled code was no
faster than the evaluator, and both were two to three orders of magnitude off the
C twin: `data_matmul` at `-O2` ran slower than the evaluator, and a68g
interpreted beat both by a factor of fifteen. Changing optimisation level barely
moved either number, which points at a generic row-descriptor helper the host C
compiler cannot see through rather than at the generated control flow.

## A divergence from Algol 68 Genie

`a68lean` is more permissive than a68g when coercing a display to a union:

```algol68
BEGIN
  MODE U = UNION ([] INT, INT);
  U u := U ((1, 2, 3));
  CASE u IN ([] INT r): print((UPB r, newline)), (INT k): print((k, newline)) ESAC
END
```

a68g rejects this, and is right to: a display has no a priori mode, so it cannot
be the operand of a union coercion. `a68lean` accepts it and prints `+3`. Since
this only affects programs a68g refuses outright, it cannot change the output of
any program a68g accepts. The converse case agrees: uniting a `CHAR` to
`UNION (INT, STRING)` is rejected by both.

## Constructs checked and found to agree

Two-dimensional slices in both directions with `LWB`, `UPB` and `[@n]`; a
`STRUCT` holding a row, nested inside a two-dimensional row of `STRUCT`; `FLEX`
growth for `INT` and `CHAR`; whole-row slice assignment; in-place list reversal
through `REF NODE`; a recursive binary search tree with `REF REF NODE`
parameters; structure value-copy semantics; `STRING` slice assignment and open
trims; and unions of `[]INT`, `STRUCT` and `STRING`.
