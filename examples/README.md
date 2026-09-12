# Examples

* `tictactoe.a68` — a game against the machine.
* `quicksort.a68` — quicksort over a row of `STRUCT (STRING name, INT age)`: a recursive
  procedure taking a `REF [] PERSON` and a comparison procedure as parameters, and
  `printf` with patterns. `quicksort.c` is what `a68lean compile quicksort.a68 -O2 --c -c`
  generates from it: the fixed prelude of runtime prototypes and inline helpers, the
  program's mode, format and string tables as a string literal, one C function per
  routine (`a68_fn0` the program, `a68_fn1` `quicksort`, `a68_fn2` `by age`), the
  dispatchers the runtime calls back through, and `main`. Its output is byte for byte
  a68g's; the binary links the C library only.

```
.lake/build/bin/a68lean compile examples/quicksort.a68 -O2 -o quicksort && ./quicksort
```
