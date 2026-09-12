# Examples

Every program here prints byte for byte what Algol 68 Genie prints; each is built with
`.lake/build/bin/a68lean compile examples/<name>.a68 -O2 -o <name> && ./<name>`.
The generated files show what the compiler emits for them.

* `tictactoe.a68` — a game against the machine.
* `sieve.a68` — the sieve of Eratosthenes over `[1:100] BOOL`, then the primes as a
  table. `sieve.mir` (`a68lean dump-mir sieve.a68 -O2`) is the program after lowering
  and the verified MIR passes; `sieve.ll` is the LLVM IR printed from it. Look for the
  inner `WHILE` loop (`line 12` in `sieve.mir`): the row's bounds are the constants of
  its declaration, an element write is a bounds test, a defined byte and the element
  byte (`mem_st_i8`), and the runtime is reached only on the slow path
  (`a68rt_set_row_bool`) or to report an error (`a68rt_index_error`).
* `linked_list.a68` — a singly linked list of `HEAP NODE`s: pushing, reversing, mapping
  with a procedure parameter, folding. `next OF q` on a name is followed inline, `q ISNT
  NIL` is a tag test, and `q := next OF q` copies the name's 16 bytes.
* `shapes.a68` — a row of `UNION (CIRCLE, RECT, TRIANGLE)` dispatched by conformity
  clauses: total area, a count per kind, the largest shape. The united values live in
  the row; the compiled conformity clause reads their mode index and content in place and
  binds the alternative's identifier to a register.
* `quicksort.a68` — quicksort over a row of `STRUCT (STRING name, INT age)`: a recursive
  procedure taking a `REF [] PERSON` and a comparison procedure as parameters, and
  `printf` with patterns. `quicksort.ll` is the LLVM IR the compiler emits for it:
  the program's mode, format and string tables as a constant, one function per routine
  (`a68_fn0` the program, `a68_fn1` `quicksort`, `a68_fn2` `by age`), the dispatchers
  the runtime calls back through, and `main`. `quicksort.c` is the same program through
  the C back end (`a68lean compile quicksort.a68 -O2 --c -c`), kept for comparison.

The binaries link the C runtime (`liba68rt.a`) and the C library only.
