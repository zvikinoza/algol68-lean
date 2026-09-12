# The LLVM back end

`a68lean compile --llvm` lowers the optimised core representation to **MIR**, a typed
register-machine intermediate representation defined in Lean, optimises it there, and
prints LLVM IR that the system C compiler assembles (`clang -O2 prog.ll liba68rt.a -lm`).
The C back end (`A68/CodeGen.lean`) stays as it is; both produce the same bytes and
link the same runtime.

## 1. Why a second back end, and what LLVM does and does not buy

The C output already receives every LLVM optimisation through clang, so emitting IR
adds none of them. What the C back end cannot express is what this one is for:

* **Exact semantics with no C in the middle.** Integer checks are explicit branches, a
  routine that leaves by a jump uses the flag the runtime already keeps, deep recursion
  can be a tail call, and facts the generator knows (`noalias`, `dereferenceable`,
  `nsw`) are stated rather than hoped for.
* **A verifiable middle.** MIR has a semantics in Lean (`A68.MIR.Sem`); the lowering of
  the formal core to MIR and each MIR optimisation is a theorem (`A68.Verified.MIR`).
  The C back end's optimisations are string manipulation on C text and cannot be.
* **Precise garbage collection in native code** through LLVM statepoints: the code
  keeps heap pointers in registers and the stack map tells the collector where they
  are at every call that may collect. From C, roots must stay on the runtime's operand
  stack, which is where much of the remaining cost of the C back end sits.

Where the performance of the C back end is lost — `data_list` at 24x the hand-written
C, `data_slice` at 2.7x — is not LLVM but representation: values that are not
primitive live in 16-byte tagged slots behind runtime calls, opaque to every
optimiser. MIR gives every mode a static representation the optimiser can see through.

## 2. MIR

A function is a set of basic blocks over typed variables; a variable may be assigned
more than once (the LLVM printer allocates it with `alloca` and lets `mem2reg` build
the SSA form, exactly as clang does for C locals). Types: `i64` (INT, BITS), `f64`
(REAL), `i1` (BOOL), `i32` (CHAR), and from milestone 2 `ptr` (a heap object) and `val`
(a runtime slot). Instructions: assignments of an operand, of a scalar operation with
a68g's checks, or of a call's result; calls of runtime entry points, of compiled
routines and of format holes; the line marker. Terminators: branch, conditional
branch, switch, return, unreachable. The checked operations are single instructions
whose semantics trap — the printer expands each into the compare-and-branch LLVM
needs — so the model stays small.

The runtime a MIR program calls is the C runtime of compiled programs unchanged
(`csrc/`): the boxed calling convention (`a68_fn<n>()` with the arguments on the
operand stack, `a68rt_enter_args`), the frame chain, the operand stack, the jump flag,
format holes and the mode/format/string tables in the program's blob. An LLVM-compiled
routine and a C-compiled one are therefore interchangeable, which is how the port is
made incrementally with the suites green at every step.

## 3. Milestones

1. **Parity.** MIR, the lowering of every core construct, the LLVM printer, the driver.
   Scalars are native (`INT`, `REAL`, `BOOL`, `CHAR`, `BITS` values are `i64`, `f64`,
   `i1`, `i32`); everything else goes through the runtime as the C back end's general
   path does. Every case, corpus program and fuzz program byte-identical.
2. **Native representations.** Escape analysis over MIR: cells that nothing references
   through a name or a closure become variables (LLVM registers); rows of primitive
   elements, structures and strings get direct access to the runtime's own layout; heap
   pointers live in `ptr` variables with **statepoints** at every call that may collect,
   and the runtime reads the LLVM stack maps to find them (`csrc/stackmap.c`).
3. **The optimiser**, each pass with its theorem: constant and copy propagation, common
   subexpression elimination, dead code and dead store elimination, check hoisting and
   bounds-check elimination by range analysis, loop-invariant code motion, inlining and
   devirtualisation of procedure values, copy elision for row values, scalar
   replacement of structures, tail calls. Register allocation, scheduling, instruction
   selection and vectorisation are LLVM's.
4. **Generational collection** on the statepoint roots.

## 4. What is proved and what is not

Proved in Lean: the semantics of MIR; the lowering of the formal core (the language of
`A68.Verified`, extended milestone by milestone) to MIR; each MIR→MIR optimisation.
Trusted: LLVM, the textual printing of IR, and the C runtime — checked instead by the
same differential tests as the C back end: every program through both back ends and
through the evaluator must give the same bytes, plus the MIR interpreter against the
evaluator on the fuzzers' programs. This boundary is stated here so that no claim
outruns it.

## 5. Status

Done, on branch `llvm`, every step byte-identical to a68g on the case suite (68/68 at
`-O0` and `-O2`, and under `A68LEAN_GC=stress,verify`), the fuzzers (300-program
batches) and the golden corpus (the same 763 of 773 as the C back end):

* **Milestone 1, parity.** MIR (`A68/MIR.lean`), the lowering of every core construct
  (`A68/Lower.lean`), the printer (`A68/LLVM.lean`), the driver (`--llvm`, `dump-mir`).
* **The verified optimiser** (`A68/MIR/Sem.lean`, `A68/MIR/Opt.lean`,
  `A68/Verified/MIR.lean`): copy and constant propagation, constant folding, branch
  folding, dead assignment elimination and unreachable block removal, each with its
  theorem that `run` is preserved for every fuel, runtime and runtime state; the
  pipeline `Opt.run` is proved from them (axioms: `propext`, `Classical.choice`,
  `Quot.sound` only).
* **Milestone 2 in part.** Scalars in registers; locals and loop counters promoted by the
  C back end's escape analysis; routines whose frame is exactly their primitive
  parameters get a plain entry point `a68_nf<k>` (typed arguments and result, no
  run-time frame) called directly when the callee is known and its environment is in
  effect, or through `@a68_nf_of_fn` after reading a procedure-valued cell, with the
  boxed call as fallback; `INT ** k` unrolled; conditionals in void position without
  the stack; label blocks keeping a scalar value in a register.

  Rows, structures, unions, strings and names are reached **inline through the
  runtime's own object layout** (`csrc/a68rt.h`): the address of a frame's cells is
  returned by `a68rt_enter`/`a68rt_enter_args` (or read once at the function entry for
  a captured frame), the descriptor's bounds are checked inline, an element of a leaf
  store is loaded or stored directly with its defined bit, a row of structures is
  followed to the field, a united value's mode index is compared with each alternative's
  (the runtime's cached `conforms` decides when they differ), `p IS NIL` reads a tag,
  a name in a cell is followed to the slot it refers to, and a value of a REF mode is
  copied as its 16 bytes. Every inline path has a runtime fallback taken when a tag is
  not as expected — an undefined value, a name where a value was expected, a slots
  store where a leaf was, a shared store on a write — so the runtime's checks and
  messages are those of the evaluator. A fresh row of a primitive mode is a leaf from
  the start (`a68rt_new_row_of`); `s +:= t` appends in place. The memory operations
  are `mem_ld_*`/`mem_st_*` native calls in MIR — opaque runtime steps to the
  semantics, so the optimiser stays verified — printed as `getelementptr` and
  `load`/`store`; the address arithmetic uses the unchecked `addW`/`mulW`/`shlW`/…
  operations, whose semantics wrap at 64 bits as LLVM's do.

  GC safety of the inline paths rests on three facts: the collector does not move
  objects; a frame on the environment chain, and what its cells reach, is never
  collected; and no inline path keeps a pointer into an object across a runtime call —
  each access re-derives it from the cell, which LLVM then hoists out of call-free loops
  by itself. Statepoints (`csrc/stackmap.c` is in place) are therefore not needed yet;
  they become necessary once native pointers are kept live across calls.

  A loop whose body (outside its slow paths) calls only runtime entry points that change
  no cell and no store — a trial lowering of the body tells — reads the descriptor,
  bounds, offset and store of every row it reaches inline once before the loop into
  variables and recomputes them after any slow path, so its element accesses are
  register-based. The inline accesses carry alias information (TBAA: a frame cell, an
  object header, leaf data, a slot value never overlap) for LLVM's own hoisting.

  Routines that cannot complete a jump to a label outside themselves (no jump to a
  foreign label, calls only of builtins and of such sibling routines — a fixpoint over
  a block's routines) are called without a check of the jump flag afterwards, and the
  flag itself is read inline. The printer stores the line number lazily: only before a
  call and in trap blocks, since the runtime reads it only to report an error. A leaf
  store keeps a defined byte per element (not a bit), so an element write is two plain
  stores.

  A non-flexible row variable declared with literal bounds keeps them for life, so a
  loop's cache of it holds the bounds and strides as constants and LLVM folds the bounds
  check into the loop condition.

`a68lean compile` is the LLVM back end; `--c` selects the C back end, kept as the second
implementation the suites compare against. Benchmarks (`benchmarks/bench.sh`,
`VARIANTS="native comp2 llvm2" REPS=5`, quiet machine), LLVM back end relative to the C
back end: `sieve` 1.0, `arraysum` 1.1, `ctl_mutual` 0.8, `ctl_fib` 1.0, `calls` 1.0,
`ctl_hof` 1.0, `ctl_case` 0.75, `num_mandel` 0.67, `num_real` 0.5, `num_divmod` 0.75,
`intloop` 0.9, `data_matmul` 1.0, `data_slice` 0.7, `data_list` 0.07, `data_union` 2.0,
`data_struct` 2.0, `data_string` 6.0. Relative to hand-written C: 1.0x–2.0x on twenty of
the twenty-two (`ctl_mutual` 1.3x, `arraysum` 1.7x, `sieve` at the timer's resolution),
`data_union` 3x and `data_string` further. What is left on rows is the per-access defined
byte and index arithmetic, and on strings the runtime's row representation; both are
addressed by the next step of milestone 2, promoting rows and strings that never escape
to native arrays and buffers in MIR.

Not done: the remainder of milestone 2 (promotion of non-escaping rows and strings to
native arrays; statepoints once pointers live across calls); milestone 3 (further
verified passes — CSE, LICM, bounds-check elimination, inlining — and the verified
lowering of the formal core); milestone 4 (generational collection).
