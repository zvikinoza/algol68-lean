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
