# Optimisations

What the compiler does to the code it emits, where each mechanism lives, and what it
is worth. Every mechanism is general: it applies to any program with the shape it
recognises, never to a benchmark by name. The benchmark ratios are against the
hand-written C twins in `benchmarks/native/` (LLVM back end, best of five).

The pipeline: `A68/Elab.lean` (elaboration) → `A68/Opt.lean` (core optimiser, proved
in `A68/Verified/Opt.lean`) → `A68/Lower.lean` (lowering to MIR: most of what follows)
→ `A68/MIR/Opt.lean` (MIR passes, proved in `A68/Verified/MIR.lean`) → `A68/LLVM.lean`
(printer) → clang.

## 1. Core level (`A68/Opt.lean`, proved)

Constant folding by evaluation, coercion simplification, constant control flow and
frameless-block flattening, mirroring a68g's own optimiser. Identity constants
(`INT n = 4096`) propagate into row bounds and loop bounds, which is what lets the
interval analysis below see literals.

## 2. Values and locals

* **Scalars in registers.** `INT`, `REAL`, `BOOL`, `CHAR`, `BITS` are `i64`/`f64`/`i1`/
  `i32`; the operations carry a68g's checks (INT range ±2147483647, zero divisors,
  NaN/infinite REAL results). `Lower.lean`: `lowerDyop`, `lowerMonop`, `emitBin`.
* **Locals that cannot escape are registers**, with an "assigned" flag only when a read
  before assignment is possible (`PVar`; the escape analysis is the C back end's
  `CodeGen.planFrame`). Loop counters likewise (`lowerLoopBody`).
* **Void conditionals and label blocks** keep values in registers instead of the
  operand stack (`Dest`, `lowerCondInto`, `lowerBlock`).

## 3. Routines

* **Plain entry points.** A routine whose frame is exactly its primitive parameters
  gets a typed native function `a68_nf<k>` beside its boxed one (`lowerNative`).
  A call whose callee is known and whose environment is in effect is a direct call
  (`staticNat`); a call through a procedure value reads the slot and dispatches through
  `@a68_nf_of_fn` (`dynNat`, `natCall`), falling back to the boxed call.
* **No jump check after routines that cannot jump out** (`mayJumpOut`, `jumpFreeSet`:
  a fixpoint over a block's routines); the pending-jump flag is read inline.
* Effect: `calls`, `ctl_fib`, `ctl_mutual`, `ctl_hof` from 10x–30x of the C back end
  to 0.75x–1.2x.

## 4. Rows, structures, unions, strings, names

* **Row promotion.** A row variable that never escapes (declared by a generator with
  undefined initial value; only subscripted, updated by assigning operators, asked for
  its bounds, or read/written field by field or assigned a structure display) becomes
  native arrays: bounds in registers, one array per element field (structure-of-arrays
  for rows of structures), a defined byte per element, allocated at the declaration
  and freed with the block. `PRow`, `prowIndex`, `prowGet`, `prowSet`, `lowerBlock`.
  Effect: `data_struct` 3x → 1x, `arraysum` and `sieve` to the C back end's level.
* **Inline access to rows the runtime keeps.** Other rows are reached through the
  runtime's own object layout: the cell, the descriptor's bounds and stride, the leaf
  store's elements and defined bytes, structure objects, union boxes, names; each path
  guarded by tag checks that fall back to the runtime entry point (`cellRowd`,
  `rowIndex`, `rowLeafElem`, `selAddr`, `refTarget`, `rowWrite`, `appendElem`).
* **Loop row cache.** A loop whose body calls nothing that could change a cell or a
  store (a trial lowering tells: `callFree`, effect-tagged calls `rtCell`) reads each
  row's descriptor, bounds and store once before the loop into registers, recomputing
  them after any slow path (`RowCache`, `slowPath.recache`). Declared literal bounds
  are seeded as constants.
* **Static conformity resolution.** The mode index a united value carries is one of its
  union's constituents, so which alternative it conforms to is decided at compile time
  (`Mode.eqv`); the test is a switch on the index (`lowerConformity`). `data_union`
  from 27x to 1.2x of C.
* **In-place string append** with the runtime's spare capacity (`appendElem`), the
  runtime's contiguous-leaf fast paths for row-of-CHAR conversions, and a size-classed
  free-list allocator in the collector (`csrc/rt.c`). `data_string` from 46x to 4x.
* **Alias information.** Inline accesses carry TBAA kinds (frame cell, object header,
  leaf data, slot value) so LLVM can hoist what the runtime's layout guarantees
  (`A68/LLVM.lean: tbaaLines`).

## 5. Checks in counted loops (the numeric-kernel work)

a68g's semantics require a check per subscript, per undefined-element read, per INT
operation, per division and per REAL operation. Each was a branch to a trap, and a loop
with early exits is neither vectorised nor well scheduled. Four mechanisms remove or
defer them without changing what a failing program prints:

* **Interval analysis.** A counter running by 1 between literal bounds has a known
  interval; an index built from counters by ±constants inherits one (`intervalOf`);
  within a promoted row's declared literal bounds the subscript check and the clamp are
  not emitted (`prowIndex`, `counterRange`, `PRow.litBounds`).
* **Definedness.** A loop nest over exactly a promoted row's declared bounds that assigns
  every element, as a statement of the row's own block (no labels), leaves the row known
  defined per field (`initTargets`, `setKnown`); reads then skip the defined-byte test.
  Storing an undefined value clears the knowledge.
* **Deferred traps.** A counted loop whose body calls only what a second run may
  repeat, reaches no row through the runtime, and has no jump, WHILE or label becomes a
  region (`DeferCtx`, `lowerLoop`): every remaining check ORs into one flag
  (`deferFail`) and every memory index is clamped, so the body has no early exit. If
  the flag is set at the loop's end, registers are restored to their entry values, rows
  the loop both read and wrote are restored from a copy taken before the loop (taken
  only for loops of at least 32 steps covering at least an eighth of the row; shorter
  ones are lowered as usual, their inner loops forming regions of their own), and the
  loop runs again in checked form, which stops at the first failure with its exact
  message. Nothing observable happens in between, so output, message and exit status
  are the evaluator's. The unchecked INT and REAL forms are `emitBin`; MIR has `select`,
  `addFW`…`divFW`, `overW`/`modW` and `badF` for this, with semantics, passes and proofs.
* **Finiteness tests sunk to chain ends.** A NaN or infinity survives `+ - *`, so a
  chain of those is tested once where it ends — a statement's, branch's or loop
  body's end, or before a division or a mathematical function (`flushPending`) — with
  one unordered compare of |x| against DBL_MAX (`UnOp.badF`).

Effect on the kernels (`benchmarks/progs/ai_*`): from 12x–17x of hand-written C to
`ai_dot` 1.0x, `ai_matmul_real` 1.1x, `ai_softmax` 1.2x, `ai_layernorm` 1.3x, `ai_sgd`
1.4x, `ai_kmeans` and `ai_dense` 2x, `ai_attention` 2.4x, `ai_conv2d` 3x, `ai_conv1d`
8x. What separates the last four from their twins is vectorisation across independent
output elements, which clang performs on the C and the compiler does not yet perform on
MIR loop nests.

## 6. MIR level (`A68/MIR/Opt.lean`, proved)

Copy and constant propagation, constant folding, branch folding, dead assignment
elimination, unreachable block removal, each with a theorem that `run` is preserved for
every fuel, runtime and runtime state (`A68/Verified/MIR.lean`, axioms `propext`,
`Classical.choice`, `Quot.sound` only). `INT ** k` for a constant `k` is the
square-and-multiply loop of `Sem.powI` unrolled into checked multiplications.

## 7. Printer (`A68/LLVM.lean`)

Line numbers stored lazily (only before a call and in trap blocks, which is when the
runtime reads them); a repeated line-number instruction dropped by the lowering.

## Not done

Outer-loop vectorisation of MIR loop nests (independent output elements in lanes,
order-preserving); promotion of non-escaping strings and rows of unions; statepoints
once native pointers live across calls; further verified MIR passes (CSE, LICM,
bounds-check elimination on MIR, inlining); a generational collector.
