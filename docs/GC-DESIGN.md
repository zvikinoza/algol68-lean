# Garbage collection in compiled programs: design

This document is the outcome of milestone 0. It fixes the representation of
Algol 68 values in compiled programs, the collector, the invariants the emitted
code and the runtime keep, and what is proved. Every decision records the
alternatives considered and why they were not taken.

## 1. The problem

A compiled program today keeps every non-scalar value as a Lean object in the
runtime's cell array (`Rt.heap`), reached from C by index; the emitted C holds
scalars only. Cells are never freed, except by the mark/release fast path
around boxed calls. A collector written in C cannot walk Lean objects, so the
requirement that *the emitted program collects its own heap* forces one
decision before all others:

**Compiled programs keep their Algol values in C memory.** Lean is called from
a compiled program only for services on converted data: number formatting,
formatted transput, reading, the multi-precision arithmetic of `LONG` modes,
and the operating-system procedures. `a68lean run` keeps the Lean runtime and
remains the reference implementation of the semantics.

What other implementations do (milestone 0 study):

| implementation | heap |
|---|---|
| a68g 3.13.3 | handles with mark bits; `colour_object` walks values by mode; compacting sweep moves objects, REFs point at handles (`rts-heap.c`) |
| ga68 (GCC 15/16) | `malloc`, or the Boehm conservative collector when built with `LIBGA68_WITH_GC` (`libga68/ga68-alloc.c`) |
| a68toc (Algol 68RS) | Boehm |

None is precise and non-moving with a proof. a68g's descriptor-driven marking
is the one idea kept.

## 2. How the switch is made without losing byte equality

The generator already emits calls to 109 runtime entry points whose interface
is integers and native scalars only (`a68rt_push_int`, `a68rt_slice(nidx,
kinds, viaRef)`, …). Those entry points get a C implementation over a C heap,
`csrc/rt.c`, with the same names and contracts. The emitted code is unchanged
except for what the collector needs; the Lean `A68.Runtime` keeps serving the
evaluator. The evaluator (`A68.Interp`) is the specification each C entry point
is written against, and the 62 cases, 773 corpus programs and the fuzzers
check the port byte for byte.

Rejected: rewriting the generator to produce typed C directly. It would give
the same heap and more speed, but changes everything at once; the entry-point
port keeps the generator's escape analysis, native calls and promotion, and
the operand stack and environment stack become C arrays, which is exactly the
root set the collector needs. Direct C generation for more shapes comes after,
as optimisation of a working system.

Rejected: a hybrid where Lean values may point at C objects and C objects at
Lean values during migration. Marking would then have to traverse Lean values,
so the collector would be partly in Lean, and the final state has to be the
full C heap anyway.

## 3. Value representation

### 3.1 Slots

Every place a value can be — a cell, a structure field, a row element, an
operand-stack entry — is a 16-byte slot:

```c
typedef struct { uint32_t tag; uint32_t aux; union { int64_t i; double r; uint64_t u; a68_obj* p; } v; } a68_val;
```

`tag` is the kind of value: `UNDEF`, `INT`, `REAL`, `BOOL`, `CHAR`, `BITS`,
`VOID`, `NIL`, `REF`, `ROW`, `STRUCT`, `UNION`, `PROC`, `CPROC`, `BUILTIN`,
`FMT`, `FILE`, `MP`, `BIGINT`. `aux` carries what the kind needs: the mode index
of a united value, the byte offset of a name, the parameter count of a
procedure, the file id. The collector decides whether `v.p` is a pointer from
the tag alone — no mode descriptor is needed to scan a slot, which is what
makes the marking loop small enough to transcribe from its Lean model.

Rejected: unboxed layouts per mode (an `INT` field is 8 bytes, a `BOOL` 1 byte),
as a68g and ga68 have. They halve the memory traffic of rows of scalars, but
Algol 68 needs an "uninitialised" state per scalar (a68g spends a status word on
it, so its `INT` is 16 bytes too), and scanning then needs a descriptor per
mode. Rows of primitive elements are the case where this matters, and they get
a packed representation of their own (3.3), which is where the traffic is.

### 3.2 Objects

```c
typedef struct a68_obj { uint32_t kind_and_mark; uint32_t n; uint64_t size_class_and_mode; } a68_obj;
```

followed by the payload. Kinds:

| kind | payload | holds pointers |
|---|---|---|
| `SLOTS` | `n` slots: a structure's fields, a frame's cells, a boxed row's elements, a union's value, a procedure's captured frames | yes |
| `LEAF` | `n` bytes of scalar data: packed rows (3.3), multi-precision digits, big `BITS` | no |
| `ROWD` | a row descriptor: dimensions, bounds, strides, offset, and one pointer to the element storage (`SLOTS` or `LEAF`) | one |
| `FRAME` | a frame: `n` cell slots and a pointer to the static-chain frame | yes |

The mark bit lives in the header. Objects are never moved.

### 3.3 Rows

A row *value* is a pointer to a `ROWD` descriptor. Slicing and trimming create a
new descriptor sharing the storage, as a68g does, so `a[2:5]`, `a[,j]` and
`a[@0]` cost a descriptor and no copying, and a name to a sub-row is a name of
that descriptor. This replaces the evaluator's `Sel.sub` element-offset arrays:
a descriptor with strides expresses every view the evaluator can express, and
the equivalence is checked by the corpus (the evaluator stays as it is).

Storage of a row of primitive mode is a `LEAF`: `n` elements of 8 bytes (`INT`,
`REAL`, `BITS`), 4 (`CHAR`), 1 (`BOOL`), followed by a bitmap of one bit per
element saying whether it has a value. Strings are rows of `CHAR`. Storage of a
row of any other mode is `SLOTS`.

Rejected: keeping the evaluator's offset arrays. A trim of a 2-dimensional row
would allocate an array of offsets the size of the view, and the collector would
have to know that those integers are not pointers.

### 3.4 Names

A name is a slot with tag `REF`, `v.p` the base of the object holding the
target and `aux` the byte offset of the target within it. The pointer is always
an object base, never interior, so marking a name marks its object without a
lookup, and the collector never has to find an object from an address inside
it. `NIL` is a tag of its own.

Cells: a variable declared in a block is a slot in its frame object; `HEAP`
and `LOC` generators allocate a one-slot `SLOTS` object; the name of a variable
of mode `STRUCT` points at the structure object itself (offset of its first
field), so `x OF s` is a name with the field's offset, and `s := t` copies the
fields of `t` into the object `s` names, which keeps every name into `s` valid.
A row variable's slot holds its descriptor; assignment to a non-`FLEX` name
copies elements into the existing storage after the bounds check, and
assignment to a `FLEX` name replaces the descriptor. These are the evaluator's
`assignTo` and `updatePath` rules, restated for the representation.

### 3.5 Frames and closures

Every frame the emitted code pushes (`a68rt_enter`) is a `FRAME` object with a
static link, allocated in the heap; the environment stack is a C array of
frame pointers. A procedure value is `CPROC` with `v.p` the frame it captured;
a format value is `FMT` with the frame and the format-table index. Frames
therefore need no special treatment: a frame no closure captured and no name
points into becomes garbage when it is left.

Rejected: a separate frame stack with escape-on-capture. It saves an allocation
per boxed call, but every frame that any routine text, format text or generator
can see would have to be copied out at capture time, and the analysis already
avoids pushing frames whose slots are all C variables — the frames left are the
ones that can be captured.

### 3.6 Values that stay in Lean

Multi-precision numbers are `LEAF` objects holding the digits; each `LONG`
operation converts operands to `MP.MP` and the result back. Files are ids into
the runtime's file table, as now. Format texts are indices into the serialised
format table plus a frame pointer. `evaluate` is served by converting the
program's visible names to Lean names at the boundary (3.8).

### 3.7 Errors and messages

Every check the evaluator makes — uninitialised value, bounds, `NIL`, overflow,
division by zero, non-finite reals — is made in the same place with the same
text, reported through the line the emitted code records, so that the exit
status and standard error keep matching. `a68lean run` remains the arbiter
where the C runtime and the evaluator disagree.

### 3.8 The boundary to Lean

A call of a builtin (`print`, `printf`, `read`, `whole`, `system`, …) converts
its arguments to Lean `Value`s: scalars directly, rows and structures deeply,
names to a Lean `Value.cref addr mode` whose `readRef`/`writeRef` call back into
C (`a68c_load`, `a68c_store`). The result is converted back. Conversion is
linear in the size of the value, which is what printing it costs anyway.

Invariant B1: *a C object referenced by a Lean value during a builtin call is
reachable from the operand stack for the duration of the call* — arguments stay
on the stack until the builtin returns, and objects created for a result are
created at return. The collector never runs during conversion.

## 4. The collector

### 4.1 Algorithm

Precise, non-moving mark–sweep with size-classed free lists.

* Allocation: size classes of 16-byte multiples up to 2048 bytes, each with a
  free list threaded through free objects; larger objects from `malloc` on a
  large-object list. A class with an empty free list takes a fresh 64 KB block.
* Trigger: a collection is requested when bytes allocated since the last one
  exceed `max(MIN, F × live bytes after the last collection)`, `F = 2`, and
  performed at the next allocation. Allocation is the safe point (4.2).
* Mark: roots are the operand stack, the environment stack, the saved-environment
  stack, the file table's associated names and event routines, and the pin
  stack (4.2). Marking uses an explicit worklist array, never recursion, so a
  40,000-node list cannot exhaust the C stack. A `SLOTS` or `FRAME` object
  contributes each slot whose tag says pointer; a `ROWD` contributes its storage;
  a `LEAF` contributes nothing.
* Sweep: every block is walked; unmarked objects go on their class's free list
  with their payload cleared, marked objects have their bit cleared. Sweeping is
  eager in milestone 2 (the proof is of the eager sweep) and made lazy in the
  performance milestone once the eager version is verified.
* Generational (milestone 3): sticky mark bits — objects marked by a full
  collection stay marked and are treated as old; a minor collection marks from
  the roots and from a card table; the write barrier on `a68rt_store`,
  `a68rt_assign` and `a68rt_sel_store` marks the card of an old object that
  receives a pointer. Non-moving, so no read barrier and no relocation.

Rejected: copying or compacting. Moving objects invalidates names, which a68g
answers with a handle per object and an indirection on every access; a
non-moving collector keeps `REF` a plain pointer. Fragmentation is bounded by
the size classes.

Rejected: reference counting. Cyclic structures are ordinary in Algol 68
(doubly linked lists, trees with parent links), and a count per slot store
costs more than a card mark.

### 4.2 Roots and safe points: the invariants the emitted code keeps

Invariant R1: *the emitted C never holds a heap pointer in a C variable across
a call that can allocate.* This holds by construction of the generator: C
variables hold scalars; promoted rows, strings and union payloads are
`malloc`ed buffers of primitive values that the collector does not manage and
that hold no pointers; the plain entry points `a68_nf{k}` take scalars; the
only pointers the generated code sees are function pointers. Therefore no
shadow stack is needed and no safe-point polls are emitted.

Invariant R2: *inside the C runtime, every heap pointer held across an
allocation is on the operand stack or the pin stack.* The runtime is written
to this rule (an entry point that allocates twice pushes the first object
before allocating the second), and the rule is checked by the `stress` mode,
which collects at every allocation.

Invariant R3: *callbacks are rooted.* `a68rt_call` on a compiled procedure
pushes the arguments and the callee before dispatching; a format hole runs
with its frame on the environment stack; an event routine is called through
`a68rt_call`. Lean-side services that call back (`printf` holes, `on logical
file end`) hold converted copies, and B1 covers the objects those copies refer
to.

Allocation is therefore the only safe point, and it is always safe.

### 4.3 Modes

`A68LEAN_GC=stats` prints collections, bytes freed, peak live size and time at
exit; `stress` collects at every allocation; `verify` walks every object after
each sweep and checks that no reachable slot points at a freed object and that
every free-list entry is unmarked; `off` disables collection (the program grows
as today). `stress` and `verify` together over the corpus and the fuzzers are
the acceptance test of milestone 2.

`sweep heap`, `gc heap`, `preemptive gc`, `collections`, `sweeps`, `garbage`,
`garbage seconds`, `garbage refused` are provided with the meanings a68g gives
them; their values are those of this collector. `--heap N` (opt-in) limits the
heap and stops with *not enough memory* when a collection cannot satisfy an
allocation.

## 5. What is proved

`A68/Verified/GC.lean` models the heap as a finite map from object identifiers
to objects, an object as a vector of slots, a slot as either a scalar or a
pointer to an identifier, and a root set as a list of slots. Theorems:

1. `mark_reachable`: the worklist marking algorithm (with a fuel measure equal
   to the number of objects) terminates and marks exactly the identifiers
   reachable from the roots.
2. `sweep_sound`: sweeping frees exactly the unmarked identifiers and leaves
   every reachable object with its contents unchanged; hence a well-formed heap
   (no slot points at a freed identifier) stays well-formed.
3. `alloc_fresh`: an identifier taken from the free list is not reachable from
   the roots before allocation, and allocation preserves well-formedness.
4. `store_wf`: a store of a pointer to a live object preserves well-formedness.
5. (milestone 3) `barrier_invariant`: with the card table as the extra root
   set, a minor collection marks every young object reachable from an old one.

The C collector transcribes the model's functions one to one (`gc_mark` is the
worklist loop, `gc_sweep` the sweep loop, `gc_alloc` the free-list pop), each
annotated with the theorem it implements, and the `verify` mode checks the
well-formedness invariant of theorem 2 at run time. What is not proved is the
transcription itself and the C runtime's adherence to R2, which `stress` and
`verify` test.

## 6. Milestones (revised)

* **M1 — C runtime.** `csrc/rt.c`: object model, the 109 entry points, the
  boundary conversion, the file hooks. Collection off. Exit: 62 cases and the
  corpus byte-identical under the C runtime; no benchmark slower.
* **M2 — Collector.** Mark, sweep, trigger, the four modes, a68g's procedures,
  `--heap`. Exit: corpus and fuzz under `stress` and `verify`; bounded memory
  on the churn programs.
* **M3 — Generational.**
* **M4 — Proofs.** `A68/Verified/GC.lean` and the annotated transcription.
* **M5 — Native code for the new representation.** Field access and link
  following in C (`data_list`), descriptor-based slicing in C (`data_slice`).
* **M6 — Documentation and hardening.**

## 7. Status

* M1 (C runtime) and M2 (collector) are implemented in `csrc/rt.c`; the Lean services
  are `A68/Runtime.lean` and the codec `A68/Blob.lean`. The collector is eager
  mark–sweep over a linked list of `malloc`ed objects; size-classed free lists and
  lazy sweeping (§4.1) are performance work still to do, as is the generational
  collector (M3).
* M4: `A68/Verified/GC.lean` proves the four theorems of §5 on the model.
* The operators of the primitive modes, strings and row bounds run natively; `LONG`,
  `COMPL`, `BYTES` and rows compared as values still cross to the Lean side (§3.8).
