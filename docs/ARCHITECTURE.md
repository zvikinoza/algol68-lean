# Architecture

`a68lean` is organised as a classical compiler front end, followed by either an
evaluator for the core representation or a C back end. Every stage is a total
Lean function except where noted.

```
source text
   │  A68.Lexer.lex                (total: recursion on remaining input)
   ▼
tokens ──► A68.Parser.prescan      (collects MODE / OP / PRIO names and priorities)
   │  A68.Parser.parse             (recursive descent, backtracking where Algol 68 needs it)
   ▼
A68.Syntax  (parse tree)
   │  A68.Elab.elabProgram         (modes, coercions, operator identification, scopes)
   ▼
A68.Core    (typed core representation with explicit coercions and resolved names)
   │  A68.Opt.run                  (constant folding, coercion and block simplification)
   ▼
A68.Core    (optimised)
   ├── A68.Interp.run              → run directly            (a68lean run)
   └── A68.CodeGen.program         → C → system C compiler   (a68lean compile)
   ▼
observable behaviour (stdout bytes, files, exit status)
```

Both back ends share `A68.Runtime`, so `print`, `printf`, the operators and the
number formatting are one implementation reached two ways; that is what makes a
compiled program and an interpreted one produce the same bytes.

## Lexer (`A68/Lexer.lean`)

The tokeniser handles a68g's upper-stropping conventions. Two decisions matter
for compatibility:

* Tags may contain spaces: `new line` and `newline` are the same identifier.
  The lexer joins a tag across spaces when the next character can continue a
  tag; `FOR i TO n DO` still splits correctly because bold words cannot
  continue a tag.
* Operator symbols follow a68g's scanner exactly: an operator is a *monad*
  (`% ^ & + - ~ ! ?`) or *nomad* (`> < / = *`) character, optionally followed
  by one nomad, then optionally `=`, `:`, `=` (in that order). Consequently
  `x:=-1` lexes as `x := -1`, `2**-1` as `2 ** -1`, and `+:=`, `<<:=`, `=:=`
  are single operator symbols.

Comments and pragmats are consumed by the lexer; pragmats are kept as tokens
so that `precision`, `echo` and `regression` can be honoured.

## Parser (`A68/Parser.lean`)

Algol 68 cannot be parsed without knowing which bold words are mode indicants
and which are operators, and with what priority. `prescan` walks the token
stream once, tracking bracket depth, and records every `MODE`, `OP` and `PRIO`
declaration. The parser proper is recursive descent with precedence climbing
for formulas (all dyadic operators are left associative; monadic operators
bind tightest, so `-2**2 = 4` as in a68g).

Constructs that need lookahead beyond one token — routine texts, conformity
alternatives, declarations versus casts, enquiry clauses versus collaterals —
are recognised by speculative parsing that backtracks on failure. Once a
routine header or a `declarer identifier` prefix has been seen the parser
commits, so that errors inside the body are reported rather than swallowed.

The parser is the one component written with `partial def` (termination of
a backtracking parser is not worth proving); it is nevertheless total in
practice because every alternative consumes input or fails.

## Modes (`A68/Mode.lean`)

Modes are a first-order type: `int n`, `real n` (with the `LONG` level `n`),
`ref`, `row dims flex`, `proc`, `struct`, `union`, and `named` for mode
indicants. Recursive modes (`MODE NODE = STRUCT (INT v, REF NODE next)`) stay
as `named` references into a table; equivalence (`Mode.eqv`) unfolds them
with a fuel bound, ignores the `FLEX` flag (which only affects assignment), and
compares structurally.

## Elaboration (`A68/Elab.lean`)

The elaborator implements the Revised Report's coercion discipline. Every unit
is elaborated in a *context*:

| context | permitted coercions |
|---|---|
| strong (target mode known) | deproceduring, dereferencing, uniting, widening, rowing, voiding |
| firm (operands) | deproceduring, dereferencing, uniting |
| meek (conditions, subscripts, calls) | deproceduring, dereferencing |
| weak (slices, selections) | dereferencing down to a name of a row/struct |
| soft (assignment destinations) | deproceduring |

`coerce` searches for a coercion sequence and returns the core term with the
coercions made explicit (`deref`, `deproc`, `widen`, `rowOf`, `unite`,
`voiding`). Balancing (`balance`) chooses a common mode for the branches of
conditional and case clauses when no target mode is known; branches that never
yield a value (`stop`, jumps) do not take part.

Operator identification searches user-declared operators innermost-scope-first
with firm coercions of the operands, then falls back to the standard prelude,
where a68g's widening of mixed `INT`/`REAL`/`LONG` operands is applied.

Name resolution assigns every declared object a `(frame depth, slot)` pair.
Every serial clause, routine text, loop and conformity alternative opens a
frame, and the evaluator pushes a frame at exactly the same points, so the
static depth computed here equals the dynamic environment depth. Enquiry
clauses (`IF INT c = …; c > 0 THEN … c … FI`) keep their frame alive for the
branches, as the language requires.

## Core representation (`A68/Core.lean`)

`Core` is a small language: literals, cell loads and name creation
(`loadCell`, `refCell`), explicit coercions, assignment, identity relation,
builtin operators tagged with their operand modes, calls, routine texts,
slices, selections, row creation, generators, blocks with label tables,
collaterals, conditionals, cases, loops, jumps, short-circuit operators and
format texts. Values (`Value`) are immutable data: integers (unbounded `Int`,
range-checked per mode), floats, booleans, byte characters, bits, rows (bounds
plus a flat element array), structs, united values (tagged with their
constituent mode), names (`ref cell path`), closures, formats and files.

## Evaluator (`A68/Interp.lean`)

The runtime keeps a heap of *cells* (`Array Value`); a name is a cell number
plus a path of selections (field, element, or a trimmed sub-row view). Because
values are immutable, assignment through a name is a functional update along
the path; the value is detached from its cell first so that Lean's runtime
performs the update in place when the value is not shared, which keeps
element-wise array filling linear.

Environments are lists of frames; closures capture the environment at routine
text evaluation. Control flow that leaves an expression (jumps, `stop`, run
time errors, mended file ends) is an `ExceptT` exception caught by the
enclosing block or loop.

Numeric semantics mirror a68g: `INT` is 32-bit with overflow detection on every
operation, `LONG INT`/`LONG LONG INT` have 49 and 84 decimal digits (or the
`PR precision` value), `REAL` operations raise a runtime error on infinities
and NaNs, `REAL ** INT` is square-and-multiply in a68g's order, and
`REAL ** REAL` is `exp (y · ln x)`.

`LONG` and `LONG LONG` reals (and complex numbers) are `Value.mp` numbers of
`A68.MP`, a digit-for-digit re-implementation of a68g's multi-precision library:
`A68.MP` has the arithmetic and conversions, `A68.MPMath` the elementary
functions with a68g's caches of π and logarithms, and `A68.MPFmt` the formatting
of long values. A `LONG` real denotation is elaborated as a `DENOT` operator on
its text, converted at run time at the precision of its length, so no double
ever stands in for it.

The one place a68g's own arithmetic is inexact, the quotient-digit estimate of its
division routines (doubles combined with fused multiply-add), is reproduced exactly
but cheaply: `MP.qDigit` first computes the estimate with plain doubles, and falls
back to the exact big-integer emulation only when that quotient lies within 10⁻⁶ of
an integer. Both estimates are within 2·10⁻¹⁵ of the exact quotient, so outside that
margin they truncate to the same digit. `LONG INT` arithmetic stays on exact integers,
which is what a68g's multi-precision routines compute for in-range integers.

Transput lives in the same module: unformatted `print`/`put`, the formatted
`printf`/`putf` picture machine (frames, moulds, sign shifting, zero
suppression, replicated collections, embedded formats, column alignment),
`read`/`get`/`getf`, and files (disk files, string-associated files, standard
streams, logical-file-end and value-error menders).

## Number formatting (`A68/Numfmt.lean`)

All conversions go through an exact decimal type `Dec = mant × 10^exp` and
follow a68g's algorithms step by step (`whole`, `fixed`, `float` and its
helpers `sub_fixed`, `standardize`). The only inexact step in a68g is the
conversion of a C `double` into its multi-precision representation, which
extracts 21 significant digits with a floating-point loop; `realToDec`
reproduces that loop bit for bit (including a68g's `ten_up` power table), so
that outputs such as `123456789012345671.653` for the double
`123456789012345678.0` are identical. See
[COMPATIBILITY.md](COMPATIBILITY.md) for details.

## Optimiser (`A68/Opt.lean`)

The passes are those of a68g's optimiser (`plugin-folder.c`, `plugin-inline.c`),
applied to the core representation before either back end runs:

* **Constant folding.** An operator, coercion or widening whose operands are all
  literals is replaced by the literal it evaluates to. The folding is done *by
  running the unit with the run-time evaluator* in a scratch state with no
  output, so a folded value cannot differ from what the program would have
  computed, and a unit that would fail at run time (overflow, division by zero)
  is simply left alone.
* **Coercion simplification.** `deref (refCell d s)` becomes `loadCell d s`,
  and a widening between equal modes disappears.
* **Constant control flow.** A conditional, short-circuit operator or case with
  a constant selector becomes the branch it selects.
* **Frameless blocks.** A block that allocates no cells, declares nothing and
  has no labels needs no run-time frame; its units become a sequence. Removing a
  frame changes what every enclosed name is relative to, so the pass shifts the
  depth of each name that reaches past the removed frame — the same de Bruijn
  shift a compiler performs when it drops a scope.

`-O2` adds three more:

* **Constant propagation.** An identity declaration binds a value once; if that
  value is a scalar literal and no `refCell` ever names the cell, the uses of the
  cell become the literal, wherever they are nested.
* **Common subexpression elimination.** An expression evaluated twice in
  straight-line order inside one block is evaluated once, into a slot added to
  that block's frame. Only expressions that read cells and nothing else are
  shared, and never across an assignment that could change what they read.
* **Algebraic simplification.** `x + 0`, `x * 1`, `x OVER 1`, `x / 1.0`, `x ** 1`
  and their mirrors, where the discarded operand is a literal.

`-O0` disables the passes, `-O1` (the default) runs the cheap ones once, `-O2`
runs everything three times (a propagated literal is folded on the next round).
`A68.Verified.Opt` proves the same rewrites correct over the formal core.
[OPTIMISATION.md](OPTIMISATION.md) describes each pass, what it is allowed to
assume, and which parts are proved.

## C back end (`A68/CodeGen.lean`, `A68/Runtime.lean`, `A68/Serial.lean`)

`a68lean compile` emits a self-contained C program and hands it to the system C
compiler. The division of labour mirrors a68g's optimiser, which also compiles
units to C against its own runtime, except that the result here is a whole
program rather than a plugin loaded back into an interpreter:

* **Structure is compiled.** Blocks, conditionals, cases, loops and jumps become
  C control flow; every routine text becomes its own C function.
* **Values of primitive mode are compiled to native C.** `INT`, `REAL`, `BOOL`,
  `CHAR` and `BITS` at their unwidened length are computed in `int64_t`,
  `double`, `uint8_t`, `uint32_t` and `uint64_t`, so `(s + i * 3) MOD 1000003`
  is one line of C arithmetic that allocates nothing. Each helper reproduces the
  check its interpreted counterpart performs, so overflow, division by zero and
  a non-finite real still fail in the same place with the same message. Longer
  lengths keep the runtime's arbitrary-precision representation.
* **Locals that cannot escape become C variables.** A slot qualifies when its
  declared mode is primitive, nothing takes a reference to it, and no routine
  text or format text inside the frame reads or names it. Those are compiled
  into C functions of their own and reach the frame through the run-time
  environment, so a slot they can see keeps its cell; the analysis asks exactly
  that (`seenByOtherFn`, on a traversal that covers every constructor and counts
  the frames entered on the way down), so declaring a procedure in a block no
  longer costs the block its C variables. When every slot of a frame qualifies
  and no such text is present, no run-time frame is pushed for it, and
  `rtDepthOf` translates the syntactic depths that `loadCell` and `refCell`
  carry into the run-time depths that remain. A `FOR` counter becomes the C
  induction variable itself, and `x +:= e` on such a variable is a C update.
* **Everything else goes through the runtime.** `A68.Runtime` exposes the
  evaluator's operations as a C-callable API that is deliberately integer-only,
  so the generated C never touches a Lean object: an environment stack of frames
  of cells (`a68rt_enter` / `a68rt_leave`) and an operand stack of values
  (`a68rt_push_*`, `a68rt_dyop`, …), which is the discipline the verified stack
  machine models. Rows and structures have short cuts: an element of a row held
  directly in a cell, or a chain of field selections rooted at one, is read and
  written by one call that carries a native value, `s +:= c` appends to a string
  in place, and anything else falls back to the general machinery.
* **Reaching a statement is a store, not a call.** The current line lives in a C
  variable that the error reporters read when a compiled program is running.
* **Tables are rebuilt at start-up.** Modes tag united values and drive the
  layout of `print`; format texts carry the pictures. Both are serialised by
  `A68.Serial` into a blob the C program carries as a string literal and hands
  to `a68rt_boot`.
* **Calls back into compiled code.** A compiled procedure is a `Value.cproc`
  holding a function index and its captured environment; the dynamic parts of a
  format text are `Core.hole` nodes. When the runtime needs either, it calls
  `a68_dispatch_proc` / `a68_dispatch_hole`, which the generated program
  defines. The `a68lean` binary itself links stubs for them (`csrc/stubs.c`).
* **Direct calls.** A routine whose frame is exactly its parameters, all of
  primitive mode, whose result is primitive or `VOID`, and which contains no
  further routine or format text, is compiled a second time as a plain C
  function `a68_nf{k}`: parameters are C arguments, the result is the C return
  value, and no run-time frame is pushed (`natSigOf`, `genNative`). A call goes
  there only when that is certainly the same thing: the callee is a slot declared
  by a routine text, which as an identity declaration holds nothing else, and the
  frame the slot lives in is the innermost run-time frame, so the environment the
  routine captured is already in effect (`staticNat`). A block's units see a
  routine once its declaration has been passed; a routine body also sees those
  declared with it in the same run of routine declarations, which makes
  recursion and mutual recursion direct. Everything else — a `PROC` variable, a
  procedure parameter, a call from somewhere an environment switch is needed —
  keeps the boxed entry point and the operand-stack call.
* **Calls inside expressions keep their order.** An expression containing a
  direct call is emitted in A-normal form (`anf`): each call is a statement
  followed by the jump check, and the left operand of an operator whose right
  operand calls is hoisted first, unless it is a literal or a C variable that
  needs no undefined test, which no callee can reach and whose reading can
  neither fail nor act. C's unspecified order of evaluating operands therefore
  never decides the order of an Algol program's side effects.
* **Jumps.** A jump to a label of the enclosing C function is a C `goto`. A jump
  out of a routine sets a pending label — a plain C variable, `a68_jump_flag`,
  since every call site tests it — and returns, with a dummy value from a plain C
  entry point; each call site checks it and either lands on one of its own labels
  or returns in turn, so the C stack unwinds without `longjmp`. Landing clears the
  pending label and restores the environment and operand stack to the depths
  recorded at block entry, which is what the evaluator does when it re-enters a
  block at a label.

Promotion depends on the optimiser having flattened the block structure: at
`-O0` each unit sits in its own block, so an assignment is the value of its
block rather than a statement, and the escape analysis rightly refuses. `-O1`
and `-O2` flatten first, and that is where the native code appears.

A compiled program links the Lean runtime and this compiler's library, so the
binaries are large (about 18 MB) and need the Lean toolchain at link time, not
at run time.
