# The optimiser

`A68.Opt.run` rewrites the core representation between elaboration and the two back
ends. It runs at three levels:

| level | passes |
|---|---|
| `-O0` | none; `run` returns the program unchanged |
| `-O1` (default) | constant folding, coercion simplification, constant control flow, frameless blocks — one round |
| `-O2` | the above plus constant propagation, common subexpression elimination and algebraic simplification — three rounds |

`a68lean run` does not optimise at all: the interpreter is the reference against
which the compiled program is compared.

Every pass is a rewrite of `A68.Core`, so both back ends inherit it. `-O2`'s extra
rounds exist because the new passes *expose* work for the old ones — a propagated
literal is folded on the next round.

For measuring one pass on its own, `A68LEAN_DISABLE` takes a comma-separated list of
`algebra`, `constprop`, `cse`.

## The rule every pass obeys

Optimisation may not change observable behaviour, and in this language "observable"
includes failing. `INT` arithmetic is checked at 32 bits, `REAL` operations reject
infinities and NaNs, subscripts are bounds-checked and reading an uninitialised value
is an error. So a rewrite may not

* **drop** the evaluation of anything that could fail or have an effect,
* **reorder** two things when either of them could fail or be observed,
* **introduce** an operation that could fail where none could before.

That is why `x * 0` is not `0`, and why `(a + b) - b` is not `a`.

---

## 1. Constant folding, coercions, constant control flow, frameless blocks (`-O1`)

Described in [ARCHITECTURE.md](ARCHITECTURE.md). One correction was needed: the
de Bruijn shift that the frameless-block pass performs did not descend into **format
texts**, which carry core terms of their own — a dynamic replicator `n(k)d`, the
arguments of `g`, an included format. A name inside one that reached past the removed
frame kept its old depth and read the wrong cell. `A68.Opt.shiftFmt` fixes it. Before:

```algol68
BEGIN INT k := 5; INT x := 42;
  BEGIN printf(($n(k)d l$, x)) END      # the inner block is frameless
END
```

printed `00042` at `-O0` and panicked with `index out of bounds` at `-O1`.

---

## 2. Constant propagation (`-O2`)

An identity declaration binds a value once — unlike a variable declaration, which
declares a *name* that can be assigned. So in

```algol68
INT k = 3;
... k ...
```

the elaborator emits `CoreStmt.decl slot (lit 3)` and every use is
`Core.loadCell depth slot`, where `depth` counts the frames pushed between the use and
the declaring block. The pass replaces those uses by the literal.

**What it assumes.**

* The declaration's right hand side, after `at` wrappers are stripped, is a **scalar**
  literal: `int`, `real`, `bool`, `char` or `bits`. Composite values are not
  propagated (nothing would be gained, and `undef` must never be).
* **No `refCell depth slot` names the cell** anywhere in the block, at any depth.
  `refCell` is the only way to obtain a name of a frame cell, so if none exists the
  cell cannot be assigned — not through an alias either, since an alias must come from
  a `refCell` too. `A68.Opt.refsSlot` checks this over the whole subtree, following the
  same depth arithmetic as `shift`, and descending into format texts, which carry core
  terms of their own.
* The slot is declared exactly once in the block.
* **The block has no labels.** With a label, a jump could reach a use without the
  declaration having run, where the original program reports an uninitialised value.

**Depth arithmetic.** `A68.Opt.substLit` mirrors `A68.Opt.shift` exactly: the depth
grows by one at every construct that pushes a frame — a block, a routine text, the
`while` part and body of a loop (but not its bounds, which are evaluated outside the
iteration frame), and a conformity alternative.

**Effect.** Propagation alone removes no nodes — a literal is one node and so is a
cell load. It pays off through the folding it exposes on the next round.

---

## 3. Common subexpression elimination (`-O2`)

Inside one block, an expression that is evaluated twice in straight-line order is
evaluated once.

The IR has no temporaries, so one is made by **extending the block's frame with a fresh
slot**. That is safe: a frame is an array of cells allocated on entry, and nothing
outside the block can see how many there are. Changing frame *nesting* would not be
safe, and is not done — no name's depth changes.

**Which expressions may be shared** (`A68.Opt.shareable`): literals of scalar mode,
`loadCell`, `deref (refCell …)`, widening between scalar modes, and the standard
prelude's arithmetic and comparison `dyop`/`monop` on scalar modes
(`+ - * / % %* ** = /= < <= > >=`, `- + ABS SIGN ODD NOT BIN REPR ROUND ENTIER SHORTEN
LENG`). Such an expression reads cells and nothing else: it cannot assign, allocate,
call or print. User-defined operators are not `dyop` nodes — the elaborator turns them
into calls — so a whitelisted name always denotes the prelude's operator.

A shared expression may still **fail**, which is why it is never moved across anything
that could itself fail or be observed.

**Where occurrences are looked for.** `A68.Opt.cseGo` walks a statement in the order the
evaluator does. It descends into everything that is unconditionally evaluated, and
stops at anything conditional or opaque: the branches of `cond`/`caseInt`/`caseConf`,
the right operand of `andThen`/`orElse`, a loop's body and `while` (its bounds are
visited — they are evaluated in this frame), and a nested `block` or `routine`. Nested
blocks get their own turn, since `opt` recurses before it calls this pass.

**What invalidates a temporary.** After the first occurrence, the walk stops replacing
when it meets

* a `call`, `deproc`, `newRow`, `fmt`, `goto`, `stop`, a nested block or loop, or a
  non-whitelisted operator — anything that could assign, call or print;
* an assignment through a computed name (a slice, a selection, a dereference);
* an assignment to `refCell d s` where the shared expression reads cell `(d, s)`.
  Assignments to *other* cells are harmless, which is what makes the pass useful at
  all: `x := a + b; y := a + b` is shared even though `x` is assigned in between.

`gen` is not a barrier: it allocates a fresh cell, which no existing expression reads.

**Where the definition goes.** Two forms, chosen by whether the first occurrence can be
lifted out of its statement:

* If everything evaluated before it in that statement is *total* — only `lit`,
  `refCell`, `routine` and `skip` nodes, none of which can fail or have an effect — the
  definition becomes a `CoreStmt.decl` in front of that statement and all occurrences
  become `loadCell 0 slot`. This is the common case: an assignment evaluates its
  destination `refCell` first, so the whole right hand side qualifies. The hoisted
  initialiser is wrapped in the `at` node that was in force at the occurrence, so a run
  time error still quotes the same source position.
* Otherwise the definition is made where it stands, as
  `deref (assign (refCell 0 slot) e)`: the expression is evaluated in its original
  place, stored and read straight back. Nothing moves.

The pass is refused for a block with labels (a jump backwards could reach a use of the
temporary without its definition), and a rewrite is kept only if it does not make the
core tree bigger. At most four expressions are shared per block per round.

**Effect.** Node counts barely move — the hoisted form replaces `n` copies of an
expression of size `s` by one copy plus `n` cell loads — but one evaluation is saved
per occurrence. On the corpus this pass fires rarely (see *Measurements*); the reason
is the shareable grammar. Array subscripts, which are what real Algol 68 repeats, are
deliberately excluded: a slice or a selection can yield an *uninitialised* element, and
`loadCell` rejects `undef`, so routing one through a cell would turn a value the
original program passes along into an error.

---

## 4. Algebraic simplification (`-O2`)

`A68.Opt.algebraic` rewrites a `dyop` whose *discarded* operand is a literal and whose
kept operand was going to be evaluated anyway. Every rule keeps the result mode, so no
coercion appears or disappears.

| mode | rules |
|---|---|
| `INT` (any length), `m1 = m2` | `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x`, `x OVER 1` |
| `INT ** INT` | `x ** 1` (the exponent's mode is always `INT`, the result's the base's) |
| `REAL` (any length), `m1 = m2` | `x - 0.0`, `x * 1.0`, `1.0 * x`, `x / 1.0` |
| `REAL ** INT` | `x ** 1` |

`INT / INT` never appears — the elaborator widens both operands to `REAL` — so `n / 1`
in the source is simplified by the `REAL` rule.

**What is deliberately absent.**

* `x * 0 → 0` and `x - x → 0`: they drop the evaluation of `x`, which can overflow.
* `(a + b) - b → a`: false for checked 32-bit `INT`.
* `x MOD 1`: this is `0`, not `x` — a68g's `MOD` is `%*`, `Int.emod x 1 = 0` — and
  rewriting it to `0` would drop `x`. So `MOD` has no rule at all. (The task list that
  prompted this pass named `x MOD 1`; `x OVER 1` is the identity that actually holds.)
* `x + 0.0` and `0.0 + x`: `-0.0 + 0.0` is `+0.0`, so the rule would change the sign of
  a zero, and `-0.0` prints differently. `x - 0.0` is safe (`-0.0 - 0.0 = -0.0`), and
  the literal is checked to be `+0.0` and not `-0.0`.
* `x ** 1.0` for `REAL ** REAL`: a68g computes that as `exp (y × ln x)`, which is
  neither exact nor defined for negative `x`.

`x ** 1` is safe for both `INT` and `REAL` bases because a68g's square-and-multiply
returns the base itself for exponent 1, with no rounding and no range check that could
newly fail.

---

## What is proved

`A68/Verified/Opt.lean` states each rewrite over the formal expression core of
`A68/Verified/StackMachine.lean` — integer literals, de Bruijn identifiers, `+ - *`,
monadic minus and `let` (an identity declaration) — where evaluation is a total
function and semantics preservation is an equation. Everything below is checked by
`lake build` and depends on no axioms beyond `propext` and `Quot.sound`.

| theorem | statement |
|---|---|
| `algebraic_eval` | `(algebraic e).eval env = e.eval env` for `x+0`, `0+x`, `x-0`, `x*1`, `1*x` |
| `substLit_eval` | substituting a literal for an identifier that denotes it preserves `eval`, at any binder depth |
| `constProp_correct` | `(constProp e).eval env = e.eval env` |
| `liftN_eval` | shifting the identifiers that reach past `c` binders is compensated by an environment with one more entry at the cut |
| `abstract_eval` | `(abstract t e).eval (t.eval env :: env) = e.eval env` |
| `cse_correct` | `(cse t e).eval env = e.eval env`, for **every** choice of shared expression `t` |
| `optLet_eval` | an optimised identity declaration denotes what the declaration denotes |
| `opt2_correct` | folding, algebraic simplification and constant propagation together preserve `eval` |
| `opt2_compile_correct` | the *code generated* for the optimised program computes what the source denotes |
| `cse_compile_correct` | the same, for a shared expression |

(The earlier `opt_correct`, `opt_size`, `opt_idempotent` and `compile_correct` are
unchanged. `A68/Verified/Opt.lean` was not reachable from the root module before, so
`lake build` did not check it; it is imported now.)

---

## Measurements

139 programs of the Rosetta Code corpus that elaborate and compile
(`a68lean compile x.a68 -v` prints `core nodes: N -> M`; `A68LEAN_DISABLE` turns one
pass off).

| | core nodes |
|---|---|
| unoptimised | 48 164 |
| `-O1` | 42 979 (10.8 % removed) |
| `-O2` | 42 931 (10.9 % removed) |

`-O2` removes 48 nodes beyond `-O1` — 0.11 % of the `-O1` tree. Per pass, counting both
the nodes it removes and how often it changes the generated code at all:

| pass | nodes removed | changes the code |
|---|---|---|
| constant propagation | 44 | 35 / 139 programs |
| common subexpression elimination | 4 | 3 / 139 |
| algebraic simplification | 0 | 0 / 139 |

The two numbers differ because propagation is node-neutral on its own (23 of its 35
programs only get literals where they had cell loads, with nothing further to fold),
and because the hoisted form of CSE is node-neutral by construction — it saves an
*evaluation*, not a node.

The biggest single win is `Arithmetic-Integer`, 79 → 65 nodes, where
`INT a = 355, b = 113` are propagated and the arithmetic on them folds away.
`Air-mass` runs 33.3 s at `-O0` and 27.9 s at `-O2`.

**Why so little.** These programs are not written the way the passes reward.

* Algol 68 code says `INT n = read int`, not `INT n = 3`, so few identity declarations
  are literal; and where they are, `-O1`'s folding has usually already done the
  interesting part inside the declaration itself.
* Nobody writes `x + 0`.
* What real programs repeat is `a[i]`, `s[k]` and calls — none of which are shareable
  here, for the reasons in §3. Restricted to arithmetic on scalars in straight-line
  positions, repetition is rare.

The passes are worth having for what they guarantee rather than for what they remove
today. `tests/opt/` exercises each of them on a program written for it and checks that
`a68lean run`, `-O0`, `-O1` and `-O2` all produce the same bytes as a68g:

```
./tests/opt/run.sh              # pass=4 fail=0
./tests/opt/run.sh --record     # regenerate the expected files with a68g
```

Widening the shareable grammar to subscripts is the obvious next step, and needs a way
to move a value through a cell without `loadCell`'s uninitialised-value check.

---

### Two back end bugs the new passes uncovered

Neither is an optimisation bug, but both made `-O2` disagree with `-O0`, so they are
fixed here.

* **`REAL` literals lost precision in the C back end.** `CodeGen.creal` rendered a
  `Float` with Lean's `toString`, which keeps six decimals — so *every* `REAL`
  denotation in a compiled program was rounded, at every level including `-O0`.
  Constant propagation made it visible by turning `pi` into a literal. Literals are
  now written as C99 hexadecimal floating constants (`0x1.921fb54442d18p+1`), which
  are the bit pattern itself. On 80 corpus programs this alone took the number whose
  compiled output matches a68g byte for byte from 34 to 40.
* **`a68rt_push_bigint` was emitted without its world argument**, so any program whose
  optimiser produced an integer literal outside 32 bits failed to compile — already
  true at `-O1`.

### What the model does and does not capture

* **Constant propagation** is captured faithfully, including the part that is easy to
  get wrong: `substLit` steps its index at every binder, which is the frame-depth
  arithmetic of the production pass.
* **CSE** is captured *more* strictly than the production pass needs. In `Expr` the only
  way to add a slot is a new `let`, which pushes a frame, so `abstract` must lift every
  free identifier of the body past it — a shift the real pass never performs, because it
  adds a slot to the frame that is already there. `abstract` also refuses to replace
  occurrences under a binder, which is the production pass's rule that it never
  descends into a nested frame. What the model cannot express is the *side condition*:
  `Expr.eval` is total and pure, so there is nothing in it corresponding to "this
  expression may fail" or "an assignment happened in between". The barrier analysis of
  §3 is therefore argued in prose, not proved.
* **Algebraic simplification** is captured for the five rules the core can express.
  The core's `Int` is unbounded, so it cannot express the *reason* the other identities
  are refused — `sub (add a b) b → a` would be provable here and is false for checked
  `INT`. That asymmetry is why the production list is shorter than the model would
  allow, and it is noted in the module.
