import A68.Core
import A68.Interp

/-!
# A68.Opt — optimisation passes over the core representation

The `-O1` passes mirror those of Algol 68 Genie's optimiser (`plugin-folder.c`,
`plugin-inline.c`): fold constant units, remove coercions that do nothing,
short-circuit constant conditions, and flatten blocks that need no frame.
`-O2` adds constant propagation, common subexpression elimination within a block
and algebraic simplification; see `docs/OPTIMISATION.md` for what each is allowed
to assume and why.

Two design decisions keep the passes trustworthy:

* **Folding is done by evaluation.** A constant unit is folded by running it
  with the very evaluator that would run it at run time, in a scratch state
  with no output.  A folded literal therefore cannot differ from the value the
  unfolded program would have produced, and an operation that would fail at
  run time (overflow, division by zero) simply is not folded.
* **The structural passes are the ones proved.** `A68.Verified.Opt` states and
  proves the same rewrites over the formal expression core, where evaluation is
  a total function and semantics preservation can be stated as an equation.
-/
namespace A68.Opt

/-- Units that can be folded: no names, no calls, no transput — only literals,
    operators and the coercions between them. -/
partial def isConst : Core → Bool
  | .lit (.int _) | .lit (.real _) | .lit (.bool _) | .lit (.char _) | .lit (.bits _) => true
  | .dyop _ _ _ a b => isConst a && isConst b
  | .monop _ _ e => isConst e
  | .widen _ _ e => isConst e
  | .at _ e => isConst e
  | _ => false

/-- Is this a literal already? -/
def isLit : Core → Bool
  | .lit _ => true
  | _ => false

/-- A scratch runtime for compile-time evaluation: output is discarded and no
    files or arguments are available, so only pure units can be folded. -/
private def scratchRt : IO Interp.Rt := do
  return { heap := ← IO.mkRef #[], out := ← IO.mkRef ByteArray.empty, pos := ← IO.mkRef {},
           modes := {}, files := ← IO.mkRef #[], rng := ← IO.mkRef (Interp.tausSet 1),
           args := #[], ll := Numfmt.defaultLLDigits, regression := false, col := ← IO.mkRef 0 }

/-- Evaluate a constant unit with the run-time evaluator; `none` if it would fail. -/
def evalConst (rt : Interp.Rt) (c : Core) : IO (Option Value) := do
  match (← ((Interp.eval [] c).run rt).run) with
  | .ok v =>
    match v with
    | .int _ | .real _ | .bool _ | .char _ | .bits _ => return some v
    | _ => return none
  | .error _ => return none

-- Remove one frame from the environment chain: every name that reaches past the
-- removed frame moves one level closer.  `cutoff` counts the frames pushed between
-- the current point and the frame being removed, so it grows at every construct that
-- pushes one: blocks, routine texts, loop iterations and conformity alternatives.
mutual
partial def shift (cutoff : Nat) : Core → Core
  | .loadCell d s => .loadCell (if d > cutoff then d - 1 else d) s
  | .refCell d s => .refCell (if d > cutoff then d - 1 else d) s
  | .block size stmts lb nl => .block size (stmts.map (shiftStmt (cutoff + 1))) lb nl
  | .routine np fs body => .routine np fs (shift (cutoff + 1) body)
  | .loop slot f b t w body =>
    -- the bounds are evaluated outside the iteration frame, the rest inside it
    .loop slot (shift cutoff f) (shift cutoff b) (t.map (shift cutoff))
          (w.map (shift (cutoff + 1))) (shift (cutoff + 1) body)
  | .caseConf sel alts out =>
    .caseConf (shift cutoff sel) (alts.map fun (m, s, c) => (m, s, shift (cutoff + 1) c))
              (shift cutoff out)
  | .deref e => .deref (shift cutoff e)
  | .deproc e => .deproc (shift cutoff e)
  | .rowOf e => .rowOf (shift cutoff e)
  | .voiding e => .voiding (shift cutoff e)
  | .gen e => .gen (shift cutoff e)
  | .at p e => .at p (shift cutoff e)
  | .widen a b e => .widen a b (shift cutoff e)
  | .unite m e => .unite m (shift cutoff e)
  | .monop op m e => .monop op m (shift cutoff e)
  | .select i e r => .select i (shift cutoff e) r
  | .assign a b f => .assign (shift cutoff a) (shift cutoff b) f
  | .identRel a b i => .identRel (shift cutoff a) (shift cutoff b) i
  | .andThen a b => .andThen (shift cutoff a) (shift cutoff b)
  | .orElse a b => .orElse (shift cutoff a) (shift cutoff b)
  | .seq a b => .seq (shift cutoff a) (shift cutoff b)
  | .dyop op m1 m2 a b => .dyop op m1 m2 (shift cutoff a) (shift cutoff b)
  | .call f args => .call (shift cutoff f) (args.map (shift cutoff))
  | .slice a idx r => .slice (shift cutoff a) (idx.map (shiftIdx cutoff)) r
  | .newRow bs i f => .newRow (bs.map fun (l, u) => (shift cutoff l, shift cutoff u)) (shift cutoff i) f
  | .collateral es st d => .collateral (es.map (shift cutoff)) st d
  | .cond c t e => .cond (shift cutoff c) (shift cutoff t) (shift cutoff e)
  | .caseInt s alts o => .caseInt (shift cutoff s) (alts.map (shift cutoff)) (shift cutoff o)
  | .fmt items => .fmt (items.map (shiftFmt cutoff))
  | other => other

/-- A format text carries core terms of its own — dynamic replicators, the arguments
    of `general`, an included format — and they name cells like any other term. -/
partial def shiftFmt (cutoff : Nat) : CoreFmt → CoreFmt
  | .rep n dyn item => .rep n (dyn.map (shift cutoff)) (shiftFmt cutoff item)
  | .general args => .general (args.map (shift cutoff))
  | .include f => .include (shift cutoff f)
  | .group items => .group (items.map (shiftFmt cutoff))
  | it => it

partial def shiftStmt (cutoff : Nat) : CoreStmt → CoreStmt
  | .decl slot m init => .decl slot m (shift cutoff init)
  | .unit e => .unit (shift cutoff e)
  | st => st

partial def shiftIdx (cutoff : Nat) : CoreIdx → CoreIdx
  | .index e => .index (shift cutoff e)
  | .trim l u a => .trim (l.map (shift cutoff)) (u.map (shift cutoff)) (a.map (shift cutoff))
end

/-- A block that allocates no cells, declares nothing and has no labels needs no frame:
    its units become a sequence, with the names inside shifted one level closer. -/
def flattenBlock (size : Nat) (stmts : Array CoreStmt) (nl : Nat) : Option Core :=
  if size != 0 || nl != 0 then none
  else
    let units := stmts.toList.filterMap fun
      | .unit e => some e
      | _ => none
    if units.length != stmts.size then none      -- a declaration, label or EXIT is present
    else match units.map (shift 0) with
      | [] => some (.lit .void)
      | [e] => some e
      | e :: rest => some (rest.foldl (fun acc u => .seq acc u) e)

/-- Count the nodes of a core term (used to report what the optimiser removed). -/
partial def size : Core → Nat
  | .deref e | .deproc e | .rowOf e | .voiding e | .gen e | .at _ e
  | .widen _ _ e | .unite _ e | .monop _ _ e | .select _ e _ => 1 + size e
  | .assign a b _ | .identRel a b _ | .andThen a b | .orElse a b | .seq a b => 1 + size a + size b
  | .dyop _ _ _ a b => 1 + size a + size b
  | .call f args => 1 + size f + (args.map size).foldl (· + ·) 0
  | .routine _ _ b => 1 + size b
  | .slice a idx _ => 1 + size a + (idx.map (fun
      | .index e => size e
      | .trim l u a => (l.map size).getD 0 + (u.map size).getD 0 + (a.map size).getD 0)).foldl (· + ·) 0
  | .newRow bs i _ => 1 + size i + (bs.map (fun (l, u) => size l + size u)).foldl (· + ·) 0
  | .block _ stmts _ _ => 1 + (stmts.toList.map (fun
      | .decl _ _ c => size c
      | .unit c => size c
      | _ => 0)).foldl (· + ·) 0
  | .collateral es _ _ => 1 + (es.map size).foldl (· + ·) 0
  | .cond c t e => 1 + size c + size t + size e
  | .caseInt s alts o => 1 + size s + (alts.map size).foldl (· + ·) 0 + size o
  | .caseConf s alts o => 1 + size s + (alts.map (fun (_, _, c) => size c)).foldl (· + ·) 0 + size o
  | .loop _ f b t w body =>
    1 + size f + size b + (t.map size).getD 0 + (w.map size).getD 0 + size body
  | _ => 1

/-! ## Helpers shared by the `-O2` passes -/

/-- The scalar (non-composite) values: exactly the ones a literal may hold. -/
def isScalarValue : Value → Bool
  | .int _ | .real _ | .bool _ | .char _ | .bits _ => true
  | _ => false

/-- Equality of scalar literals.  `0.0` and `-0.0` compare equal under IEEE `==` but
    are *different literals* (they print differently), so they are told apart here. -/
def scalarEq : Value → Value → Bool
  | .int a, .int b => a == b
  | .real a, .real b => a == b && (a != 0.0 || 1.0 / a == 1.0 / b)
  | .bool a, .bool b => a == b
  | .char a, .char b => a == b
  | .bits a, .bits b => a == b
  | _, _ => false

/-- Modes whose values live in one cell and are copied by value. -/
def isScalarMode : Mode → Bool
  | .int _ | .real _ | .bool | .char | .bits _ => true
  | _ => false

/-- Drop `at` wrappers; they only set the position quoted in run time errors. -/
partial def stripAt : Core → Core
  | .at _ e => stripAt e
  | e => e

/-- The immediate `Core` children of a node, each with the number of frames that are
    pushed between the node and that child.  Used by the analyses that have to know
    what a `loadCell`/`refCell` depth is relative to; it follows `shift` exactly. -/
partial def fmtChildren : CoreFmt → List Core
  | .rep _ dyn item => dyn.toList ++ fmtChildren item
  | .general args => args
  | .include f => [f]
  | .group items => items.flatMap fmtChildren
  | _ => []

partial def childrenD : Core → List (Nat × Core)
  | .deref e | .deproc e | .rowOf e | .voiding e | .gen e | .at _ e
  | .widen _ _ e | .unite _ e | .monop _ _ e | .select _ e _ => [(0, e)]
  | .assign a b _ | .identRel a b _ | .andThen a b | .orElse a b | .seq a b
  | .dyop _ _ _ a b => [(0, a), (0, b)]
  | .call f args => (0, f) :: args.map ((0, ·))
  | .routine _ _ b => [(1, b)]
  | .slice a idx _ => (0, a) :: idx.flatMap (fun
      | .index e => [(0, e)]
      | .trim l u a => (l.toList ++ u.toList ++ a.toList).map ((0, ·)))
  | .newRow bs i _ => bs.flatMap (fun (l, u) => [(0, l), (0, u)]) ++ [(0, i)]
  | .block _ stmts _ _ => stmts.toList.flatMap (fun
      | .decl _ _ c => [(1, c)]
      | .unit c => [(1, c)]
      | _ => [])
  | .collateral es _ _ => es.map ((0, ·))
  | .cond c t e => [(0, c), (0, t), (0, e)]
  | .caseInt s alts o => (0, s) :: alts.map ((0, ·)) ++ [(0, o)]
  | .caseConf s alts o => (0, s) :: alts.map (fun (_, _, c) => (1, c)) ++ [(0, o)]
  | .loop _ f b t w body =>
    [(0, f), (0, b)] ++ t.toList.map ((0, ·)) ++ w.toList.map ((1, ·)) ++ [(1, body)]
  | .fmt items => items.flatMap (fun it => (fmtChildren it).map ((0, ·)))
  | _ => []

/-- Does `refCell d slot` — a *name* of the cell, through which it could be assigned —
    occur anywhere below, `d` counted relative to the frame this term sits in? -/
partial def refsSlot (slot : Nat) (d : Nat) (c : Core) : Bool :=
  match c with
  | .refCell d' s => d' == d && s == slot
  | _ => (childrenD c).any fun (k, ch) => refsSlot slot (d + k) ch

/-! ## Constant propagation

An identity declaration binds its value once; if that value is a scalar literal and
no `refCell` ever names the cell, every use of the cell in the rest of the block —
however deeply nested — denotes that literal. -/

mutual

/-- Replace `loadCell d slot` by `lit v`, `d` counted from the declaring block. -/
partial def substLit (slot : Nat) (v : Value) (d : Nat) : Core → Core
  | .loadCell d' s => if d' == d && s == slot then .lit v else .loadCell d' s
  | .block size stmts lb nl => .block size (stmts.map (substLitStmt slot v (d + 1))) lb nl
  | .routine np fs body => .routine np fs (substLit slot v (d + 1) body)
  | .loop sl f b t w body =>
    .loop sl (substLit slot v d f) (substLit slot v d b) (t.map (substLit slot v d))
          (w.map (substLit slot v (d + 1))) (substLit slot v (d + 1) body)
  | .caseConf sel alts out =>
    .caseConf (substLit slot v d sel) (alts.map fun (m, s, c) => (m, s, substLit slot v (d + 1) c))
              (substLit slot v d out)
  | .deref e => .deref (substLit slot v d e)
  | .deproc e => .deproc (substLit slot v d e)
  | .rowOf e => .rowOf (substLit slot v d e)
  | .voiding e => .voiding (substLit slot v d e)
  | .gen e => .gen (substLit slot v d e)
  | .at p e => .at p (substLit slot v d e)
  | .widen a b e => .widen a b (substLit slot v d e)
  | .unite m e => .unite m (substLit slot v d e)
  | .monop op m e => .monop op m (substLit slot v d e)
  | .select i e r => .select i (substLit slot v d e) r
  | .assign a b f => .assign (substLit slot v d a) (substLit slot v d b) f
  | .identRel a b i => .identRel (substLit slot v d a) (substLit slot v d b) i
  | .andThen a b => .andThen (substLit slot v d a) (substLit slot v d b)
  | .orElse a b => .orElse (substLit slot v d a) (substLit slot v d b)
  | .seq a b => .seq (substLit slot v d a) (substLit slot v d b)
  | .dyop op m1 m2 a b => .dyop op m1 m2 (substLit slot v d a) (substLit slot v d b)
  | .call f args => .call (substLit slot v d f) (args.map (substLit slot v d))
  | .slice a idx r => .slice (substLit slot v d a) (idx.map (substLitIdx slot v d)) r
  | .newRow bs i f =>
    .newRow (bs.map fun (l, u) => (substLit slot v d l, substLit slot v d u)) (substLit slot v d i) f
  | .collateral es st dm => .collateral (es.map (substLit slot v d)) st dm
  | .cond c t e => .cond (substLit slot v d c) (substLit slot v d t) (substLit slot v d e)
  | .caseInt s alts o =>
    .caseInt (substLit slot v d s) (alts.map (substLit slot v d)) (substLit slot v d o)
  | .fmt items => .fmt (items.map (substLitFmt slot v d))
  | other => other

partial def substLitFmt (slot : Nat) (v : Value) (d : Nat) : CoreFmt → CoreFmt
  | .rep n dyn item => .rep n (dyn.map (substLit slot v d)) (substLitFmt slot v d item)
  | .general args => .general (args.map (substLit slot v d))
  | .include f => .include (substLit slot v d f)
  | .group items => .group (items.map (substLitFmt slot v d))
  | it => it

partial def substLitStmt (slot : Nat) (v : Value) (d : Nat) : CoreStmt → CoreStmt
  | .decl s m init => .decl s m (substLit slot v d init)
  | .unit e => .unit (substLit slot v d e)
  | st => st

partial def substLitIdx (slot : Nat) (v : Value) (d : Nat) : CoreIdx → CoreIdx
  | .index e => .index (substLit slot v d e)
  | .trim l u a => .trim (l.map (substLit slot v d)) (u.map (substLit slot v d)) (a.map (substLit slot v d))

end

/-- Propagate the scalar literals bound by the identity declarations of one block.

    The pass is refused when the block has labels: a jump could then reach a use
    without the declaration having run, where the original program reports an
    uninitialised value. -/
def constPropBlock (stmts : Array CoreStmt) (nl : Nat) : Array CoreStmt :=
  if nl != 0 then stmts else Id.run do
    let mut out := stmts
    for i in [0:out.size] do
      match out[i]! with
      | .decl slot _ init =>
        match stripAt init with
        | .lit v =>
          -- one declaration of the slot, and no name of the cell anywhere in the block
          let declared := out.foldl (fun n st => match st with
            | .decl s _ _ => if s == slot then n + 1 else n
            | _ => n) 0
          let named := out.any fun
            | .decl _ _ c => refsSlot slot 0 c
            | .unit c => refsSlot slot 0 c
            | _ => false
          if isScalarValue v && declared == 1 && !named then
            for j in [i + 1:out.size] do
              out := out.set! j (substLitStmt slot v 0 out[j]!)
        | _ => pure ()
      | _ => pure ()
    return out

/-! ## Algebraic simplification -/

/-- Is this float the literal `+0.0` (and not `-0.0`)? -/
def isPosZero (x : Float) : Bool := x == 0.0 && 1.0 / x > 0.0

/-- The identities of Algol 68 Genie's arithmetic that keep *both* the value and the
    mode, and that drop only an operand which is a literal — the operand that is kept
    was going to be evaluated anyway, so nothing that could fail or have an effect is
    lost.  `x * 0`, `x - x` and `(a + b) - b` are deliberately absent: `INT` is 32-bit
    checked, so they do not hold, and dropping `x` would drop its evaluation. -/
def algebraic (op : String) (m1 m2 : Mode) (l r : Core) : Option Core :=
  match m1, m2 with
  | .int _, .int _ =>
    match op, stripAt r with
    -- `INT ** INT` keeps the length of the base, so `m1` and `m2` differ for LONG
    | "**", .lit (.int 1) => some l
    | _, _ =>
      if m1 != m2 then none else
      match op, stripAt l, stripAt r with
      | "+", _, .lit (.int 0) => some l
      | "+", .lit (.int 0), _ => some r
      | "-", _, .lit (.int 0) => some l
      | "*", _, .lit (.int 1) => some l
      | "*", .lit (.int 1), _ => some r
      | "%", _, .lit (.int 1) => some l          -- OVER; `MOD 1` is 0, not `x`
      | _, _, _ => none
  | .real _, .int _ =>
    match op, stripAt r with
    | "**", .lit (.int 1) => some l              -- a68g's square-and-multiply returns x
    | _, _ => none
  | .real _, .real _ =>
    if m1 != m2 then none else
    match op, stripAt l, stripAt r with
    -- `x + 0.0` is *not* here: it turns `-0.0` into `+0.0`
    | "-", _, .lit (.real y) => if isPosZero y then some l else none
    | "*", _, .lit (.real y) => if y == 1.0 then some l else none
    | "*", .lit (.real y), _ => if y == 1.0 then some r else none
    | "/", _, .lit (.real y) => if y == 1.0 then some l else none
    | _, _, _ => none
  | _, _ => none

/-! ## Common subexpression elimination inside one block

The IR has no temporaries, so one is made by extending the block's frame with a fresh
slot.  Growing a frame is invisible to everything else (a frame is an array of cells
allocated on entry); changing frame *nesting* is not, and is not done here.

Only expressions built from literals, `loadCell`, `deref (refCell …)`, widening and the
standard arithmetic and comparison operators are shared.  Such an expression reads
cells and nothing else: it cannot assign, allocate, call or print.  It may still
*fail* (overflow, an uninitialised value), which is why the first occurrence is never
moved across anything that could itself fail or be observed. -/

/-- Dyadic operators of the standard prelude that only read their operands. -/
def pureDyop (op : String) : Bool :=
  op == "+" || op == "-" || op == "*" || op == "/" || op == "%" || op == "%*" ||
  op == "**" || op == "=" || op == "/=" || op == "<" || op == "<=" || op == ">" || op == ">="

/-- Monadic operators of the standard prelude that only read their operand. -/
def pureMonop (op : String) : Bool :=
  op == "-" || op == "+" || op == "ABS" || op == "SIGN" || op == "ODD" || op == "NOT" ||
  op == "BIN" || op == "REPR" || op == "ROUND" || op == "ENTIER" ||
  op == "SHORTEN" || op == "LENG"

/-- The expressions that may be shared. -/
partial def shareable : Core → Bool
  | .lit v => isScalarValue v
  | .loadCell _ _ => true
  | .deref (.refCell _ _) => true
  | .widen s d e => isScalarMode s && isScalarMode d && shareable e
  | .monop op m e => pureMonop op && isScalarMode m && shareable e
  | .dyop op m1 m2 a b =>
    pureDyop op && isScalarMode m1 && isScalarMode m2 && shareable a && shareable b
  | _ => false

/-- Structural equality on shareable expressions. -/
partial def shareEq : Core → Core → Bool
  | .lit a, .lit b => scalarEq a b
  | .loadCell d1 s1, .loadCell d2 s2 => d1 == d2 && s1 == s2
  | .refCell d1 s1, .refCell d2 s2 => d1 == d2 && s1 == s2
  | .deref a, .deref b => shareEq a b
  | .widen s1 d1 a, .widen s2 d2 b => s1 == s2 && d1 == d2 && shareEq a b
  | .monop o1 m1 a, .monop o2 m2 b => o1 == o2 && m1 == m2 && shareEq a b
  | .dyop o1 a1 b1 l1 r1, .dyop o2 a2 b2 l2 r2 =>
    o1 == o2 && a1 == a2 && b1 == b2 && shareEq l1 l2 && shareEq r1 r2
  | _, _ => false

/-- Does a shareable expression read the cell `(d, s)`? -/
partial def readsCell (d s : Nat) : Core → Bool
  | .loadCell d' s' => d' == d && s' == s
  | .deref e => readsCell d s e
  | .refCell d' s' => d' == d && s' == s
  | .widen _ _ e => readsCell d s e
  | .monop _ _ e => readsCell d s e
  | .dyop _ _ _ a b => readsCell d s a || readsCell d s b
  | .at _ e => readsCell d s e
  | _ => false

/-- State threaded through the rewrite, which walks the block in evaluation order. -/
structure CseSt where
  count   : Nat := 0            -- occurrences replaced
  defined : Bool := false       -- the temporary already holds the value
  live    : Bool := true        -- nothing has invalidated it since
  total   : Bool := true        -- everything evaluated so far in this statement is total
  hoist   : Bool := false       -- the definition may be lifted before its statement
  cur     : Option Pos := none  -- innermost `at` position
  defAt   : Option Pos := none  -- the `at` position where the definition goes
  deriving Inhabited

namespace CseSt
/-- Anything that could assign, allocate, call or print invalidates the temporary. -/
def killAll (st : CseSt) : CseSt := if st.defined then { st with live := false } else st
def killCell (e : Core) (d s : Nat) (st : CseSt) : CseSt :=
  if st.defined && readsCell d s e then { st with live := false } else st
/-- Record that something which might fail has now been evaluated. -/
def used (st : CseSt) : CseSt := { st with total := false }
end CseSt

mutual

/-- Rewrite one term, replacing the occurrences of `e0` that a single temporary in slot
    `t` can serve.  The walk visits sub-terms in the order the evaluator does, and stops
    descending at anything conditional (a branch is not always evaluated) or opaque. -/
partial def cseGo (e0 : Core) (t : Nat) (c : Core) (st : CseSt) : Core × CseSt :=
  if st.live && shareEq c e0 then
    let first := !st.defined
    let hoist := if first then st.total else st.hoist
    let defAt := if first then st.cur else st.defAt
    let st' : CseSt :=
      { count := st.count + 1, defined := true, live := st.live, total := false,
        hoist := hoist, cur := st.cur, defAt := defAt }
    if !first || st.total then (.loadCell 0 t, st')
    -- the definition cannot be lifted out of the statement, so it is made where it
    -- stands: store into the temporary and read it straight back
    else (.deref (.assign (.refCell 0 t) c false), st')
  else match c with
  | .lit _ | .refCell _ _ | .routine _ _ _ | .skip _ => (c, st)
  | .loadCell _ _ => (c, st.used)
  | .at p a =>
    let (a', st') := cseGo e0 t a { st with cur := some p }
    (.at p a', { st' with cur := st.cur })
  | .deref a => let (a', st) := cseGo e0 t a st; (.deref a', st.used)
  | .widen s d a => let (a', st) := cseGo e0 t a st; (.widen s d a', st.used)
  | .unite m a => let (a', st) := cseGo e0 t a st; (.unite m a', st.used)
  | .rowOf a => let (a', st) := cseGo e0 t a st; (.rowOf a', st.used)
  | .voiding a => let (a', st) := cseGo e0 t a st; (.voiding a', st.used)
  | .gen a => let (a', st) := cseGo e0 t a st; (.gen a', st.used)   -- a fresh cell: no kill
  | .select i a r => let (a', st) := cseGo e0 t a st; (.select i a' r, st.used)
  | .deproc a => let (a', st) := cseGo e0 t a st; (.deproc a', st.used.killAll)
  | .monop op m a =>
    let (a', st) := cseGo e0 t a st
    let st := if pureMonop op && isScalarMode m then st.used else st.used.killAll
    (.monop op m a', st)
  | .dyop op m1 m2 a b =>
    let (a', st) := cseGo e0 t a st
    let (b', st) := cseGo e0 t b st
    let st := if pureDyop op && isScalarMode m1 && isScalarMode m2 then st.used
              else st.used.killAll
    (.dyop op m1 m2 a' b', st)
  | .identRel a b i =>
    let (a', st) := cseGo e0 t a st
    let (b', st) := cseGo e0 t b st
    (.identRel a' b' i, st.used)
  | .seq a b =>
    let (a', st) := cseGo e0 t a st
    let (b', st) := cseGo e0 t b st
    (.seq a' b', st)
  | .assign d s f =>
    let (d', st) := cseGo e0 t d st
    let (s', st) := cseGo e0 t s st
    let st := match stripAt d with
      | .refCell dd ss => (st.used.killCell e0 dd ss)
      | _ => st.used.killAll
    (.assign d' s' f, st)
  | .call f args =>
    let (f', st) := cseGo e0 t f st
    let (args', st) := cseGoList e0 t args st
    (.call f' args', st.used.killAll)
  | .slice a idx r =>
    let (a', st) := cseGo e0 t a st
    let (idx', st) := idx.foldl (fun (acc, st) i =>
      match i with
      | .index e => let (e', st) := cseGo e0 t e st; (acc ++ [CoreIdx.index e'], st)
      | .trim lo hi at_ =>
        let (lo', st) := cseGoOpt e0 t lo st
        let (hi', st) := cseGoOpt e0 t hi st
        let (at', st) := cseGoOpt e0 t at_ st
        (acc ++ [CoreIdx.trim lo' hi' at'], st)) ([], st)
    (.slice a' idx' r, st.used)
  | .newRow bs i f =>
    let (bs', st) := bs.foldl (fun (acc, st) (l, u) =>
      let (l', st) := cseGo e0 t l st
      let (u', st) := cseGo e0 t u st
      (acc ++ [(l', u')], st)) ([], st)
    let (i', st) := cseGo e0 t i st
    (.newRow bs' i' f, st.used)
  | .collateral es sr dm =>
    let (es', st) := cseGoList e0 t es st
    (.collateral es' sr dm, st.used)
  -- the enquiry of a conditional is evaluated, the branches are not always: stop here
  | .cond c' th el =>
    let (c'', st) := cseGo e0 t c' st
    (.cond c'' th el, st.used.killAll)
  | .andThen a b => let (a', st) := cseGo e0 t a st; (.andThen a' b, st.used.killAll)
  | .orElse a b => let (a', st) := cseGo e0 t a st; (.orElse a' b, st.used.killAll)
  | .caseInt s alts o =>
    let (s', st) := cseGo e0 t s st
    (.caseInt s' alts o, st.used.killAll)
  | .caseConf s alts o =>
    let (s', st) := cseGo e0 t s st
    (.caseConf s' alts o, st.used.killAll)
  -- the loop bounds are evaluated in this frame; the body is not (and runs many times)
  | .loop sl f b to_ w body =>
    let (f', st) := cseGo e0 t f st
    let (b', st) := cseGo e0 t b st
    let (to', st) := cseGoOpt e0 t to_ st
    (.loop sl f' b' to' w body, st.used.killAll)
  | other => (other, st.used.killAll)

partial def cseGoList (e0 : Core) (t : Nat) (cs : List Core) (st : CseSt) : List Core × CseSt :=
  cs.foldl (fun (acc, st) c => let (c', st) := cseGo e0 t c st; (acc ++ [c'], st)) ([], st)

partial def cseGoOpt (e0 : Core) (t : Nat) (c : Option Core) (st : CseSt) : Option Core × CseSt :=
  match c with
  | none => (none, st)
  | some c => let (c', st) := cseGo e0 t c st; (some c', st)

end

/-- Rewrite one statement; the "everything so far is total" flag restarts at each one. -/
def cseStmt (e0 : Core) (t : Nat) (s : CoreStmt) (st : CseSt) : CoreStmt × CseSt :=
  let st := { st with total := true, cur := none }
  match s with
  | .decl slot m init => let (i', st) := cseGo e0 t init st; (.decl slot m i', st)
  | .unit e => let (e', st) := cseGo e0 t e st; (.unit e', st)
  | .label _ => (s, { st with total := false })
  | .exit => (s, st.killAll)

/-- The total number of core nodes of a statement array. -/
def stmtsSize (stmts : Array CoreStmt) : Nat :=
  stmts.foldl (fun n st => n + match st with
    | .decl _ _ c => size c
    | .unit c => size c
    | _ => 0) 0

/-- Share one expression across a block, if that makes the block smaller.
    Returns the new frame size and statements. -/
def cseTry (fsize : Nat) (stmts : Array CoreStmt) (e0 : Core) : Option (Nat × Array CoreStmt) :=
  Id.run do
    let t := fsize
    let mut st : CseSt := {}
    let mut out : Array CoreStmt := #[]
    let mut hoistAt : Option (Nat × Option Pos) := none
    for i in [0:stmts.size] do
      let before := st.defined
      let (s', st') := cseStmt e0 t stmts[i]! st
      if !before && st'.defined && st'.hoist then hoistAt := some (out.size, st'.defAt)
      out := out.push s'
      st := st'
    if st.count < 2 then return none
    let n := st.count
    let sz := size e0
    match hoistAt with
    | some (k, p) =>
      -- the definition becomes a declaration in front of its statement
      let init := match p with | some p => Core.at p e0 | none => e0
      if n * sz < size init + n then return none
      let mut res : Array CoreStmt := #[]
      for j in [0:out.size] do
        -- `.void` keeps the temporary in a run-time cell: the code generator promotes a
        -- slot to a C variable only when it knows the slot's mode, and a shared
        -- subexpression's mode is not recorded here
        if j == k then res := res.push (.decl t .void init)
        res := res.push out[j]!
      return some (fsize + 1, res)
    | none =>
      -- the definition stays where it stands, as `deref (refCell := e)`
      if n * sz ≤ sz + 3 + (n - 1) then return none
      return some (fsize + 1, out)

/-- Every shareable sub-expression worth a temporary. -/
partial def collectShareable (c : Core) (acc : Array Core) : Array Core :=
  let acc := if size c ≥ 3 && shareable c then acc.push c else acc
  (childrenD c).foldl (fun a (_, ch) => collectShareable ch a) acc

/-- Eliminate common subexpressions in one block.  Refused when the block has labels:
    a jump backwards could then reach a use of the temporary without its definition. -/
partial def cseBlock (fuel : Nat) (fsize : Nat) (stmts : Array CoreStmt) (nl : Nat) :
    Nat × Array CoreStmt :=
  if nl != 0 || fuel == 0 then (fsize, stmts) else Id.run do
    let mut cands : Array Core := #[]
    for s in stmts do
      match s with
      | .decl _ _ c | .unit c => cands := collectShareable c cands
      | _ => pure ()
    -- one temporary per candidate expression; keep the one that shrinks the block most
    let mut seen : Array Core := #[]
    let mut best : Option (Nat × Nat × Array CoreStmt) := none
    for c in cands do
      if seen.size < 96 && !(seen.any (shareEq c)) then
        seen := seen.push c
        match cseTry fsize stmts c with
        | some (sz, ss) =>
          let n := stmtsSize ss
          match best with
          | some (_, bn, _) => if n < bn then best := some (sz, n, ss)
          | none => best := some (sz, n, ss)
        | none => pure ()
    match best with
    | none => return (fsize, stmts)
    | some (sz, _, ss) => return cseBlock (fuel - 1) sz ss nl

/-- Which of the `-O2` passes are enabled.  The individual flags exist so that the
    effect of one pass can be measured on its own (`A68LEAN_DISABLE=cse`, …). -/
structure Cfg where
  algebra   : Bool := false
  constProp : Bool := false
  cse       : Bool := false
  deriving Inhabited


mutual

/-- Constant folding and the structural simplifications. -/
partial def opt (rt : Interp.Rt) (cfg : Cfg) (c : Core) : IO Core := do
  match c with
  | .dyop op m1 m2 a b =>
    let a ← opt rt cfg a
    let b ← opt rt cfg b
    let node := Core.dyop op m1 m2 a b
    if isLit a && isLit b then
      match (← evalConst rt node) with
      | some v => return .lit v
      | none => return node
    else if cfg.algebra then
      match algebraic op m1 m2 a b with
      | some e => return e
      | none => return node
    else return node
  | .monop op m e =>
    let e ← opt rt cfg e
    let node := Core.monop op m e
    if isLit e then
      match (← evalConst rt node) with
      | some v => return .lit v
      | none => return node
    else return node
  | .widen s d e =>
    let e ← opt rt cfg e
    if s == d then return e
    let node := Core.widen s d e
    if isLit e then
      match (← evalConst rt node) with
      | some v => return .lit v
      | none => return node
    else return node
  -- coercions that reduce to a cheaper node
  | .deref e =>
    match (← opt rt cfg e) with
    | .refCell d s => return .loadCell d s
    | e' => return .deref e'
  -- constant conditions
  | .cond c t e =>
    let c ← opt rt cfg c
    match c with
    | .lit (.bool true) => opt rt cfg t
    | .lit (.bool false) => opt rt cfg e
    | _ => return .cond c (← opt rt cfg t) (← opt rt cfg e)
  | .andThen a b =>
    match (← opt rt cfg a) with
    | .lit (.bool false) => return .lit (.bool false)
    | .lit (.bool true) => opt rt cfg b
    | a' => return .andThen a' (← opt rt cfg b)
  | .orElse a b =>
    match (← opt rt cfg a) with
    | .lit (.bool true) => return .lit (.bool true)
    | .lit (.bool false) => opt rt cfg b
    | a' => return .orElse a' (← opt rt cfg b)
  | .caseInt sel alts out =>
    let sel ← opt rt cfg sel
    let alts ← alts.mapM (opt rt cfg)
    let out ← opt rt cfg out
    match sel with
    | .lit (.int i) =>
      if i ≥ 1 && i ≤ alts.length then return alts[(i - 1).toNat]! else return out
    | _ => return .caseInt sel alts out
  -- a block that needs no frame, declares nothing and has no labels needs no frame
  | .block size stmts lb nl =>
    let stmts ← stmts.mapM (optStmt rt cfg)
    match flattenBlock size stmts nl with
    | some c => return c
    | none =>
      let stmts := if cfg.constProp then constPropBlock stmts nl else stmts
      let (size, stmts) := if cfg.cse then cseBlock 4 size stmts nl else (size, stmts)
      return .block size stmts lb nl
  -- congruence cases
  | .deproc e => return .deproc (← opt rt cfg e)
  | .rowOf e => return .rowOf (← opt rt cfg e)
  | .unite m e => return .unite m (← opt rt cfg e)
  | .voiding e => return .voiding (← opt rt cfg e)
  | .gen e => return .gen (← opt rt cfg e)
  | .at p e => return .at p (← opt rt cfg e)
  | .assign d s f => return .assign (← opt rt cfg d) (← opt rt cfg s) f
  | .identRel a b i => return .identRel (← opt rt cfg a) (← opt rt cfg b) i
  | .seq a b => return .seq (← opt rt cfg a) (← opt rt cfg b)
  | .call f args => return .call (← opt rt cfg f) (← args.mapM (opt rt cfg))
  | .routine np fs body => return .routine np fs (← opt rt cfg body)
  | .select i e r => return .select i (← opt rt cfg e) r
  | .slice a idx r => return .slice (← opt rt cfg a) (← idx.mapM (optIdx rt cfg)) r
  | .newRow bs i f =>
    let bs ← bs.mapM fun (l, u) => do return (← opt rt cfg l, ← opt rt cfg u)
    return .newRow bs (← opt rt cfg i) f
  | .collateral es st d => return .collateral (← es.mapM (opt rt cfg)) st d
  | .caseConf sel alts out =>
    let alts ← alts.mapM fun (m, s, c) => do return (m, s, ← opt rt cfg c)
    return .caseConf (← opt rt cfg sel) alts (← opt rt cfg out)
  | .loop slot f b t w body =>
    return .loop slot (← opt rt cfg f) (← opt rt cfg b) (← t.mapM (opt rt cfg)) (← w.mapM (opt rt cfg)) (← opt rt cfg body)
  | other => return other

partial def optStmt (rt : Interp.Rt) (cfg : Cfg) : CoreStmt → IO CoreStmt
  | .decl slot m init => return .decl slot m (← opt rt cfg init)
  | .unit e => return .unit (← opt rt cfg e)
  | st => return st

partial def optIdx (rt : Interp.Rt) (cfg : Cfg) : CoreIdx → IO CoreIdx
  | .index e => return .index (← opt rt cfg e)
  | .trim l u a => return .trim (← l.mapM (opt rt cfg)) (← u.mapM (opt rt cfg)) (← a.mapM (opt rt cfg))

end

/-- Run the optimiser (`level = 0` leaves the program alone). -/
def run (core : Core) (level : Nat) : IO Core := do
  if level == 0 then return core
  let rt ← scratchRt
  let off := ((← IO.getEnv "A68LEAN_DISABLE").getD "").splitOn ","
  let on (name : String) : Bool := level ≥ 2 && !off.contains name
  let cfg : Cfg := { algebra := on "algebra", constProp := on "constprop", cse := on "cse" }
  let mut c := core
  -- the passes are idempotent after two rounds on every program in the corpus;
  -- at -O2 a third round lets constant folding consume what propagation exposed
  for _ in [0:if level ≥ 2 then 3 else 1] do
    c ← opt rt cfg c
  return c

end A68.Opt
