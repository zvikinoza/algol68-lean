import A68.Core
import A68.Interp

/-!
# A68.Opt — optimisation passes over the core representation

The passes mirror those of Algol 68 Genie's optimiser (`plugin-folder.c`,
`plugin-inline.c`): fold constant units, remove coercions that do nothing,
short-circuit constant conditions, and flatten blocks that need no frame.

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
  | other => other

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

mutual

/-- Constant folding and the structural simplifications. -/
partial def opt (rt : Interp.Rt) (c : Core) : IO Core := do
  match c with
  | .dyop op m1 m2 a b =>
    let a ← opt rt a
    let b ← opt rt b
    let node := Core.dyop op m1 m2 a b
    if isLit a && isLit b then
      match (← evalConst rt node) with
      | some v => return .lit v
      | none => return node
    else return node
  | .monop op m e =>
    let e ← opt rt e
    let node := Core.monop op m e
    if isLit e then
      match (← evalConst rt node) with
      | some v => return .lit v
      | none => return node
    else return node
  | .widen s d e =>
    let e ← opt rt e
    if s == d then return e
    let node := Core.widen s d e
    if isLit e then
      match (← evalConst rt node) with
      | some v => return .lit v
      | none => return node
    else return node
  -- coercions that reduce to a cheaper node
  | .deref e =>
    match (← opt rt e) with
    | .refCell d s => return .loadCell d s
    | e' => return .deref e'
  -- constant conditions
  | .cond c t e =>
    let c ← opt rt c
    match c with
    | .lit (.bool true) => opt rt t
    | .lit (.bool false) => opt rt e
    | _ => return .cond c (← opt rt t) (← opt rt e)
  | .andThen a b =>
    match (← opt rt a) with
    | .lit (.bool false) => return .lit (.bool false)
    | .lit (.bool true) => opt rt b
    | a' => return .andThen a' (← opt rt b)
  | .orElse a b =>
    match (← opt rt a) with
    | .lit (.bool true) => return .lit (.bool true)
    | .lit (.bool false) => opt rt b
    | a' => return .orElse a' (← opt rt b)
  | .caseInt sel alts out =>
    let sel ← opt rt sel
    let alts ← alts.mapM (opt rt)
    let out ← opt rt out
    match sel with
    | .lit (.int i) =>
      if i ≥ 1 && i ≤ alts.length then return alts[(i - 1).toNat]! else return out
    | _ => return .caseInt sel alts out
  -- a block that needs no frame, declares nothing and has no labels needs no frame
  | .block size stmts lb nl =>
    let stmts ← stmts.mapM (optStmt rt)
    match flattenBlock size stmts nl with
    | some c => return c
    | none => return .block size stmts lb nl
  -- congruence cases
  | .deproc e => return .deproc (← opt rt e)
  | .rowOf e => return .rowOf (← opt rt e)
  | .unite m e => return .unite m (← opt rt e)
  | .voiding e => return .voiding (← opt rt e)
  | .gen e => return .gen (← opt rt e)
  | .at p e => return .at p (← opt rt e)
  | .assign d s f => return .assign (← opt rt d) (← opt rt s) f
  | .identRel a b i => return .identRel (← opt rt a) (← opt rt b) i
  | .seq a b => return .seq (← opt rt a) (← opt rt b)
  | .call f args => return .call (← opt rt f) (← args.mapM (opt rt))
  | .routine np fs body => return .routine np fs (← opt rt body)
  | .select i e r => return .select i (← opt rt e) r
  | .slice a idx r => return .slice (← opt rt a) (← idx.mapM (optIdx rt)) r
  | .newRow bs i f =>
    let bs ← bs.mapM fun (l, u) => do return (← opt rt l, ← opt rt u)
    return .newRow bs (← opt rt i) f
  | .collateral es st d => return .collateral (← es.mapM (opt rt)) st d
  | .caseConf sel alts out =>
    let alts ← alts.mapM fun (m, s, c) => do return (m, s, ← opt rt c)
    return .caseConf (← opt rt sel) alts (← opt rt out)
  | .loop slot f b t w body =>
    return .loop slot (← opt rt f) (← opt rt b) (← t.mapM (opt rt)) (← w.mapM (opt rt)) (← opt rt body)
  | other => return other

partial def optStmt (rt : Interp.Rt) : CoreStmt → IO CoreStmt
  | .decl slot m init => return .decl slot m (← opt rt init)
  | .unit e => return .unit (← opt rt e)
  | st => return st

partial def optIdx (rt : Interp.Rt) : CoreIdx → IO CoreIdx
  | .index e => return .index (← opt rt e)
  | .trim l u a => return .trim (← l.mapM (opt rt)) (← u.mapM (opt rt)) (← a.mapM (opt rt))

end

/-- Run the optimiser (`level = 0` leaves the program alone). -/
def run (core : Core) (level : Nat) : IO Core := do
  if level == 0 then return core
  let rt ← scratchRt
  let mut c := core
  -- the passes are idempotent after two rounds on every program in the corpus
  for _ in [0:if level ≥ 2 then 2 else 1] do
    c ← opt rt c
  return c

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

end A68.Opt
