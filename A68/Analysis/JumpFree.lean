import A68.Lower.State

/-!
# A68.Analysis.JumpFree

Analysis: which of a block's routines cannot complete a jump to a label outside
themselves (a fixpoint over the calls they make).  A call of such a routine needs no
check of the jump flag afterwards.  See docs/OPTIMIZATIONS.md §3.
-/
namespace A68.Lower
open A68.MIR

/-- Can the routine `body` complete a jump to a label outside itself?  Not when every jump
    in it goes to one of its own labels and every call is of a builtin or of a sibling
    routine in `known` (its declaring frame is `depth` frames out); anything else — a
    format, a deprocedure, a call through a value — may. -/
partial def mayJumpOut (labels : List Nat) (known : Nat → Bool) (depth : Nat) (c : Core) : Bool :=
  match c with
  | .goto l => !labels.contains l
  | .fmt _ | .deproc _ => true
  | .call f args =>
    let calleeOk := match CodeGen.strip f with
      | .lit (.builtin _) => true
      | .loadCell d s => d == depth && known s
      | _ => false
    !calleeOk || args.any (mayJumpOut labels known depth)
  | .routine _ _ _ => false   -- a routine text does nothing until called
  | _ => (CodeGen.childrenD c).any fun (k, ch) => mayJumpOut labels known (depth + k) ch

/-- Which of a block's routines (slot, body) cannot jump out: the greatest set closed under
    the calls its members make. -/
partial def jumpFreeSet (rs : List (Nat × Core)) : List Nat := Id.run do
  let mut known := rs.map (·.1)
  let mut changed := true
  while changed do
    changed := false
    for (sl, body) in rs do
      if known.contains sl && mayJumpOut (CodeGen.labelsOf body) (known.contains ·) 1 body then
        known := known.filter (· != sl)
        changed := true
  return known

end A68.Lower
