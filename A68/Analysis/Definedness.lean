import A68.Lower.State

/-!
# A68.Analysis.Definedness

Analysis: definedness of promoted rows.  A loop nest running over exactly a row's
declared bounds and assigning every element leaves the row known defined (per field),
so reads after it need no undefined-element test.  See docs/OPTIMIZATIONS.md §5.
-/
namespace A68.Lower
open A68.MIR

/-- Mark field `f` (every field when `none`) of promoted row `s` of the innermost frame as
    known defined, or not. -/
def setKnown (s : Nat) (f : Option Nat) (val : Bool) : L Unit :=
  modify fun st => match st.fb.frames with
    | fr :: rest =>
      match (fr.rows[s]?).join with
      | some pr =>
        let known := if pr.known.isEmpty then Array.replicate pr.fields.size false else pr.known
        let known := match f with
          | some k => known.set! k val
          | none => known.map fun _ => val
        { st with fb := { st.fb with frames := { fr with rows := fr.rows.set! s (some { pr with known := known }) } :: rest } }
      | none => st
    | [] => st

/-- Are two bounds the same expression, evaluated at the same level: the same literal, or
    the same cell? -/
def sameBound (a b : Core) : Bool :=
  match CodeGen.strip a, CodeGen.strip b with
  | .lit (.int x), .lit (.int y) => x == y
  | .loadCell d1 s1, .loadCell d2 s2 => d1 == d2 && s1 == s2
  | _, _ => false

/-- The elements a loop nest writes for every index of a row declared in the innermost
    frame with bounds `decl`: the loop nest must run over exactly those bounds by 1, its
    body must be assignments (in a sequence, possibly in a block without declarations or
    labels) to `a[i]`, `a[i, j]` or `f OF a[i]`, indexed by the counters, of defined
    values.  Returns the row slots and the field (none for the whole element) so written. -/
partial def initTargets (decl : Nat → Option (List (Core × Core))) (e : Core) : List (Nat × Option Nat) :=
  go e [] 0
where
  -- `bounds` collected so far (outermost first); `extra`: block levels between the loops
  go (e : Core) (bounds : List (Core × Core)) (extra : Nat) : List (Nat × Option Nat) :=
    match e with
    | .at _ e' | .voiding e' => go e' bounds extra
    | .loop (some _) f (.lit (.int 1)) (some t) none body =>
      if bounds.length ≥ 2 then [] else go body (bounds ++ [(f, t)]) 0
    | .loop _ _ _ _ _ _ => []
    | _ =>
      if bounds.isEmpty then [] else
      let dims := bounds.length
      stmtsOf e extra |>.filterMap fun st => target st dims bounds
  -- the units of a body: a sequence, or a block without declarations or labels
  stmtsOf (e : Core) (extra : Nat) : List (Core × Nat) :=
    match e with
    | .at _ e' | .voiding e' => stmtsOf e' extra
    | .seq a b => stmtsOf a extra ++ stmtsOf b extra
    | .block _ stmts _ _ =>
      if stmts.any (fun st => match st with | .unit _ => false | _ => true) then []
      else stmts.toList.flatMap fun st => match st with
        | .unit u => stmtsOf u (extra + 1)
        | _ => []
    | e' => [(e', extra)]
  target (st : Core × Nat) (dims : Nat) (bounds : List (Core × Core)) : Option (Nat × Option Nat) :=
    let (e, extra) := st
    match CodeGen.strip e with
    | .assign dst src _ =>
      if (match CodeGen.strip src with | .lit .undef => true | _ => false) then none else
      match CodeGen.strip dst with
      | .slice base idx true => elem base idx dims extra none bounds
      | .select f (.slice base idx true) true => elem base idx dims extra (some f) bounds
      | _ => none
    | _ => none
  elem (base : Core) (idx : List CoreIdx) (dims extra : Nat) (f : Option Nat) (bounds : List (Core × Core)) : Option (Nat × Option Nat) :=
    match CodeGen.strip base with
    | .refCell dd s =>
      if dd != extra + dims || idx.length != dims then none else
      let ok := (List.range dims).all fun k => match idx[k]! with
        | .index ie => (match CodeGen.strip ie with | .loadCell d 0 => d == extra + dims - 1 - k | _ => false)
        | _ => false
      if !ok then none else
      -- the loop bounds must be the declared ones
      match decl s with
      | some bs =>
        if bs.length == dims && (List.range dims).all (fun k =>
              sameBound (bs[k]!).1 (bounds[k]!).1 && sameBound (bs[k]!).2 (bounds[k]!).2)
        then some (s, f) else none
      | none => none
    | _ => none

end A68.Lower
