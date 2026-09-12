import A68.Lower.State

/-!
# A68.Analysis.Interval

Analysis: the interval of an INT expression — a literal, a loop counter with literal
bounds, and sums, differences and products by constants of such — from which a
subscript check the loop cannot violate is omitted.  See docs/OPTIMIZATIONS.md §5.
-/
namespace A68.Lower
open A68.MIR

/-- The interval of an INT expression, when it is known: a literal, a loop counter with
    literal bounds, and sums, differences and products by constants of such. -/
partial def intervalOf (c : Core) : L (Option (Int × Int)) := do
  match c with
  | .at _ e => intervalOf e
  | .lit (.int n) => return some (n, n)
  | .loadCell d s =>
    match ← pvarOf d s with
    | some pv => return pv.range
    | none => return none
  | .dyop op m1 m2 l r =>
    if (← resolve m1) != .int 0 || (← resolve m2) != .int 0 then return none
    match op, ← intervalOf l, ← intervalOf r with
    | "+", some (a, b), some (c', d) => return some (a + c', b + d)
    | "-", some (a, b), some (c', d) => return some (a - d, b - c')
    | "*", some (a, b), some (c', d) =>
      let ps := [a * c', a * d, b * c', b * d]
      return some (ps.foldl min (a * c'), ps.foldl max (a * c'))
    | _, _, _ => return none
  | _ => return none

end A68.Lower
