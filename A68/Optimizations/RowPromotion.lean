import A68.Optimizations.DeferredTraps

/-!
# A68.Optimizations.RowPromotion

Optimisation: row promotion.  A row variable that never escapes (the C back end's
escape analysis, `CodeGen.planFrame`, decides) is native arrays with its bounds in
registers; its element accesses are a bounds test and direct loads and stores, the
test itself omitted when the interval analysis (`A68.Analysis.Interval`) or the
definedness analysis (`A68.Analysis.Definedness`) has discharged it.  The arrays are
allocated and freed in `A68.Lower.lowerBlock`.  See docs/OPTIMIZATIONS.md §4–5.
-/
namespace A68.Lower
open A68.MIR

def prowOf (d s : Nat) : L (Option PRow) := do
  match (← get).fb.frames[d]? with
  | some f => return (f.rows[s]?).join
  | none => return none

/-- The element offset of `a[i]` or `a[i, j]` in a promoted row, with the evaluator's
    subscript checks (`CodeGen: a68_ao`). -/
def prowIndex (pr : PRow) (is : Array Opnd) (ranges : Array (Option (Int × Int)) := #[]) : L Var := do
  let deferring := (← get).defer.isSome
  let mut idx : Option Var := none
  let mut allIn : Option Var := none
  for k in [0:pr.dims] do
    let i := is[k]!
    let l := pr.lo[k]!; let u := pr.hi[k]!
    -- a subscript whose interval lies within the declared literal bounds needs no check
    let inRange : Bool := match (ranges[k]?).join, pr.litBounds with
      | some (a, b), some bs => match bs[k]? with
        | some (lo, hi) => lo ≤ a && b ≤ hi
        | none => false
      | _, _ => false
    if inRange then
      let t ← binv .i64 .subW i (.v l)
      idx ← match idx with
        | none => pure (some t)
        | some prev =>
          let m ← binv .i64 .mulW (.v prev) (.v pr.ext1)
          pure (some (← binv .i64 .addW (.v m) (.v t)))
      continue
    let ge ← binv .i1 .ge i (.v l)
    let le ← binv .i1 .le i (.v u)
    let inb ← binv .i1 .andB (.v ge) (.v le)
    if deferring then
      let out ← newVar .i1; emit (.set out (.un .notB (.v inb)))
      deferFail (.v out) 1 (some (i, .v l, .v u))
      allIn ← match allIn with
        | none => pure (some inb)
        | some prev => pure (some (← binv .i1 .andB (.v prev) (.v inb)))
    else
      let errB ← newBlock
      guard (.v inb) errB
      let cur := (← get).fb.cur
      switchTo errB
      rt "a68rt_index_error" #[i, .v l, .v u]
      terminate .unreachable
      switchTo cur
    let t ← binv .i64 .subW i (.v l)
    idx ← match idx with
      | none => pure (some t)
      | some prev =>
        let m ← binv .i64 .mulW (.v prev) (.v pr.ext1)
        pure (some (← binv .i64 .addW (.v m) (.v t)))
  match allIn with
  | some ok =>
    -- a subscript out of bounds has been recorded: the access is made safe
    let c ← newVar .i64
    emit (.set c (.select (.v ok) (.v idx.get!) (ki 0)))
    return c
  | none => return idx.get!

/-- Field `f` of the element at offset `idx`, as its MIR type; undefined is reported. -/
def prowGet (pr : PRow) (f : Nat) (idx : Var) : L Var := do
  let pid := pr.data[0]!.id
  modify fun st =>
    let seen := if st.prowSeen.any (·.data[0]!.id == pid) then st.prowSeen else pr :: st.prowSeen
    { st with prowReads := st.prowReads.push pid, prowSeen := seen }
  let (info, ty, _) := pr.fields[f]!
  if pr.known[f]?.getD false then pure ()   -- every element defined: no test
  else if (← get).defer.isSome then
    let flag ← ld "i8" .i64 pr.flags[f]! (.v idx) KLEAF
    let undef ← binv .i1 .eq (.v flag) (ki 0)
    deferFail (.v undef) (2 + info.kind)
  else
    let flag ← ld "i8" .i64 pr.flags[f]! (.v idx) KLEAF
    let undefB ← newBlock
    guard (.v (← binv .i1 .ne (.v flag) (ki 0))) undefB
    let cur := (← get).fb.cur
    switchTo undefB
    rt "a68rt_undef_error" #[ku info.kind]
    terminate .unreachable
    switchTo cur
  let eoff ← binv .i64 .mulW (.v idx) (ki info.es)
  let raw ← ld info.w (if info.w == "f64" then .f64 else .i64) pr.data[f]! (.v eoff) KLEAF
  match ty with
  | .i1 => binv .i1 .ne (.v raw) (ki 0)
  | .i32 => do let v ← newVar .i32; emit (.set v (.opnd (.v raw))); return v
  | _ => return raw

/-- Write field `f` of the element at offset `idx` and mark it defined. -/
def prowSet (pr : PRow) (f : Nat) (idx : Var) (v : Opnd) : L Unit := do
  let pid := pr.data[0]!.id
  modify fun st =>
    let seen := if st.prowSeen.any (·.data[0]!.id == pid) then st.prowSeen else pr :: st.prowSeen
    { st with prowWrites := st.prowWrites.push pid, prowSeen := seen }
  let (info, _, _) := pr.fields[f]!
  st "i8" pr.flags[f]! (.v idx) (ki 1) KLEAF
  let eoff ← binv .i64 .mulW (.v idx) (ki info.es)
  st info.w pr.data[f]! (.v eoff) v KLEAF

end A68.Lower
