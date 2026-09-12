import A68.Lower.Mem

/-!
# A68.Optimizations.DeferredTraps

Optimisation: deferred traps.  In a region (a counted loop the analysis in
`A68.Analysis.Repeatable` accepts) every check only sets one flag instead of branching,
the unchecked INT and REAL operations are used, and a chain of REAL `+ - *` is tested for
finiteness once where it ends.  The region itself — the flag, the copies, the checked
second run — is built in `A68.Lower.lowerLoop`.  See docs/OPTIMIZATIONS.md §5.
-/
namespace A68.Lower
open A68.MIR

/-- In a region of deferred traps: note that `cond` failed; outside one, nothing. -/
def deferFail (cond : Opnd) (_code : Int) (_ix : Option (Opnd × Opnd × Opnd) := none) : L Unit := do
  let some ctx := (← get).defer | return
  let b ← binv .i1 .orB (.v ctx.bad) cond
  emit (.set ctx.bad (.opnd (.v b)))

/-- Test every pending REAL result of the region for finiteness now: at the end of a
    statement, a branch or a loop body, and before an operation through which a NaN or
    infinity would not survive (a division, a mathematical function). -/
def flushPending : L Unit := do
  let ps := (← get).pendingF
  if ps.isEmpty then return
  modify fun st => { st with pendingF := [] }
  for v in ps do
    let bad ← newVar .i1
    emit (.set bad (.un .badF (.v v)))
    deferFail (.v bad) 12

/-- A checked dyadic operation: as it is, or, in a region of deferred traps, the unchecked
    operation with its check recorded (`Sem.binSem`'s conditions: the INT range
    ±2147483647, a zero divisor, a NaN or infinite REAL result). -/
def emitBin (v : Var) (bop : BinOp) (a b : Opnd) : L Unit := do
  match (← get).defer with
  | none =>
    match bop with
    | .powI | .powFI | .powFF => modify fun st => { st with hardTraps := st.hardTraps + 1 }
    | _ => pure ()
    emit (.set v (.bin bop a b))
  | some _ =>
    match bop with
    | .addI | .subI | .mulI =>
      let w : BinOp := match bop with | .addI => .addW | .subI => .subW | _ => .mulW
      let t ← binv .i64 w a b
      let hi ← binv .i1 .gt (.v t) (ki 2147483647)
      let lo ← binv .i1 .lt (.v t) (ki (-2147483647))
      let bad ← binv .i1 .orB (.v hi) (.v lo)
      deferFail (.v bad) 10
      emit (.set v (.opnd (.v t)))
    | .overI | .modI =>
      let bad ← binv .i1 .eq b (ki 0)
      let d ← newVar .i64
      emit (.set d (.select (.v bad) (ki 1) b))
      deferFail (.v bad) 11
      emit (.set v (.bin (if bop == .overI then .overW else .modW) a (.v d)))
    | .addF | .subF | .mulF =>
      -- a NaN or infinity survives + - *: the result is tested where the chain ends
      -- (`flushPending`), not at every step
      let w : BinOp := match bop with | .addF => .addFW | .subF => .subFW | _ => .mulFW
      let t ← binv .f64 w a b
      emit (.set v (.opnd (.v t)))
      modify fun st => { st with pendingF := v :: st.pendingF }
    | .divF =>
      flushPending
      let bad ← binv .i1 .eq b (.k .f64 (.f 0.0))
      let d ← newVar .f64
      emit (.set d (.select (.v bad) (.k .f64 (.f 1.0)) b))
      deferFail (.v bad) 13
      emit (.set v (.bin .divFW a (.v d)))
    | _ => emit (.set v (.bin bop a b))

/-- A monadic operation; `entier`, `round` and `repr` trap and are not deferred. -/
def emitUn (v : Var) (uop : UnOp) (a : Opnd) : L Unit := do
  match uop with
  | .entier | .round | .reprI => modify fun st => { st with hardTraps := st.hardTraps + 1 }
  | _ => pure ()
  emit (.set v (.un uop a))

end A68.Lower
