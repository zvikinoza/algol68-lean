import A68.Lower.State

/-!
# A68.Optimizations.NativeCalls

Optimisation: direct and table-dispatched calls of plain routine entry points
(`a68_nf<k>`): which routine a call goes to when it is known, and the signature a call
through a procedure value would use.  The entry points themselves are built in
`A68.Lower.lowerNative`.  See docs/OPTIMIZATIONS.md §3.
-/
namespace A68.Lower
open A68.MIR

/-- The routine a call certainly goes to, when it has a plain entry point that can be
    called right here: the callee is a slot known to hold that routine, and the frame the
    slot lives in is the innermost run-time frame, so the environment the routine captured
    is the one in effect and the call needs no environment switch. -/
def staticNat (f : Core) : L (Option (Nat × CodeGen.NatSig × Bool)) := do
  match CodeGen.strip f with
  | .loadCell d s =>
    let some fr := (← get).fb.frames[d]? | return none
    let some pi := (fr.procs[s]?).join | return none
    if (← pvarOf d s).isSome || (← rtd d) != 0 then return none
    return some pi
  | _ => return none

/-- A call through a procedure-valued slot whose routine cannot be known statically, such as
    a procedure parameter: the signature a plain entry point for it would have, when the
    slot's mode allows one.  Which routine the slot holds is looked up at run time. -/
def dynNat (f : Core) : L (Option CodeGen.NatSig) := do
  match CodeGen.strip f with
  | .loadCell d s =>
    if (← pvarOf d s).isSome || (← staticNat f).isSome then return none
    let some m ← slotMode d s | return none
    match ← resolve m with
    | .proc ps r =>
      let some ptys := ps.mapM CodeGen.CTy.ofMode | return none
      let rty : Option (Option CodeGen.CTy) := match r with
        | .void => some none
        | _ => (CodeGen.CTy.ofMode r).map some
      let some rty := rty | return none
      return some { ptys := ptys.toArray, rty := rty }
    | _ => return none
  | _ => return none

/-- The mode of a call whose callee has a plain entry point. -/
def natResultMode (f : Core) : L (Option Mode) := do
  match ← staticNat f with
  | some (_, sg, _) => return sg.rty.map CodeGen.CTy.toMode
  | none =>
    match ← dynNat f with
    | some sg => return sg.rty.map CodeGen.CTy.toMode
    | none => return none

end A68.Lower
