import A68.Lower.State
import A68.Optimizations.NativeCalls
import A68.Lower.Frames
import A68.Lower.Mem
import A68.Optimizations.DeferredTraps
import A68.Optimizations.InlineRows
import A68.Optimizations.RowPromotion
import A68.Optimizations.RowCache
import A68.Analysis.JumpFree
import A68.Analysis.Repeatable
import A68.Analysis.Definedness
import A68.Analysis.Interval


namespace A68.Lower
open A68.MIR

-- ## Expressions

mutual

/-- The value of `c`, wanted. -/
partial def lower (c : Core) : L Res := do
  match c with
  | .at p e => emit (.line p.line); lower e
  | .lit v => lowerLit v
  | .loadCell d s => readCell d s
  | .refCell d s =>
    match ← pvarOf d s with
    | some _ => rt "a68rt_push_void"; return .stack   -- never reached: the analysis keeps such slots in cells
    | none => rt "a68rt_push_ref" #[ku (← rtd d), ku s]; return .stack
  | .deref e =>
    match CodeGen.strip e with
    | .refCell d s => readCell d s
    | .slice base idx true =>
      match ← rowRead base idx with
      | some r => return r
      | none =>
        match ← selRead e with
        | some r => return r
        | none => let _ ← lowerStack e; rt "a68rt_deref"; return .stack
    | .select _ _ true =>
      match ← selRead e with
      | some r => return r
      | none => let _ ← lowerStack e; rt "a68rt_deref"; return .stack
    | _ => let _ ← lowerStack e; rt "a68rt_deref"; return .stack
  | .deproc e => let _ ← lowerStack e; rt "a68rt_deproc"; jumpCheck; return .stack
  | .widen a b e =>
    match ← resolve a, ← resolve b with
    | .int 0, .real 0 =>
      let x ← toScalar (← lower e) (.int 0)
      let v ← newVar .f64
      emit (.set v (.un .i2f x))
      return .sc (.v v)
    | _, _ =>
      lowerStackM e a
      rt "a68rt_widen" #[ku (← putMode a), ku (← putMode b)]
      return .stack
  | .rowOf e => let _ ← lowerStack e; rt "a68rt_row_of"; return .stack
  | .unite m e => let _ ← lowerStack e; rt "a68rt_unite" #[ku (← putMode m)]; return .stack
  | .voiding e => lowerVoid e; rt "a68rt_push_void"; return .stack
  | .assign d s flex =>
    match CodeGen.strip d with
    | .refCell dd ss =>
      if ← storeScalar dd ss s then
        rt "a68rt_push_ref" #[ku (← rtd dd), ku ss]
        return .stack
      lowerAssignGeneral d s flex
    | _ => lowerAssignGeneral d s flex
  | .identRel l r isnt =>
    -- `p IS NIL` on a variable held in a cell
    let cellOf (x : Core) : Option (Nat × Nat) := match CodeGen.strip x with
      | .loadCell d s => some (d, s)
      | .deref e => match CodeGen.strip e with | .refCell d s => some (d, s) | _ => none
      | _ => none
    let side := if CodeGen.isNilLit r then cellOf l else if CodeGen.isNilLit l then cellOf r else none
    match side with
    | some (d, s) =>
      if (← pvarOf d s).isNone then
        let z ← newVar .i1
        match ← cellAddr d s with
        | some (b, off) =>
          -- the cell's tag says: NIL, or a name; anything else the runtime reports
          let slow ← newBlock; let done ← newBlock
          let tag ← ld "i32" .i64 b (ki off) KCELL
          let isNil ← binv .i1 .eq (.v tag) (ki T_NIL)
          let isRef ← binv .i1 .eq (.v tag) (ki T_REF)
          guard (.v (← binv .i1 .orB (.v isNil) (.v isRef))) slow
          emit (.set z (.opnd (.v isNil)))
          terminate (.br done)
          switchTo slow
          slowPath slow none do
            let r ← rtv "a68rt_cell_isnil" #[ku (← rtd d), ku s]
            emit (.set z (.opnd (.v r)))
          terminate (.br done)
          switchTo done
        | none =>
          let r ← rtv "a68rt_cell_isnil" #[ku (← rtd d), ku s]
          emit (.set z (.opnd (.v r)))
        if isnt then
          let v ← newVar .i1
          emit (.set v (.un .notB (.v z)))
          return .sc (.v v)
        return .sc (.v z)
    | none => pure ()
    let _ ← lowerStack l; let _ ← lowerStack r
    rt "a68rt_ident_rel" #[kb isnt]
    return .stack
  | .dyop op m1 m2 l r => lowerDyop op m1 m2 l r
  | .monop op m e => lowerMonop op m e
  | .call f args =>
    match CodeGen.strip f, args with
    | .lit (.builtin n), [arg] =>
      if CodeGen.nativeMathFns.contains n && (← modeOf arg) == some (.real 0) then
        let x ← toScalar (← lower arg) (.real 0)
        flushPending
        let v ← newVar .f64
        emit (.set v (.un (.math n) x))
        return .sc (.v v)
      else lowerCall f args
    | _, _ =>
      match ← natCall f args with
      | some (some o) => return .sc o
      | some none => rt "a68rt_push_void"; return .stack
      | none => lowerCall f args
  | .routine nparams frameSize body =>
    let idx ← lowerFunction nparams frameSize body
    rt "a68rt_push_proc" #[ku idx, ku nparams]
    return .stack
  | .slice arr idx false =>
    match ← rowRead arr idx with
    | some r => return r
    | none => lowerSlice arr idx false
  | .slice arr idx viaRef => lowerSlice arr idx viaRef
  | .select i e viaRef =>
    let _ ← lowerStack e
    rt "a68rt_select" #[ku i, kb viaRef]
    return .stack
  | .newRow bounds init flex =>
    let hint := (← get).rowHint
    modify fun st => { st with rowHint := none }
    let _ ← lowerStack init
    for (l, u) in bounds do lowerStackM l (.int 0); lowerStackM u (.int 0)
    match hint with
    | some ek => rt "a68rt_new_row_of" #[ku bounds.length, kb flex, ku ek.toNat]
    | none => rt "a68rt_new_row" #[ku bounds.length, kb flex]
    return .stack
  | .gen init => let _ ← lowerStack init; rt "a68rt_gen"; return .stack
  | .block size stmts _ _ => lowerBlock size stmts true
  | .collateral es isStruct dims =>
    for e in es do let _ ← lowerStack e
    rt "a68rt_collateral" #[ku es.length, kb isStruct, ku dims]
    return .stack
  | .cond cc t e =>
    match ← modeOf c with
    | some m =>
      match tyOf (← resolve m) with
      | some ty =>
        let v ← newVar ty
        lowerCondInto (.var ty v m) cc t e
        return .sc (.v v)
      | none => lowerCondInto .stack cc t e; return .stack
    | none => lowerCondInto .stack cc t e; return .stack
  | .caseInt sel alts out =>
    match ← modeOf c with
    | some m =>
      match tyOf (← resolve m) with
      | some ty =>
        let v ← newVar ty
        lowerCaseInto (.var ty v m) sel alts out
        return .sc (.v v)
      | none => lowerCaseInto .stack sel alts out; return .stack
    | none => lowerCaseInto .stack sel alts out; return .stack
  | .caseConf sel alts out => lowerConformity .stack sel alts out; return .stack
  | .loop slot f b t w body => lowerLoop slot f b t w body; rt "a68rt_push_void"; return .stack
  | .goto l => lowerGoto l; return .stack
  | .skip m => rt "a68rt_push_skip" #[ku (← putMode m)]; return .stack
  | .andThen l r =>
    let v ← newVar .i1
    let a ← toScalar (← lower l) .bool
    let rb ← newBlock; let fb ← newBlock; let done ← newBlock
    terminate (.condBr a rb fb)
    switchTo rb
    let b ← toScalar (← lower r) .bool
    emit (.set v (.opnd b)); terminate (.br done)
    switchTo fb
    emit (.set v (.opnd (kb false))); terminate (.br done)
    switchTo done
    return .sc (.v v)
  | .orElse l r =>
    let v ← newVar .i1
    let a ← toScalar (← lower l) .bool
    let tb ← newBlock; let rb ← newBlock; let done ← newBlock
    terminate (.condBr a tb rb)
    switchTo tb
    emit (.set v (.opnd (kb true))); terminate (.br done)
    switchTo rb
    let b ← toScalar (← lower r) .bool
    emit (.set v (.opnd b)); terminate (.br done)
    switchTo done
    return .sc (.v v)
  | .fmt items =>
    let items ← items.mapM lowerFmtItem
    rt "a68rt_push_format" #[ku (← putFmtList items)]
    return .stack
  | .stop => rt "a68rt_stop"; return .stack
  | .seq a b => lowerVoid a; lower b
  | .hole _ _ => rt "a68rt_push_void"; return .stack

/-- The value of a cell or promoted variable. -/
partial def readCell (d s : Nat) : L Res := do
  match ← pvarOf d s with
  | some pv => return .sc (← readPVar pv)
  | none =>
    match (← slotMode d s).bind tyOf with
    | some _ =>
      let m := (← slotMode d s).get!
      return .sc (.v (← rtv (cellFn (← resolve m)) #[ku (← rtd d), ku s]))
    | none => rt "a68rt_push_cell" #[ku (← rtd d), ku s]; return .stack

/-- The cell a row or structure access is rooted at, when the base is a cell that holds
    the row (`refCell`) or a name of it (`loadCell`, `deref refCell`). -/
partial def cellBase (base : Core) : L (Option (Nat × Nat × Bool)) := do
  match CodeGen.strip base with
  | .refCell d s => if (← pvarOf d s).isSome then return none else return some (d, s, false)
  | .loadCell d s => if (← pvarOf d s).isSome then return none else return some (d, s, true)
  | .deref e =>
    match CodeGen.strip e with
    | .refCell d s => if (← pvarOf d s).isSome then return none else return some (d, s, true)
    | _ => return none
  | _ => return none

/-- The subscripts of a promoted row access: each lowered to a scalar, with its interval
    for the bounds check, then the element offset. -/
partial def prowIdx (pr : PRow) (idx : List CoreIdx) : L (Option Var) := do
  if idx.length != pr.dims then return none
  let mut is : Array Opnd := #[]
  let mut ranges : Array (Option (Int × Int)) := #[]
  for ix in idx do
    match ix with
    | .index e =>
      ranges := ranges.push (← intervalOf e)
      is := is.push (← toScalar (← lower e) (.int 0))
    | _ => return none
  return some (← prowIndex pr is ranges)

/-- `a[i]` or `a[i, j]` on a row a cell holds, of a primitive element mode: one runtime call
    that checks the bounds and reads the element (`a68rt_row_int` and its relatives). -/
partial def rowRead (base : Core) (idx : List CoreIdx) : L (Option Res) := do
  let some (d, s, viaName) ← cellBase base | return none
  -- a promoted row: the element from its arrays
  match ← prowOf d s with
  | some pr =>
    if pr.fields.size != 1 then return none
    let some ix ← prowIdx pr idx | return none
    return some (.sc (.v (← prowGet pr 0 ix)))
  | none => pure ()
  let some m ← slotMode d s | return none
  let mr ← resolve m
  -- a cell holding a name of a row (`REF [] INT` parameter) is not a row the runtime's
  -- element entry points can subscript directly
  let rowM ← match viaName, mr with
    | _, r@(.row _ _ _) => pure (some r)
    | _, _ => pure none
  let some (.row dims _ em) := rowM | return none
  let emr ← resolve em
  let some ty := tyOf emr | return none
  if idx.length != dims || dims > 2 then return none
  let mut is : Array Opnd := #[]
  for ix in idx do
    match ix with
    | .index e => is := is.push (← toScalar (← lower e) (.int 0))
    | _ => return none
  let fn := match ty with
    | .i64 => if emr matches .bits _ then "a68rt_row_bits" else "a68rt_row_int"
    | .f64 => "a68rt_row_real" | .i1 => "a68rt_row_bool" | .i32 => "a68rt_row_char" | .ptr => ""
  let j := is[1]?.getD (ki 0)
  match ← cellAddr d s, elemInfo emr with
  | some (b, off), some info =>
    -- inline when the cell holds a row over a leaf store, else the runtime
    let res ← newVar ty
    let fid ← cellFid d
    let slow ← newBlock; let done ← newBlock
    let (store, idx, n?, _) ← rowLeafElemC fid b off s dims is info slow
    let v ← leafGet store idx info ty n?
    emit (.set res (.opnd (.v v)))
    terminate (.br done)
    switchTo slow
    slowPath slow (some (fid, s)) do
      let sv ← rtv fn #[ku (← rtd d), ku s, ku dims, is[0]!, j]
      emit (.set res (.opnd (.v sv)))
    terminate (.br done)
    switchTo done
    return some (.sc (.v res))
  | _, _ => return some (.sc (.v (← rtv fn #[ku (← rtd d), ku s, ku dims, is[0]!, j])))

/-- The selector chain of `f OF … OF x[i]` rooted at a cell, as the runtime's `sel_*`
    entry points take it: depth, slot, spec, i, j, fields. -/
partial def selChain (c : Core) : L (Option (Nat × Nat × Nat × Opnd × Opnd × List Nat × Bool)) := do
  -- (depth, slot, rank, i, j, fields, viaCellRef)
  match c with
  | .at _ e => selChain e
  | .refCell d s =>
    if (← pvarOf d s).isSome then return none
    return some (d, s, 0, ki 0, ki 0, [], false)
  | .loadCell d s | .deref (.refCell d s) =>
    if (← pvarOf d s).isSome then return none
    return some (d, s, 0, ki 0, ki 0, [], true)
  | .slice base idx true =>
    let some (d, s, rank, _, _, fields, via) ← selChain base | return none
    if via || rank != 0 || !fields.isEmpty then return none
    match idx with
    | [.index a] => return some (d, s, 1, ← toScalar (← lower a) (.int 0), ki 0, [], false)
    | [.index a, .index b] =>
      let ia ← toScalar (← lower a) (.int 0)
      let ib ← toScalar (← lower b) (.int 0)
      return some (d, s, 2, ia, ib, [], false)
    | _ => return none
  | .select f e true =>
    let some (d, s, rank, i, j, fields, via) ← selChain e | return none
    if fields.length ≥ 4 || f ≥ 256 then return none
    return some (d, s, rank, i, j, fields ++ [f], via)
  | _ => return none

partial def specOf (rank : Nat) (via : Bool) (fields : List Nat) : Nat := rank + (if via then 4 else 0) + 256 * fields.length
partial def fieldsWord (fields : List Nat) : Nat := Id.run do
  let mut w := 0
  let mut k := 0
  for f in fields do
    w := w + f * 256 ^ k
    k := k + 1
  return w

/-- `f OF … OF x` of a primitive mode, read by one runtime call. -/
partial def selRead (c : Core) : L (Option Res) := do
  -- `f OF a[i]` on a promoted row of structures
  match CodeGen.strip c with
  | .select f (.slice base idx true) true =>
    match ← cellBase base with
    | some (d, s, false) =>
      match ← prowOf d s with
      | some pr =>
        if f < pr.fields.size then
          match ← prowIdx pr idx with
          | some ixv => return some (.sc (.v (← prowGet pr f ixv)))
          | none => pure ()
      | none => pure ()
    | _ => pure ()
  | _ => pure ()
  let some m ← modeOfRef c | return none
  let mr ← resolve m
  let some ty := tyOf mr | return none
  let some (d, s, rank, i, j, fields, via) ← selChain c | return none
  if fields.isEmpty then return none
  let fn := match ty with
    | .i64 => if mr matches .bits _ then "a68rt_sel_bits" else "a68rt_sel_int"
    | .f64 => "a68rt_sel_real" | .i1 => "a68rt_sel_bool" | .i32 => "a68rt_sel_char" | .ptr => ""
  let slowCall : L Var := do rtv fn #[ku (← rtd d), ku s, ku (specOf rank via fields), i, j, ku (fieldsWord fields)]
  match ← cellAddr d s, elemInfo mr with
  | some (b, off), some info =>
    -- inline through the name, the row element and the structure objects when every tag
    -- is as expected, else the runtime
    let res ← newVar ty
    let fid ← cellFid d
    let slow ← newBlock; let done ← newBlock
    let (p, o, pk) ← selAddr b off rank #[i, j] fields slow via (some (fid, s))
    let v ← valGet p o info ty slow pk
    emit (.set res (.opnd (.v v)))
    terminate (.br done)
    switchTo slow
    slowPath slow (some (fid, s)) do
      let sv ← slowCall
      emit (.set res (.opnd (.v sv)))
    terminate (.br done)
    switchTo done
    return some (.sc (.v res))
  | _, _ => return some (.sc (.v (← slowCall)))

/-- The general slice: the row and the indexers on the stack, then the runtime. -/
partial def lowerSlice (arr : Core) (idx : List CoreIdx) (viaRef : Bool) : L Res := do
  let _ ← lowerStack arr
  let mut kinds : Nat := 0
  let mut i := 0
  for ix in idx do
    match ix with
    | .index e => lowerStackM e (.int 0)
    | .trim l u a =>
      let mut bits := 1
      match l with | some e => lowerStackM e (.int 0); bits := bits + 2 | none => pure ()
      match u with | some e => lowerStackM e (.int 0); bits := bits + 4 | none => pure ()
      match a with | some e => lowerStackM e (.int 0); bits := bits + 8 | none => pure ()
      kinds := kinds + bits * 16 ^ i
    i := i + 1
  rt "a68rt_slice" #[ku idx.length, ki kinds, kb viaRef]
  return .stack

/-- `a[i] := <scalar>` and `f OF … OF x := <scalar>` written in place by one runtime call.
    Returns whether it applied. -/
partial def storeTyped (dst src : Core) : L Bool := do
  -- a promoted row: `a[i] := v`, `a[i] := (f₁, …)` on a row of structures, `f OF a[i] := v`
  match CodeGen.strip dst with
  | .slice base idx true =>
    match ← cellBase base with
    | some (d, s, false) =>
      match ← prowOf d s with
      | some pr =>
        if idx.length != pr.dims then return false
        if pr.fields.size == 1 then
          let (_, _, em) := pr.fields[0]!
          let some ix ← prowIdx pr idx | return false
          let v ← toScalar (← lower src) em
          prowSet pr 0 ix v
          return true
        else
          match CodeGen.strip src with
          | .collateral es _ _ =>
            if es.length != pr.fields.size then return false
            -- the fields in order, then the stores (`CodeGen`: a structure display into an element)
            let some ix ← prowIdx pr idx | return false
            let mut vs : Array (Option Opnd) := #[]
            let mut k := 0
            for e in es do
              let (_, _, em) := pr.fields[k]!
              match CodeGen.strip e with
              | .lit .undef => vs := vs.push none
              | _ => vs := vs.push (some (← toScalar (← lower e) em))
              k := k + 1
            for f in [0:pr.fields.size] do
              match vs[f]! with
              | some v => prowSet pr f ix v
              | none =>
                st "i8" pr.flags[f]! (.v ix) (ki 0) KLEAF
                if d == 0 then setKnown s (some f) false
            return true
          | _ => return false
      | none => pure ()
    | _ => pure ()
  | .select f (.slice base idx true) true =>
    match ← cellBase base with
    | some (d, s, false) =>
      match ← prowOf d s with
      | some pr =>
        if f ≥ pr.fields.size then return false
        let some ix ← prowIdx pr idx | return false
        let (_, _, em) := pr.fields[f]!
        let v ← toScalar (← lower src) em
        prowSet pr f ix v
        return true
      | none => pure ()
    | _ => pure ()
  | _ => pure ()
  let some m ← modeOfRef dst | return false
  let mr ← resolve m
  let some ty := tyOf mr | return false
  match ← modeOf src with
  | some sm => if (← resolve sm) != mr then return false
  | none => return false
  match CodeGen.strip dst with
  | .slice base idx true =>
    let some (d, s, false) ← cellBase base | return false
    let some bm ← slotMode d s | return false
    let some (.row dims _ _) := some (← resolve bm) | return false
    if idx.length != dims || dims > 2 then return false
    let mut is : Array Opnd := #[]
    for ix in idx do
      match ix with
      | .index e => is := is.push (← toScalar (← lower e) (.int 0))
      | _ => return false
    let v ← toScalar (← lower src) mr
    let fn := match ty with
      | .i64 => if mr matches .bits _ then "a68rt_set_row_bits" else "a68rt_set_row_int"
      | .f64 => "a68rt_set_row_real" | .i1 => "a68rt_set_row_bool" | .i32 => "a68rt_set_row_char" | .ptr => ""
    rowWrite d s dims is mr v fn
    return true
  | .select _ _ true =>
    let some (d, s, rank, i, j, fields, via) ← selChain dst | return false
    if fields.isEmpty then return false
    let v ← toScalar (← lower src) mr
    let fn := match ty with
      | .i64 => if mr matches .bits _ then "a68rt_set_sel_bits" else "a68rt_set_sel_int"
      | .f64 => "a68rt_set_sel_real" | .i1 => "a68rt_set_sel_bool" | .i32 => "a68rt_set_sel_char" | .ptr => ""
    let slowCall : L Unit := do rt fn #[ku (← rtd d), ku s, ku (specOf rank via fields), i, j, ku (fieldsWord fields), v]
    match ← cellAddr d s, elemInfo mr with
    | some (b, off), some info =>
      let fid ← cellFid d
      let slow ← newBlock; let done ← newBlock
      let (p, o, pk) ← selAddr b off rank #[i, j] fields slow via (some (fid, s))
      if mr == .char then guard (.v (← binv .i1 .lt v (.k .i32 (.i 256)))) slow
      valSet p o info v pk
      terminate (.br done)
      switchTo slow
      slowPath slow (some (fid, s)) slowCall
      terminate (.br done)
      switchTo done
    | _, _ => slowCall
    return true
  | _ => return false

/-- The scalar operation of an assigning operator, with its checks. -/
partial def assignBin (op : String) (m : Mode) : Option BinOp :=
  match m, op with
  | .int _, "+:=" => some .addI | .int _, "-:=" => some .subI | .int _, "*:=" => some .mulI
  | .int _, "%:=" => some .overI | .int _, "%*:=" => some .modI
  | .real _, "+:=" => some .addF | .real _, "-:=" => some .subF | .real _, "*:=" => some .mulF
  | .real _, "/:=" => some .divF
  | .bits _, "&:=" => some .andU | .bits _, "|:=" => some .orU
  | _, _ => none

/-- `x +:= e` and its relatives in statement position on a variable of primitive mode: the
    right operand, then the variable's value, the operation, the write.  Returns whether
    it applied. -/
partial def assignOpVoid (op : String) (m1 m2 : Mode) (l r : Core) : L Bool := do
  let .ref tm ← resolve m1 | return false
  let tmr ← resolve tm
  -- `s +:= t` where `s` is a whole cell holding a row: one call that appends to the row
  -- in place, instead of a reference, a rowing and an operator that rebuilds the row
  if op == "+:=" then
    match tmr, CodeGen.strip l with
    | .row 1 _ em, .refCell d s =>
      if (← pvarOf d s).isNone then
        let emr ← resolve em
        match CodeGen.strip r with
        | .rowOf e =>
          if emr == .char && (← modeOf e) == some .char then
            let c ← toScalar (← lower e) .char
            appendElem d s .char c "a68rt_append_char"
          else
            let _ ← lowerStack r
            rtCell "a68rt_append" (← cellFid d) s #[ku (← rtd d), ku s]
        | _ =>
          let _ ← lowerStack r
          rtCell "a68rt_append" (← cellFid d) s #[ku (← rtd d), ku s]
        return true
    | _, _ => pure ()
  let some _ := tyOf tmr | return false
  let some bop := assignBin op tmr | return false
  if (tyOf (← resolve m2)).isNone then return false
  match CodeGen.strip l with
  | .refCell dd ss =>
    let rs ← toScalar (← lower r) m2
    match ← pvarOf dd ss with
    | some pv =>
      let cur ← readPVar pv
      let v ← newVar pv.v.ty
      emitBin v bop cur rs
      writePVar pv (.v v)
      return true
    | none =>
      let some sm ← slotMode dd ss | return false
      if (← resolve sm) != tmr then return false
      let cur ← rtv (cellFn tmr) #[ku (← rtd dd), ku ss]
      let v ← newVar cur.ty
      emitBin v bop (.v cur) rs
      rt (setCellFn tmr) #[ku (← rtd dd), ku ss, .v v]
      return true
  | .select f (.slice base idx true) true =>
    -- `f OF a[i] +:= e` on a promoted row of structures
    let some (d, s, false) ← cellBase base | return false
    let some pr ← prowOf d s | return false
    if f ≥ pr.fields.size then return false
    let (_, _, em) := pr.fields[f]!
    if (← resolve em) != tmr then return false
    let some ixv ← prowIdx pr idx | return false
    let rs ← toScalar (← lower r) m2
    let cur ← prowGet pr f ixv
    let v ← newVar cur.ty
    emitBin v bop (.v cur) rs
    prowSet pr f ixv (.v v)
    return true
  | .slice base idx true =>
    -- `a[i] +:= e` on a row a cell holds, or on a promoted row
    let some (d, s, false) ← cellBase base | return false
    match ← prowOf d s with
    | some pr =>
      if pr.fields.size != 1 then return false
      let (_, _, em) := pr.fields[0]!
      if (← resolve em) != tmr then return false
      let some ixv ← prowIdx pr idx | return false
      let rs ← toScalar (← lower r) m2
      let cur ← prowGet pr 0 ixv
      let v ← newVar cur.ty
      emitBin v bop (.v cur) rs
      prowSet pr 0 ixv (.v v)
      return true
    | none => pure ()
    let some bm ← slotMode d s | return false
    let .row dims _ em ← resolve bm | return false
    if (← resolve em) != tmr || idx.length != dims || dims > 2 then return false
    let mut is : Array Opnd := #[]
    for ix in idx do
      match ix with
      | .index e => is := is.push (← toScalar (← lower e) (.int 0))
      | _ => return false
    let rs ← toScalar (← lower r) m2
    let j := is[1]?.getD (ki 0)
    let (rd, wr) := match tyOf tmr with
      | some .i64 => if tmr matches .bits _ then ("a68rt_row_bits", "a68rt_set_row_bits") else ("a68rt_row_int", "a68rt_set_row_int")
      | some .f64 => ("a68rt_row_real", "a68rt_set_row_real") | some .i1 => ("a68rt_row_bool", "a68rt_set_row_bool")
      | _ => ("a68rt_row_char", "a68rt_set_row_char")
    let cur ← rtv rd #[ku (← rtd d), ku s, ku dims, is[0]!, j]
    let v ← newVar cur.ty
    emitBin v bop (.v cur) rs
    rt wr #[ku (← rtd d), ku s, ku dims, is[0]!, j, .v v]
    return true
  | _ => return false

/-- Lower `c` and leave its value on the operand stack. -/
partial def lowerStack (c : Core) : L Unit := do
  match ← lower c with
  | .stack => pure ()
  | .sc o =>
    -- the mode is known from the node when it yields a scalar
    match ← modeOf c with
    | some m => rt (pushFnM (← resolve m)) #[o]
    | none => rt (pushFn o.ty) #[o]

/-- The same, with the mode supplied by the context (needed to tell BITS from INT). -/
partial def lowerStackM (c : Core) (m : Mode) : L Unit := do
  let mr ← resolve m
  if (tyOf mr).isNone then lowerStack c else
  match ← lower c with
  | .stack => pure ()
  | .sc o => rt (pushFnM mr) #[o]

partial def lowerLit (v : Value) : L Res := do
  match v with
  | .int n =>
    if n ≥ -2147483647 && n ≤ 2147483647 then return .sc (ki n)
    rt "a68rt_push_bigint" #[ku (← putStr (toString n))]; return .stack
  | .real x => return .sc (.k .f64 (.f x))
  | .bool b => return .sc (kb b)
  | .char c => return .sc (.k .i32 (.i c))
  | .bits b =>
    if b < 2 ^ 64 then rt "a68rt_push_bits" #[ki b]; return .stack
    rt "a68rt_push_bigbits" #[ku (← putStr (toString b))]; return .stack
  | .void => rt "a68rt_push_void"; return .stack
  | .nil => rt "a68rt_push_nil"; return .stack
  | .undef => rt "a68rt_push_undef"; return .stack
  | .union m .undef => rt "a68rt_push_undef"; rt "a68rt_unite" #[ku (← putMode m)]; return .stack
  | .builtin n => rt "a68rt_push_builtin" #[ku (← putStr n)]; return .stack
  | .file id => rt "a68rt_push_file" #[ku id]; return .stack
  | .row _ _ es =>
    if es.all (fun e => match e with | .char _ => true | _ => false) then
      let str := String.ofList (es.toList.map fun e => match e with | .char c => Char.ofNat c | _ => '?')
      rt "a68rt_push_str" #[ku (← putStr str)]
    else
      for e in es do
        let r ← lowerLit e
        match r with
        | .sc o => rt (pushFn o.ty) #[o]
        | .stack => pure ()
      rt "a68rt_collateral" #[ku es.size, kb false, ku 1]
    return .stack
  | _ => rt "a68rt_push_void"; return .stack

/-- `x := e` written straight into the cell when both are of one primitive mode. -/
partial def storeScalar (dd ss : Nat) (src : Core) : L Bool := do
  match ← pvarOf dd ss with
  | some pv =>
    -- a promoted variable has no cell: this must always apply
    let ty := pv.v.ty
    let mr ← resolve pv.m
    let v ← newVar ty
    lowerInto (.var ty v mr) src
    writePVar pv (.v v)
    return true
  | none =>
  match ← slotMode dd ss with
  | some m =>
    let mr ← resolve m
    match tyOf mr with
    | some _ =>
      match ← modeOf src with
      | some sm =>
        if (← resolve sm) == mr then
          let o ← toScalar (← lower src) mr
          rt (setCellFn mr) #[ku (← rtd dd), ku ss, o]
          return true
        else return false
      | none => return false
    | none => return false
  | none => return false

/-- `p := q`, `p := f OF … OF x` or `p := NIL` on a cell of a REF mode: the 16-byte value
    is copied inline, once its tag is seen to be a name or NIL (a name is a value: the
    runtime's `slot_put` copies it as it is).  Returns whether it applied. -/
partial def storeRef (dst : Core) (dd ss : Nat) (src : Core) (flex : Bool) : L Bool := do
  if (← pvarOf dd ss).isSome then return false
  let some m ← slotMode dd ss | return false
  let .ref _ ← resolve m | return false
  let some (db, doff) ← cellAddr dd ss | return false
  -- where the source value is
  let srcAddr : Option (L (Nat × (Var × Opnd × Nat))) ← do   -- the slow block, then the address
    match CodeGen.strip src with
    | .lit .nil => pure none
    | .loadCell d s | .deref (.refCell d s) =>
      if (← pvarOf d s).isSome then pure none else
      match ← slotMode d s with
      | some sm =>
        match ← resolve sm with
        | .ref _ =>
          match ← cellAddr d s with
          | some (b, off) => pure (some (do let slow ← newBlock; pure (slow, (b, ki off, KCELL))))
          | none => pure none
        | _ => pure none
      | none => pure none
    | .deref e =>
      match ← modeOfRef e with
      | some rm =>
        match ← resolve rm with
        | .ref _ =>
          match ← selChain e with
          | some (d, s, rank, i, j, fields, via) =>
            if fields.isEmpty then pure none else
            match ← cellAddr d s with
            | some (b, off) => pure (some (do
                let slow ← newBlock
                let (p, o, pk) ← selAddr b off rank #[i, j] fields slow via
                pure (slow, (p, o, pk))))
            | none => pure none
          | none => pure none
        | _ => pure none
      | none => pure none
    | _ => pure none
  match CodeGen.strip src, srcAddr with
  | .lit .nil, _ =>
    st "i64" db (ki doff) (ki T_NIL) KCELL
    st "i64" db (ki (doff + 8)) (ki 0) KCELL
    return true
  | _, some act =>
    let (slow, (p, o, pk)) ← act
    let done ← newBlock
    let tag ← ld "i32" .i64 p o pk
    let isNil ← binv .i1 .eq (.v tag) (ki T_NIL)
    let isRef ← binv .i1 .eq (.v tag) (ki T_REF)
    guard (.v (← binv .i1 .orB (.v isNil) (.v isRef))) slow
    let w0 ← ld "i64" .i64 p o pk
    let o8 ← binv .i64 .addW o (ki 8)
    let w1 ← ld "i64" .i64 p (.v o8) pk
    st "i64" db (ki doff) (.v w0) KCELL
    st "i64" db (ki (doff + 8)) (.v w1) KCELL
    terminate (.br done)
    switchTo slow
    slowPath slow none do
      let _ ← lowerAssignGeneral dst src flex
      rt "a68rt_pop"
    terminate (.br done)
    switchTo done
    return true
  | _, none => return false

partial def lowerAssignGeneral (d s : Core) (flex : Bool) : L Res := do
  let _ ← lowerStack d
  let _ ← lowerStack s
  rt "a68rt_assign" #[kb flex]
  return .stack

partial def lowerCall (f : Core) (args : List Core) : L Res := do
  let _ ← lowerStack f
  for a in args do let _ ← lowerStack a
  rt "a68rt_call" #[ku args.length]
  jumpCheck
  return .stack

/-- The arguments of a plain call, evaluated left to right into scalars. -/
partial def natArgs (ptys : Array CodeGen.CTy) (args : List Core) : L (Array Opnd) := do
  let mut as : Array Opnd := #[]
  for i in [0:args.length] do
    as := as.push (← toScalar (← lower args[i]!) (ptys[i]!).toMode)
  return as

/-- A call that can go to a plain entry point: directly when the routine is known, else
    through the table of entry points after reading the slot, falling back to the boxed
    call for a routine without one.  `some none` is a completed VOID call; `none` says the
    call is not a plain one. -/
partial def natCall (f : Core) (args : List Core) : L (Option (Option Opnd)) := do
  match ← staticNat f with
  | some (k, sg, jumpFree) =>
    if args.length != sg.ptys.size then return none
    let as ← natArgs sg.ptys args
    match sg.rty with
    | some t =>
      let v ← newVar (tyOfC t)
      emit (.set v (.call (.nfn k) as))
      if !jumpFree then jumpCheck
      return some (some (.v v))
    | none =>
      emit (.call (.nfn k) as)
      if !jumpFree then jumpCheck
      return some none
  | none =>
  match ← dynNat f, CodeGen.strip f with
  | some sg, .loadCell d s =>
    if args.length != sg.ptys.size then return none
    let ptys := sg.ptys.map tyOfC
    let rty := sg.rty.map tyOfC
    -- the slot is read first and the arguments are evaluated after it, once, on whichever
    -- path is taken, which is the evaluator's order
    let p ← rtv "a68rt_cell_cproc" #[ku (← rtd d), ku s]
    let fp ← newVar .ptr
    emit (.set fp (.natTab (.v p)))
    let c ← newVar .i1
    emit (.set c (.bin .ne (.v fp) (.k .ptr (.i 0))))
    let rv : Option Var ← match rty with
      | some t => pure (some (← newVar t))
      | none => pure none
    let thenB ← newBlock; let elseB ← newBlock; let done ← newBlock
    terminate (.condBr (.v c) thenB elseB)
    switchTo thenB
    let as ← natArgs sg.ptys args
    match rv with
    | some v => emit (.set v (.call (.ind ptys rty) (#[.v fp] ++ as)))
    | none => emit (.call (.ind ptys rty) (#[.v fp] ++ as))
    jumpCheck
    terminate (.br done)
    switchTo elseB
    let _ ← lowerCall f args
    match rv, sg.rty with
    | some v, some t => let o ← toScalar .stack t.toMode; emit (.set v (.opnd o))
    | _, _ => rt "a68rt_pop"
    terminate (.br done)
    switchTo done
    return some (rv.map (.v ·))
  | _, _ => return none

/-- `k LWB a` or `k UPB a` for a row a cell holds: the bound read from the descriptor when
    the cell holds a row value, else `slowAct`, which leaves the result on the stack. -/
partial def rowBound (isUpb : Bool) (k : Nat) (e : Core) (slowAct : L Unit) : L (Option Res) := do
  let some (d, s, _) ← cellBase e | return none
  match ← prowOf d s with
  | some pr =>
    if k < 1 || k > pr.dims then return none
    return some (.sc (.v (if isUpb then pr.hi[k - 1]! else pr.lo[k - 1]!)))
  | none => pure ()
  let some m ← slotMode d s | return none
  let .row dims _ _ ← resolve m | return none
  if k < 1 || k > dims then return none
  let some (b, off) ← cellAddr d s | return none
  let fid ← cellFid d
  let res ← newVar .i64
  let slow ← newBlock; let done ← newBlock
  -- a cache of the row (of either store kind) has the bound
  let cached : Option RowCache ← do
    match ← lookupCache fid s 0 with
    | some c => pure (some c)
    | none =>
      match (← get).caches.find? (fun c => c.fid == fid && c.slot == s) with
      | some c => pure (some c)
      | none => pure none
  match cached with
  | some c =>
    guard (.v c.valid) slow
    let (l, u, _) := c.dim[k - 1]!
    emit (.set res (.opnd (.v (if isUpb then u else l))))
  | none =>
    let r ← cellRowd b off slow
    let v ← ld "i64" .i64 r (ki (48 + 24 * (k - 1) + (if isUpb then 8 else 0))) KHDR
    emit (.set res (.opnd (.v v)))
  terminate (.br done)
  switchTo slow
  slowPath slow (some (fid, s)) do
    slowAct
    let sv ← rtv "a68rt_pop_int"
    emit (.set res (.opnd (.v sv)))
  terminate (.br done)
  switchTo done
  return some (.sc (.v res))

partial def lowerDyop (op : String) (m1 m2 : Mode) (l r : Core) : L Res := do
  let r1 ← resolve m1
  let r2 ← resolve m2
  let general : L Res := do
    lowerStackM l m1; lowerStackM r m2
    rt "a68rt_dyop" #[ku (← putStr op), ku (← putMode m1), ku (← putMode m2)]
    return .stack
  -- `k LWB a`, `k UPB a` on a row a cell holds
  if (op == "LWB" || op == "UPB") && r1 == .int 0 then
    match CodeGen.strip l with
    | .lit (.int k) =>
      if k ≥ 1 then
        let slowAct : L Unit := do
          lowerStackM l m1; lowerStackM r m2
          rt "a68rt_dyop" #[ku (← putStr op), ku (← putMode m1), ku (← putMode m2)]
        match ← rowBound (op == "UPB") k.toNat r slowAct with
        | some res => return res
        | none => pure ()
    | _ => pure ()
  -- REAL ** INT
  if op == "**" && r1 == .real 0 && r2 == .int 0 then
    let a ← toScalar (← lower l) r1
    let b ← toScalar (← lower r) r2
    let v ← newVar .f64
    emit (.set v (.bin .powFI a b))
    return .sc (.v v)
  -- INT ** constant: the square-and-multiply loop of `Sem.powI`, unrolled, so that every
  -- product the loop range-checks is a checked `mulI` here and nothing else is
  if op == "**" && r1 == .int 0 && r2 == .int 0 then
    match CodeGen.strip r with
    | .lit (.int k) =>
      if 0 ≤ k && k ≤ 64 then
        let a ← toScalar (← lower l) r1
        if k == 0 then return .sc (ki 1)
        let nn := k.toNat
        let mut mm : Opnd := a
        let mut p : Option Opnd := none      -- `none` is the initial 1
        let mut bit := 1
        while true do
          if nn &&& bit != 0 then
            match p with
            | none => p := some mm
            | some pv => let v ← newVar .i64; emitBin v .mulI pv mm; p := some (.v v)
          bit := bit <<< 1
          if bit ≤ nn then
            let v ← newVar .i64; emitBin v .mulI mm mm; mm := .v v
          else break
        return .sc (p.getD a)
    | _ => pure ()
  if r1 != r2 then general else
  match tyOf r1, binOf op r1, dyopResult op r1 with
  | some _, some bop, some res =>
    let a ← toScalar (← lower l) r1
    let b ← toScalar (← lower r) r2
    let v ← newVar ((tyOf (← resolve res)).getD .i1)
    emitBin v bop a b
    return .sc (.v v)
  | _, _, _ => general

partial def lowerMonop (op : String) (m : Mode) (e : Core) : L Res := do
  let mr ← resolve m
  if op == "LWB" || op == "UPB" then
    let slowAct : L Unit := do
      lowerStackM e m
      rt "a68rt_monop" #[ku (← putStr op), ku (← putMode m)]
    match ← rowBound (op == "UPB") 1 e slowAct with
    | some res => return res
    | none => pure ()
  match tyOf mr, unOf op mr, monopResult op mr with
  | some _, some uop, some res =>
    let x ← toScalar (← lower e) mr
    let v ← newVar ((tyOf (← resolve res)).getD .i64)
    emitUn v uop x
    return .sc (.v v)
  | some _, none, some _ =>
    if isPlus op then lower e else do
      lowerStackM e m
      rt "a68rt_monop" #[ku (← putStr op), ku (← putMode m)]
      return .stack
  | _, _, _ =>
    lowerStackM e m
    rt "a68rt_monop" #[ku (← putStr op), ku (← putMode m)]
    return .stack

/-- `c` in statement position: its value is not wanted. -/
partial def lowerVoid (c : Core) : L Unit := do
  match c with
  | .at p e => emit (.line p.line); lowerVoid e
  | .voiding e => lowerVoid e
  | .seq a b => lowerVoid a; lowerVoid b
  | .lit _ | .skip _ | .loadCell _ _ | .refCell _ _ => pure ()
  | .assign d s flex =>
    match CodeGen.strip d with
    | .refCell dd ss =>
      if ← storeScalar dd ss s then pure ()
      else if ← storeRef d dd ss s flex then pure ()
      else do let _ ← lowerAssignGeneral d s flex; rt "a68rt_pop"
    | _ =>
      if ← storeTyped d s then pure ()
      else do let _ ← lowerAssignGeneral d s flex; rt "a68rt_pop"
  | .dyop op m1 m2 l r =>
    if ← assignOpVoid op m1 m2 l r then pure ()
    else
      match ← lower c with
      | .stack => rt "a68rt_pop"
      | .sc _ => pure ()
  | .cond cc t e => lowerCondInto .void cc t e
  | .block size stmts _ _ => let _ ← lowerBlock size stmts false
  | .loop slot f b t w body => lowerLoop slot f b t w body
  | .caseInt sel alts out => lowerCaseInto .void sel alts out
  | .caseConf sel alts out => lowerConformity .void sel alts out
  | .goto l => lowerGoto l
  | .stop => rt "a68rt_stop"
  | .call f args =>
    match ← natCall f args with
    | some _ => pure ()
    | none =>
      match ← lower c with
      | .stack => rt "a68rt_pop"
      | .sc _ => pure ()
  | _ =>
    match ← lower c with
    | .stack => rt "a68rt_pop"
    | .sc _ => pure ()

/-- Run a lowering whose value went to the stack, and discard it. -/
partial def lowerVoidOf (act : L Unit) : L Unit := do act; rt "a68rt_pop"

/-- A conditional whose branches either assign a scalar variable or leave a value on
    the stack. -/
partial def lowerCondInto (dest : Dest) (cc t e : Core) : L Unit := do
  let cond ← toScalar (← lower cc) .bool
  let tb ← newBlock; let eb ← newBlock; let done ← newBlock
  terminate (.condBr cond tb eb)
  switchTo tb; lowerInto dest t; flushPending; terminate (.br done)
  switchTo eb; lowerInto dest e; flushPending; terminate (.br done)
  switchTo done

/-- Compute `c` into the destination: a scalar variable, or the stack. -/
partial def lowerInto (dest : Dest) (c : Core) : L Unit := do
  match dest with
  | .void => lowerVoid c
  | .stack => lowerStack c
  | .var _ v m =>
    match c with
    | .at p e => emit (.line p.line); lowerInto dest e
    | .seq a b => lowerVoid a; lowerInto dest b
    | .cond cc t e => lowerCondInto dest cc t e
    | .caseInt sel alts out => lowerCaseInto dest sel alts out
    | _ =>
      let o ← toScalar (← lower c) m
      emit (.set v (.opnd o))

partial def lowerCaseInto (dest : Dest) (sel : Core) (alts : List Core) (out : Core) : L Unit := do
  let n := alts.length
  let k : Opnd ← match ← lower sel with
    | .sc o => pure o
    | .stack => pure (.v (← rtv "a68rt_case_index" #[ku n]))
  let done ← newBlock
  let dflt ← newBlock
  let mut cases : Array (Int × Nat) := #[]
  let mut blocks : Array Nat := #[]
  for i in [0:n] do
    let b ← newBlock
    cases := cases.push ((i + 1 : Int), b)
    blocks := blocks.push b
  terminate (.switch k cases dflt)
  let mut i := 0
  for a in alts do
    switchTo blocks[i]!
    lowerInto dest a
    flushPending
    terminate (.br done)
    i := i + 1
  switchTo dflt
  lowerInto dest out
  flushPending
  terminate (.br done)
  switchTo done

/-- A conformity clause.  When the selector is a union a cell holds, or an element of a
    row of unions a cell holds, and every alternative is of a primitive mode whose bound
    identifier can be a variable, the united value's mode and content are read inline: the
    mode is compared with each alternative's (equal table indices conform; otherwise the
    runtime's `conforms` decides) and the content goes into the variable.  Anything else
    — a united value of another shape, an undefined value — takes the general path, which
    evaluates the selector onto the stack and asks the runtime per alternative. -/
partial def lowerConformity (dest : Dest) (sel : Core) (alts : List (Mode × Option Nat × Core)) (out : Core) : L Unit := do
  let done ← newBlock
  -- the general path, from the selector on the stack
  let general : L Unit := do
    for (m, slot, body) in alts do
      let mi ← putMode m
      let ok ← rtv "a68rt_conform" #[ku mi, kb slot.isSome]
      let yes ← newBlock; let no ← newBlock
      terminate (.condBr (.v ok) yes no)
      switchTo yes
      let cells ← rtv "a68rt_enter" #[ku (if slot.isSome then 1 else 0)]
      if slot.isSome then rt "a68rt_bind_cell" #[ku 0, ku 0]
      pushFrame #[if slot.isSome then some m else none] #[] true (some cells)
      match dest with
      | .stack => let _ ← lowerStack body; popFrame; rt "a68rt_nip"; rt "a68rt_leave"
      | _ => lowerInto dest body; popFrame; rt "a68rt_leave"; rt "a68rt_pop"
      terminate (.br done)
      switchTo no
    match dest with
    | .stack => let _ ← lowerStack out; rt "a68rt_nip"
    | _ => lowerInto dest out; rt "a68rt_pop"
  -- can the alternatives be taken inline?
  let mut infos : Array (ElemInfo × Ty) := #[]
  let mut inlineOk := true
  for (m, slot, body) in alts do
    let mr ← resolve m
    match elemInfo mr, tyOf mr with
    | some info, some ty => infos := infos.push (info, ty)
    | _, _ => inlineOk := false
    if slot.isSome && (CodeGen.hasOtherFn body || CodeGen.slotEscapes (fun _ => false) 0 0 body) then
      inlineOk := false
  -- where the united value is: a cell, or an element of a row of unions in a cell
  let src : Option (Nat × Nat × Option Core × Bool × List Mode) ← do   -- depth, slot, index, via a name, constituents
    match CodeGen.strip sel with
    | .loadCell d s | .deref (.refCell d s) =>
      match ← slotMode d s with
      | some m =>
        match ← resolve m with
        | .union cs => pure (some (d, s, none, false, cs))
        | _ => pure none
      | none => pure none
    | .slice base [.index e] viaRef | .deref (.slice base [.index e] viaRef) =>
      match ← cellBase base with
      | some (d, s, _) =>
        match ← slotMode d s with
        | some m =>
          match ← resolve m with
          | .row 1 _ em =>
            match ← resolve em with
            | .union cs => pure (some (d, s, some e, viaRef, cs))
            | _ => pure none
          | _ => pure none
        | none => pure none
      | none => pure none
    | _ => pure none
  match inlineOk, src with
  | true, some (d, s, idx, viaRef, cs) =>
    match ← cellAddr d s with
    | none => let _ ← lowerStack sel; general; terminate (.br done)
    | some (b, off) =>
      let i : Option Opnd ← match idx with
        | some e => pure (some (← toScalar (← lower e) (.int 0)))
        | none => pure none
      let slow ← newBlock
      -- the address of the united value
      let fid ← cellFid d
      let (p, o, pk) : Var × Opnd × Nat ← match i with
        | none => pure (b, ki off, KCELL)
        | some iv =>
          let (store, eo, _) ← selAddr b off 1 #[iv] [] slow false (some (fid, s))
          pure (store, eo, KSLOT)
      let tag ← ld "i32" .i64 p o pk
      guard (.v (← binv .i1 .eq (.v tag) (ki T_UNION))) slow
      let ao ← binv .i64 .addW o (ki 4)
      let vm ← ld "i32" .i64 p (.v ao) pk
      let bo ← binv .i64 .addW o (ki 8)
      let box ← ld "ptr" .ptr p (.v bo) pk
      let itag ← ld "i32" .i64 box (ki 24) KSLOT
      guard (.v (← binv .i1 .ne (.v itag) (ki T_UNION))) slow
      let mut k := 0
      for (m, slot, body) in alts do
        let (info, ty) := infos[k]!
        k := k + 1
        let mi ← putMode m
        let yes ← newBlock; let no ← newBlock; let ask ← newBlock
        -- Conformity resolved statically: the value's mode index is one a unite gave it,
        -- normally that of a constituent of the union (as written or as resolved), and
        -- whether such a mode conforms to the alternative is known here (`Mode.eqv`, the
        -- runtime's `mode_eqv`).  Only an index the compiler did not enumerate asks the
        -- runtime.
        let tab := (← get).modeTab
        let mr ← resolve m
        let mut cands : List (Int × Bool) := [((mi : Int), true)]
        for c in cs do
          for c' in [c, Mode.resolve tab c] do
            let ci ← putMode c'
            if !(cands.any (·.1 == (ci : Int))) then cands := cands ++ [((ci : Int), Mode.eqv tab mr c')]
        terminate (.switch (.v vm) (cands.toArray.map fun (ci, ok) => (ci, if ok then yes else no)) ask)
        switchTo ask
        let ok ← rtv "a68rt_conforms" #[ku mi, .v vm]
        terminate (.condBr (.v ok) yes no)
        switchTo yes
        match slot with
        | some _ =>
          let v ← valGet box (ki 24) info ty slow KSLOT
          pushFrame #[some m] #[some { v := v, m := m }] false none
          lowerInto dest body
          popFrame
        | none => lowerInto dest body
        flushPending
        terminate (.br done)
        switchTo no
      lowerInto dest out
      terminate (.br done)
      switchTo slow
      -- the general path, with the index already evaluated
      slowPath slow none do
        match i with
        | none => let _ ← lowerStack sel
        | some iv =>
          match CodeGen.strip sel with
          | .slice base _ _ => let _ ← lowerStack base; rt "a68rt_push_int" #[iv]; rt "a68rt_slice" #[ku 1, ki 0, kb viaRef]
          | .deref (.slice base _ _) =>
            let _ ← lowerStack base; rt "a68rt_push_int" #[iv]; rt "a68rt_slice" #[ku 1, ki 0, kb viaRef]; rt "a68rt_deref"
          | _ => let _ ← lowerStack sel
        general
      terminate (.br done)
  | _, _ => let _ ← lowerStack sel; general; terminate (.br done)
  switchTo done

partial def lowerGoto (l : Nat) : L Unit := do
  let fb := (← get).fb
  match fb.labelBlk.find? (·.1 == l) with
  | some (_, b) => terminate (.br b)
  | none => rt "a68rt_raise_jump" #[ku l]; retFn
  -- whatever follows is unreachable
  let dead ← newBlock
  switchTo dead

/-- A loop: the counter is a variable; the body gets a frame holding the counter's cell
    when the loop declares one. -/
partial def lowerLoop (slot : Option Nat) (f b : Core) (t : Option Core) (w : Option Core) (body : Core) : L Unit := do
  let from_ ← toScalar (← lower f) (.int 0)
  let by_ ← toScalar (← lower b) (.int 0)
  let to_ : Option Opnd ← match t with
    | some tc => pure (some (← toScalar (← lower tc) (.int 0)))
    | none => pure none
  -- Which rows does the body reach inline, and does it call anything that could change a
  -- cell or a store?  A trial lowering tells; then, for each such row whose frame exists
  -- before the loop, the descriptor and store are read once before the loop and kept in
  -- variables (recomputed after any slow path), so that the accesses are register-based.
  let snapshot ← get
  modify fun st => { st with rowUses := #[], slowRanges := #[], cellCalls := #[], hardTraps := 0,
                             prowReads := #[], prowWrites := #[], prowSeen := [] }
  let v0 := (← get).fb.vars.size
  let blk0 := (← get).fb.blocks.size
  lowerLoopBody slot from_ by_ to_ w body
  let blk1 := (← get).fb.blocks.size
  let uses := (← get).rowUses
  let safe ← callFree blk0 blk1
  -- may the loop's checks be deferred to its end?  Only a counted loop, outside another
  -- such region and not in a second run, whose body is repeatable (calls only what a
  -- second run may repeat, reaches no row through the runtime, reads no promoted row it
  -- writes), has no jump, WHILE or label, and emits no check that cannot be deferred
  let trialSt ← get
  let (rep, mods) ← repeatable blk0 blk1 v0
  -- the promoted rows the loop both reads and writes: a second run needs them as they
  -- were, so they are copied before the loop (a loop long enough to be worth the copy)
  let rw : List PRow := trialSt.prowSeen.filter fun pr =>
    trialSt.prowWrites.contains pr.data[0]!.id && trialSt.prowReads.contains pr.data[0]!.id
  let deferOK := w.isNone && snapshot.defer.isNone && !snapshot.noDefer && rep
    && (rw.isEmpty || to_.isSome)
    && trialSt.slowRanges.isEmpty && trialSt.cellCalls.isEmpty && trialSt.hardTraps == 0
    && !hasJumpsOrWhile body
  set snapshot
  let mut added : List RowCache := []
  if safe then
    let fids := (← get).fb.frames.map (·.fid)
    let mut seen : List (Nat × Nat × Int) := []
    for (fid, sl, ek, dims) in uses do
      if seen.contains (fid, sl, ek) then continue
      seen := (fid, sl, ek) :: seen
      -- only a frame in place before the loop, and no cache of it already in scope
      if !(fids.contains fid || fid ≥ 1000000) then continue
      if (← lookupCache fid sl ek).isSome then continue
      let valid ← newVar .i1; let rcOK ← newVar .i1
      let r ← newVar .ptr; let store ← newVar .ptr; let off ← newVar .i64; let n ← newVar .i64
      let mut dim : Array (Var × Var × Var) := #[]
      for _ in [0:dims] do
        dim := dim.push (← newVar .i64, ← newVar .i64, ← newVar .i64)
      let c : RowCache := { fid := fid, slot := sl, ek := ek, dims := dims, valid := valid, rcOK := rcOK,
                            r := r, store := store, off := off, dim := dim, n := n }
      slowPath.recache c
      added := c :: added
  modify fun st => { st with caches := added ++ st.caches }
  if deferOK then
    let cont ← newBlock
    -- with rows to copy: only a loop of at least 32 steps that covers its rows takes the
    -- fast form; otherwise the loop is lowered as usual (its inner loops may still form
    -- regions of their own)
    let checkedB ← newBlock
    if !rw.isEmpty then
      let some tv := to_ | pure ()
      -- the number of steps: (to - from) / by + 1 (a zero step: never worth it)
      let n ← binv .i64 .subW tv from_
      let byZero ← binv .i1 .eq by_ (ki 0)
      let b1 ← newVar .i64; emit (.set b1 (.select (.v byZero) (ki 1) by_))
      let steps ← binv .i64 .overW (.v n) (.v b1)
      let n1 ← binv .i64 .addW (.v steps) (ki 1)
      -- a copy is worth it only for a loop of at least 32 steps that covers at least an
      -- eighth of every row it would copy
      let mut short ← binv .i1 .lt (.v n1) (ki 32)
      short ← binv .i1 .orB (.v short) (.v byZero)
      for pr in rw do
        let e0 ← binv .i64 .subW (.v pr.hi[0]!) (.v pr.lo[0]!)
        let e0 ← binv .i64 .addW (.v e0) (ki 1)
        let cnt ← binv .i64 .mulW (.v e0) (.v pr.ext1)
        let work ← binv .i64 .mulW (.v n1) (ki 8)
        let small ← binv .i1 .lt (.v work) (.v cnt)
        short ← binv .i1 .orB (.v short) (.v small)
      let fastB ← newBlock; let normalB ← newBlock
      terminate (.condBr (.v short) normalB fastB)
      switchTo normalB
      lowerLoopBody slot from_ by_ to_ w body
      terminate (.br cont)
      switchTo fastB
      -- the copies: the elements and defined bytes of each such row, into shadows
      -- allocated on first use
      for pr in rw do
        let e0 ← binv .i64 .subW (.v pr.hi[0]!) (.v pr.lo[0]!)
        let e0 ← binv .i64 .addW (.v e0) (ki 1)
        let neg ← binv .i1 .lt (.v e0) (ki 0)
        let cnt0 ← newVar .i64; emit (.set cnt0 (.select (.v neg) (ki 0) (.v e0)))
        let cnt ← binv .i64 .mulW (.v cnt0) (.v pr.ext1)
        for f in [0:pr.fields.size] do
          let (info, _, _) := pr.fields[f]!
          let bytes ← binv .i64 .mulW (.v cnt) (ki info.es)
          for (sh, src, nb) in [(pr.shadowD[f]!, pr.data[f]!, bytes), (pr.shadowF[f]!, pr.flags[f]!, cnt)] do
            let isNull ← binv .i1 .eq (.v sh) (.k .ptr (.i 0))
            let allocB ← newBlock; let haveB ← newBlock
            terminate (.condBr (.v isNull) allocB haveB)
            switchTo allocB
            let p ← natv "a68n_alloc" .ptr #[.v nb]
            emit (.set sh (.opnd (.v p)))
            terminate (.br haveB)
            switchTo haveB
            emit (.call (.nat "a68n_memcpy") #[.v sh, .v src, .v nb])
    -- the registers the loop assigns, saved for a second run
    let mut saved : List (Var × Var) := []
    for v in mods do
      let sv ← newVar v.ty
      emit (.set sv (.opnd (.v v)))
      saved := (v, sv) :: saved
    let bad ← newVar .i1
    emit (.set bad (.opnd (kb false)))
    modify fun st => { st with defer := some { bad := bad } }
    lowerLoopBody slot from_ by_ to_ w body
    flushPending
    modify fun st => { st with defer := none }
    -- a failure: back to the entry state, then the loop again with its checks in place,
    -- which stops at the first failure as the evaluator does
    let rerunB ← newBlock
    terminate (.condBr (.v bad) rerunB cont)
    switchTo rerunB
    for (v, sv) in saved do emit (.set v (.opnd (.v sv)))
    for pr in rw do
      let e0 ← binv .i64 .subW (.v pr.hi[0]!) (.v pr.lo[0]!)
      let e0 ← binv .i64 .addW (.v e0) (ki 1)
      let neg ← binv .i1 .lt (.v e0) (ki 0)
      let cnt0 ← newVar .i64; emit (.set cnt0 (.select (.v neg) (ki 0) (.v e0)))
      let cnt ← binv .i64 .mulW (.v cnt0) (.v pr.ext1)
      for f in [0:pr.fields.size] do
        let (info, _, _) := pr.fields[f]!
        let bytes ← binv .i64 .mulW (.v cnt) (ki info.es)
        emit (.call (.nat "a68n_memcpy") #[.v pr.data[f]!, .v pr.shadowD[f]!, .v bytes])
        emit (.call (.nat "a68n_memcpy") #[.v pr.flags[f]!, .v pr.shadowF[f]!, .v cnt])
    terminate (.br checkedB)
    switchTo checkedB
    modify fun st => { st with noDefer := true }
    lowerLoopBody slot from_ by_ to_ w body
    modify fun st => { st with noDefer := false }
    terminate (.br cont)
    switchTo cont
  else
    lowerLoopBody slot from_ by_ to_ w body
  modify fun st => { st with caches := st.caches.drop added.length }

/-- The loop proper, from its evaluated bounds. -/
partial def lowerLoopBody (slot : Option Nat) (from_ by_ : Opnd) (to_ : Option Opnd) (w : Option Core) (body : Core) : L Unit := do
  -- a counter running by 1 between literal bounds has a known interval
  let counterRange : Option (Int × Int) := match from_, by_, to_ with
    | .k _ (.i a), .k _ (.i 1), some (.k _ (.i b)) => if a ≤ b then some (a, b) else none
    | _, _, _ => none
  let i ← newVar .i64
  emit (.set i (.opnd from_))
  let head ← newBlock; let bodyB ← newBlock; let exitB ← newBlock; let stepB ← newBlock
  terminate (.br head)
  switchTo head
  -- the termination test: by > 0 ∧ i > to, or by < 0 ∧ i < to
  match to_ with
  | some tv =>
    let pos ← newVar .i1; emit (.set pos (.bin .gt by_ (ki 0)))
    let over ← newVar .i1; emit (.set over (.bin .gt (.v i) tv))
    let c1 ← newVar .i1; emit (.set c1 (.bin .andB (.v pos) (.v over)))
    let neg ← newVar .i1; emit (.set neg (.bin .lt by_ (ki 0)))
    let under ← newVar .i1; emit (.set under (.bin .lt (.v i) tv))
    let c2 ← newVar .i1; emit (.set c2 (.bin .andB (.v neg) (.v under)))
    let stop ← newVar .i1; emit (.set stop (.bin .orB (.v c1) (.v c2)))
    terminate (.condBr (.v stop) exitB bodyB)
  | none => terminate (.br bodyB)
  switchTo bodyB
  -- the counter stays a variable when nothing inside needs a cell for it
  let others := CodeGen.hasOtherFn body || (match w with | some e => CodeGen.hasOtherFn e | none => false)
  let ok := CodeGen.assignsNatively CodeGen.CTy.i64
  let promote := match slot with
    | some sl => !others && sl == 0 && !(CodeGen.slotEscapesV ok 0 sl body
        || (match w with | some e => CodeGen.slotEscapes ok 0 sl e | none => false))
    | none => !others
  let pushed := !promote
  let frameSize := if slot.isSome then 1 else 0
  let mut cells : Option Var := none
  if pushed then
    cells := some (← rtv "a68rt_enter" #[ku frameSize])
    match slot with
    | some sl => rt "a68rt_set_int" #[ku 0, ku sl, .v i]
    | none => pure ()
  pushFrame (if slot.isSome then #[some (.int 0)] else #[])
    (if promote && slot.isSome then #[some { v := i, m := .int 0, range := counterRange }] else #[]) pushed cells
  match w with
  | some wc =>
    let cnd ← toScalar (← lower wc) .bool
    let go ← newBlock; let leaveB ← newBlock
    terminate (.condBr cnd go leaveB)
    switchTo leaveB
    if pushed then rt "a68rt_leave"
    terminate (.br exitB)
    switchTo go
  | none => pure ()
  lowerVoid body
  flushPending
  popFrame
  if pushed then rt "a68rt_leave"
  terminate (.br stepB)
  switchTo stepB
  let ni ← newVar .i64
  emitBin ni .addI (.v i) by_
  emit (.set i (.opnd (.v ni)))
  terminate (.br head)
  switchTo exitB

/-- A block: its frame, its statements, its labels.  Yields the value of the last unit
    when one is wanted. -/
partial def lowerBlock (size : Nat) (stmts : Array CoreStmt) (wantValue : Bool) : L Res := do
  let modes : Array (Option Mode) := Id.run do
    let mut a : Array (Option Mode) := Array.replicate size none
    for st in stmts do
      match st with
      | .decl sl m _ => if sl < size then a := a.set! sl (some m)
      | _ => pure ()
    return a
  let hasLabels := stmts.any fun st => match st with | .label _ => true | _ => false
  let hasJumps := stmts.any fun st => match st with | .label _ | .exit => true | _ => false
  let vp := CodeGen.voidPositions stmts wantValue
  -- which slots become variables: the C back end's escape analysis decides
  let plan := CodeGen.planFrame 0 size modes stmts wantValue (← get).modeTab
  let mut pvars : Array (Option PVar) := #[]
  for i in [0:size] do
    match (plan.vars[i]?).join, (modes[i]?).join with
    | some (_, cty, u), some m =>
      let ty : Ty := match cty with | .i64 => .i64 | .f64 => .f64 | .u8 => .i1 | .u32 => .i32 | .u64 => .i64
      let v ← newVar ty
      let flag ← if u then some <$> newVar .i1 else pure none
      match flag with
      | some fl => emit (.set fl (.opnd (kb false)))
      | none => pure ()
      pvars := pvars.push (some { v := v, m := m, flag := flag })
    | _, _ => pvars := pvars.push none
  -- a non-flexible row variable declared by a generator with literal, non-empty bounds
  -- keeps those bounds for life
  let mut bounds : Array (Option (List (Int × Int))) := Array.replicate size none
  for st in stmts do
    match st with
    | .decl sl m init =>
      if sl < size then
        match ← resolve m, CodeGen.strip init with
        | .row dims false _, .newRow bs _ false =>
          let lits : Option (List (Int × Int)) := bs.mapM fun (l, u) =>
            match CodeGen.strip l, CodeGen.strip u with
            | .lit (.int lo), .lit (.int hi) => if lo ≤ hi then some (lo, hi) else none
            | _, _ => none
          match lits with
          | some ls => if ls.length == dims then bounds := bounds.set! sl (some ls)
          | none => pure ()
        | _, _ => pure ()
    | _ => pure ()
  -- rows that never escape become native arrays (the C back end's analysis decides)
  let mut prows : Array (Option PRow) := #[]
  for i in [0:size] do
    match (plan.rows[i]?).join with
    | some rv =>
      if !rv.umodes.isEmpty || rv.dims < 1 || rv.dims > 2 then prows := prows.push none else
      let ctys : Array CodeGen.CTy := if rv.fields.isEmpty then #[rv.ty] else rv.fields
      let mut fields : Array (ElemInfo × Ty × Mode) := #[]
      let mut okF := true
      for t in ctys do
        let m := t.toMode
        match elemInfo m, tyOf m with
        | some info, some ty => fields := fields.push (info, ty, m)
        | _, _ => okF := false
      if !okF then prows := prows.push none else
      let mut lo : Array Var := #[]; let mut hi : Array Var := #[]
      for _ in [0:rv.dims] do
        lo := lo.push (← newVar .i64); hi := hi.push (← newVar .i64)
      let ext1 ← newVar .i64
      let mut data : Array Var := #[]; let mut flags : Array Var := #[]
      let mut shadowD : Array Var := #[]; let mut shadowF : Array Var := #[]
      for _ in [0:fields.size] do
        let dv ← newVar .ptr; let fv ← newVar .ptr; let sd ← newVar .ptr; let sf ← newVar .ptr
        for v in [dv, fv, sd, sf] do emit (.set v (.opnd (.k .ptr (.i 0))))
        data := data.push dv; flags := flags.push fv; shadowD := shadowD.push sd; shadowF := shadowF.push sf
      prows := prows.push (some { dims := rv.dims, lo := lo, hi := hi, ext1 := ext1, fields := fields, data := data, flags := flags,
                                  litBounds := (bounds[i]?).join, shadowD := shadowD, shadowF := shadowF })
    | none => prows := prows.push none
  let pushed := plan.pushed || (List.range size).any fun i => (pvars[i]?.join).isNone && (prows[i]?.join).isNone
  -- the routines with plain entry points this block declares; a routine sees those of its
  -- own run of consecutive routine declarations and of the runs before it, since no unit
  -- can run between the declarations of a run
  let mut procsAll : Array (Option (Nat × CodeGen.NatSig × Bool)) := Array.replicate size none
  let mut runOf : Array Nat := Array.replicate size 0
  let mut runNo := 0
  let mut inRun := false
  -- the routines that cannot complete a jump to a label outside themselves: a call of
  -- one needs no check of the jump flag afterwards
  let routines : List (Nat × Core) := stmts.toList.filterMap fun st => match st with
    | .decl sl _ init => match CodeGen.strip init with
      | .routine _ _ body => some (sl, body)
      | _ => none
    | _ => none
  let jumpFree := jumpFreeSet routines
  for st in stmts do
    match st with
    | .decl sl dm init =>
      match CodeGen.strip init, ← resolve dm with
      | .routine np fsz body, dmr@(.proc _ _) =>
        if !inRun then runNo := runNo + 1
        inRun := true
        match CodeGen.natSigOf dmr np fsz body with
        | some sg =>
          if sl < size && pushed && (pvars[sl]?.join).isNone then
            let k ← reserveNative
            procsAll := procsAll.set! sl (some (k, sg, jumpFree.contains sl))
            runOf := runOf.set! sl runNo
        | none => pure ()
      | _, _ => inRun := false
    | _ => inRun := false
  let visible (r : Nat) : Array (Option (Nat × CodeGen.NatSig × Bool)) :=
    (Array.range size).map fun i => if runOf[i]! ≤ r then procsAll[i]! else none
  runNo := 0
  inRun := false
  -- where a jump lands: the depths to return to
  let depths : Option (Var × Var) ← if hasLabels then do
      let e ← rtv "a68rt_env_depth"
      let s ← rtv "a68rt_stack_depth"
      pure (some (e, s))
    else pure none
  -- the blocks the labels of this block land in
  let mut lbl : Array (Nat × Nat) := #[]
  for st in stmts do
    match st with
    | .label id => lbl := lbl.push (id, ← newBlock)
    | _ => pure ()
  modify fun s => { s with fb := { s.fb with labelBlk := s.fb.labelBlk ++ lbl } }
  let cells : Option Var ← if pushed then some <$> rtv "a68rt_enter" #[ku size] else pure none
  pushFrame modes pvars pushed cells bounds prows
  -- the bounds each promoted row was declared with, as expressions, for the definedness
  -- analysis: a loop nest over exactly them assigning every element makes it known defined
  let declBounds : Array (Option (List (Core × Core))) := stmts.foldl (fun acc st =>
    match st with
    | .decl sl _ init =>
      match CodeGen.strip init with
      | .newRow bs _ _ => if sl < size then acc.set! sl (some bs) else acc
      | _ => acc
    | _ => acc) (Array.replicate size none)
  -- the scalar mode every unit that may yield the block's value has, when they agree: the
  -- value then goes into a variable, so that it survives the frame and needs no stack
  let varTy : Option (Ty × Mode) ← if wantValue then do
      let mut r : Option (Option (Ty × Mode × Mode)) := none   -- `some none`: they disagree
      for i in [0:stmts.size] do
        if vp[i]! == false then
          match stmts[i]! with
          | .unit e =>
            let this : Option (Ty × Mode × Mode) ← match ← modeOf e with
              | some m => do let mr ← resolve m; pure ((tyOf mr).map fun ty => (ty, m, mr))
              | none => pure none
            match this, r with
            | some t, none => r := some (some t)
            | some t, some (some t') => if t.2.2 != t'.2.2 then r := some none
            | _, _ => r := some none
          | _ => pure ()
      pure ((r.bind id).map fun (ty, m, _) => (ty, m))
    else pure none
  -- with jumps and no such variable, a placeholder on the stack takes the value
  let onStack := wantValue && hasJumps && varTy.isNone
  if onStack then rt "a68rt_push_void"
  let endB ← newBlock
  let mut result : Res := .stack
  let mut produced := false
  let dest : Option (Ty × Var × Mode) ← match varTy with
    | some (ty, m) => do let v ← newVar ty; pure (some (ty, v, m))
    | none => pure none
  for i in [0:stmts.size] do
    -- which routines a call in this statement may go to directly
    match stmts[i]! with
    | .decl _ _ init =>
      match CodeGen.strip init with
      | .routine _ _ _ => if !inRun then runNo := runNo + 1; inRun := true
      | _ => inRun := false
    | _ => inRun := false
    setProcs (visible runNo)
    match stmts[i]! with
    | .decl slot _ init =>
      match CodeGen.strip init, modes[slot]?.join with
      | .routine _ _ _, some pm@(.proc _ _) => modify fun st => { st with procMode := some pm }
      | .newRow _ _ _, some m =>
        -- a row of a primitive mode starts life as a leaf store, which the inline element
        -- access reads
        match ← resolve m with
        | .row _ _ em =>
          match elemInfo (← resolve em) with
          | some info => modify fun st => { st with rowHint := some info.ek }
          | none => pure ()
        | _ => pure ()
      | _, _ => pure ()
      let boxedIdx := (← get).fns.size
      match (pvars[slot]?).join, (prows[slot]?).join with
      | _, some pr =>
        -- the bounds, in order, then the arrays (zeroed: every element undefined)
        match CodeGen.strip init with
        | .newRow bs _ _ =>
          let mut k := 0
          for (l, u) in bs do
            if k < pr.dims then
              let lv ← toScalar (← lower l) (.int 0)
              let uv ← toScalar (← lower u) (.int 0)
              emit (.set pr.lo[k]! (.opnd lv)); emit (.set pr.hi[k]! (.opnd uv))
            k := k + 1
          -- extents, clamped at 0
          let mut n : Opnd := ki 1
          for kd in [0:pr.dims] do
            let e ← binv .i64 .subW (.v pr.hi[kd]!) (.v pr.lo[kd]!)
            let e1 ← binv .i64 .addW (.v e) (ki 1)
            let ext ← newVar .i64
            emit (.set ext (.opnd (.v e1)))
            let neg ← binv .i1 .lt (.v e1) (ki 0)
            let zB ← newBlock; let cont ← newBlock
            terminate (.condBr (.v neg) zB cont)
            switchTo zB
            emit (.set ext (.opnd (ki 0)))
            terminate (.br cont)
            switchTo cont
            if kd == 1 then emit (.set pr.ext1 (.opnd (.v ext)))
            n := .v (← binv .i64 .mulW n (.v ext))
          if pr.dims == 1 then emit (.set pr.ext1 (.opnd (ki 1)))
          for f in [0:pr.fields.size] do
            let (info, _, _) := pr.fields[f]!
            let bytes ← binv .i64 .mulW n (ki info.es)
            let dp ← natv "a68n_alloc" .ptr #[.v bytes]
            emit (.set pr.data[f]! (.opnd (.v dp)))
            let fp ← natv "a68n_alloc" .ptr #[n]
            emit (.set pr.flags[f]! (.opnd (.v fp)))
        | _ => pure ()
      | some _, none =>
        match CodeGen.strip init with
        | .lit .undef => pure ()      -- stays undefined; reads test the flag
        | _ => let _ ← storeScalar 0 slot init; pure ()
      | none, none =>
        match modes[slot]?.join with
        | some m =>
          if ← storeScalar 0 slot init then pure ()
          else
            lowerStackM init m
            rt "a68rt_store" #[ku 0, ku slot]
        | none =>
          let _ ← lowerStack init
          rt "a68rt_store" #[ku 0, ku slot]
      modify fun st => { st with procMode := none, rowHint := none }
      match CodeGen.strip init, procsAll[slot]?.join with
      | .routine np _ body, some (k, sg, _) =>
        lowerNative k sg np body
        if !CodeGen.outerRef 1 body then
          modify fun st => { st with nfnOf := st.nfnOf.push (boxedIdx, k) }
      | _, _ => pure ()
    | .unit e =>
      if vp[i]! == true then lowerVoid e
      else if onStack then do let _ ← lowerStack e; rt "a68rt_nip"
      else if wantValue then
        match dest with
        | some (ty, v, m) => lowerInto (.var ty v m) e; produced := true; result := .sc (.v v)
        | none => let _ ← lowerStack e; produced := true; result := .stack
      else lowerVoid e
      flushPending
      -- a loop nest that assigns every element of a promoted row of this block leaves it
      -- known defined for what follows (unconditionally: this is a statement of the block,
      -- and the block has no labels a jump could skip it by)
      if !hasLabels then
        for (sl, f) in initTargets (fun sl => (declBounds[sl]?).join) e do
          match (prows[sl]?).join with
          | some pr =>
            match f with
            | some k => if k < pr.fields.size then setKnown sl (some k) true
            | none => setKnown sl none true
          | none => pure ()
    | .label id =>
      match lbl.find? (·.1 == id), depths with
      | some (_, b), some (e, s) =>
        terminate (.br b)
        switchTo b
        rt "a68rt_jump_clear"
        let e1 ← newVar .i32
        emit (.set e1 (.bin .addI (.v e) (ku (if pushed then 1 else 0))))
        rt "a68rt_env_truncate" #[.v e1]
        rt "a68rt_stack_truncate" #[.v s]
        if onStack then rt "a68rt_push_void"
      | _, _ => pure ()
    | .exit => terminate (.br endB); let dead ← newBlock; switchTo dead
  if wantValue && !onStack && !produced then
    match dest with
    | some _ => pure ()
    | none => rt "a68rt_push_void"; result := .stack
  terminate (.br endB)
  switchTo endB
  popFrame
  -- the storage of promoted rows goes with the block; a jump out of the block leaves it
  for pr? in prows do
    match pr? with
    | some pr =>
      for f in [0:pr.fields.size] do
        emit (.call (.nat "a68n_free") #[.v pr.data[f]!])
        emit (.call (.nat "a68n_free") #[.v pr.flags[f]!])
        emit (.call (.nat "a68n_free") #[.v pr.shadowD[f]!])
        emit (.call (.nat "a68n_free") #[.v pr.shadowF[f]!])
    | none => pure ()
  if pushed then rt "a68rt_leave"
  return (if wantValue then result else .stack)

/-- A routine text as a function of its own (boxed convention); returns its index. -/
partial def lowerFunction (nparams frameSize : Nat) (body : Core) : L Nat := do
  let s ← get
  let idx := s.fns.size
  set { s with fns := s.fns.push none }
  let saved := s.fb
  let pmodes : Array (Option Mode) := match s.procMode with
    | some (.proc ps _) => (Array.range frameSize).map fun i => ps[i]?
    | _ => Array.replicate frameSize none
  let resultMode : Option Mode := match s.procMode with
    | some (.proc _ r) => some r
    | _ => none
  set { (← get) with fb := { name := s!"a68_fn{idx}", labels := CodeGen.labelsOf body }, procMode := none }
  let _ ← newBlock
  let cells ← rtv "a68rt_enter_args" #[ku frameSize, ku nparams]
  modify fun st => { st with fb := { st.fb with hoistAt := st.fb.blocks[0]!.instrs.size, entryDepth := 1 } }
  pushFrame pmodes #[] true (some cells)
  match resultMode with
  | some m => lowerStackM body m
  | none => lowerStack body
  popFrame
  rt "a68rt_leave"
  terminate .ret
  finishDispatch
  finishHoist
  let fb := (← get).fb
  let f : Func := { name := fb.name, vars := fb.vars, blocks := fb.blocks }
  modify fun st => { st with fns := st.fns.set! idx (some f), fb := saved }
  return idx

/-- The plain entry point `a68_nf{k}` of a routine.  Its parameters are variables, no
    run-time frame is pushed, and the frames outside it are those of its declaration, so
    its depths translate exactly as they would in the boxed entry point. -/
partial def lowerNative (k : Nat) (sg : CodeGen.NatSig) (nparams : Nat) (body : Core) : L Unit := do
  let s ← get
  let saved := s.fb
  let outer := s.fb.frames.map fun f => { f with vars := #[], cells := none, outer := true }
  let ptys := sg.ptys.map tyOfC
  let rty := sg.rty.map tyOfC
  set { s with fb := { name := s!"a68_nf{k}", labels := CodeGen.labelsOf body, retTy := rty }, procMode := none }
  let mut pvars : Array (Option PVar) := #[]
  for i in [0:nparams] do
    let v ← newVar (ptys[i]?.getD .i64)
    pvars := pvars.push (some { v := v, m := (sg.ptys[i]?.getD .i64).toMode })
  let pmodes : Array (Option Mode) := sg.ptys.map fun t => some t.toMode
  let _ ← newBlock
  modify fun st => { st with fb := { st.fb with frames := { modes := pmodes, vars := pvars, pushed := false } :: outer } }
  match sg.rty with
  | some t =>
    let rv ← newVar (tyOfC t)
    lowerInto (.var (tyOfC t) rv t.toMode) body
    terminate (.retVal (.v rv))
  | none =>
    lowerVoid body
    terminate .ret
  finishDispatch
  finishHoist
  let fb := (← get).fb
  let f : Func := { name := fb.name, vars := fb.vars, blocks := fb.blocks, params := ptys, ret := rty }
  modify fun st => { st with nfns := st.nfns.set! k (some f), fb := saved }

/-- Format items: the dynamic parts become holes computed by compiled code. -/
partial def lowerFmtItem (it : CoreFmt) : L CoreFmt := do
  match it with
  | .rep n dyn item =>
    let d ← match dyn with
      | some c => some <$> lowerHole c
      | none => pure none
    return .rep n d (← lowerFmtItem item)
  | .general args => return .general (← args.mapM lowerHole)
  | .group items => return .group (← items.mapM lowerFmtItem)
  | .include f => return .include (← lowerHole f)
  | other => return other

partial def lowerHole (c : Core) : L Core := do
  let s ← get
  let idx := s.holes.size
  set { s with holes := s.holes.push none }
  let saved := s.fb
  set { (← get) with fb := { name := s!"a68_hole{idx}" } }
  let _ ← newBlock
  lowerStack c
  terminate .ret
  finishDispatch
  finishHoist
  let fb := (← get).fb
  let f : Func := { name := fb.name, vars := fb.vars, blocks := fb.blocks }
  modify fun st => { st with holes := st.holes.set! idx (some f), fb := saved }
  return .hole 0 idx

end

/-- Lower a whole program. -/
def program (core : Core) (modes : Mode.Table) (ll : Nat) (regression : Bool)
    (echoes : List String) (srcName : String) : MIR.Program := Id.run do
  let (_, st) := (lowerFunction 0 0 core).run { modeTab := modes }
  let decls := modes.toArray.qsort (fun a b => a.1 < b.1)
  let st := decls.foldl (fun st (n, m) =>
      let (si, w) := st.w.str n
      let (mi, w) := Serial.putMode w m
      let (_, w) := w.add s!"n {si} {mi}"
      { st with w := w }) st
  return { fns := st.fns.map (·.getD default), holes := st.holes.map (·.getD default),
           nfns := st.nfns.map (·.getD default),
           nfnTab := (Array.range st.fns.size).map fun i => (st.nfnOf.find? (·.1 == i)).map (·.2),
           blob := st.w.render ++ "\n", src := srcName, ll := ll, regression := regression, echoes := echoes }

end A68.Lower
