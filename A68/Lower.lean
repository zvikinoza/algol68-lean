import A68.MIR
import A68.Serial
import A68.CodeGen

/-!
# A68.Lower — the core representation lowered to MIR

Milestone 1 of the LLVM back end (docs/LLVM-DESIGN.md).  Every construct is lowered;
values of primitive mode (`INT`, `REAL`, `BOOL`, `CHAR`, `BITS`) are computed in MIR
variables, and every other value goes through the runtime's operand stack, with the
protocol the C back end's general path uses (`A68.CodeGen.genNode`), so that routines
compiled either way can call each other.

A lowered expression yields a `Res`: its value is on the operand stack, or it is a
scalar operand.  Consumers ask for the form they need (`toStack`, `toScalar`).
-/
namespace A68.Lower
open A68.MIR

/-- What a lowered expression left behind. -/
inductive Res where
  | stack             -- on top of the operand stack
  | sc (o : Opnd)     -- a scalar
  deriving Inhabited

/-- Per-slot modes of a frame, for typed cell access. -/
structure FrameInfo where
  modes : Array (Option Mode) := #[]
  deriving Inhabited

/-- The function under construction. -/
structure FnB where
  name     : String := ""
  vars     : Array Ty := #[]
  blocks   : Array Block := #[]
  cur      : Nat := 0
  labels   : List Nat := []
  labelBlk : Array (Nat × Nat) := #[]     -- label id, block
  frames   : List FrameInfo := []
  dispatch : Option Nat := none            -- the block that acts on a pending jump
  dispatchSw : Option (Var × Nat) := none  -- its switch operand and the block that leaves the function
  deriving Inhabited

structure St where
  w        : Serial.Writer := {}
  fns      : Array (Option Func) := #[]
  holes    : Array (Option Func) := #[]
  fb       : FnB := {}
  modeTab  : Mode.Table := {}
  procMode : Option Mode := none
  deriving Inhabited

abbrev L := StateM St

-- ## The builder

def newVar (ty : Ty) : L Var := do
  let s ← get
  let id := s.fb.vars.size
  set { s with fb := { s.fb with vars := s.fb.vars.push ty } }
  return { id := id, ty := ty }

/-- A fresh block, not yet reached; its terminator is set when it is left. -/
def newBlock : L Nat := do
  let s ← get
  let id := s.fb.blocks.size
  set { s with fb := { s.fb with blocks := s.fb.blocks.push { term := .unreachable } } }
  return id

def emit (i : Instr) : L Unit :=
  modify fun s =>
    let b := s.fb.blocks[s.fb.cur]!
    { s with fb := { s.fb with blocks := s.fb.blocks.set! s.fb.cur { b with instrs := b.instrs.push i } } }

def terminate (t : Term) : L Unit :=
  modify fun s =>
    let b := s.fb.blocks[s.fb.cur]!
    { s with fb := { s.fb with blocks := s.fb.blocks.set! s.fb.cur { b with term := t } } }

def switchTo (b : Nat) : L Unit := modify fun s => { s with fb := { s.fb with cur := b } }

/-- Leave the current block for `b` and continue there. -/
def jumpTo (b : Nat) : L Unit := do terminate (.br b); switchTo b

def rtSigOf (n : String) : Option RtSig := (rtSigs.find? (·.1 == n)).map (·.2)

def rt (name : String) (args : Array Opnd := #[]) : L Unit := emit (.call (.rt name) args)

def rtv (name : String) (args : Array Opnd := #[]) : L Var := do
  let ret := match rtSigOf name with
    | some sg => sg.ret.ty.getD .i32
    | none => .i32
  let v ← newVar ret
  emit (.set v (.call (.rt name) args))
  return v

def natv (name : String) (ty : Ty) (args : Array Opnd) : L Var := do
  let v ← newVar ty
  emit (.set v (.call (.nat name) args))
  return v

def ki (n : Int) : Opnd := .k .i64 (.i n)
def ku (n : Nat) : Opnd := .k .i32 (.i n)
def kb (b : Bool) : Opnd := .k .i1 (.i (if b then 1 else 0))

def putStr (s : String) : L Nat := do
  let st ← get
  let (i, w) := st.w.str s
  set { st with w := w }
  return i

def putMode (m : Mode) : L Nat := do
  let st ← get
  let (i, w) := Serial.putMode st.w m
  set { st with w := w }
  return i

def putFmtList (items : List CoreFmt) : L Nat := do
  let st ← get
  let (i, w) := Serial.putFmtList st.w items
  set { st with w := w }
  return i

def resolve (m : Mode) : L Mode := do return Mode.resolve (← get).modeTab m

def tyOf : Mode → Option Ty
  | .int 0 => some .i64
  | .real 0 => some .f64
  | .bool => some .i1
  | .char => some .i32
  | .bits 0 => some .i64
  | _ => none

def tyOfM (m : Mode) : L (Option Ty) := do return tyOf (← resolve m)

/-- The mode of a slot, as recorded by the block or routine that declared it. -/
def slotMode (d s : Nat) : L (Option Mode) := do
  let fs := (← get).fb.frames
  match fs[d]? with
  | some f => return (f.modes[s]?).join
  | none => return none

def pushFn : Ty → String
  | .i64 => "a68rt_push_int" | .f64 => "a68rt_push_real" | .i1 => "a68rt_push_bool" | .i32 => "a68rt_push_char"
def popFn : Ty → String
  | .i64 => "a68rt_pop_int" | .f64 => "a68rt_pop_real" | .i1 => "a68rt_pop_bool" | .i32 => "a68rt_pop_char"
def cellFn : Mode → String
  | .bits _ => "a68rt_cell_bits" | .int _ => "a68rt_cell_int" | .real _ => "a68rt_cell_real"
  | .bool => "a68rt_cell_bool" | _ => "a68rt_cell_char"
def setCellFn : Mode → String
  | .bits _ => "a68rt_set_cell_bits" | .int _ => "a68rt_set_cell_int" | .real _ => "a68rt_set_cell_real"
  | .bool => "a68rt_set_cell_bool" | _ => "a68rt_set_cell_char"
def pushFnM : Mode → String
  | .bits _ => "a68rt_push_bits" | .int _ => "a68rt_push_int" | .real _ => "a68rt_push_real"
  | .bool => "a68rt_push_bool" | _ => "a68rt_push_char"
def popFnM : Mode → String
  | .bits _ => "a68rt_pop_bits" | .int _ => "a68rt_pop_int" | .real _ => "a68rt_pop_real"
  | .bool => "a68rt_pop_bool" | _ => "a68rt_pop_char"

/-- Put a result on the operand stack.  A scalar's mode is needed to tell BITS from INT,
    which share `i64`. -/
def toStack (r : Res) (m : Mode) : L Unit := do
  match r with
  | .stack => pure ()
  | .sc o =>
    let mr ← resolve m
    -- a mode the optimiser left unknown (`.void` on a shared subexpression): the scalar's
    -- own type decides, which only conflates INT with BITS
    rt (if (tyOf mr).isSome then pushFnM mr else pushFn o.ty) #[o]

def toScalar (r : Res) (m : Mode) : L Opnd := do
  match r with
  | .sc o => return o
  | .stack => return .v (← rtv (popFnM (← resolve m)))

-- ## Static modes of expressions, where the node tells

def dyopResult := CodeGen.dyopResult
def monopResult := CodeGen.monopResult

partial def modeOf (c : Core) : L (Option Mode) := do
  match c with
  | .at _ e => modeOf e
  | .lit (.int _) => return some (.int 0)
  | .lit (.real _) => return some (.real 0)
  | .lit (.bool _) => return some .bool
  | .lit (.char _) => return some .char
  | .lit (.bits _) => return some (.bits 0)
  | .loadCell d s => slotMode d s
  | .deref (.refCell d s) => slotMode d s
  | .deref (.at _ e) => modeOf (.deref e)
  | .dyop op m1 m2 _ _ =>
    if op == "LWB" || op == "UPB" || op == "ELEMS" then return some (.int 0)
    let r1 ← resolve m1
    let r2 ← resolve m2
    if op == "**" && r1 == .real 0 && r2 == .int 0 then return some (.real 0)
    -- the result tables assume operands of one mode; `INT * STRING` is a replication
    if r1 != r2 then return none
    return dyopResult op r1
  | .monop op m _ =>
    if op == "LWB" || op == "UPB" || op == "ELEMS" then return some (.int 0)
    return monopResult op (← resolve m)
  | .widen _ d _ => return some d
  | .cond _ t e => do
    match ← modeOf t with
    | some m => return some m
    | none => modeOf e
  | .andThen _ _ | .orElse _ _ | .identRel _ _ _ => return some .bool
  | .call f [_] =>
    match CodeGen.strip f with
    | .lit (.builtin n) => return (if CodeGen.nativeMathFns.contains n then some (.real 0) else none)
    | _ => return none
  | .seq _ b => modeOf b
  | .skip m => return some m
  | .caseInt _ (a :: _) _ => modeOf a
  | .block _ stmts _ _ =>
    -- the last unit gives the value, when the block has no labels
    if stmts.any (fun st => match st with | .label _ | .exit => true | _ => false) then return none
    match stmts.toList.reverse.find? (fun st => match st with | .unit _ => true | _ => false) with
    | some (.unit e) =>
      -- the unit may read the block's own slots, which are one frame deeper
      modify fun s => { s with fb := { s.fb with frames := {} :: s.fb.frames } }
      let r ← modeOf e
      modify fun s => { s with fb := { s.fb with frames := s.fb.frames.tail } }
      return r
    | _ => return none
  | _ => return none

/-- The scalar operation of a dyadic operator on operands of a primitive mode. -/
def binOf (op : String) (m : Mode) : Option BinOp :=
  match m, op with
  | .int _, "+" => some .addI | .int _, "-" => some .subI | .int _, "*" => some .mulI
  | .int _, "%" => some .overI | .int _, "%*" => some .modI | .int _, "**" => some .powI
  | .real _, "+" => some .addF | .real _, "-" => some .subF | .real _, "*" => some .mulF
  | .real _, "/" => some .divF | .real _, "**" => some .powFF
  | .bool, "AND" => some .andB | .bool, "OR" => some .orB | .bool, "XOR" => some .xorB
  | .bits _, "AND" => some .andU | .bits _, "OR" => some .orU | .bits _, "XOR" => some .xorU
  | _, "=" => some .eq | _, "/=" => some .ne
  | .bool, _ => none
  | _, "<" => some .lt | _, "<=" => some .le | _, ">" => some .gt | _, ">=" => some .ge
  | _, _ => none

def unOf (op : String) (m : Mode) : Option UnOp :=
  match op, m with
  | "-", .int _ => some .negI | "-", .real _ => some .negF
  | "ABS", .int _ => some .absI | "ABS", .real _ => some .absF | "ABS", .char => some .absC | "ABS", .bool => some .absB
  | "REPR", .int _ => some .reprI
  | "SIGN", .int _ => some .signI | "SIGN", .real _ => some .signF
  | "ODD", .int _ => some .oddI
  | "NOT", .bool => some .notB
  | "ENTIER", .real _ => some .entier | "ROUND", .real _ => some .round
  | _, _ => none

def isPlus (op : String) : Bool := op == "+"

-- ## Jumps

/-- The block that acts on a pending jump: to a label of this function, or out. -/
def dispatchBlock : L Nat := do
  match (← get).fb.dispatch with
  | some b => return b
  | none =>
    let saved := (← get).fb.cur
    let b ← newBlock
    modify fun s => { s with fb := { s.fb with dispatch := some b } }
    switchTo b
    let f ← rtv "a68rt_jump_pending"
    let k ← newVar .i32
    emit (.set k (.bin .subI (.v f) (ku 1)))
    let outB ← newBlock
    -- the labels are only all known when the function is complete: the switch is filled
    -- in by `finishDispatch`
    terminate (.switch (.v k) #[] outB)
    modify fun s => { s with fb := { s.fb with dispatchSw := some (k, outB) } }
    switchTo outB
    terminate .ret
    switchTo saved
    return b

/-- Complete the jump dispatch of the function with every label it has. -/
def finishDispatch : L Unit := do
  let fb := (← get).fb
  match fb.dispatch, fb.dispatchSw with
  | some b, some (k, outB) =>
    let cases := fb.labelBlk.map fun (l, blk) => ((l : Int), blk)
    modify fun s =>
      let blk := s.fb.blocks[b]!
      { s with fb := { s.fb with blocks := s.fb.blocks.set! b { blk with term := .switch (.v k) cases outB } } }
  | _, _ => pure ()

/-- After a call that may have left a jump pending. -/
def jumpCheck : L Unit := do
  let f ← rtv "a68rt_jump_pending"
  let c ← newVar .i1
  emit (.set c (.bin .ne (.v f) (ku 0)))
  let d ← dispatchBlock
  let cont ← newBlock
  terminate (.condBr (.v c) d cont)
  switchTo cont

def pushFrame (modes : Array (Option Mode)) : L Unit :=
  modify fun s => { s with fb := { s.fb with frames := { modes := modes } :: s.fb.frames } }
def popFrame : L Unit :=
  modify fun s => { s with fb := { s.fb with frames := s.fb.frames.tail } }

-- ## Expressions

mutual

/-- The value of `c`, wanted. -/
partial def lower (c : Core) : L Res := do
  match c with
  | .at p e => emit (.line p.line); lower e
  | .lit v => lowerLit v
  | .loadCell d s =>
    match (← slotMode d s).bind tyOf with
    | some _ =>
      let m := (← slotMode d s).get!
      return .sc (.v (← rtv (cellFn (← resolve m)) #[ku d, ku s]))
    | none => rt "a68rt_push_cell" #[ku d, ku s]; return .stack
  | .refCell d s => rt "a68rt_push_ref" #[ku d, ku s]; return .stack
  | .deref e =>
    match CodeGen.strip e with
    | .refCell d s =>
      match (← slotMode d s).bind tyOf with
      | some _ =>
        let m := (← slotMode d s).get!
        return .sc (.v (← rtv (cellFn (← resolve m)) #[ku d, ku s]))
      | none => rt "a68rt_push_cell" #[ku d, ku s]; return .stack
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
        rt "a68rt_push_ref" #[ku dd, ku ss]
        return .stack
      lowerAssignGeneral d s flex
    | _ => lowerAssignGeneral d s flex
  | .identRel l r isnt =>
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
        let v ← newVar .f64
        emit (.set v (.un (.math n) x))
        return .sc (.v v)
      else lowerCall f args
    | _, _ => lowerCall f args
  | .routine nparams frameSize body =>
    let idx ← lowerFunction nparams frameSize body
    rt "a68rt_push_proc" #[ku idx, ku nparams]
    return .stack
  | .slice arr idx viaRef =>
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
  | .select i e viaRef =>
    let _ ← lowerStack e
    rt "a68rt_select" #[ku i, kb viaRef]
    return .stack
  | .newRow bounds init flex =>
    let _ ← lowerStack init
    for (l, u) in bounds do lowerStackM l (.int 0); lowerStackM u (.int 0)
    rt "a68rt_new_row" #[ku bounds.length, kb flex]
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
        lowerCondInto (some (ty, v, m)) cc t e
        return .sc (.v v)
      | none => lowerCondInto none cc t e; return .stack
    | none => lowerCondInto none cc t e; return .stack
  | .caseInt sel alts out =>
    match ← modeOf c with
    | some m =>
      match tyOf (← resolve m) with
      | some ty =>
        let v ← newVar ty
        lowerCaseInto (some (ty, v, m)) sel alts out
        return .sc (.v v)
      | none => lowerCaseInto none sel alts out; return .stack
    | none => lowerCaseInto none sel alts out; return .stack
  | .caseConf sel alts out => lowerConformity sel alts out; return .stack
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
  match ← slotMode dd ss with
  | some m =>
    let mr ← resolve m
    match tyOf mr with
    | some _ =>
      match ← modeOf src with
      | some sm =>
        if (← resolve sm) == mr then
          let o ← toScalar (← lower src) mr
          rt (setCellFn mr) #[ku dd, ku ss, o]
          return true
        else return false
      | none => return false
    | none => return false
  | none => return false

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

partial def lowerDyop (op : String) (m1 m2 : Mode) (l r : Core) : L Res := do
  let r1 ← resolve m1
  let r2 ← resolve m2
  let general : L Res := do
    lowerStackM l m1; lowerStackM r m2
    rt "a68rt_dyop" #[ku (← putStr op), ku (← putMode m1), ku (← putMode m2)]
    return .stack
  -- REAL ** INT
  if op == "**" && r1 == .real 0 && r2 == .int 0 then
    let a ← toScalar (← lower l) r1
    let b ← toScalar (← lower r) r2
    let v ← newVar .f64
    emit (.set v (.bin .powFI a b))
    return .sc (.v v)
  if r1 != r2 then general else
  match tyOf r1, binOf op r1, dyopResult op r1 with
  | some _, some bop, some res =>
    let a ← toScalar (← lower l) r1
    let b ← toScalar (← lower r) r2
    let v ← newVar ((tyOf (← resolve res)).getD .i1)
    emit (.set v (.bin bop a b))
    return .sc (.v v)
  | _, _, _ => general

partial def lowerMonop (op : String) (m : Mode) (e : Core) : L Res := do
  let mr ← resolve m
  match tyOf mr, unOf op mr, monopResult op mr with
  | some _, some uop, some res =>
    let x ← toScalar (← lower e) mr
    let v ← newVar ((tyOf (← resolve res)).getD .i64)
    emit (.set v (.un uop x))
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
      else do let _ ← lowerAssignGeneral d s flex; rt "a68rt_pop"
    | _ => let _ ← lowerAssignGeneral d s flex; rt "a68rt_pop"
  | .cond cc t e => lowerCondInto none cc t e |> lowerVoidOf
  | .block size stmts _ _ => let _ ← lowerBlock size stmts false
  | .loop slot f b t w body => lowerLoop slot f b t w body
  | .caseInt sel alts out => lowerVoidOf (lowerCaseInto none sel alts out)
  | .caseConf sel alts out => lowerConformity sel alts out; rt "a68rt_pop"
  | .goto l => lowerGoto l
  | .stop => rt "a68rt_stop"
  | _ =>
    match ← lower c with
    | .stack => rt "a68rt_pop"
    | .sc _ => pure ()

/-- Run a lowering whose value went to the stack, and discard it. -/
partial def lowerVoidOf (act : L Unit) : L Unit := do act; rt "a68rt_pop"

/-- A conditional whose branches either assign a scalar variable or leave a value on
    the stack. -/
partial def lowerCondInto (dest : Option (Ty × Var × Mode)) (cc t e : Core) : L Unit := do
  let cond ← toScalar (← lower cc) .bool
  let tb ← newBlock; let eb ← newBlock; let done ← newBlock
  terminate (.condBr cond tb eb)
  switchTo tb; lowerInto dest t; terminate (.br done)
  switchTo eb; lowerInto dest e; terminate (.br done)
  switchTo done

/-- Compute `c` into the destination: a scalar variable, or the stack. -/
partial def lowerInto (dest : Option (Ty × Var × Mode)) (c : Core) : L Unit := do
  match dest with
  | none => lowerStack c
  | some (_, v, m) =>
    match c with
    | .at p e => emit (.line p.line); lowerInto dest e
    | .seq a b => lowerVoid a; lowerInto dest b
    | .cond cc t e => lowerCondInto dest cc t e
    | .caseInt sel alts out => lowerCaseInto dest sel alts out
    | _ =>
      let o ← toScalar (← lower c) m
      emit (.set v (.opnd o))

partial def lowerCaseInto (dest : Option (Ty × Var × Mode)) (sel : Core) (alts : List Core) (out : Core) : L Unit := do
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
    terminate (.br done)
    i := i + 1
  switchTo dflt
  lowerInto dest out
  terminate (.br done)
  switchTo done

/-- A conformity clause; the value it yields goes to the stack. -/
partial def lowerConformity (sel : Core) (alts : List (Mode × Option Nat × Core)) (out : Core) : L Unit := do
  let _ ← lowerStack sel
  let done ← newBlock
  for (m, slot, body) in alts do
    let mi ← putMode m
    let ok ← rtv "a68rt_conform" #[ku mi, kb slot.isSome]
    let yes ← newBlock; let no ← newBlock
    terminate (.condBr (.v ok) yes no)
    switchTo yes
    if slot.isSome then
      rt "a68rt_enter" #[ku 1]
      rt "a68rt_bind_cell" #[ku 0, ku 0]
    else rt "a68rt_enter" #[ku 0]
    pushFrame #[if slot.isSome then some m else none]
    let _ ← lowerStack body
    popFrame
    rt "a68rt_nip"
    rt "a68rt_leave"
    terminate (.br done)
    switchTo no
  let _ ← lowerStack out
  rt "a68rt_nip"
  terminate (.br done)
  switchTo done

partial def lowerGoto (l : Nat) : L Unit := do
  let fb := (← get).fb
  match fb.labelBlk.find? (·.1 == l) with
  | some (_, b) => terminate (.br b)
  | none => rt "a68rt_raise_jump" #[ku l]; terminate .ret
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
  let frameSize := if slot.isSome then 1 else 0
  rt "a68rt_enter" #[ku frameSize]
  match slot with
  | some sl => rt "a68rt_set_int" #[ku 0, ku sl, .v i]
  | none => pure ()
  pushFrame (if slot.isSome then #[some (.int 0)] else #[])
  match w with
  | some wc =>
    let cnd ← toScalar (← lower wc) .bool
    let go ← newBlock; let leaveB ← newBlock
    terminate (.condBr cnd go leaveB)
    switchTo leaveB
    rt "a68rt_leave"
    terminate (.br exitB)
    switchTo go
  | none => pure ()
  lowerVoid body
  popFrame
  rt "a68rt_leave"
  terminate (.br stepB)
  switchTo stepB
  let ni ← newVar .i64
  emit (.set ni (.bin .addI (.v i) by_))
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
  let onStack := wantValue && stmts.any fun st => match st with | .label _ | .exit => true | _ => false
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
  rt "a68rt_enter" #[ku size]
  pushFrame modes
  if onStack then rt "a68rt_push_void"
  let endB ← newBlock
  let vp := CodeGen.voidPositions stmts wantValue
  let mut result : Res := .stack
  let mut produced := false
  -- the value of a scalar last unit goes into a variable, so that it survives the frame
  let lastTy : Option (Ty × Mode) ← if wantValue && !onStack then do
      match stmts.toList.reverse.find? (fun st => match st with | .unit _ => true | _ => false) with
      | some (.unit e) =>
        match ← modeOf e with
        | some m => pure ((tyOf (← resolve m)).map fun ty => (ty, m))
        | none => pure none
      | _ => pure none
    else pure none
  let dest : Option (Ty × Var × Mode) ← match lastTy with
    | some (ty, m) => do let v ← newVar ty; pure (some (ty, v, m))
    | none => pure none
  for i in [0:stmts.size] do
    match stmts[i]! with
    | .decl slot _ init =>
      match CodeGen.strip init, modes[slot]?.join with
      | .routine _ _ _, some pm@(.proc _ _) => modify fun st => { st with procMode := some pm }
      | _, _ => pure ()
      match modes[slot]?.join with
      | some m =>
        if ← storeScalar 0 slot init then pure ()
        else
          lowerStackM init m
          rt "a68rt_store" #[ku 0, ku slot]
      | none =>
        let _ ← lowerStack init
        rt "a68rt_store" #[ku 0, ku slot]
      modify fun st => { st with procMode := none }
    | .unit e =>
      if vp[i]! == true then lowerVoid e
      else if onStack then do let _ ← lowerStack e; rt "a68rt_nip"
      else if wantValue then
        match dest with
        | some d => lowerInto (some d) e; produced := true; result := .sc (.v d.2.1)
        | none => let _ ← lowerStack e; produced := true; result := .stack
      else lowerVoid e
    | .label id =>
      match lbl.find? (·.1 == id), depths with
      | some (_, b), some (e, s) =>
        terminate (.br b)
        switchTo b
        rt "a68rt_jump_clear"
        let e1 ← newVar .i32
        emit (.set e1 (.bin .addI (.v e) (ku 1)))
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
  rt "a68rt_leave"
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
  rt "a68rt_enter_args" #[ku frameSize, ku nparams]
  pushFrame pmodes
  match resultMode with
  | some m => lowerStackM body m
  | none => lowerStack body
  popFrame
  rt "a68rt_leave"
  terminate .ret
  finishDispatch
  let fb := (← get).fb
  let f : Func := { name := fb.name, vars := fb.vars, blocks := fb.blocks }
  modify fun st => { st with fns := st.fns.set! idx (some f), fb := saved }
  return idx

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
           blob := st.w.render ++ "\n", src := srcName, ll := ll, regression := regression, echoes := echoes }

end A68.Lower
