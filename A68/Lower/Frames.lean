import A68.Optimizations.NativeCalls

/-!
# A68.Lower.Frames

Reading and writing promoted variables, the operand stack, static modes of expressions,
the scalar operator tables, jumps and dispatch, and the frame stack.
-/
namespace A68.Lower
open A68.MIR

def undefKind : Ty → Nat
  | .i64 => 0 | .f64 => 1 | .i1 => 2 | .i32 => 3 | .ptr => 0

/-- Read a promoted variable, reporting an undefined one as the evaluator would. -/
def readPVar (pv : PVar) : L Opnd := do
  match pv.flag with
  | none => return .v pv.v
  | some fl =>
    modify fun st => { st with hardTraps := st.hardTraps + 1 }
    let ok ← newBlock; let bad ← newBlock
    terminate (.condBr (.v fl) ok bad)
    switchTo bad
    let kind := if (← resolve pv.m) matches .bits _ then 4 else undefKind pv.v.ty
    rt "a68rt_undef_error" #[ku kind]
    terminate .unreachable
    switchTo ok
    return .v pv.v

def writePVar (pv : PVar) (o : Opnd) : L Unit := do
  emit (.set pv.v (.opnd o))
  match pv.flag with
  | some fl => emit (.set fl (.opnd (kb true)))
  | none => pure ()

def pushFn : Ty → String
  | .i64 => "a68rt_push_int" | .f64 => "a68rt_push_real" | .i1 => "a68rt_push_bool" | .i32 => "a68rt_push_char"
  | .ptr => "a68rt_push_int"   -- never lowered: a pointer is not an Algol 68 value
def popFn : Ty → String
  | .i64 => "a68rt_pop_int" | .f64 => "a68rt_pop_real" | .i1 => "a68rt_pop_bool" | .i32 => "a68rt_pop_char"
  | .ptr => "a68rt_pop_int"
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

/-- The mode of `row[idx]` when every indexer is a subscript. -/
partial def elemMode (rowMode : Mode) (idx : List CoreIdx) : L (Option Mode) := do
  match rowMode with
  | .row dims _ em =>
    if idx.length == dims && idx.all (fun ix => match ix with | .index _ => true | _ => false) then return some em
    return none
  | _ => return none


mutual

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
  | .deref e =>
    match ← modeOfRef e with
    | some m => return some m
    | none => return none
  | .slice base idx false =>
    -- an element of a row value held in a cell
    match CodeGen.strip base with
    | .loadCell d s =>
      match ← slotMode d s with
      | some m => elemMode (← resolve m) idx
      | none => return none
    | _ => return none
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
    -- every branch must have the mode: the optimiser folds a widened literal to the
    -- literal, so one branch of a LONG conditional may look like an INT
    match ← modeOf t, ← modeOf e with
    | some m, some m' => return (if (← resolve m) == (← resolve m') then some m else none)
    | _, _ => return none
  | .andThen _ _ | .orElse _ _ | .identRel _ _ _ => return some .bool
  | .call f args =>
    match CodeGen.strip f, args with
    | .lit (.builtin n), [_] => return (if CodeGen.nativeMathFns.contains n then some (.real 0) else none)
    | _, _ => natResultMode f
  | .seq _ b => modeOf b
  | .skip m => return some m
  | .caseInt _ alts out => do
    let mut r ← modeOf out
    for a in alts do
      match r, ← modeOf a with
      | some m, some m' => if (← resolve m) != (← resolve m') then r := none
      | _, _ => r := none
    return r
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

/-- The mode a reference expression designates: `&x`, `a[i]`, `f OF s`, `p` holding a name. -/
partial def modeOfRef (c : Core) : L (Option Mode) := do
  match c with
  | .at _ e => modeOfRef e
  | .refCell d s => slotMode d s
  | .loadCell d s | .deref (.refCell d s) =>
    match ← slotMode d s with
    | some m =>
      match ← resolve m with
      | .ref t => return some t
      | _ => return none
    | none => return none
  | .slice base idx true =>
    match ← modeOfRef base with
    | some m => elemMode (← resolve m) idx
    | none => return none
  | .select f e true =>
    match ← modeOfRef e with
    | some m =>
      match ← resolve m with
      | .struct fs => return (fs[f]?).map (·.2)
      | _ => return none
    | none => return none
  | _ => return none

end

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

/-- The pending jump, read from the runtime's flag inline. -/
def jumpFlag : L Var := natv "jump_flag" .i32 #[]

/-- Leave the function: a plain routine returns a dummy of its result type. -/
def retFn : L Unit := do
  terminate (match (← get).fb.retTy with | some t => .retVal (.k t (.i 0)) | none => .ret)

/-- The block that acts on a pending jump: to a label of this function, or out. -/
def dispatchBlock : L Nat := do
  match (← get).fb.dispatch with
  | some b => return b
  | none =>
    let saved := (← get).fb.cur
    let b ← newBlock
    modify fun s => { s with fb := { s.fb with dispatch := some b } }
    switchTo b
    let f ← jumpFlag
    let k ← newVar .i32
    emit (.set k (.bin .subI (.v f) (ku 1)))
    let outB ← newBlock
    -- the labels are only all known when the function is complete: the switch is filled
    -- in by `finishDispatch`
    terminate (.switch (.v k) #[] outB)
    modify fun s => { s with fb := { s.fb with dispatchSw := some (k, outB) } }
    switchTo outB
    retFn
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
  let f ← jumpFlag
  let c ← newVar .i1
  emit (.set c (.bin .ne (.v f) (ku 0)))
  let d ← dispatchBlock
  let cont ← newBlock
  terminate (.condBr (.v c) d cont)
  switchTo cont

def pushFrame (modes : Array (Option Mode)) (vars : Array (Option PVar) := #[]) (pushed : Bool := true)
    (cells : Option Var := none) (bounds : Array (Option (List (Int × Int))) := #[])
    (rows : Array (Option PRow) := #[]) : L Unit :=
  modify fun s =>
    let f : FrameInfo := { modes := modes, vars := vars, pushed := pushed, cells := cells, fid := s.nextFid, bounds := bounds, rows := rows }
    { s with nextFid := s.nextFid + 1, fb := { s.fb with frames := f :: s.fb.frames } }

/-- The routines the innermost frame's slots are known to hold. -/
def setProcs (procs : Array (Option (Nat × CodeGen.NatSig × Bool))) : L Unit :=
  modify fun s => match s.fb.frames with
    | f :: fs => { s with fb := { s.fb with frames := { f with procs := procs } :: fs } }
    | [] => s

def popFrame : L Unit :=
  modify fun s => { s with fb := { s.fb with frames := s.fb.frames.tail } }

end A68.Lower
