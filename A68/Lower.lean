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

/-- Where a lowered value goes. -/
inductive Dest where
  | void                       -- nowhere: the value is not wanted
  | stack                      -- the operand stack
  | var (t : Ty) (v : Var) (m : Mode)   -- a scalar variable
  deriving Inhabited

/-- What a lowered expression left behind. -/
inductive Res where
  | stack             -- on top of the operand stack
  | sc (o : Opnd)     -- a scalar
  deriving Inhabited

/-- A slot promoted to a MIR variable: the variable, its mode, and the flag that says it
    has been given a value, when reads must test for an undefined variable. -/
structure PVar where
  v    : Var
  m    : Mode
  flag : Option Var := none
  range : Option (Int × Int) := none   -- a loop counter with literal bounds: its interval
  deriving Inhabited

/-- A primitive element mode in a leaf store: its tag, its size in bytes, the memory width
    it is read and written with, and the kind of `a68rt_undef_error`. -/
structure ElemInfo where
  ek   : Int
  es   : Nat
  w    : String
  kind : Nat
  deriving Inhabited

def elemInfo : Mode → Option ElemInfo
  | .int 0 => some ⟨1, 8, "i64", 0⟩
  | .real 0 => some ⟨2, 8, "f64", 1⟩
  | .bool => some ⟨3, 1, "i8", 2⟩
  | .char => some ⟨4, 1, "i8", 3⟩
  | .bits 0 => some ⟨5, 8, "i64", 4⟩
  | _ => none

def T_REF : Int := 8
def T_STRUCT : Int := 10
def T_UNION : Int := 11
def K_SLOTS : Int := 1
def VIEW_OFF : Int := 4294967295

/-- A row variable promoted to native arrays: it never escapes (the C back end's escape
    analysis, `CodeGen.planFrame`), so it has no descriptor, no store and no collector
    object — its bounds are variables, and each element field (one for a row of a
    primitive mode, one per field for a row of structures) is an array allocated at the
    declaration and freed with the block, with a defined byte per element beside it. -/
structure PRow where
  dims   : Nat
  lo     : Array Var                 -- per dimension
  hi     : Array Var
  ext1   : Var                       -- the extent of the second dimension (1 for one)
  fields : Array (ElemInfo × Ty × Mode)
  data   : Array Var                 -- per field: the elements
  flags  : Array Var                 -- per field: the defined bytes
  known  : Array Bool := #[]         -- per field: every element is known to be defined here
  litBounds : Option (List (Int × Int)) := none   -- the declared bounds when literal
  shadowD : Array Var := #[]         -- per field: a copy of the elements, for a loop's second run (allocated on first use)
  shadowF : Array Var := #[]         -- per field: a copy of the defined bytes
  deriving Inhabited

/-- A frame as the lowering sees it: the modes of its slots, which slots are variables,
    and whether a run-time frame is pushed for it at all (a frame all of whose slots are
    variables needs none, and the depths of cell accesses skip it). -/
structure FrameInfo where
  modes  : Array (Option Mode) := #[]
  vars   : Array (Option PVar) := #[]
  pushed : Bool := true
  /-- per slot: the routine it certainly holds and its plain entry point, once a call can
      see its declaration -/
  procs  : Array (Option (Nat × CodeGen.NatSig × Bool)) := #[]   -- entry point, signature, cannot jump out
  /-- the first cell of the run-time frame, when it is pushed: cells are addressed from it -/
  cells  : Option Var := none
  /-- a frame of the enclosing function, kept for its `procs`: its cells are captured -/
  outer  : Bool := false
  /-- a number unique to the frame, for the row caches -/
  fid    : Nat := 0
  /-- per slot: the literal bounds a non-flexible row variable was declared with, which it
      keeps for life (an assignment of other bounds is an error) -/
  bounds : Array (Option (List (Int × Int))) := #[]
  /-- per slot: the native arrays a row variable was promoted to -/
  rows   : Array (Option PRow) := #[]
  deriving Inhabited

/-- What a loop keeps in variables about a row a cell holds, so that the elements are
    reached without re-reading the cell and the descriptor at every access (`recache`
    computes it; a slow path recomputes it).  `ek` is the leaf kind expected, 0 when the
    store must be one of slots. -/
structure RowCache where
  fid   : Nat
  slot  : Nat
  ek    : Int
  dims  : Nat
  valid : Var                     -- the cell holds a row whose store is as expected
  rcOK  : Var                     -- valid, and the store is unshared (a write may go inline)
  r     : Var                     -- the descriptor
  store : Var
  off   : Var
  dim   : Array (Var × Var × Var)  -- l, u, stride per dimension
  n     : Var                     -- the store's element count
  deriving Inhabited

/-- A region of deferred traps: a counted loop whose body makes no call and no jump, in
    which every check only sets a flag instead of branching, and every memory index is
    clamped, so that the body has no early exit — what LLVM's vectoriser needs.  When the
    flag is set at the loop's end (an erroneous program), the registers the loop assigned
    are restored to their values at its entry and the loop runs again in checked form,
    which stops at the first failure with its message: nothing observable happened
    between the point where the evaluator would have stopped and the second run, and the
    second run sees what the first saw, since a loop is only made such a region when it
    reads no array it writes. -/
structure DeferCtx where
  bad : Var       -- i1: some check failed in the loop so far
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
  retTy    : Option Ty := none             -- a plain routine: what it returns
  hoist    : Array Instr := #[]            -- instructions to insert at the entry, after the frame is pushed
  hoistAt  : Nat := 0                      -- where in block 0 they go
  entryDepth : Nat := 0                    -- how many frames the entry pushes (0 or 1)
  outerCells : List (Nat × Var) := []      -- per captured frame (0 = the declaring one): its cells
  lastLine : Option Nat := none            -- the line number in force since the block began or the last call
  curLine  : Nat := 0                      -- the line number of the code being lowered
  deriving Inhabited

structure St where
  w        : Serial.Writer := {}
  fns      : Array (Option Func) := #[]
  holes    : Array (Option Func) := #[]
  nfns     : Array (Option Func) := #[]    -- the plain entry points
  nfnOf    : Array (Nat × Nat) := #[]      -- boxed routine index, plain entry point usable from any environment
  fb       : FnB := {}
  modeTab  : Mode.Table := {}
  procMode : Option Mode := none
  rowHint  : Option Int := none            -- the leaf kind of the row generator being lowered
  nextFid  : Nat := 1
  caches   : List RowCache := []           -- the row caches in scope, innermost first
  rowUses  : Array (Nat × Nat × Int × Nat) := #[]   -- rows accessed inline: fid, slot, store kind, dims
  slowRanges : Array (Nat × Nat) := #[]    -- block ranges [from, to) that are slow paths
  cellCalls : Array (Nat × Nat) := #[]     -- (block, instruction) of runtime calls that change one named cell only
  defer    : Option DeferCtx := none       -- the region of deferred traps being lowered
  pendingF : List Var := []                -- REAL results of + - * in the region not yet tested for finiteness
  noDefer  : Bool := false                 -- lowering the checked second run of a region: no new region
  hardTraps : Nat := 0                     -- checks emitted that cannot be deferred (a trial counts them)
  prowReads : Array Nat := #[]             -- promoted rows read / written (by the variable of their first field)
  prowWrites : Array Nat := #[]
  prowSeen : List PRow := []               -- the promoted rows accessed, for their snapshots
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

/-- Append an instruction to the current block.  A line-number store that repeats the one
    in force is dropped: the number is read only by the runtime's error reporting, and a
    call resets what is known since the callee sets its own. -/
def emit (i : Instr) : L Unit :=
  modify fun s =>
    match i with
    | .line n =>
      if s.fb.lastLine == some n then { s with fb := { s.fb with curLine := n } } else
      let b := s.fb.blocks[s.fb.cur]!
      { s with fb := { s.fb with blocks := s.fb.blocks.set! s.fb.cur { b with instrs := b.instrs.push i }, lastLine := some n, curLine := n } }
    | _ =>
      let isCall := match i with | .call _ _ | .set _ (.call _ _) => true | _ => false
      let b := s.fb.blocks[s.fb.cur]!
      { s with fb := { s.fb with blocks := s.fb.blocks.set! s.fb.cur { b with instrs := b.instrs.push i },
                                 lastLine := if isCall then none else s.fb.lastLine } }

def terminate (t : Term) : L Unit :=
  modify fun s =>
    let b := s.fb.blocks[s.fb.cur]!
    { s with fb := { s.fb with blocks := s.fb.blocks.set! s.fb.cur { b with term := t } } }

def switchTo (b : Nat) : L Unit := modify fun s => { s with fb := { s.fb with cur := b, lastLine := none } }

/-- Leave the current block for `b` and continue there. -/
def jumpTo (b : Nat) : L Unit := do terminate (.br b); switchTo b

def rtSigOf (n : String) : Option RtSig := (rtSigs.find? (·.1 == n)).map (·.2)

def rt (name : String) (args : Array Opnd := #[]) : L Unit := emit (.call (.rt name) args)

def rtv (name : String) (args : Array Opnd := #[]) : L Var := do
  let ret := match rtSigOf name with
    | some sg => sg.ret.ty.getD .i32
    | none => panic! s!"a68lean: no signature for runtime function {name}"
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

/-- The MIR type of a C type of the C back end's signatures. -/
def tyOfC : CodeGen.CTy → Ty
  | .i64 => .i64 | .f64 => .f64 | .u8 => .i1 | .u32 => .i32 | .u64 => .i64

/-- Reserve the index of a plain entry point. -/
def reserveNative : L Nat := do
  let s ← get
  set { s with nfns := s.nfns.push none }
  return s.nfns.size

/-- The mode of a slot, as recorded by the block or routine that declared it. -/
def slotMode (d s : Nat) : L (Option Mode) := do
  let fs := (← get).fb.frames
  match fs[d]? with
  | some f => return (f.modes[s]?).join
  | none => return none

/-- The run-time depth of syntactic depth `d`: only pushed frames count.  Frames past the
    end of the list belong to enclosing functions and are always real. -/
def rtd (d : Nat) : L Nat := do
  let fs := (← get).fb.frames
  let mut r := 0
  let mut i := 0
  for f in fs do
    if i ≥ d then break
    if f.pushed then r := r + 1
    i := i + 1
  if d > fs.length then r := r + (d - fs.length)
  return r

def pvarOf (d s : Nat) : L (Option PVar) := do
  match (← get).fb.frames[d]? with
  | some f => return (f.vars[s]?).join
  | none => return none

/-- The address of cell `(d, s)`: a pointer to the first cell of its frame and a byte
    offset.  The frames of this function keep their cells pointer; a captured frame's is
    read once at the entry of the function (`hoist`), since frames never move and one on
    the environment chain is never collected. -/
def cellAddr (d s : Nat) : L (Option (Var × Int)) := do
  let fb := (← get).fb
  let own := (fb.frames.takeWhile (!·.outer)).length
  match fb.frames[d]? with
  | some f => if !f.outer then return f.cells.map fun b => (b, 16 * s) else captured fb (d - own) s
  | none => captured fb (d - own) s
where
  /-- captured frame `k` (0 = the declaring one): its cells, read at the entry -/
  captured (fb : FnB) (k s : Nat) : L (Option (Var × Int)) := do
    match fb.outerCells.find? (·.1 == k) with
    | some (_, b) => return some (b, 16 * s)
    | none =>
      let b ← newVar .ptr
      modify fun st => { st with fb := { st.fb with
        hoist := st.fb.hoist.push (.set b (.call (.rt "a68rt_frame_cells") #[ku (st.fb.entryDepth + k)])),
        outerCells := (k, b) :: st.fb.outerCells } }
      return some (b, 16 * s)

/-- Put the hoisted instructions of the function in place. -/
def finishHoist : L Unit :=
  modify fun st =>
    let fb := st.fb
    if fb.hoist.isEmpty then st else
    let b0 := fb.blocks[0]!
    let instrs := b0.instrs.extract 0 fb.hoistAt ++ fb.hoist ++ b0.instrs.extract fb.hoistAt b0.instrs.size
    { st with fb := { fb with blocks := fb.blocks.set! 0 { b0 with instrs := instrs }, hoist := #[] } }

/-- The frame id of cell `(d, s)`'s frame: a captured frame gets an id of its own. -/
def cellFid (d : Nat) : L Nat := do
  let fb := (← get).fb
  let own := (fb.frames.takeWhile (!·.outer)).length
  match fb.frames[d]? with
  | some f => if !f.outer then return f.fid else return 1000000 + (d - own)
  | none => return 1000000 + (d - own)

-- ## Memory: the runtime's objects, addressed inline

/-- What a memory access touches, for the printer's alias information: accesses of
    different kinds never overlap, and `KANY` may overlap a cell or a slot. -/
def KCELL : Nat := 1   -- a frame cell
def KHDR : Nat := 2    -- an object header, a descriptor's fields included
def KLEAF : Nat := 3   -- the elements and the defined bitmap of a leaf store
def KSLOT : Nat := 4   -- a value in a slots store: a row element, a field, a union's content
def KANY : Nat := 5    -- a cell or a slot

def ld (w : String) (ty : Ty) (p : Var) (off : Opnd) (kind : Nat := 0) : L Var := do
  let v ← newVar ty
  emit (.set v (.call (.nat s!"mem_ld_{w}") #[.v p, off, ki kind]))
  return v

def st (w : String) (p : Var) (off : Opnd) (v : Opnd) (kind : Nat := 0) : L Unit :=
  emit (.call (.nat s!"mem_st_{w}") #[.v p, off, v, ki kind])

def binv (ty : Ty) (op : BinOp) (a b : Opnd) : L Var := do
  let v ← newVar ty
  emit (.set v (.bin op a b))
  return v

/-- Continue in a fresh block when `c` holds, else go to `no`. -/
def guard (c : Opnd) (no : Nat) : L Unit := do
  let yes ← newBlock
  terminate (.condBr c yes no)
  switchTo yes

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

/-- The layout of the runtime's objects (`csrc/a68rt.h`). -/
def T_ROW : Int := 9
def K_LEAF : Int := 2
def K_ROWD : Int := 3

/-- The descriptor of the row cell `(b, off)` holds: a row value, or a name of a sub-row
    (a view, `REF [] INT v = a[2:5]`); anything else takes `slow` (`rt.c: cell_rowd`). -/
def cellRowd (b : Var) (off : Int) (slow : Nat) : L Var := do
  let r ← newVar .ptr
  let tag ← ld "i32" .i64 b (ki off) KCELL
  let isRow ← binv .i1 .eq (.v tag) (ki T_ROW)
  let rowB ← newBlock; let notRow ← newBlock; let done ← newBlock
  terminate (.condBr (.v isRow) rowB notRow)
  switchTo rowB
  let p ← ld "ptr" .ptr b (ki (off + 8)) KCELL
  emit (.set r (.opnd (.v p)))
  terminate (.br done)
  switchTo notRow
  guard (.v (← binv .i1 .eq (.v tag) (ki T_REF))) slow
  let aux ← ld "i32" .i64 b (ki (off + 4)) KCELL
  guard (.v (← binv .i1 .eq (.v aux) (ki VIEW_OFF))) slow
  let p2 ← ld "ptr" .ptr b (ki (off + 8)) KCELL
  let pk ← ld "i8" .i64 p2 (ki 0) KHDR
  guard (.v (← binv .i1 .eq (.v pk) (ki K_ROWD))) slow
  emit (.set r (.opnd (.v p2)))
  terminate (.br done)
  switchTo done
  return r

/-- The store index of `a[i]` or `a[i, j]` for descriptor `r`, with the evaluator's
    subscript checks (`rt.c: elem_index`); `slow` when the descriptor selects a field. -/
def rowIndex (r : Var) (dims : Nat) (is : Array Opnd) (slow : Nat) : L Var := do
  let field ← ld "i32" .i64 r (ki 40) KHDR
  guard (.v (← binv .i1 .eq (.v field) (ki 0))) slow
  let mut idx : Var ← ld "i64" .i64 r (ki 32) KHDR
  for k in [0:dims] do
    let l ← ld "i64" .i64 r (ki (48 + 24 * k)) KHDR
    let u ← ld "i64" .i64 r (ki (56 + 24 * k)) KHDR
    let stride ← ld "i64" .i64 r (ki (64 + 24 * k)) KHDR
    let i := is[k]!
    let ge ← binv .i1 .ge i (.v l)
    let le ← binv .i1 .le i (.v u)
    let inb ← binv .i1 .andB (.v ge) (.v le)
    let errB ← newBlock
    guard (.v inb) errB
    let cur := (← get).fb.cur
    switchTo errB
    rt "a68rt_index_error" #[i, .v l, .v u]
    terminate .unreachable
    switchTo cur
    let t ← binv .i64 .subW i (.v l)
    let m ← binv .i64 .mulW (.v t) (.v stride)
    idx ← binv .i64 .addW (.v idx) (.v m)
  return idx

/-- The store of descriptor `r`: through the owner when the descriptor is a view. -/
def rowStore (r : Var) : L Var := do
  let base ← ld "ptr" .ptr r (ki 24) KHDR
  let bk ← ld "i8" .i64 base (ki 0) KHDR
  let store ← newVar .ptr
  emit (.set store (.opnd (.v base)))
  let isView ← binv .i1 .eq (.v bk) (ki K_ROWD)
  let viaB ← newBlock; let cont ← newBlock
  terminate (.condBr (.v isView) viaB cont)
  switchTo viaB
  let inner ← ld "ptr" .ptr base (ki 24) KHDR
  emit (.set store (.opnd (.v inner)))
  terminate (.br cont)
  switchTo cont
  return store

/-- The store and store index of `a[i]` or `a[i, j]` for the row cell `(b, off)` holds,
    with the evaluator's subscript checks, continuing in the fast block; `slow` is taken
    when the cell does not hold a row value itself, when its descriptor selects a field,
    or when the store is not a leaf of the element's kind (`rt.c: row_elem`). -/
def rowLeafElem (b : Var) (off : Int) (dims : Nat) (is : Array Opnd) (info : ElemInfo) (slow : Nat) : L (Var × Var × Var) := do
  let r ← cellRowd b off slow
  let idx ← rowIndex r dims is slow
  let store ← rowStore r
  let sk ← ld "i8" .i64 store (ki 0) KHDR
  guard (.v (← binv .i1 .eq (.v sk) (ki K_LEAF))) slow
  let ek ← ld "i16" .i64 store (ki 2) KHDR
  guard (.v (← binv .i1 .eq (.v ek) (ki info.ek))) slow
  return (r, store, idx)

/-- The address (object, byte offset) of the value `f OF … OF x[i]` names, for the cell
    `(b, off)` holding the value itself: the row element, then each field through the
    structure object (`rt.c: sel_read`); `slow` when a tag is not as expected. -/
def T_NIL : Int := 7
def K_FRAME : Int := 4

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

/-- The cache in scope for the row cell `(fid, slot)` with store kind `ek`. -/
def lookupCache (fid slot : Nat) (ek : Int) : L (Option RowCache) := do
  return (← get).caches.find? fun c => c.fid == fid && c.slot == slot && c.ek == ek

/-- Note an inline access to a row, for the loop that may cache it. -/
def noteRowUse (fid slot : Nat) (ek : Int) (dims : Nat) : L Unit :=
  modify fun st => { st with rowUses := st.rowUses.push (fid, slot, ek, dims) }

/-- A slow path: the block `slow` and every block created by `act` are marked as such, so
    that a loop does not count their runtime calls against caching; afterwards the caches
    of the cell `key` (all of them when `key` is `none`) are recomputed, since the call
    may have changed the cell or its store. -/
def slowPath (slow : Nat) (key : Option (Nat × Nat)) (act : L Unit) : L Unit := do
  let a := (← get).fb.blocks.size
  act
  -- recompute the caches this call may have invalidated
  let cs := (← get).caches.filter fun c => match key with
    | some (fid, slot) => c.fid == fid && c.slot == slot
    | none => true
  for c in cs do recache c
  let b := (← get).fb.blocks.size
  modify fun st => { st with slowRanges := (st.slowRanges.push (slow, slow + 1)).push (a, b) }
where
  /-- compute the cache from the cell: valid only when everything is as the accesses expect -/
  recache (c : RowCache) : L Unit := do
    let done ← newBlock
    emit (.set c.valid (.opnd (kb false)))
    emit (.set c.rcOK (.opnd (kb false)))
    let fb := (← get).fb
    -- the cell's address: this frame's cells, or a captured frame's
    let d? := (List.range fb.frames.length).find? fun d => match fb.frames[d]? with
      | some f => !f.outer && f.fid == c.fid
      | none => false
    let addr : Option (Var × Int) ← match d? with
      | some d => cellAddr d c.slot
      | none =>
        if c.fid ≥ 1000000 then
          let own := (fb.frames.takeWhile (!·.outer)).length
          cellAddr (own + (c.fid - 1000000)) c.slot
        else pure none
    -- the bounds the row was declared with, when the variable keeps them for life
    let known : Option (List (Int × Int)) := match d? with
      | some d => match fb.frames[d]? with
        | some f => (f.bounds[c.slot]?).join
        | none => none
      | none => none
    match addr with
    | none => terminate (.br done); switchTo done
    | some (b, off) =>
      let tag ← ld "i32" .i64 b (ki off) KCELL
      guard (.v (← binv .i1 .eq (.v tag) (ki T_ROW))) done
      let r ← ld "ptr" .ptr b (ki (off + 8)) KCELL
      emit (.set c.r (.opnd (.v r)))
      let field ← ld "i32" .i64 r (ki 40) KHDR
      guard (.v (← binv .i1 .eq (.v field) (ki 0))) done
      match known with
      | some bs =>
        -- a fresh row's descriptor: offset 0, the last dimension's stride 1, each earlier
        -- one's the extent of the next (`rt.c: a68rt_new_row_of`)
        emit (.set c.off (.opnd (ki 0)))
        let mut stride : Int := 1
        let mut strides : Array Int := Array.replicate c.dims 1
        for k' in [0:c.dims] do
          let k := c.dims - 1 - k'
          strides := strides.set! k stride
          let (l, u) := bs[k]!
          let ext := u - l + 1
          stride := stride * (if ext > 0 then ext else 0)
        for k in [0:c.dims] do
          let (lv, uv, sv) := c.dim[k]!
          let (l, u) := bs[k]!
          emit (.set lv (.opnd (ki l))); emit (.set uv (.opnd (ki u))); emit (.set sv (.opnd (ki strides[k]!)))
      | none =>
        let off0 ← ld "i64" .i64 r (ki 32) KHDR
        emit (.set c.off (.opnd (.v off0)))
        for k in [0:c.dims] do
          let (lv, uv, sv) := c.dim[k]!
          let l ← ld "i64" .i64 r (ki (48 + 24 * k)) KHDR
          let u ← ld "i64" .i64 r (ki (56 + 24 * k)) KHDR
          let stride ← ld "i64" .i64 r (ki (64 + 24 * k)) KHDR
          emit (.set lv (.opnd (.v l))); emit (.set uv (.opnd (.v u))); emit (.set sv (.opnd (.v stride)))
      let store ← rowStore r
      emit (.set c.store (.opnd (.v store)))
      let sk ← ld "i8" .i64 store (ki 0) KHDR
      if c.ek == 0 then
        guard (.v (← binv .i1 .eq (.v sk) (ki K_SLOTS))) done
      else
        guard (.v (← binv .i1 .eq (.v sk) (ki K_LEAF))) done
        let ek ← ld "i16" .i64 store (ki 2) KHDR
        guard (.v (← binv .i1 .eq (.v ek) (ki c.ek))) done
      let n ← ld "i32" .i64 store (ki 4) KHDR
      emit (.set c.n (.opnd (.v n)))
      emit (.set c.valid (.opnd (kb true)))
      let rc ← ld "i32" .i64 store (ki 8) KHDR
      let ok ← binv .i1 .le (.v rc) (ki 1)
      emit (.set c.rcOK (.opnd (.v ok)))
      terminate (.br done)
      switchTo done

/-- Recompute the caches of cell `(fid, slot)`. -/
def recacheFor (fid slot : Nat) : L Unit := do
  for c in (← get).caches do
    if c.fid == fid && c.slot == slot then slowPath.recache c

/-- A runtime call whose only effect is on the cell `(fid, slot)` it names (`a68rt_append*`):
    a loop's caches of other rows survive it, and this cell's are recomputed after it. -/
def rtCell (name : String) (fid slot : Nat) (args : Array Opnd) : L Unit := do
  let fb := (← get).fb
  let at_ := (fb.cur, fb.blocks[fb.cur]!.instrs.size)
  rt name args
  modify fun st => { st with cellCalls := st.cellCalls.push at_ }
  recacheFor fid slot

/-- The store index of `a[i]` or `a[i, j]` from a cache, with the subscript checks. -/
def rowIndexCached (c : RowCache) (is : Array Opnd) : L Var := do
  let mut idx : Var := c.off
  for k in [0:c.dims] do
    let (l, u, stride) := c.dim[k]!
    let i := is[k]!
    let ge ← binv .i1 .ge i (.v l)
    let le ← binv .i1 .le i (.v u)
    let inb ← binv .i1 .andB (.v ge) (.v le)
    let errB ← newBlock
    guard (.v inb) errB
    let cur := (← get).fb.cur
    switchTo errB
    rt "a68rt_index_error" #[i, .v l, .v u]
    terminate .unreachable
    switchTo cur
    let t ← binv .i64 .subW i (.v l)
    let m ← binv .i64 .mulW (.v t) (.v stride)
    idx ← binv .i64 .addW (.v idx) (.v m)
  return idx

/-- `rowLeafElem` through the loop's cache when there is one: the store, the index, and
    the store's element count when it is known. -/
def rowLeafElemC (fid : Nat) (b : Var) (off : Int) (s dims : Nat) (is : Array Opnd) (info : ElemInfo) (slow : Nat) : L (Var × Var × Option Var × Option RowCache) := do
  noteRowUse fid s info.ek dims
  match ← lookupCache fid s info.ek with
  | some c =>
    guard (.v c.valid) slow
    let idx ← rowIndexCached c is
    return (c.store, idx, some c.n, some c)
  | none =>
    let (_, store, idx) ← rowLeafElem b off dims is info slow
    return (store, idx, none, none)


/-- The address of the value the name in cell `(b, off)` refers to: a slot of a structure
    object or a cell of a frame (`rt.c: ref_slot`); `slow` for NIL, an undefined name, or
    a name into a row (which the runtime resolves). -/
def refTarget (b : Var) (off : Int) (slow : Nat) : L (Var × Opnd) := do
  let tag ← ld "i32" .i64 b (ki off) KCELL
  guard (.v (← binv .i1 .eq (.v tag) (ki T_REF))) slow
  let aux ← ld "i32" .i64 b (ki (off + 4)) KCELL
  let obj ← ld "ptr" .ptr b (ki (off + 8)) KCELL
  let kind ← ld "i8" .i64 obj (ki 0) KHDR
  let base ← newVar .i64
  let isSlots ← binv .i1 .eq (.v kind) (ki K_SLOTS)
  let slotsB ← newBlock; let notSlots ← newBlock; let cont ← newBlock
  terminate (.condBr (.v isSlots) slotsB notSlots)
  switchTo slotsB
  emit (.set base (.opnd (ki 24)))
  terminate (.br cont)
  switchTo notSlots
  guard (.v (← binv .i1 .eq (.v kind) (ki K_FRAME))) slow
  emit (.set base (.opnd (ki 40)))
  terminate (.br cont)
  switchTo cont
  let o ← binv .i64 .addW (.v base) (.v aux)
  return (obj, .v o)

def selAddr (b : Var) (off : Int) (rank : Nat) (is : Array Opnd) (fields : List Nat) (slow : Nat) (via : Bool := false)
    (key : Option (Nat × Nat) := none) : L (Var × Opnd × Nat) := do
  let mut cur : Var × Opnd × Nat := (b, ki off, KCELL)
  if via then
    let (p, o) ← refTarget b off slow
    cur := (p, o, KANY)
  if rank > 0 then
    let cached : Option RowCache ← match key with
      | some (fid, slot) =>
        noteRowUse fid slot 0 rank
        lookupCache fid slot 0
      | none => pure none
    let (store, idx) ← match cached with
      | some c =>
        guard (.v c.valid) slow
        let idx ← rowIndexCached c is
        pure (c.store, idx)
      | none =>
        let r ← cellRowd b off slow
        let idx ← rowIndex r rank is slow
        let store ← rowStore r
        let sk ← ld "i8" .i64 store (ki 0) KHDR
        guard (.v (← binv .i1 .eq (.v sk) (ki K_SLOTS))) slow
        pure (store, idx)
    let eo ← binv .i64 .mulW (.v idx) (ki 16)
    let eo ← binv .i64 .addW (.v eo) (ki 24)
    cur := (store, .v eo, KSLOT)
  for f in fields do
    let tag ← ld "i32" .i64 cur.1 cur.2.1 cur.2.2
    guard (.v (← binv .i1 .eq (.v tag) (ki T_STRUCT))) slow
    let po ← binv .i64 .addW cur.2.1 (ki 8)
    let sp ← ld "ptr" .ptr cur.1 (.v po) cur.2.2
    cur := (sp, ki (24 + 16 * f), KSLOT)
  return cur

/-- Read the primitive value at `(p, off)` as `ty`; `slow` when its tag is not `info.ek`
    (an undefined value included: the runtime reports it). -/
def valGet (p : Var) (off : Opnd) (info : ElemInfo) (ty : Ty) (slow : Nat) (kind : Nat := 0) : L Var := do
  let tag ← ld "i32" .i64 p off kind
  guard (.v (← binv .i1 .eq (.v tag) (ki info.ek))) slow
  let vo ← binv .i64 .addW off (ki 8)
  let raw ← ld (if info.w == "f64" then "f64" else "i64") (if info.w == "f64" then .f64 else .i64) p (.v vo) kind
  match ty with
  | .i1 => binv .i1 .ne (.v raw) (ki 0)
  | .i32 => do let v ← newVar .i32; emit (.set v (.opnd (.v raw))); return v
  | _ => return raw

/-- Write the primitive value `v` at `(p, off)`: tag, aux 0, payload (`rt.c: mk_int`). -/
def valSet (p : Var) (off : Opnd) (info : ElemInfo) (v : Opnd) (kind : Nat := 0) : L Unit := do
  st "i32" p off (ki info.ek) kind
  let ao ← binv .i64 .addW off (ki 4)
  st "i32" p (.v ao) (ki 0) kind
  let vo ← binv .i64 .addW off (ki 8)
  st (if info.w == "f64" then "f64" else "i64") p (.v vo) v kind

/-- The offset of the defined byte of store index `idx` in a leaf: after the elements. -/
def leafFlag (store idx : Var) (es : Nat) (n? : Option Var := none) : L Var := do
  let n ← match n? with
    | some n => pure n
    | none => ld "i32" .i64 store (ki 4) KHDR
  let bytes ← binv .i64 .mulW (.v n) (ki es)
  let o1 ← binv .i64 .addW (.v bytes) (.v idx)
  binv .i64 .addW (.v o1) (ki 24)

/-- The element at store index `idx` of a leaf, as a value of the element's MIR type;
    an undefined element is reported as the evaluator reports it. -/
def leafGet (store idx : Var) (info : ElemInfo) (ty : Ty) (n? : Option Var := none) : L Var := do
  let foff ← leafFlag store idx info.es n?
  let flag ← ld "i8" .i64 store (.v foff) KLEAF
  let undefB ← newBlock
  guard (.v (← binv .i1 .ne (.v flag) (ki 0))) undefB
  let cur := (← get).fb.cur
  switchTo undefB
  rt "a68rt_undef_error" #[ku info.kind]
  terminate .unreachable
  switchTo cur
  let eoff ← binv .i64 .mulW (.v idx) (ki info.es)
  let eoff ← binv .i64 .addW (.v eoff) (ki 24)
  let raw ← ld info.w (if info.w == "f64" then .f64 else .i64) store (.v eoff) KLEAF
  match ty with
  | .i1 => binv .i1 .ne (.v raw) (ki 0)
  | .i32 => do let v ← newVar .i32; emit (.set v (.opnd (.v raw))); return v
  | _ => return raw

/-- Write the element at store index `idx` of a leaf and mark it defined. -/
def leafSet (store idx : Var) (info : ElemInfo) (v : Opnd) (n? : Option Var := none) : L Unit := do
  let foff ← leafFlag store idx info.es n?
  st "i8" store (.v foff) (ki 1) KLEAF
  let eoff ← binv .i64 .mulW (.v idx) (ki info.es)
  let eoff ← binv .i64 .addW (.v eoff) (ki 24)
  st info.w store (.v eoff) v KLEAF

/-- `s +:= v` for one element `v` on the row variable cell `(d, s)` holds: inline when the
    row starts at 1, is its own owner, unshared, over a leaf store of the element's kind
    with room to spare (`rt.c: append_in_place`): the element and its defined byte are
    written after the last one and the upper bound moves up; otherwise the runtime, which
    grows the store or takes the operator's way. -/
def appendElem (d s : Nat) (em : Mode) (v : Opnd) (fn : String) : L Unit := do
  let fid ← cellFid d
  match ← cellAddr d s, elemInfo em with
  | some (b, off), some info =>
    noteRowUse fid s info.ek 1
    let slow ← newBlock; let done ← newBlock
    let (r, store, u, n?, uv?) : Var × Var × Var × Option Var × Option Var ← match ← lookupCache fid s info.ek with
      | some c =>
        guard (.v c.valid) slow
        guard (.v c.rcOK) slow
        let (l, u, stride) := c.dim[0]!
        guard (.v (← binv .i1 .eq (.v l) (ki 1))) slow
        guard (.v (← binv .i1 .eq (.v c.off) (ki 0))) slow
        guard (.v (← binv .i1 .eq (.v stride) (ki 1))) slow
        pure (c.r, c.store, u, some c.n, some u)
      | none =>
        let r ← cellRowd b off slow
        let field ← ld "i32" .i64 r (ki 40) KHDR
        guard (.v (← binv .i1 .eq (.v field) (ki 0))) slow
        let l ← ld "i64" .i64 r (ki 48) KHDR
        guard (.v (← binv .i1 .eq (.v l) (ki 1))) slow
        let off0 ← ld "i64" .i64 r (ki 32) KHDR
        guard (.v (← binv .i1 .eq (.v off0) (ki 0))) slow
        let stride ← ld "i64" .i64 r (ki 64) KHDR
        guard (.v (← binv .i1 .eq (.v stride) (ki 1))) slow
        let u ← ld "i64" .i64 r (ki 56) KHDR
        let store ← ld "ptr" .ptr r (ki 24) KHDR
        let sk ← ld "i8" .i64 store (ki 0) KHDR
        guard (.v (← binv .i1 .eq (.v sk) (ki K_LEAF))) slow
        let ek ← ld "i16" .i64 store (ki 2) KHDR
        guard (.v (← binv .i1 .eq (.v ek) (ki info.ek))) slow
        let rc ← ld "i32" .i64 store (ki 8) KHDR
        guard (.v (← binv .i1 .le (.v rc) (ki 1))) slow
        pure (r, store, u, none, none)
    -- the row is its own owner (not a view) and has room for one more
    let bk ← ld "i8" .i64 store (ki 0) KHDR
    guard (.v (← binv .i1 .ne (.v bk) (ki K_ROWD))) slow
    let cap ← match n? with
      | some n => pure n
      | none => ld "i32" .i64 store (ki 4) KHDR
    guard (.v (← binv .i1 .lt (.v u) (.v cap))) slow
    if em == .char then guard (.v (← binv .i1 .lt v (.k .i32 (.i 256)))) slow
    leafSet store u info v n?
    let u1 ← binv .i64 .addW (.v u) (ki 1)
    st "i64" r (ki 56) (.v u1) KHDR
    match uv? with
    | some uv => emit (.set uv (.opnd (.v u1)))
    | none => pure ()
    terminate (.br done)
    switchTo slow
    slowPath slow (some (fid, s)) do rt fn #[ku (← rtd d), ku s, v]
    terminate (.br done)
    switchTo done
  | _, _ => rtCell fn fid s #[ku (← rtd d), ku s, v]

/-- `a[i] := v` on the row cell `(d, s)` holds: inline when the cell holds a row value over
    a leaf store of the element's kind that no other kept value shares (`rt.c: store_ref`
    would copy it first), else the runtime entry point `fn`. -/
def rowWrite (d s dims : Nat) (is : Array Opnd) (mr : Mode) (v : Opnd) (fn : String) : L Unit := do
  let j := is[1]?.getD (ki 0)
  match ← prowOf d s with
  | some pr =>
    let ix ← prowIndex pr is
    prowSet pr 0 ix v
    return
  | none => pure ()
  match ← cellAddr d s, elemInfo mr with
  | some (b, off), some info =>
    let fid ← cellFid d
    let slow ← newBlock; let done ← newBlock
    let (store, idx, n?, c?) ← rowLeafElemC fid b off s dims is info slow
    match c? with
    | some c => guard (.v c.rcOK) slow
    | none =>
      let rc ← ld "i32" .i64 store (ki 8) KHDR
      guard (.v (← binv .i1 .le (.v rc) (ki 1))) slow
    if mr == .char then guard (.v (← binv .i1 .lt v (.k .i32 (.i 256)))) slow
    leafSet store idx info v n?
    terminate (.br done)
    switchTo slow
    slowPath slow (some (fid, s)) do rt fn #[ku (← rtd d), ku s, ku dims, is[0]!, j, v]
    terminate (.br done)
    switchTo done
  | _, _ => rt fn #[ku (← rtd d), ku s, ku dims, is[0]!, j, v]

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

def popFrame : L Unit :=
  modify fun s => { s with fb := { s.fb with frames := s.fb.frames.tail } }

/-- Does the loop body jump, loop by a WHILE (possibly forever), or leave a block by a
    label or EXIT?  Such a body cannot have its traps deferred to the loop's end. -/
partial def hasJumpsOrWhile (c : Core) : Bool :=
  match c with
  | .goto _ => true
  | .loop _ f b t w body =>
    w.isSome || hasJumpsOrWhile f || hasJumpsOrWhile b
      || (match t with | some e => hasJumpsOrWhile e | none => false) || hasJumpsOrWhile body
  | .block _ stmts _ _ =>
    stmts.any (fun st => match st with
      | .label _ | .exit => true
      | .decl _ _ init => hasJumpsOrWhile init
      | .unit e => hasJumpsOrWhile e)
  | _ => (CodeGen.childrenD c).any fun (_, ch) => hasJumpsOrWhile ch

/-- The runtime entry points that change no cell and no row store: a loop calling only
    these (outside its slow paths) may keep what it knows about a row in variables. -/
def harmlessRt : List String :=
  [ "a68rt_enter", "a68rt_leave", "a68rt_set_int", "a68rt_set_cell_int", "a68rt_set_cell_real",
    "a68rt_set_cell_bool", "a68rt_set_cell_char", "a68rt_set_cell_bits", "a68rt_cell_int",
    "a68rt_cell_real", "a68rt_cell_bool", "a68rt_cell_char", "a68rt_cell_bits", "a68rt_cell_isnil",
    "a68rt_cell_cproc", "a68rt_push_int", "a68rt_push_real", "a68rt_push_bool", "a68rt_push_char",
    "a68rt_push_bits", "a68rt_pop_int", "a68rt_pop_real", "a68rt_pop_bool", "a68rt_pop_char",
    "a68rt_pop_bits", "a68rt_pop", "a68rt_jump_pending", "a68rt_jump_clear", "a68rt_index_error",
    "a68rt_undef_error", "a68rt_arith_error", "a68rt_conforms", "a68rt_frame_cells",
    "a68rt_env_depth", "a68rt_stack_depth", "a68rt_env_truncate", "a68rt_stack_truncate" ]

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

/-- The runtime entry points a loop may call and still be run twice: they change nothing
    a second run could see differently. -/
def repeatableRt : List String :=
  [ "a68rt_enter", "a68rt_leave", "a68rt_cell_int", "a68rt_cell_real", "a68rt_cell_bool",
    "a68rt_cell_char", "a68rt_cell_bits", "a68rt_cell_isnil", "a68rt_cell_cproc", "a68rt_push_int",
    "a68rt_push_real", "a68rt_push_bool", "a68rt_push_char", "a68rt_push_bits", "a68rt_pop_int",
    "a68rt_pop_real", "a68rt_pop_bool", "a68rt_pop_char", "a68rt_pop_bits", "a68rt_pop",
    "a68rt_jump_pending", "a68rt_conforms", "a68rt_frame_cells", "a68rt_env_depth", "a68rt_stack_depth",
    -- the checks: those that cannot be deferred are counted separately (`hardTraps`)
    "a68rt_index_error", "a68rt_undef_error", "a68rt_arith_error" ]

/-- Do blocks `[from, to)` call only what a second run may repeat, and reach no row through
    the runtime (no slow path)?  The registers a second run must restore are those assigned
    in the blocks that existed before it (`v0`). -/
def repeatable (from_ to v0 : Nat) : L (Bool × List Var) := do
  let st ← get
  let ok (f : Callee) : Bool := match f with
    | .rt name => repeatableRt.contains name
    | .nat _ => true
    | _ => false
  let mut mods : List Var := []
  for b in [from_:to] do
    let some blk := st.fb.blocks[b]? | continue
    for ins in blk.instrs do
      match ins with
      | .call f _ => if !ok f then return (false, [])
      | .set d (.call f _) =>
        if !ok f then return (false, [])
        if d.id < v0 && !mods.any (·.id == d.id) then mods := d :: mods
      | .set d _ => if d.id < v0 && !mods.any (·.id == d.id) then mods := d :: mods
      | _ => pure ()
  return (true, mods)

/-- Does every runtime call in blocks `[from, to)` outside the slow paths leave cells and
    row stores alone?  A call of a routine may do anything. -/
def callFree (from_ to : Nat) : L Bool := do
  let st ← get
  let slow (b : Nat) : Bool := st.slowRanges.any fun (a, z) => a ≤ b && b < z
  let ok (f : Callee) : Bool := match f with
    | .rt name => harmlessRt.contains name
    | .nat _ => true
    | _ => false
  for b in [from_:to] do
    if slow b then continue
    let some blk := st.fb.blocks[b]? | continue
    for i in [0:blk.instrs.size] do
      if st.cellCalls.contains (b, i) then continue
      match blk.instrs[i]! with
      | .call f _ => if !ok f then return false
      | .set _ (.call f _) => if !ok f then return false
      | _ => pure ()
  return true


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
