import A68.MIR
import A68.Serial
import A68.CodeGen

/-!
# A68.Lower.State

The state of the lowering: what a lowered value looks like, the promoted variable and
row representations, the frames as the lowering sees them, the function under
construction, the MIR builder, and the addressing of cells.
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

end A68.Lower
