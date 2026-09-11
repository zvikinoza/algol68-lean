import A68.Core
import A68.Serial

/-!
# A68.CodeGen — translation of the core representation to C

The emitted program is self-contained C: the program's *structure* becomes C
control flow (blocks, conditionals, cases, loops, jumps and one C function per
routine text), and values are handled by the runtime of `A68.Runtime`, which is
the same code the interpreter runs.  This mirrors Algol 68 Genie's optimiser,
which also compiles units to C against its own runtime, except that here the
result is a whole program rather than a plugin loaded back into an interpreter.

Two conventions govern the generated code:

* **Operand stack.** Every expression leaves exactly one value on the runtime's
  operand stack; a block leaves its result there too. This is the discipline
  proved correct for the expression core in `A68.Verified.StackMachine`.
* **Jumps.** A jump to a label of the enclosing C function is a C `goto`. A jump
  out of a routine sets a pending label and returns; every call site checks and
  either lands on its own label or returns in turn, so the C stack unwinds
  without `longjmp`.  Landing on a label restores the environment and operand
  stack to the depths recorded when the block was entered, which is what the
  interpreter does when it re-enters a block at a label.
-/
namespace A68.CodeGen

inductive CTy where
  | i64      -- INT
  | f64      -- REAL
  | u8       -- BOOL
  | u32      -- CHAR
  | u64      -- BITS
  deriving BEq, Inhabited

def CTy.ofMode : Mode → Option CTy
  | .int 0 => some .i64
  | .real 0 => some .f64
  | .bool => some .u8
  | .char => some .u32
  | .bits 0 => some .u64
  | _ => none

def CTy.name : CTy → String
  | .i64 => "int64_t" | .f64 => "double" | .u8 => "uint8_t"
  | .u32 => "uint32_t" | .u64 => "uint64_t"

/-- The one-letter suffix naming a type's helpers in the emitted C. -/
def CTy.sfx : CTy → String
  | .i64 => "i" | .f64 => "r" | .u8 => "b" | .u32 => "c" | .u64 => "u"

/-- How a scalar of this type is pushed onto the operand stack when it has to be boxed. -/
def CTy.pushFn : CTy → String
  | .i64 => "a68rt_push_int" | .f64 => "a68rt_push_real" | .u8 => "a68rt_push_bool"
  | .u32 => "a68rt_push_char" | .u64 => "a68rt_push_bits"

/-- How a scalar of this type is read out of a cell. -/
def CTy.cellFn : CTy → String
  | .i64 => "a68_cell_i" | .f64 => "a68_cell_r" | .u8 => "a68_cell_b"
  | .u32 => "a68_cell_c" | .u64 => "a68_cell_u"

/-- How a scalar of this type is taken off the operand stack into a C variable. -/
def CTy.popFn : CTy → String
  | .i64 => "a68_pop_i" | .f64 => "a68_pop_r" | .u8 => "a68_pop_b"
  | .u32 => "a68_pop_c" | .u64 => "a68_pop_u"

/-- How one element of a row of this mode is read, and written, without building a
    reference to it or going through the general slicing machinery. -/
def CTy.rowFn : CTy → String
  | .i64 => "a68_row_i" | .f64 => "a68_row_r" | .u8 => "a68_row_b"
  | .u32 => "a68_row_c" | .u64 => "a68_row_u"

def CTy.rowSetFn : CTy → String
  | .i64 => "a68_set_row_i" | .f64 => "a68_set_row_r" | .u8 => "a68_set_row_b"
  | .u32 => "a68_set_row_c" | .u64 => "a68_set_row_u"

/-- How one field of a structure reached from a cell is read, and written, without
    building the reference to it a selector at a time. -/
def CTy.selFn : CTy → String
  | .i64 => "a68_sel_i" | .f64 => "a68_sel_r" | .u8 => "a68_sel_b"
  | .u32 => "a68_sel_c" | .u64 => "a68_sel_u"

def CTy.selSetFn : CTy → String
  | .i64 => "a68_set_sel_i" | .f64 => "a68_set_sel_r" | .u8 => "a68_set_sel_b"
  | .u32 => "a68_set_sel_c" | .u64 => "a68_set_sel_u"

/-- The mode a native type stands for.  Promotion only ever happens for these modes, so
    this is exact, not an approximation. -/
def CTy.toMode : CTy → Mode
  | .i64 => .int 0 | .f64 => .real 0 | .u8 => .bool | .u32 => .char | .u64 => .bits 0

/-- The reporter for a read of an uninitialised promoted variable. -/
def CTy.undefFn : CTy → String
  | .i64 => "a68_und_i" | .f64 => "a68_und_r" | .u8 => "a68_und_b"
  | .u32 => "a68_und_c" | .u64 => "a68_und_u"

/-- How a scalar of this type is written straight into a cell, without boxing it first. -/
def CTy.setFn : CTy → String
  | .i64 => "a68_set_i" | .f64 => "a68_set_r" | .u8 => "a68_set_b"
  | .u32 => "a68_set_c" | .u64 => "a68_set_u"

/-- `x +:= e` and its relatives as C.  These are exactly the assigning operators whose
    effect on a name of primitive mode is `x := x op e` with the same checks.  `/:=` on
    REAL is deliberately not among them: it reports a different error than `/` does. -/
def assignOpExpr (op : String) (ty : CTy) (x y : String) : Option String :=
  match op, ty with
  | "+:=", .i64 => some s!"a68_add_i({x}, {y})"
  | "-:=", .i64 => some s!"a68_sub_i({x}, {y})"
  | "*:=", .i64 => some s!"a68_mul_i({x}, {y})"
  | "%:=", .i64 => some s!"a68_over_i({x}, {y})"
  | "%*:=", .i64 => some s!"a68_mod_i({x}, {y})"
  | "+:=", .f64 => some s!"a68_chk_r(({x}) + ({y}))"
  | "-:=", .f64 => some s!"a68_chk_r(({x}) - ({y}))"
  | "*:=", .f64 => some s!"a68_chk_r(({x}) * ({y}))"
  | "&:=", .u64 => some s!"(({x}) & ({y}))"
  | "|:=", .u64 => some s!"(({x}) | ({y}))"
  | _, _ => none

/-- A row of primitive elements promoted to a C array: `{name}_p` holds the elements,
    `{name}_d` a flag per element saying whether it has been given a value, and
    `{name}_l0`, `{name}_u0` (and `_l1`, `_u1` for a second dimension) its bounds. -/
structure RowVar where
  name : String
  ty   : CTy
  dims : Nat
  /-- for a row of structures, the type of each field, each kept in `{name}_p{k}` with its
      flags in `{name}_d{k}`; empty for a row of primitive elements -/
  fields : Array CTy := #[]
  deriving Inhabited

/-- The C signature of a routine that is also compiled as a plain C function: parameters
    arrive as C arguments instead of on the operand stack, and the result comes back as the
    C return value instead of being boxed and pushed.  `rty` is `none` for VOID. -/
structure NatSig where
  ptys : Array CTy
  rty  : Option CTy
  deriving Inhabited, BEq

/-- A routine a slot is known to hold, together with its plain C entry point. -/
structure ProcInfo where
  nidx : Nat
  sig  : NatSig
  deriving Inhabited

/-- A frame as the generator sees it.  `vars` names the C variable a slot was promoted
    to, when it has one; `pushed` says whether a run-time frame was emitted for it at all.
    A frame every one of whose slots is a C variable needs no run-time frame, so the
    depths in `loadCell`/`refCell` — which count syntactic frames — have to be translated
    into run-time depths, which count only the frames that were actually pushed. -/
structure Frame where
  /-- per slot: C variable name, its type, and whether reads must test for undefined -/
  vars   : Array (Option (String × CTy × Bool)) := #[]
  /-- per slot: the routine it certainly holds, once a call can see its declaration -/
  procs  : Array (Option ProcInfo) := #[]
  /-- per slot: the C array a row was promoted to -/
  rows   : Array (Option RowVar) := #[]
  /-- per slot: its mode, where known; a procedure-valued slot's mode gives the C signature
      of a plain entry point for whatever routine it holds -/
  modes  : Array (Option Mode) := #[]
  pushed : Bool := true
  deriving Inhabited

/-- Translate a syntactic depth into the run-time depth.  Frames past the end of the
    list belong to enclosing C functions and are always real. -/
def rtDepthOf (env : List Frame) (d : Nat) : Nat := Id.run do
  let mut r := 0
  let mut i := 0
  for f in env do
    if i ≥ d then break
    if f.pushed then r := r + 1
    i := i + 1
  if d > env.length then r := r + (d - env.length)
  return r

def varOf (env : List Frame) (d s : Nat) : Option (String × CTy × Bool) := do
  let f ← env[d]?
  let v ← f.vars[s]?
  v

def rowOf (env : List Frame) (d s : Nat) : Option RowVar := do
  let f ← env[d]?
  let r ← f.rows[s]?
  r

/-- The promoted row a node names through its variable, `a` in `LWB a`. -/
def rowName (env : List Frame) (c : Core) : Option RowVar :=
  match c with
  | .at _ e => rowName env e
  | .loadCell d s => rowOf env d s
  | .deref (.refCell d s) => rowOf env d s
  | .deref (.at _ e) => rowName env (.deref e)
  | _ => none

/-- The C expression reading a promoted variable, with the undefined test when one is
    needed.  The test is a perfectly predicted branch, and it keeps the run-time error
    that the evaluator would have reported. -/
def readVar : (String × CTy × Bool) → String
  | (v, ty, false) => v
  | (v, ty, true) => s!"({v}_i ? {v} : {ty.undefFn}())"

structure Fn where
  name  : String
  body  : Array String := #[]
  deriving Inhabited

structure St where
  w      : Serial.Writer := {}
  fns    : Array Fn := #[]
  holes  : Array Fn := #[]
  cur    : Array String := #[]     -- lines of the function being emitted
  labels : List Nat := []          -- labels owned by the function being emitted
  depth  : Nat := 0                -- indentation
  tmp    : Nat := 0
  frames : List Frame := []   -- innermost first
  nfns   : Array (String × Array String) := #[]   -- plain C entry points: signature, body
  ret    : String := "return;"  -- how the function being emitted returns when a jump leaves it
  procMode : Option Mode := none   -- the mode of the routine text about to be compiled, if declared
  modeTab : Mode.Table := {}       -- the program's mode declarations, to see through declared names
  nativeOfFn : Array (Nat × Nat) := #[]   -- boxed function index, plain entry point index
  deriving Inhabited

abbrev M := StateM St

def emit (line : String) : M Unit :=
  modify fun s => { s with cur := s.cur.push (String.ofList (List.replicate (2 * s.depth) ' ') ++ line) }

def indent (act : M α) : M α := do
  modify fun s => { s with depth := s.depth + 1 }
  let r ← act
  modify fun s => { s with depth := s.depth - 1 }
  return r

def fresh : M Nat := do
  let s ← get
  set { s with tmp := s.tmp + 1 }
  return s.tmp

def putMode (m : Mode) : M Nat := do
  let s ← get
  let (i, w) := Serial.putMode s.w m
  set { s with w := w }
  return i

def putStr (str : String) : M Nat := do
  let s ← get
  let (i, w) := s.w.str str
  set { s with w := w }
  return i

def putFmtList (items : List CoreFmt) : M Nat := do
  let s ← get
  let (i, w) := Serial.putFmtList s.w items
  set { s with w := w }
  return i

/-- C string literal for an arbitrary byte string. -/
def cstring (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n" else if c == '\t' then "\\t"
    else if c.toNat < 32 || c.toNat > 126 then
      let n := c.toNat % 256
      let d := "0123456789abcdef"
      "\\x" ++ String.singleton (d.get ⟨n / 16⟩) ++ String.singleton (d.get ⟨n % 16⟩)
    else String.singleton c) ++ "\""

/-- One lower-case hexadecimal figure. -/
def hexFig (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- A `REAL` literal as C source.  Lean's `toString` on a `Float` keeps six decimals,
    which is far short of a double, so the literal is written as a C99 hexadecimal
    floating constant: that is the bit pattern itself, and the C compiler cannot round
    it.  A compiled program therefore sees exactly the value the evaluator computed. -/
def creal (x : Float) : String :=
  if x.isNaN then "(0.0/0.0)"
  else if x.isInf then (if x > 0 then "(1.0/0.0)" else "(-1.0/0.0)")
  else
    let b := x.toBits
    let sign := if b >>> 63 == 1 then "-" else ""
    let e := (b >>> 52) &&& 0x7FF
    let m := b &&& 0xFFFFFFFFFFFFF
    let figs := String.ofList ((List.range 13).map fun i =>
      hexFig (((m >>> (48 - 4 * i).toUInt64) &&& 0xF).toNat))
    if e == 0 then
      if m == 0 then sign ++ "0.0" else sign ++ "0x0." ++ figs ++ "p-1022"
    else
      let ex : Int := (e.toNat : Int) - 1023
      sign ++ "0x1." ++ figs ++ "p" ++ (if ex < 0 then toString ex else "+" ++ toString ex)

/-- Labels declared directly in this function (not inside nested routine texts). -/
partial def labelsOf : Core → List Nat
  | .block _ stmts _ _ =>
    stmts.toList.flatMap fun st => match st with
      | .label id => [id]
      | .decl _ _ c => labelsOf c
      | .unit c => labelsOf c
      | .exit => []
  | .deref e | .deproc e | .rowOf e | .voiding e | .gen e | .at _ e => labelsOf e
  | .widen _ _ e | .unite _ e | .monop _ _ e | .select _ e _ => labelsOf e
  | .assign a b _ | .identRel a b _ | .andThen a b | .orElse a b | .seq a b => labelsOf a ++ labelsOf b
  | .dyop _ _ _ a b => labelsOf a ++ labelsOf b
  | .call f args => labelsOf f ++ args.flatMap labelsOf
  | .slice a idx _ => labelsOf a ++ idx.flatMap fun
      | .index e => labelsOf e
      | .trim l u a => (l.map labelsOf).getD [] ++ (u.map labelsOf).getD [] ++ (a.map labelsOf).getD []
  | .newRow bs i _ => bs.flatMap (fun (l, u) => labelsOf l ++ labelsOf u) ++ labelsOf i
  | .collateral es _ _ => es.flatMap labelsOf
  | .cond c t e => labelsOf c ++ labelsOf t ++ labelsOf e
  | .caseInt s alts o => labelsOf s ++ alts.flatMap labelsOf ++ labelsOf o
  | .caseConf s alts o => labelsOf s ++ alts.flatMap (fun (_, _, c) => labelsOf c) ++ labelsOf o
  | .loop _ f b t w body =>
    labelsOf f ++ labelsOf b ++ (t.map labelsOf).getD [] ++ (w.map labelsOf).getD [] ++ labelsOf body
  | _ => []

/-- After a call that may raise a jump, land on our own label or propagate. -/
def jumpCheck : M Unit := do
  let s ← get
  if s.labels.isEmpty then
    emit s!"if (a68_jump()) {s.ret}"
  else
    emit "if (a68_jump()) { switch (a68_jump()-1) {"
    for l in s.labels do
      emit s!"  case {l}: goto L{l};"
    emit s!"  default: {s.ret} } }"

/-- `x +:= e` and its relatives, as a C expression for the new value.  These are the
    assigning operators: the left operand is a name, and the operator writes through it,
    so in statement position the whole thing is an update rather than a reference handed
    to the runtime.  Each form reproduces the check the evaluator performs. -/
def nativeAssignOp (op : String) (ty : CTy) (a b : String) : Option String :=
  match ty, op with
  | .i64, "+:=" => some s!"a68_add_i({a}, {b})"
  | .i64, "-:=" => some s!"a68_sub_i({a}, {b})"
  | .i64, "*:=" => some s!"a68_mul_i({a}, {b})"
  | .i64, "%:=" => some s!"a68_over_i({a}, {b})"
  | .i64, "%*:=" => some s!"a68_mod_i({a}, {b})"
  | .f64, "+:=" => some s!"a68_chk_r(({a}) + ({b}))"
  | .f64, "-:=" => some s!"a68_chk_r(({a}) - ({b}))"
  | .f64, "*:=" => some s!"a68_chk_r(({a}) * ({b}))"
  | .f64, "/:=" => some s!"a68_diveq_r({a}, {b})"
  | .u64, "&:=" => some s!"(({a}) & ({b}))"
  | .u64, "|:=" => some s!"((({a}) | ({b})) & 0xffffffffull)"
  | _, _ => none

/-- Is this assigning operator one that a slot of this type can be updated with in place?
    The escape analysis has to ask exactly what the emitter can do, or a slot would be
    promoted to a C variable that the emitter then cannot write. -/
def assignsNatively (ty : CTy) (op : String) : Bool := (nativeAssignOp op ty "a" "b").isSome

/-- Peel the position markers off a node. -/
partial def strip : Core → Core
  | .at _ e => strip e
  | c => c

/-- Which statements of a block are generated in statement position, where the value is
    thrown away.  Without labels only the last unit supplies the block's value, so every
    earlier unit is a statement; with labels any unit can be the value the block exits
    with, so only an explicit VOIDing is safe to treat that way. -/
def voidPositions (stmts : Array CoreStmt) (wantValue : Bool) : Array Bool := Id.run do
  let hasLbl := stmts.any fun st => match st with | .label _ | .exit => true | _ => false
  if !wantValue then
    return stmts.map fun st => match st with | .unit _ => true | _ => false
  if hasLbl then
    return stmts.map fun st => match st with
      | .unit e => (match strip e with | .voiding _ => true | _ => false)
      | _ => false
  let mut last : Option Nat := none
  for i in [0:stmts.size] do
    match stmts[i]! with | .unit _ => last := some i | _ => pure ()
  let mut out : Array Bool := #[]
  for i in [0:stmts.size] do
    out := out.push (match stmts[i]! with
      | .unit e => last != some i || (match strip e with | .voiding _ => true | _ => false)
      | _ => false)
  return out

mutual
/-- Does anything inside `c` force slot `sl` of frame `d` to live in a run-time cell?
    A plain read is fine, and so is assigning a whole value to it in statement position;
    anything else — taking a reference to it, or using an assignment for its value — is. -/
partial def slotEscapes (ok : String → Bool) (d sl : Nat) (c : Core) : Bool :=
  match c with
  | .at _ e => slotEscapes ok d sl e
  | .lit _ => false
  | .loadCell _ _ => false
  | .refCell dd ss => dd == d && ss == sl
  | .voiding e => slotEscapesV ok d sl e
  | .deref e | .deproc e | .rowOf e | .gen e => slotEscapes ok d sl e
  | .widen _ _ e | .unite _ e | .monop _ _ e => slotEscapes ok d sl e
  | .assign dst src _ => slotEscapes ok d sl dst || slotEscapes ok d sl src
  | .identRel l r _ | .dyop _ _ _ l r | .andThen l r | .orElse l r =>
    slotEscapes ok d sl l || slotEscapes ok d sl r
  | .call f args => slotEscapes ok d sl f || args.any (slotEscapes ok d sl)
  | .routine _ _ body => slotEscapes ok (d + 1) sl body
  | .slice arr idx _ => slotEscapes ok d sl arr || idx.any (slotEscapesIdx ok d sl)
  | .select _ e _ => slotEscapes ok d sl e
  | .newRow bs init _ =>
    slotEscapes ok d sl init || bs.any fun (l, u) => slotEscapes ok d sl l || slotEscapes ok d sl u
  | .block _ stmts _ _ => slotEscapesStmts ok (d + 1) sl stmts true
  | .collateral es _ _ => es.any (slotEscapes ok d sl)
  | .cond a b e => slotEscapes ok d sl a || slotEscapes ok d sl b || slotEscapes ok d sl e
  | .caseInt sel alts out => slotEscapes ok d sl sel || alts.any (slotEscapes ok d sl) || slotEscapes ok d sl out
  | .caseConf sel alts out =>
    slotEscapes ok d sl sel || slotEscapes ok d sl out
      || alts.any fun (_, _, b) => slotEscapes ok (d + 1) sl b
  | .loop _ f b t w body =>
    slotEscapes ok d sl f || slotEscapes ok d sl b
      || (match t with | some e => slotEscapes ok d sl e | none => false)
      || (match w with | some e => slotEscapes ok (d + 1) sl e | none => false)
      || slotEscapesV ok (d + 1) sl body
  | .fmt items => items.any (slotEscapesFmt ok d sl)
  | .seq a b => slotEscapes ok d sl a || slotEscapes ok d sl b
  | _ => false

/-- The same question for a node in statement position: an assignment straight into the
    slot is then just a write, not a reference that outlives the statement. -/
partial def slotEscapesV (ok : String → Bool) (d sl : Nat) (c : Core) : Bool :=
  match strip c with
  | .voiding e => slotEscapesV ok d sl e
  | .seq a b => slotEscapesV ok d sl a || slotEscapesV ok d sl b
  | .dyop op _ _ l r =>
    (if ok op then
       match strip l with
       | .refCell dd ss => if dd == d && ss == sl then false else slotEscapes ok d sl l
       | l' => slotEscapes ok d sl l'
     else slotEscapes ok d sl l) || slotEscapes ok d sl r
  | .assign dst src _ =>
    (match strip dst with
     | .refCell dd ss => if dd == d && ss == sl then false else slotEscapes ok d sl dst
     | dst' => slotEscapes ok d sl dst') || slotEscapes ok d sl src
  | .cond a b e => slotEscapes ok d sl a || slotEscapesV ok d sl b || slotEscapesV ok d sl e
  | .block _ stmts _ _ => slotEscapesStmts ok (d + 1) sl stmts false
  | .loop _ f b t w body =>
    slotEscapes ok d sl f || slotEscapes ok d sl b
      || (match t with | some e => slotEscapes ok d sl e | none => false)
      || (match w with | some e => slotEscapes ok (d + 1) sl e | none => false)
      || slotEscapesV ok (d + 1) sl body
  | e => slotEscapes ok d sl e

partial def slotEscapesStmts (ok : String → Bool) (d sl : Nat) (stmts : Array CoreStmt) (wantValue : Bool) : Bool :=
  Id.run do
    let vp := voidPositions stmts wantValue
    for i in [0:stmts.size] do
      let bad := match stmts[i]! with
        | .decl _ _ init => slotEscapes ok d sl init
        | .unit e => if vp[i]! == true then slotEscapesV ok d sl e else slotEscapes ok d sl e
        | .label _ | .exit => false
      if bad == true then return true
    return false

partial def slotEscapesIdx (ok : String → Bool) (d sl : Nat) : CoreIdx → Bool
  | .index e => slotEscapes ok d sl e
  | .trim l u a =>
    (match l with | some e => slotEscapes ok d sl e | none => false)
      || (match u with | some e => slotEscapes ok d sl e | none => false)
      || (match a with | some e => slotEscapes ok d sl e | none => false)

partial def slotEscapesFmt (ok : String → Bool) (d sl : Nat) : CoreFmt → Bool
  | .rep _ dyn it => (match dyn with | some e => slotEscapes ok d sl e | none => false) || slotEscapesFmt ok d sl it
  | .general args => args.any (slotEscapes ok d sl)
  | .group items => items.any (slotEscapesFmt ok d sl)
  | .include f => slotEscapes ok d sl f
  | _ => false
end

mutual
/-- Is there a routine text or a format text anywhere in here?  Both are compiled into
    separate C functions that reach enclosing frames through the run-time environment, so
    a frame they can see cannot become C variables. -/
partial def hasOtherFn (c : Core) : Bool :=
  match c with
  | .routine _ _ _ | .fmt _ => true
  | .at _ e | .deref e | .deproc e | .rowOf e | .gen e | .voiding e
  | .widen _ _ e | .unite _ e | .monop _ _ e | .select _ e _ => hasOtherFn e
  | .assign l r _ | .identRel l r _ | .dyop _ _ _ l r | .andThen l r | .orElse l r
  | .seq l r => hasOtherFn l || hasOtherFn r
  | .call f args => hasOtherFn f || args.any hasOtherFn
  | .slice arr idx _ => hasOtherFn arr || idx.any hasOtherFnIdx
  | .newRow bs init _ => hasOtherFn init || bs.any (fun (l, u) => hasOtherFn l || hasOtherFn u)
  | .block _ stmts _ _ => stmts.toList.any hasOtherFnStmt
  | .collateral es _ _ => es.any hasOtherFn
  | .cond a b e => hasOtherFn a || hasOtherFn b || hasOtherFn e
  | .caseInt sel alts out => hasOtherFn sel || alts.any hasOtherFn || hasOtherFn out
  | .caseConf sel alts out => hasOtherFn sel || hasOtherFn out || alts.any (fun (_, _, b) => hasOtherFn b)
  | .loop _ f b t w body =>
    hasOtherFn f || hasOtherFn b
      || (match t with | some e => hasOtherFn e | none => false)
      || (match w with | some e => hasOtherFn e | none => false)
      || hasOtherFn body
  | _ => false

partial def hasOtherFnStmt : CoreStmt → Bool
  | .decl _ _ init => hasOtherFn init
  | .unit e => hasOtherFn e
  | .label _ | .exit => false

partial def hasOtherFnIdx : CoreIdx → Bool
  | .index e => hasOtherFn e
  | .trim l u a =>
    (match l with | some e => hasOtherFn e | none => false)
      || (match u with | some e => hasOtherFn e | none => false)
      || (match a with | some e => hasOtherFn e | none => false)
end

/-- The result mode of an operator, given its operand modes: comparisons yield BOOL,
    the arithmetic operators yield their (already widened) operand mode. -/
def dyopResult (op : String) (m1 : Mode) : Option Mode :=
  -- REAL / REAL is REAL; an INT division has had its operands widened by the elaborator,
  -- so only REAL operands are admitted here
  if op == "/" then (match m1 with | .real n => some (.real n) | _ => none) else
  if ["=", "/=", "<", "<=", ">", ">=", "AND", "OR", "XOR"].contains op then
    if ["AND", "OR", "XOR"].contains op then some m1 else some .bool
  else if ["+", "-", "*", "%", "%*", "**"].contains op then some m1
  else none

def monopResult (op : String) (m : Mode) : Option Mode :=
  match op, m with
  | "-", _ | "+", _ | "ABS", .int _ | "ABS", .real _ | "NOT", _ => some m
  | "ABS", .char | "ABS", .bool => some (.int 0)
  | "SIGN", _ => some (.int 0)
  | "ODD", _ => some .bool
  | "ENTIER", .real n | "ROUND", .real n => some (.int n)
  | "REPR", _ => some .char
  | _, _ => none

/-- A chain of selectors rooted at a cell: `f OF … OF a[i, j]`, `f OF … OF s`, or
    `f OF … OF p` where the cell holds a `REF`.  The runtime takes it as two words:
    `spec` (rank of the subscript, whether the cell holds the structure or a `REF` to it,
    and how many fields follow) and `fields` (the field indices, one byte each). -/
structure SelChain where
  depth  : Nat
  slot   : Nat
  viaCellRef : Bool := false
  rank   : Nat := 0
  i      : String := "0"
  j      : String := "0"
  fields : List Nat := []
  deriving Inhabited

def SelChain.spec (c : SelChain) : Nat :=
  c.rank + (if c.viaCellRef then 4 else 0) + 256 * c.fields.length

def SelChain.fieldsWord (c : SelChain) : Nat := Id.run do
  let mut w := 0
  let mut k := 0
  for f in c.fields do
    w := w + f * 256 ^ k
    k := k + 1
  return w

/-- The argument list every `a68rt_sel_*` entry point takes. -/
def SelChain.args (c : SelChain) : String :=
  s!"{c.depth}, {c.slot}, {c.spec}u, {c.i}, {c.j}, {c.fieldsWord}u"

/-- The C form of a monadic operator on a native operand, when it has one.  Each form
    reproduces the check its interpreted counterpart performs. -/
def monopC (op : String) (t : CTy) (x : String) : Option String :=
  match op, t with
  | "-", .i64 => some s!"a68_neg_i({x})"
  | "-", .f64 => some s!"(-({x}))"
  | "+", _ => some x
  | "ABS", .i64 => some s!"a68_abs_i({x})"
  | "ABS", .f64 => some s!"a68_fabs({x})"
  | "ABS", .u32 => some s!"((int64_t)({x}))"
  | "ABS", .u8 => some s!"((int64_t)(({x}) != 0))"
  | "REPR", .i64 => some s!"a68_repr({x})"
  | "SIGN", .i64 => some s!"a68_sign_i({x})"
  | "SIGN", .f64 => some s!"a68_sign_r({x})"
  | "ODD", .i64 => some s!"(uint8_t)((({x}) % 2) != 0)"
  | "NOT", .u8 => some s!"(uint8_t)(!({x}))"
  | "ENTIER", .f64 => some s!"a68_entier({x})"
  | "ROUND", .f64 => some s!"a68_round({x})"
  | _, _ => none

/-- The C form of a dyadic operator on native operands, when it has one. -/
def dyopC (op : String) (opnd : CTy) (a b : String) : Option String :=
  match op, opnd with
  | "+", .i64 => some s!"a68_add_i({a}, {b})"
  | "-", .i64 => some s!"a68_sub_i({a}, {b})"
  | "*", .i64 => some s!"a68_mul_i({a}, {b})"
  | "%", .i64 => some s!"a68_over_i({a}, {b})"
  | "%*", .i64 => some s!"a68_mod_i({a}, {b})"
  | "+", .f64 => some s!"a68_chk_r(({a}) + ({b}))"
  | "-", .f64 => some s!"a68_chk_r(({a}) - ({b}))"
  | "*", .f64 => some s!"a68_chk_r(({a}) * ({b}))"
  | "/", .f64 => some s!"a68_div_r({a}, {b})"
  | "AND", .u8 => some s!"(uint8_t)(({a}) && ({b}))"
  | "OR", .u8 => some s!"(uint8_t)(({a}) || ({b}))"
  | "XOR", .u8 => some s!"(uint8_t)((({a}) != 0) != (({b}) != 0))"
  | "AND", .u64 => some s!"(({a}) & ({b}))"
  | "OR", .u64 => some s!"(({a}) | ({b}))"
  | "XOR", .u64 => some s!"(({a}) ^ ({b}))"
  | "=", _ => some s!"(uint8_t)(({a}) == ({b}))"
  | "/=", _ => some s!"(uint8_t)(({a}) != ({b}))"
  | "<", _ => some s!"(uint8_t)(({a}) < ({b}))"
  | "<=", _ => some s!"(uint8_t)(({a}) <= ({b}))"
  | ">", _ => some s!"(uint8_t)(({a}) > ({b}))"
  | ">=", _ => some s!"(uint8_t)(({a}) >= ({b}))"
  | _, _ => none

/-- The REAL standard functions compiled to C, each as `a68_m_<name>`. -/
def nativeMathFns : List String := ["acos", "arccos", "arccosh", "arcsin", "arcsinh", "arctan", "arctanh", "asin", "atan", "cbrt", "cos", "cosh", "curt", "exp", "exp2", "ln", "log", "log10", "log2", "sin", "sinh", "sqrt", "tan", "tanh"]

mutual
/-- `f OF a[i]` on a row of structures kept as one C array per field. -/
partial def srowReadC (env : List Frame) (ty : CTy) (f : Nat) (e : Core) : Option String := do
  let (base, idx) ← match strip e with
    | .slice base idx true => some (base, idx)
    | _ => none
  let (d, sl) ← match strip base with
    | .refCell d sl => some (d, sl)
    | _ => none
  let rv ← rowOf env d sl
  if rv.fields.isEmpty || f ≥ rv.fields.size || rv.fields[f]! != ty || idx.length != rv.dims then none else
  let is ← idx.mapM fun | .index x => scalarExpr env (.int 0) x | _ => none
  let r := rv.name
  if rv.dims == 1 then
    some s!"a68_ar_{ty.sfx}({r}_p{f}, {r}_d{f}, {r}_l0, {r}_u0, {is[0]!})"
  else
    some s!"a68_ar2_{ty.sfx}({r}_p{f}, {r}_d{f}, {r}_l0, {r}_u0, {r}_l1, {r}_u1, {is[0]!}, {is[1]!})"

/-- `a[i]` and `a[i, j]` on a row promoted to a C array: the element, with the bounds check
    and the undefined test the evaluator performs. -/
partial def rowReadC (env : List Frame) (ty : CTy) (base : Core) (idx : List CoreIdx) : Option String := do
  let (d, sl) ← match strip base with
    | .refCell d sl => some (d, sl)
    | _ => none
  let rv ← rowOf env d sl
  if !rv.fields.isEmpty || rv.ty != ty || idx.length != rv.dims then none else
  let is ← idx.mapM fun | .index e => scalarExpr env (.int 0) e | _ => none
  let r := rv.name
  if rv.dims == 1 then
    some s!"a68_ar_{ty.sfx}({r}_p, {r}_d, {r}_l0, {r}_u0, {is[0]!})"
  else
    some s!"a68_ar2_{ty.sfx}({r}_p, {r}_d, {r}_l0, {r}_u0, {r}_l1, {r}_u1, {is[0]!}, {is[1]!})"

/-- `a[i]` and `a[i, j]` where `a` is a row held directly in a cell: one call that returns
    a native value, instead of a reference built on the operand stack and then dereferenced. -/
partial def rowRead (env : List Frame) (ty : CTy) (base : Core) (idx : List CoreIdx) : Option String := do
  let (d, sl) ← match strip base with
    | .refCell d sl => some (d, sl)
    | .loadCell d sl => some (d, sl)
    | _ => none
  if (varOf env d sl).isSome || (rowOf env d sl).isSome then none else
  match idx with
  | [.index a] => do
    let ia ← scalarExpr env (.int 0) a
    some s!"{ty.rowFn}({rtDepthOf env d}, {sl}, 1, {ia}, 0)"
  | [.index a, .index b] => do
    let ia ← scalarExpr env (.int 0) a
    let ib ← scalarExpr env (.int 0) b
    some s!"{ty.rowFn}({rtDepthOf env d}, {sl}, 2, {ia}, {ib})"
  | _ => none

/-- Recognise a chain of selectors rooted at a cell.  A slot promoted to a C variable has
    no cell for the chain to start from, and neither an index nor a bound that is not a
    native expression can be passed to the runtime, so those give `none` and the caller
    falls back to building the reference a step at a time. -/
partial def selChain (env : List Frame) : Core → Option SelChain
  | .at _ e => selChain env e
  | .refCell d s =>
    if (varOf env d s).isSome || (rowOf env d s).isSome then none
    else some { depth := rtDepthOf env d, slot := s }
  -- the cell holds a `REF`; the structure is what it designates
  | .loadCell d s | .deref (.refCell d s) =>
    if (varOf env d s).isSome then none
    else some { depth := rtDepthOf env d, slot := s, viaCellRef := true }
  | .slice base idx true => do
    let c ← selChain env base
    guard (!c.viaCellRef && c.rank == 0 && c.fields.isEmpty)
    match idx with
    | [.index a] => do
      let ia ← scalarExpr env (.int 0) a
      some { c with rank := 1, i := ia }
    | [.index a, .index b] => do
      let ia ← scalarExpr env (.int 0) a
      let ib ← scalarExpr env (.int 0) b
      some { c with rank := 2, i := ia, j := ib }
    | _ => none
  | .select f e true => do
    let c ← selChain env e
    guard (c.fields.length < 4 && f < 256)
    some { c with fields := c.fields ++ [f] }
  | _ => none

/-- The chain, but only when it actually selects a field: without one there is nothing
    here that the row and cell entry points do not already do. -/
partial def fieldChain (env : List Frame) (c : Core) : Option SelChain := do
  let ch ← selChain env c
  guard (!ch.fields.isEmpty)
  some ch

partial def scalarExpr (env : List Frame) (m : Mode) (c : Core) : Option String := do
  let ty ← CTy.ofMode m
  match c with
  | .at _ e => scalarExpr env m e
  | .lit (.int n) => if ty == .i64 && n ≥ -2147483647 && n ≤ 2147483647 then some s!"{n}LL" else none
  | .lit (.real x) => if ty == .f64 then some (creal x) else none
  | .lit (.bool b) => if ty == .u8 then some (if b then "1" else "0") else none
  | .lit (.char ch) => if ty == .u32 then some s!"{ch}u" else none
  | .lit (.bits b) => if ty == .u64 then some s!"{b}ull" else none
  | .loadCell d s =>
    match varOf env d s with
    | some (v, vt, u) => if vt == ty then some (readVar (v, vt, u)) else none
    | none => some s!"{ty.cellFn}({rtDepthOf env d}, {s})"
  | .deref (.refCell d s) =>
    match varOf env d s with
    | some (v, vt, u) => if vt == ty then some (readVar (v, vt, u)) else none
    | none => some s!"{ty.cellFn}({rtDepthOf env d}, {s})"
  | .deref (.slice base idx true) =>
    match rowReadC env ty base idx with
    | some s => some s
    | none => rowRead env ty base idx
  | .slice base idx false => rowRead env ty base idx
  | .deref (.select f e true) =>
    match srowReadC env ty f e with
    | some s => some s
    | none => do
      let ch ← fieldChain env (.select f e true)
      some s!"{ty.selFn}({ch.args})"
  | .call (.lit (.builtin n)) [arg] =>
    if ty == .f64 && nativeMathFns.contains n then do
      let x ← scalarExpr env (.real 0) arg
      some s!"a68_m_{n}({x})"
    else none
  | .widen src dst e =>
    -- only the widenings that stay inside a native type
    match src, dst with
    | .int 0, .real 0 => do let x ← scalarExpr env (.int 0) e; some s!"((double)({x}))"
    | _, _ => none
  | .monop op mm e => do
    if (op == "LWB" || op == "UPB") && ty == .i64 then
      if let some rv := rowName env e then
        return s!"{rv.name}_{if op == "LWB" then "l" else "u"}0"
    let r ← monopResult op mm
    if r != m then none else
    let x ← scalarExpr env mm e
    monopC op (← CTy.ofMode mm) x
  | .dyop op m1 m2 l r => do
    -- exponentiation, as the evaluator computes it for each pair of operand modes
    if op == "**" then
      match m1, m2, ty with
      | .int 0, .int 0, .i64 => return s!"a68_pow_i({← scalarExpr env (.int 0) l}, {← scalarExpr env (.int 0) r})"
      | .real 0, .int 0, .f64 => return s!"a68_pow_ri({← scalarExpr env (.real 0) l}, {← scalarExpr env (.int 0) r})"
      | .real 0, .real 0, .f64 => return s!"a68_pow_rr({← scalarExpr env (.real 0) l}, {← scalarExpr env (.real 0) r})"
      | _, _, _ => none
    if (op == "LWB" || op == "UPB") && ty == .i64 then
      if let some rv := rowName env r then
        match strip l with
        | .lit (.int k) =>
          if k == 1 || (k == 2 && rv.dims == 2) then
            return s!"{rv.name}_{if op == "LWB" then "l" else "u"}{k - 1}"
        | _ => pure ()
    if m1 != m2 then none else
    let opnd ← CTy.ofMode m1
    let res ← dyopResult op m1
    if res != m then none else
    let a ← scalarExpr env m1 l
    let b ← scalarExpr env m2 r
    dyopC op opnd a b
  | _ => none

end

/-- The mode a node yields, when it can be told from the node itself. -/
def resultMode : Core → Option Mode
  | .at _ e => resultMode e
  | .lit (.int _) => some (.int 0)
  | .lit (.real _) => some (.real 0)
  | .lit (.bool _) => some .bool
  | .lit (.char _) => some .char
  | .lit (.bits _) => some (.bits 0)
  | .loadCell _ _ => none
  | .dyop op m1 _ _ _ => if op == "LWB" || op == "UPB" then some (.int 0) else dyopResult op m1
  | .call f [_] =>
    match strip f with
    | .lit (.builtin n) => if nativeMathFns.contains n then some (.real 0) else none
    | _ => none
  | .monop op m _ => if op == "LWB" || op == "UPB" then some (.int 0) else monopResult op m
  | .widen _ d _ => some d
  | _ => none

/-- A native expression for a node whose mode is not supplied by the caller. -/
def scalarExprAny (env : List Frame) (c : Core) : Option (Mode × String) := do
  let m ← resultMode c
  let e ← scalarExpr env m c
  some (m, e)

/-- Is slot `slot` certainly given a value at its declaration, either by the declaration's
    own initialiser or by the assignment that immediately follows it?  When it is, reads of
    the promoted variable need no test for an undefined value. -/
def slotInitialised (stmts : Array CoreStmt) (slot : Nat) : Bool := Id.run do
  for i in [0:stmts.size] do
    match stmts[i]! with
    | .decl sl _ init =>
      if sl == slot then
        match strip init with
        | .lit .undef =>
          match stmts[i+1]? with
          | some (.unit e) =>
            match strip e with
            | .assign dst _ _ =>
              match strip dst with
              | .refCell 0 ss => return ss == slot
              | _ => return false
            | _ => return false
          | _ => return false
        | _ => return true
    | _ => pure ()
  return false

/-- The `Core` inside a format item: the dynamic replicators, the arguments of general
    patterns and the included formats. -/
partial def fmtChildren : CoreFmt → List Core
  | .rep _ dyn item => dyn.toList ++ fmtChildren item
  | .general args => args
  | .include f => [f]
  | .group items => items.flatMap fmtChildren
  | _ => []

/-- The immediate `Core` children of a node, each with the number of frames entered
    between the node and that child.  It covers every constructor, so an analysis
    written on it cannot silently miss a use. -/
partial def childrenD : Core → List (Nat × Core)
  | .deref e | .deproc e | .rowOf e | .voiding e | .gen e | .at _ e
  | .widen _ _ e | .unite _ e | .monop _ _ e | .select _ e _ => [(0, e)]
  | .assign a b _ | .identRel a b _ | .andThen a b | .orElse a b | .seq a b
  | .dyop _ _ _ a b => [(0, a), (0, b)]
  | .call f args => (0, f) :: args.map ((0, ·))
  | .routine _ _ b => [(1, b)]
  | .slice a idx _ => (0, a) :: idx.flatMap (fun
      | .index e => [(0, e)]
      | .trim l u a => (l.toList ++ u.toList ++ a.toList).map ((0, ·)))
  | .newRow bs i _ => bs.flatMap (fun (l, u) => [(0, l), (0, u)]) ++ [(0, i)]
  | .block _ stmts _ _ => stmts.toList.flatMap (fun
      | .decl _ _ c => [(1, c)]
      | .unit c => [(1, c)]
      | _ => [])
  | .collateral es _ _ => es.map ((0, ·))
  | .cond c t e => [(0, c), (0, t), (0, e)]
  | .caseInt s alts o => (0, s) :: alts.map ((0, ·)) ++ [(0, o)]
  | .caseConf s alts o => (0, s) :: alts.map (fun (_, _, c) => (1, c)) ++ [(0, o)]
  | .loop _ f b t w body =>
    [(0, f), (0, b)] ++ t.toList.map ((0, ·)) ++ w.toList.map ((1, ·)) ++ [(1, body)]
  | .fmt items => items.flatMap (fun it => (fmtChildren it).map ((0, ·)))
  | _ => []

/-- Is the slot read or named anywhere below? -/
partial def seesSlot (slot d : Nat) (c : Core) : Bool :=
  match c with
  | .refCell d' s | .loadCell d' s => d' == d && s == slot
  | _ => (childrenD c).any fun (k, ch) => seesSlot slot (d + k) ch

/-- Is the slot read or named by code that is compiled into another C function: the body
    of a routine text, or a hole of a format text?  Format holes are evaluated in the
    environment the format captured, so their depths are those of the format itself. -/
partial def seenByOtherFn (slot d : Nat) (c : Core) : Bool :=
  match c with
  | .routine _ _ b => seesSlot slot (d + 1) b
  | .fmt items => items.any fun it => (fmtChildren it).any (seesSlot slot d)
  | _ => (childrenD c).any fun (k, ch) => seenByOtherFn slot (d + k) ch

/-- The dimensions and element type of a slot that could be a C array: a fixed row of a
    primitive mode, of one or two dimensions. -/
def rowElemTy : Mode → Option (Nat × CTy)
  | .ref (.row dims false e) | .row dims false e =>
    if dims == 1 || dims == 2 then (CTy.ofMode e).map fun t => (dims, t) else none
  | _ => none

/-- The bounds of the slot's declaration, when it is declared by a row generator whose
    elements start undefined, which is what a C array with cleared flags reproduces. -/
def rowDecl (stmts : Array CoreStmt) (slot : Nat) : Option (List (Core × Core)) := Id.run do
  for st in stmts do
    match st with
    | .decl sl _ init =>
      if sl == slot then
        match strip init with
        | .newRow bs ei false =>
          match strip ei with
          | .lit .undef => return some bs
          | _ => return none
        | _ => return none
    | _ => pure ()
  return none

/-- `a[i]` or `a[i, j]` on the row slot, with a plain subscript for every dimension. -/
def rowElemIdx (d sl dims : Nat) (c : Core) : Option (List Core) :=
  match strip c with
  | .slice base idx true =>
    match strip base with
    | .refCell dd ss =>
      if dd == d && ss == sl && idx.length == dims then
        idx.mapM fun | .index e => some e | _ => none
      else none
    | _ => none
  | _ => none

def isRowNameOf (d sl : Nat) (c : Core) : Bool :=
  match strip c with
  -- the optimiser reads a variable with `loadCell` where it can; for a row variable both
  -- forms yield the same row value
  | .loadCell dd ss => dd == d && ss == sl
  | .deref e => match strip e with | .refCell dd ss => dd == d && ss == sl | _ => false
  | _ => false

mutual
/-- Does anything force the row slot to stay a run-time cell?  What a C array supports is a
    subscript in every dimension, read anywhere, written or updated by an assigning
    operator in statement position, and the bounds enquiries `LWB a`, `UPB a`, `k LWB a`
    and `k UPB a`.  Anything else — the row as a value, a slice, a trim, a reference to an
    element — keeps the cell. -/
partial def rowEscapes (ok : String → Bool) (d sl dims : Nat) (c : Core) : Bool :=
  match c with
  | .at _ e => rowEscapes ok d sl dims e
  | .refCell dd ss | .loadCell dd ss => dd == d && ss == sl
  | .deref e =>
    match rowElemIdx d sl dims e with
    | some ixs => ixs.any (rowEscapes ok d sl dims)
    | none => rowEscapes ok d sl dims e
  | .monop op _ e =>
    if (op == "LWB" || op == "UPB") && isRowNameOf d sl e then false
    else rowEscapes ok d sl dims e
  | .dyop op _ _ l r =>
    if (op == "LWB" || op == "UPB") && isRowNameOf d sl r &&
        (match strip l with | .lit (.int k) => k ≥ 1 && k ≤ (dims : Int) | _ => false) then false
    else rowEscapes ok d sl dims l || rowEscapes ok d sl dims r
  | .voiding e => rowEscapesV ok d sl dims e
  | .block _ stmts _ _ => rowEscapesStmts ok (d + 1) sl dims stmts true
  | .loop _ f b t w body =>
    rowEscapes ok d sl dims f || rowEscapes ok d sl dims b
      || (match t with | some e => rowEscapes ok d sl dims e | none => false)
      || (match w with | some e => rowEscapes ok (d + 1) sl dims e | none => false)
      || rowEscapesV ok (d + 1) sl dims body
  | _ => (childrenD c).any fun (k, ch) => rowEscapes ok (d + k) sl dims ch

partial def rowEscapesV (ok : String → Bool) (d sl dims : Nat) (c : Core) : Bool :=
  match strip c with
  | .voiding e => rowEscapesV ok d sl dims e
  | .seq a b => rowEscapesV ok d sl dims a || rowEscapesV ok d sl dims b
  | .assign dst src _ =>
    match rowElemIdx d sl dims dst with
    | some ixs => ixs.any (rowEscapes ok d sl dims) || rowEscapes ok d sl dims src
    | none => rowEscapes ok d sl dims dst || rowEscapes ok d sl dims src
  | .dyop op m1 m2 l r =>
    match rowElemIdx d sl dims l with
    | some ixs => !ok op || ixs.any (rowEscapes ok d sl dims) || rowEscapes ok d sl dims r
    | none => rowEscapes ok d sl dims (.dyop op m1 m2 l r)
  | .cond a b e => rowEscapes ok d sl dims a || rowEscapesV ok d sl dims b || rowEscapesV ok d sl dims e
  | .block _ stmts _ _ => rowEscapesStmts ok (d + 1) sl dims stmts false
  | c' => rowEscapes ok d sl dims c'

partial def rowEscapesStmts (ok : String → Bool) (d sl dims : Nat) (stmts : Array CoreStmt)
    (wantValue : Bool) : Bool := Id.run do
  let vp := voidPositions stmts wantValue
  for i in [0:stmts.size] do
    let bad := match stmts[i]! with
      | .decl _ _ init => rowEscapes ok d sl dims init
      | .unit e => if vp[i]! == true then rowEscapesV ok d sl dims e else rowEscapes ok d sl dims e
      | .label _ | .exit => false
    if bad then return true
  return false
end

/-- A fixed row of structures whose fields are all primitive, seen through declared mode
    names: its dimensions and the type of each field. -/
def rowStructTy (tab : Mode.Table) : Mode → Option (Nat × Array CTy)
  | .ref (.row dims false e) | .row dims false e =>
    if dims == 1 || dims == 2 then
      match Mode.resolve tab e with
      | .struct fs =>
        match fs.mapM (fun (_, fm) => CTy.ofMode (Mode.resolve tab fm)) with
        | some tys => if tys.isEmpty || tys.length > 16 then none else some (dims, tys.toArray)
        | none => none
      | _ => none
    else none
  | _ => none

/-- The bounds and field count of a row-of-structures declaration whose every field starts
    undefined. -/
def rowStructDecl (stmts : Array CoreStmt) (slot : Nat) : Option (List (Core × Core) × Nat) := Id.run do
  for st in stmts do
    match st with
    | .decl sl _ init =>
      if sl == slot then
        match strip init with
        | .newRow bs ei false =>
          match strip ei with
          | .collateral es _ _ =>
            return (if es.all (fun e => match strip e with | .lit .undef => true | _ => false)
                    then some (bs, es.length) else none)
          | _ => return none
        | _ => return none
    | _ => pure ()
  return none

/-- `f OF a[i]` or `f OF a[i, j]` on the row slot: the field and the subscripts. -/
def srowFieldIdx (d sl dims nf : Nat) (c : Core) : Option (Nat × List Core) :=
  match strip c with
  | .select f e true => if f < nf then (rowElemIdx d sl dims e).map fun ixs => (f, ixs) else none
  | _ => none

/-- A field of an element of a promoted row of structures, as a destination. -/
def srowFieldDst (env : List Frame) (c : Core) : Option (RowVar × Nat × List CoreIdx) :=
  match strip c with
  | .select f e true =>
    match strip e with
    | .slice base idx true =>
      match strip base with
      | .refCell d s =>
        match rowOf env d s with
        | some rv =>
          if rv.fields.isEmpty || f ≥ rv.fields.size || idx.length != rv.dims then none
          else some (rv, f, idx)
        | none => none
      | _ => none
    | _ => none
  | _ => none

mutual
/-- What a row of structures kept as C arrays supports: a field of a fully subscripted
    element, read anywhere, written or updated by an assigning operator in statement
    position; a whole element assigned from a structure display in statement position; and
    the bounds enquiries.  Anything else keeps the cell. -/
partial def srowEscapes (tys : Array CTy) (d sl dims : Nat) (c : Core) : Bool :=
  match c with
  | .at _ e => srowEscapes tys d sl dims e
  | .refCell dd ss | .loadCell dd ss => dd == d && ss == sl
  | .deref e =>
    match srowFieldIdx d sl dims tys.size e with
    | some (_, ixs) => ixs.any (srowEscapes tys d sl dims)
    | none => srowEscapes tys d sl dims e
  | .monop op _ e =>
    if (op == "LWB" || op == "UPB") && isRowNameOf d sl e then false
    else srowEscapes tys d sl dims e
  | .dyop op _ _ l r =>
    if (op == "LWB" || op == "UPB") && isRowNameOf d sl r &&
        (match strip l with | .lit (.int k) => k ≥ 1 && k ≤ (dims : Int) | _ => false) then false
    else srowEscapes tys d sl dims l || srowEscapes tys d sl dims r
  | .voiding e => srowEscapesV tys d sl dims e
  | .block _ stmts _ _ => srowEscapesStmts tys (d + 1) sl dims stmts true
  | .loop _ f b t w body =>
    srowEscapes tys d sl dims f || srowEscapes tys d sl dims b
      || (match t with | some e => srowEscapes tys d sl dims e | none => false)
      || (match w with | some e => srowEscapes tys (d + 1) sl dims e | none => false)
      || srowEscapesV tys (d + 1) sl dims body
  | _ => (childrenD c).any fun (k, ch) => srowEscapes tys (d + k) sl dims ch

partial def srowEscapesV (tys : Array CTy) (d sl dims : Nat) (c : Core) : Bool :=
  match strip c with
  | .voiding e => srowEscapesV tys d sl dims e
  | .seq a b => srowEscapesV tys d sl dims a || srowEscapesV tys d sl dims b
  | .assign dst src _ =>
    match srowFieldIdx d sl dims tys.size dst with
    | some (_, ixs) => ixs.any (srowEscapes tys d sl dims) || srowEscapes tys d sl dims src
    | none =>
      match rowElemIdx d sl dims dst, strip src with
      | some ixs, .collateral es _ _ =>
        if es.length == tys.size then
          ixs.any (srowEscapes tys d sl dims) || es.any (srowEscapes tys d sl dims)
        else true
      | _, _ => srowEscapes tys d sl dims dst || srowEscapes tys d sl dims src
  | .dyop op m1 m2 l r =>
    match srowFieldIdx d sl dims tys.size l with
    | some (f, ixs) =>
      !assignsNatively tys[f]! op || ixs.any (srowEscapes tys d sl dims) || srowEscapes tys d sl dims r
    | none => srowEscapes tys d sl dims (.dyop op m1 m2 l r)
  | .cond a b e =>
    srowEscapes tys d sl dims a || srowEscapesV tys d sl dims b || srowEscapesV tys d sl dims e
  | .block _ stmts _ _ => srowEscapesStmts tys (d + 1) sl dims stmts false
  | c' => srowEscapes tys d sl dims c'

partial def srowEscapesStmts (tys : Array CTy) (d sl dims : Nat) (stmts : Array CoreStmt)
    (wantValue : Bool) : Bool := Id.run do
  let vp := voidPositions stmts wantValue
  for i in [0:stmts.size] do
    let bad := match stmts[i]! with
      | .decl _ _ init => srowEscapes tys d sl dims init
      | .unit e => if vp[i]! == true then srowEscapesV tys d sl dims e else srowEscapes tys d sl dims e
      | .label _ | .exit => false
    if bad then return true
  return false
end

/-- Is this an assigning operator, whose left operand is a name it writes through? -/
def isAssignOpName (op : String) : Bool :=
  ["+:=", "-:=", "*:=", "/:=", "%:=", "%*:=", "&:=", "|:="].contains op

/-- A name built from a frame cell by subscripts and field selections: `x`, `a[i]`,
    `f OF a[i]`.  Read at once or written through, such a name creates no reference that
    outlives the statement. -/
partial def cellName : Core → Bool
  | .at _ e => cellName e
  | .refCell _ _ => true
  | .slice b _ true => cellName b
  | .select _ b true => cellName b
  | _ => false

mutual
/-- Could anything in `c` let a cell allocated during a routine call outlive the call?  A
    generator; a routine or format text, which captures the environment; a call of anything
    but a standard procedure, which could do either; or a reference to a local cell used as a
    value, which could be stored or returned.  A name read at once, or written through by an
    assignment or an assigning operator, is not such a reference. -/
partial def cellsEscape (c : Core) : Bool :=
  match c with
  | .at _ e => cellsEscape e
  | .gen _ | .routine _ _ _ | .fmt _ => true
  | .refCell _ _ => true
  | .slice _ _ true | .select _ _ true => if cellName c then true else subEscape c
  | .deref e => if cellName e then nameIdxEscape e else cellsEscape e
  | .assign dst src _ =>
    (if cellName dst then nameIdxEscape dst else cellsEscape dst) || cellsEscape src
  | .dyop op _ _ l r =>
    (if isAssignOpName op && cellName l then nameIdxEscape l else cellsEscape l) || cellsEscape r
  | .call f args =>
    (match strip f with | .lit (.builtin _) => false | _ => true) || args.any cellsEscape
  | _ => subEscape c

partial def subEscape (c : Core) : Bool := (childrenD c).any fun (_, ch) => cellsEscape ch

/-- The subscripts inside a name, which are ordinary expressions. -/
partial def nameIdxEscape : Core → Bool
  | .at _ e => nameIdxEscape e
  | .refCell _ _ => false
  | .slice b idx true => nameIdxEscape b || idx.any fun
      | .index e => cellsEscape e
      | .trim l u a => (l.toList ++ u.toList ++ a.toList).any cellsEscape
  | .select _ b true => nameIdxEscape b
  | e => cellsEscape e
end

/-- Can a value of this mode hold a reference to a cell, or an environment? -/
partial def modeHoldsNames (tab : Mode.Table) (m : Mode) (fuel : Nat := 16) : Bool :=
  if fuel == 0 then true else
  match Mode.resolve tab m with
  | .ref _ | .proc _ _ | .format | .file | .channel | .sema | .simplin | .named _ => true
  | .row _ _ e => modeHoldsNames tab e (fuel - 1)
  | .struct fs => fs.any fun (_, fm) => modeHoldsNames tab fm (fuel - 1)
  | .union ms => ms.any fun mm => modeHoldsNames tab mm (fuel - 1)
  | _ => false

/-- Which of a frame's slots can become C variables.  A slot qualifies when its declared
    mode is primitive and nothing inside the frame needs it to live in a cell.  If no
    routine text or format text occurs in the body — those compile to separate C functions
    that reach the frame through the run-time environment — and every slot qualifies, then
    no run-time frame is emitted for it at all. -/
def planFrame (tag : Nat) (size : Nat) (slotModes : Array (Option Mode))
    (stmts : Array CoreStmt) (wantValue : Bool) (tab : Mode.Table := {}) : Frame := Id.run do
  -- A routine text or a format text is compiled into a C function of its own and reaches
  -- this frame through the run-time environment.  A slot it can see therefore needs its
  -- cell; a slot it cannot see is as free to become a C variable as in any other block.
  -- Its depths count this frame, though, so the frame is pushed whenever one is present.
  let others := stmts.toList.any hasOtherFnStmt
  let seenElsewhere (i : Nat) : Bool :=
    others && stmts.toList.any fun
      | .decl _ _ c | .unit c => seenByOtherFn i 0 c
      | _ => false
  let mut vars : Array (Option (String × CTy × Bool)) := #[]
  let mut rows : Array (Option RowVar) := #[]
  let mut all := true
  for i in [0:size] do
    match (slotModes[i]?.join).bind CTy.ofMode with
    | some t =>
      rows := rows.push none
      if seenElsewhere i || slotEscapesStmts (assignsNatively t) 0 i stmts wantValue then
        vars := vars.push none; all := false
      else
        vars := vars.push (some (s!"p{tag}_{i}", t, !slotInitialised stmts i))
    | none =>
      vars := vars.push none
      -- a fixed row of primitive elements, used only through subscripts and bounds
      -- enquiries, can be a C array
      match (slotModes[i]?.join).bind rowElemTy, rowDecl stmts i with
      | some (dims, t), some bs =>
        if bs.length != dims || seenElsewhere i
            || rowEscapesStmts (assignsNatively t) 0 i dims stmts wantValue then
          rows := rows.push none; all := false
        else
          rows := rows.push (some { name := s!"r{tag}_{i}", ty := t, dims := dims })
      | _, _ =>
        -- a fixed row of structures of primitive fields can be one C array per field
        match (slotModes[i]?.join).bind (rowStructTy tab), rowStructDecl stmts i with
        | some (dims, tys), some (bs, nf) =>
          if bs.length != dims || nf != tys.size || seenElsewhere i
              || srowEscapesStmts tys 0 i dims stmts wantValue then
            rows := rows.push none; all := false
          else
            rows := rows.push (some { name := s!"r{tag}_{i}", ty := tys[0]!, dims := dims, fields := tys })
        | _, _ => rows := rows.push none; all := false
  return { vars := vars, rows := rows, pushed := others || !all }

def env : M (List Frame) := do return (← get).frames
def rtd (d : Nat) : M Nat := do return rtDepthOf (← env) d
def lvar (d s : Nat) : M (Option (String × CTy × Bool)) := do return varOf (← env) d s

/-- Can this routine also be a plain C function?  Its frame must be exactly its parameters,
    each of primitive mode and never named, its result primitive or VOID, and nothing
    inside may be compiled into a further C function that would reach the frame through
    the run-time environment, which a plain C function does not have. -/
def natSigOf (m : Mode) (nparams frameSize : Nat) (body : Core) : Option NatSig := do
  if frameSize != nparams then none else
  match m with
  | .proc ps r =>
    if ps.length != nparams then none else
    let ptys ← ps.mapM CTy.ofMode
    let rty : Option CTy ← (match r with
      | .void => some none
      | _ => (CTy.ofMode r).map some)
    if hasOtherFn body then none else
    if (List.range nparams).any (fun i => slotEscapes (fun _ => false) 0 i body) then none else
    some { ptys := ptys.toArray, rty := rty }
  | _ => none

/-- The routine a call certainly goes to, when it has a plain C entry point that can be
    called right here: the callee is a slot known to hold that routine, and the frame the
    slot lives in is the innermost run-time frame, so the environment the routine captured
    is the one in effect and the call needs no environment switch. -/
def staticNat (env : List Frame) (f : Core) : Option ProcInfo := do
  match strip f with
  | .loadCell d s =>
    let fr ← env[d]?
    let pi ← (fr.procs[s]?).join
    if (varOf env d s).isSome || rtDepthOf env d != 0 then none else some pi
  | _ => none

/-- Does the routine body read or name a frame outside its own?  A body that does not can be
    run from anywhere, since it needs no environment but its arguments. -/
partial def outerRef (depth : Nat) (c : Core) : Bool :=
  match c with
  | .loadCell d _ | .refCell d _ => d ≥ depth
  | _ => (childrenD c).any fun (k, ch) => outerRef (depth + k) ch

/-- A call through a procedure-valued slot whose routine cannot be known statically, such as
    a procedure parameter: the C signature a plain entry point for it would have, when the
    slot's mode allows one.  Which routine the slot holds is looked up at run time. -/
def dynNat (env : List Frame) (f : Core) : Option NatSig := do
  match strip f with
  | .loadCell d s =>
    if (varOf env d s).isSome || (staticNat env f).isSome then none else
    let fr ← env[d]?
    let m ← (fr.modes[s]?).join
    match m with
    | .proc ps r =>
      let ptys ← ps.mapM CTy.ofMode
      let rty : Option CTy ← (match r with
        | .void => some none
        | _ => (CTy.ofMode r).map some)
      some { ptys := ptys.toArray, rty := rty }
    | _ => none
  | _ => none

/-- Does the native spine of `c` contain such a call? -/
partial def hasNatCall (env : List Frame) (c : Core) : Bool :=
  match c with
  | .at _ e | .monop _ _ e | .widen _ _ e => hasNatCall env e
  | .dyop _ _ _ l r => hasNatCall env l || hasNatCall env r
  | .call f _ => (staticNat env f).isSome || (dynNat env f).isSome
  | _ => false

/-- Can `c` be computed as a native value of mode `m`, calls included? -/
partial def natOk (env : List Frame) (m : Mode) (c : Core) : Bool :=
  match c with
  | .at _ e => natOk env m e
  | .call f args =>
    match staticNat env f with
    | some pi =>
      CTy.ofMode m == pi.sig.rty && pi.sig.rty.isSome && args.length == pi.sig.ptys.size
        && (List.range args.length).all fun i => natOk env (pi.sig.ptys[i]!).toMode args[i]!
    | none =>
      match dynNat env f with
      | some sg =>
        CTy.ofMode m == sg.rty && sg.rty.isSome && args.length == sg.ptys.size
          && (List.range args.length).all fun i => natOk env (sg.ptys[i]!).toMode args[i]!
      | none => false
  | .monop op mm e =>
    monopResult op mm == some m && (match CTy.ofMode mm with
      | some t => (monopC op t "x").isSome && natOk env mm e
      | none => false)
  | .dyop op m1 m2 l r =>
    m1 == m2 && dyopResult op m1 == some m && (match CTy.ofMode m1 with
      | some t => (dyopC op t "a" "b").isSome && natOk env m1 l && natOk env m2 r
      | none => false)
  | .widen (.int 0) (.real 0) e => m == .real 0 && natOk env (.int 0) e
  | _ => (scalarExpr env m c).isSome

/-- The mode a node yields, counting the calls whose callee is known. -/
def resultModeE (env : List Frame) (c : Core) : Option Mode :=
  match strip c with
  | .call f _ =>
    match staticNat env f with
    | some pi => do let t ← pi.sig.rty; some t.toMode
    | none => do let sg ← dynNat env f; let t ← sg.rty; some t.toMode
  | _ => resultMode c

/-- May this operand be left to be evaluated after a call to its right?  Only when doing so
    is unobservable: a literal, or a C variable that needs no undefined test, since a callee
    cannot reach a C variable of this function and reading one can neither fail nor act. -/
def delayable (env : List Frame) (c : Core) : Bool :=
  match strip c with
  | .lit _ => true
  | .loadCell d s | .deref (.refCell d s) =>
    match varOf env d s with
    | some (_, _, u) => !u
    | none => false
  | _ => false

/-- Reserve the index of a plain C entry point. -/
def reserveNative : M Nat := do
  let s ← get
  set { s with nfns := s.nfns.push ("", #[]) }
  return s.nfns.size

mutual

/-- The offset of `a[i]` or `a[i, j]` in a promoted row.  The subscripts are evaluated in
    order and the bounds checked before anything else happens, which is the order the
    evaluator follows when the element is the destination of an assignment. -/
partial def rowOffset (rv : RowVar) (idx : List CoreIdx) : M String := do
  let mut xs : Array String := #[]
  for ix in idx do
    match ix with
    | .index e =>
      let v ← match scalarExpr (← env) (.int 0) e with
        | some s => pure s
        | none => do gen e; pure "a68_int()"
      let k ← fresh
      emit s!"int64_t x{k} = {v};"
      xs := xs.push s!"x{k}"
    | _ => pure ()
  let k ← fresh
  let r := rv.name
  if rv.dims == 1 then
    emit s!"size_t o{k} = a68_ao({r}_l0, {r}_u0, {xs[0]!});"
  else
    emit s!"size_t o{k} = a68_ao2({r}_l0, {r}_u0, {r}_l1, {r}_u1, {xs[0]!}, {xs[1]!});"
  return s!"o{k}"

/-- A value of the element type, computed into a C variable. -/
partial def rowValue (ty : CTy) (src : Core) : M String := do
  let ev ← env
  let k ← fresh
  match scalarExpr ev ty.toMode src with
  | some e => emit s!"{ty.name} v{k} = {e};"
  | none =>
    if hasNatCall ev src && natOk ev ty.toMode src then
      let e ← anf ty.toMode src
      emit s!"{ty.name} v{k} = {e};"
    else do
      gen src
      emit s!"{ty.name} v{k} = {ty.popFn}();"
  return s!"v{k}"

/-- The declaration of a row promoted to a C array: its bounds, evaluated in the order the
    generator evaluates them, and storage for its elements with every flag cleared. -/
partial def genRowDecl (rv : RowVar) (init : Core) : M Unit := do
  match strip init with
  | .newRow bs _ _ =>
    let mut k := 0
    for (lo, hi) in bs do
      let l ← match scalarExpr (← env) (.int 0) lo with
        | some s => pure s
        | none => do gen lo; pure "a68_int()"
      emit s!"{rv.name}_l{k} = {l};"
      let u ← match scalarExpr (← env) (.int 0) hi with
        | some s => pure s
        | none => do gen hi; pure "a68_int()"
      emit s!"{rv.name}_u{k} = {u};"
      k := k + 1
    let r := rv.name
    let n0 := s!"({r}_u0 >= {r}_l0 ? {r}_u0 - {r}_l0 + 1 : 0)"
    let n := if rv.dims == 2 then s!"{n0} * ({r}_u1 >= {r}_l1 ? {r}_u1 - {r}_l1 + 1 : 0)" else n0
    if rv.fields.isEmpty then
      emit s!"{r}_p = ({rv.ty.name}*) a68_row_alloc((size_t)({n}), sizeof({rv.ty.name})); {r}_d = (uint8_t*) a68_row_alloc((size_t)({n}), 1);"
    else
      for fk in [0:rv.fields.size] do
        let t := rv.fields[fk]!
        emit s!"{r}_p{fk} = ({t.name}*) a68_row_alloc((size_t)({n}), sizeof({t.name})); {r}_d{fk} = (uint8_t*) a68_row_alloc((size_t)({n}), 1);"
  | _ => pure ()

/-- A call through a procedure-valued slot.  When the routine the slot holds at run time has
    a plain C entry point that needs no environment, that is called; otherwise the call is
    boxed.  The slot is read first and the arguments are evaluated after it, once, on
    whichever path is taken, which is the evaluator's order. -/
partial def dynCall (sg : NatSig) (f : Core) (args : List Core) (dest : Option String) : M Unit := do
  match strip f with
  | .loadCell d s =>
    let k ← fresh
    let rtyName := match sg.rty with | some t => t.name | none => "void"
    let plist := if sg.ptys.isEmpty then "void" else ", ".intercalate (sg.ptys.toList.map CTy.name)
    let ptrTy := rtyName ++ " (*)(" ++ plist ++ ")"
    emit s!"void* f{k} = a68_nf_of_fn[a68_u32(a68rt_cell_cproc({← rtd d}, {s}, W))];"
    emit ("if (f" ++ toString k ++ ") {")
    indent do
      let as ← natArgs sg.ptys args
      let callE := "((" ++ ptrTy ++ ") f" ++ toString k ++ ")(" ++ ", ".intercalate as.toList ++ ")"
      match dest with
      | some v => emit s!"{v} = {callE};"
      | none => emit s!"(void) {callE};"
      jumpCheck
    emit "} else {"
    indent do
      genNode (.call f args)
      match dest, sg.rty with
      | some v, some t => emit s!"{v} = {t.popFn}();"
      | _, _ => emit "a68_v(a68rt_pop(W));"
    emit "}"
  | _ => genNode (.call f args)

/-- Put a native expression in a fresh C variable, so that it is evaluated here. -/
partial def hoistT (t : CTy) (e : String) : M String := do
  let k ← fresh
  emit s!"{t.name} t{k} = {e};"
  return s!"t{k}"

/-- The arguments of a direct call, evaluated left to right: an argument is hoisted into a
    C variable whenever a later argument makes a call, unless delaying it is unobservable. -/
partial def natArgs (ptys : Array CTy) (args : List Core) : M (Array String) := do
  let ev ← env
  let mut as : Array String := #[]
  for i in [0:args.length] do
    let a := args[i]!
    let pty := ptys[i]!
    let x ← anf pty.toMode a
    let later := (args.drop (i + 1)).any (hasNatCall ev)
    let x ← if later && !delayable ev a then hoistT pty x else pure x
    as := as.push x
  return as

/-- `c`, which `natOk` accepts, as a native expression, emitting its calls as statements in
    exactly the order the evaluator performs them.  A subtree without calls is rendered by
    `scalarExpr` and evaluated where it is used; the left operand of an operator whose right
    operand makes a call is hoisted first, so nothing is reordered. -/
partial def anf (m : Mode) (c : Core) : M String := do
  let ev ← env
  if !hasNatCall ev c then return (scalarExpr ev m c).getD "0"
  match c with
  | .at _ e => anf m e
  | .call f args =>
    match staticNat ev f with
    | some pi =>
      let as ← natArgs pi.sig.ptys args
      let k ← fresh
      let rty := pi.sig.rty.get!
      emit s!"{rty.name} t{k} = a68_nf{pi.nidx}({", ".intercalate as.toList});"
      jumpCheck
      return s!"t{k}"
    | none =>
      let sg := (dynNat ev f).get!
      let rty := sg.rty.get!
      let k ← fresh
      emit s!"{rty.name} t{k};"
      dynCall sg f args (some s!"t{k}")
      return s!"t{k}"
  | .monop op mm e =>
    let x ← anf mm e
    return (monopC op (CTy.ofMode mm).get! x).getD "0"
  | .dyop op m1 _ l r =>
    let t := (CTy.ofMode m1).get!
    let a ← anf m1 l
    let a ← if hasNatCall ev r && !delayable ev l then hoistT t a else pure a
    let b ← anf m1 r
    return (dyopC op t a b).getD "0"
  | .widen _ _ e =>
    let x ← anf (.int 0) e
    return s!"((double)({x}))"
  | _ => return (scalarExpr ev m c).getD "0"

/-- Emit the plain C entry point `a68_nf{k}` of a routine.  Its parameters are C variables,
    no run-time frame is pushed, and the frames outside it are those of its declaration,
    so its depths translate exactly as they would in the boxed entry point. -/
partial def genNative (k : Nat) (sg : NatSig) (body : Core) (outer : List Frame) : M Unit := do
  let s ← get
  let savedCur := s.cur
  let savedLabels := s.labels
  let savedDepth := s.depth
  let savedFrames := s.frames
  let savedRet := s.ret
  let params := (List.range sg.ptys.size).map fun i => s!"{(sg.ptys[i]!).name} a{k}_{i}"
  let plist := if params.isEmpty then "void" else ", ".intercalate params
  let rtyName := match sg.rty with | some t => t.name | none => "void"
  let pf : Frame := {
    vars := (List.range sg.ptys.size).toArray.map fun i => some (s!"a{k}_{i}", sg.ptys[i]!, false),
    pushed := false }
  let ret := match sg.rty with | some _ => "return 0;" | none => "return;"
  modify fun st => { st with cur := #[], labels := labelsOf body, depth := 1, frames := pf :: outer, ret := ret }
  match sg.rty with
  | some t =>
    emit s!"{t.name} rv{k} = 0;"
    genInto t s!"rv{k}" body
    emit s!"return rv{k};"
  | none =>
    genVoid body
    emit "return;"
  let st ← get
  set { st with cur := savedCur, labels := savedLabels, depth := savedDepth, frames := savedFrames,
                ret := savedRet, nfns := st.nfns.set! k (s!"static {rtyName} a68_nf{k}({plist})", st.cur) }

/-- Emit code leaving the value of `c` on the operand stack. -/
partial def gen (c : Core) : M Unit := do
  -- an element of a row promoted to a C array, whatever its subscripts
  match c with
  | .deref (.slice base idx true) =>
    match strip base with
    | .refCell d sl =>
      match rowOf (← env) d sl with
      | some rv =>
        if !rv.fields.isEmpty then pure () else
        let o ← rowOffset rv idx
        emit s!"a68_v({rv.ty.pushFn}(({rv.name}_d[{o}] ? {rv.name}_p[{o}] : {rv.ty.undefFn}()), W));"
        return
      | none => pure ()
    | _ => pure ()
  | .deref sel@(.select _ _ true) =>
    -- a field of an element of a row of structures kept as C arrays
    if let some (rv, f, idx) := srowFieldDst (← env) sel then
      let o ← rowOffset rv idx
      let fty := rv.fields[f]!
      emit s!"a68_v({fty.pushFn}(({rv.name}_d{f}[{o}] ? {rv.name}_p{f}[{o}] : {fty.undefFn}()), W));"
      return
  | _ => pure ()
  -- an expression that calls a routine with a plain C entry point is computed natively,
  -- its calls made as C calls, and boxed once
  let ev0 ← env
  if hasNatCall ev0 c then
    match resultModeE ev0 c with
    | some m0 =>
      match CTy.ofMode m0 with
      | some ty0 =>
        if natOk ev0 m0 c then
          let e ← anf m0 c
          emit s!"a68_v({ty0.pushFn}({e}, W));"
          return
      | none => pure ()
    | none => pure ()
  -- a value of primitive mode is computed in a native C type and boxed once, instead of
  -- pushing and popping a heap-allocated value for every intermediate result
  match scalarExprAny (← env) c with
  | some (m, e) =>
    match CTy.ofMode m with
    | some ty => emit s!"a68_v({ty.pushFn}({e}, W));"
    | none => genNode c
  | none => genNode c

/-- Compute the primitive value of `c` into the C variable `v`, instead of pushing it
    onto the operand stack.  This is what a `WHILE` condition wants: the test itself is a
    C value, and the statements that produce it are statements. -/
partial def genInto (ty : CTy) (v : String) (c : Core) : M Unit := do
  match strip c with
  | .seq a b => genVoid a; genInto ty v b
  | .cond cc t e =>
    match scalarExpr (← env) .bool cc with
    | some ce => emit ("if (" ++ ce ++ ") {")
    | none => do gen cc; emit "if (a68_bool()) {"
    indent (genInto ty v t)
    emit "} else {"
    indent (genInto ty v e)
    emit "}"
  | .block size stmts lb nl => genBlockAt size stmts lb nl true (some (ty, v))
  | .andThen l r =>
    if ty != .u8 then genFallbackInto ty v c else do
      genInto ty v l
      emit ("if (" ++ v ++ ") {")
      indent (genInto ty v r)
      emit "}"
  | .orElse l r =>
    if ty != .u8 then genFallbackInto ty v c else do
      genInto ty v l
      emit ("if (!" ++ v ++ ") {")
      indent (genInto ty v r)
      emit "}"
  | c' => genFallbackInto ty v c'

partial def genFallbackInto (ty : CTy) (v : String) (c : Core) : M Unit := do
  match scalarExpr (← env) ty.toMode c with
  | some e => emit s!"{v} = {e};"
  | none =>
    let ev ← env
    if hasNatCall ev c && natOk ev ty.toMode c then
      let e ← anf ty.toMode c
      emit s!"{v} = {e};"
    else do gen c; emit s!"{v} = {ty.popFn}();"

/-- Emit `c` in statement position.  Its value is discarded, so none of the push, nip and
    pop traffic that keeps a value on the operand stack has to be emitted at all. -/
partial def genVoid (c : Core) : M Unit := do
  match c with
  | .at p e => emit s!"a68_line({p.line});"; genVoid e
  | .voiding e => genVoid e
  | .seq a b => genVoid a; genVoid b
  | .lit _ | .skip _ | .loadCell _ _ | .refCell _ _ => pure ()
  | .assign dst src flex =>
    match ← storeScalar dst src with
    | true => pure ()
    | false =>
      gen dst
      gen src
      emit s!"a68_v(a68rt_assign({if flex then 1 else 0}, W));"
      emit "a68_v(a68rt_pop(W));"
  | .dyop op m1 m2 l r =>
    if (← assignOpVoid op m1 m2 l r) then pure ()
    else if op == "+:=" && (← appendTo m1 l r) then pure ()
    else do gen c; emit "a68_v(a68rt_pop(W));"
  | .cond c t e =>
    match scalarExpr (← env) .bool c with
    | some ce => emit ("if (" ++ ce ++ ") {")
    | none => do gen c; emit "if (a68_bool()) {"
    indent (genVoid t)
    emit "} else {"
    indent (genVoid e)
    emit "}"
  | .block size stmts lb nl => genBlockAt size stmts lb nl false
  | .loop slot f b t w body => genLoopAt slot f b t w body false
  | .goto l => genNode (.goto l)
  | .stop => emit "a68_v(a68rt_stop(W));"
  | .call f args =>
    let ev ← env
    match staticNat ev f with
    | some pi =>
      if args.length == pi.sig.ptys.size &&
          (List.range args.length).all (fun i => natOk ev (pi.sig.ptys[i]!).toMode args[i]!) then
        let as ← natArgs pi.sig.ptys args
        emit s!"(void) a68_nf{pi.nidx}({", ".intercalate as.toList});"
        jumpCheck
      else do gen c; emit "a68_v(a68rt_pop(W));"
    | none =>
      match dynNat ev f with
      | some sg =>
        if args.length == sg.ptys.size &&
            (List.range args.length).all (fun i => natOk ev (sg.ptys[i]!).toMode args[i]!) then
          dynCall sg f args none
        else do gen c; emit "a68_v(a68rt_pop(W));"
      | none => do gen c; emit "a68_v(a68rt_pop(W));"
  | _ => gen c; emit "a68_v(a68rt_pop(W));"

/-- `x +:= e` in statement position: the variable or cell is updated in place, with
    nothing boxed and no reference built.  Returns whether it applied. -/
partial def assignOpVoid (op : String) (m1 m2 : Mode) (l r : Core) : M Bool := do
  -- `a[i] +:= e` on a row promoted to a C array: the element, then the right operand, then
  -- the current value with its undefined test, as the evaluator reads them
  match strip l with
  | .slice base idx true =>
    match strip base with
    | .refCell dd ss =>
      if let some rv := rowOf (← env) dd ss then
        if !rv.fields.isEmpty || !assignsNatively rv.ty op then return false
        let o ← rowOffset rv idx
        let rs ← rowValue rv.ty r
        let cur := s!"({rv.name}_d[{o}] ? {rv.name}_p[{o}] : {rv.ty.undefFn}())"
        match nativeAssignOp op rv.ty cur rs with
        | some e => emit s!"{rv.name}_p[{o}] = {e}; {rv.name}_d[{o}] = 1;"; return true
        | none => return false
    | _ => pure ()
  | .select _ _ true =>
    if let some (rv, f, idx) := srowFieldDst (← env) l then
      let fty := rv.fields[f]!
      if !assignsNatively fty op then return false
      let o ← rowOffset rv idx
      let rs ← rowValue fty r
      let cur := s!"({rv.name}_d{f}[{o}] ? {rv.name}_p{f}[{o}] : {fty.undefFn}())"
      match nativeAssignOp op fty cur rs with
      | some e => emit s!"{rv.name}_p{f}[{o}] = {e}; {rv.name}_d{f}[{o}] = 1;"; return true
      | none => return false
  | _ => pure ()
  match m1 with
  | .ref tm =>
    match CTy.ofMode tm, strip l with
    | some ty, .refCell dd ss =>
      let ev ← env
      let promoted := varOf ev dd ss
      -- a promoted variable has no cell to take a reference to, so once the analysis has
      -- allowed the operator this path has to carry it through
      if promoted.isSome && !assignsNatively ty op then return false
      match CTy.ofMode m2 with
      | none => return false
      | some rty =>
        -- the right operand is evaluated first, as the evaluator does, and the variable
        -- is read after it, in case evaluating it wrote to the variable
        let rs : Option String ← match scalarExpr ev m2 r with
          | some e => pure (some e)
          | none =>
            -- only worth the temporary when the destination has no cell to fall back to
            if promoted.isNone then pure none else do
              let t ← fresh
              gen r
              emit s!"{rty.name} t{t} = {rty.popFn}();"
              pure (some s!"t{t}")
        let some rs := rs | return false
        let cur := match promoted with
          | some vv => readVar vv
          | none => s!"{ty.cellFn}({rtDepthOf ev dd}, {ss})"
        match nativeAssignOp op ty cur rs with
        | none => return false
        | some e =>
          match promoted with
          | some (v, _, u) => emit (if u then s!"{v} = {e}; {v}_i = 1;" else s!"{v} = {e};")
          | none => emit s!"{ty.setFn}({rtDepthOf ev dd}, {ss}, {e});"
          return true
    | _, _ => return false
  | _ => return false

/-- `s +:= t` where `s` is a whole cell holding a row: one call that appends to the row in
    place, instead of a reference, a rowing and an operator that rebuilds the whole row.
    Returns whether it applied. -/
partial def appendTo (m1 : Mode) (lhs rhs : Core) : M Bool := do
  match m1 with
  | .ref (.row 1 _ _) =>
    match strip lhs with
    | .refCell d s =>
      if (← lvar d s).isSome then return false
      let dd ← rtd d
      match strip rhs with
      | .rowOf e =>
        match scalarExpr (← env) .char e with
        | some ce => emit s!"a68_appendc({dd}, {s}, {ce});"; return true
        | none => do gen rhs; emit s!"a68_v(a68rt_append({dd}, {s}, W));"; return true
      | _ => do gen rhs; emit s!"a68_v(a68rt_append({dd}, {s}, W));"; return true
    | _ => return false
  | _ => return false

/-- `dest := <value>` written straight into its C variable or its cell, leaving nothing
    on the operand stack.  Returns whether it applied. -/
partial def storeScalar (dst src : Core) : M Bool := do
  match strip dst with
  | .refCell dd ss =>
    match ← lvar dd ss with
    | some (v, ty, u) =>
      -- a promoted variable has no cell, so this path must always succeed
      let setFlag := if u then s!" {v}_i = 1;" else ""
      match scalarExpr (← env) ty.toMode src with
      | some e => emit s!"{v} = {e};{setFlag}"
      | none =>
        let ev ← env
        if hasNatCall ev src && natOk ev ty.toMode src then
          let e ← anf ty.toMode src
          emit s!"{v} = {e};{setFlag}"
        else do gen src; emit s!"{v} = {ty.popFn}();{setFlag}"
      return true
    | none =>
      match scalarExprAny (← env) src with
      | some (m, e) =>
        match CTy.ofMode m with
        | some ty => emit s!"{ty.setFn}({← rtd dd}, {ss}, {e});"; return true
        | none => return false
      | none =>
        let ev ← env
        match resultModeE ev src with
        | some m =>
          match CTy.ofMode m with
          | some ty =>
            if hasNatCall ev src && natOk ev m src then
              let e ← anf m src
              emit s!"{ty.setFn}({← rtd dd}, {ss}, {e});"
              return true
            else return false
          | none => return false
        | none => return false
  | .slice base idx true =>
    -- `a[i] := <scalar>` writes the element in place
    match strip base with
    | .refCell dd ss =>
      if let some rv := rowOf (← env) dd ss then
        -- a promoted row: subscripts and bounds first, then the value, as the evaluator does
        let o ← rowOffset rv idx
        if rv.fields.isEmpty then
          let v ← rowValue rv.ty src
          emit s!"{rv.name}_p[{o}] = {v}; {rv.name}_d[{o}] = 1;"
        else
          -- a structure display into an element: its fields in order, then the stores
          let es : List Core := match strip src with | .collateral es _ _ => es | _ => []
          let mut vs : Array String := #[]
          for k in [0:rv.fields.size] do
            vs := vs.push (← rowValue rv.fields[k]! (es[k]?.getD (.lit .undef)))
          for k in [0:rv.fields.size] do
            emit s!"{rv.name}_p{k}[{o}] = {vs[k]!}; {rv.name}_d{k}[{o}] = 1;"
        return true
      if (← lvar dd ss).isSome then return false else
      match scalarExprAny (← env) src with
      | some (m, e) =>
        match CTy.ofMode m with
        | some ty =>
          let ev ← env
          let ixs : Option (Nat × String × String) := match idx with
            | [.index a] => do let ia ← scalarExpr ev (.int 0) a; some (1, ia, "0")
            | [.index a, .index b] => do
              let ia ← scalarExpr ev (.int 0) a
              let ib ← scalarExpr ev (.int 0) b
              some (2, ia, ib)
            | _ => none
          match ixs with
          | some (rank, ia, ib) =>
            emit s!"{ty.rowSetFn}({← rtd dd}, {ss}, {rank}, {ia}, {ib}, {e});"
            return true
          | none => return false
        | none => return false
      | none => return false
    | _ => return false
  | dst' =>
    if let some (rv, f, idx) := srowFieldDst (← env) dst' then
      -- a field of an element of a row of structures kept as C arrays
      let o ← rowOffset rv idx
      let v ← rowValue rv.fields[f]! src
      emit s!"{rv.name}_p{f}[{o}] = {v}; {rv.name}_d{f}[{o}] = 1;"
      return true
    -- `f OF … OF a[i] := <scalar>` writes the field in place
    match fieldChain (← env) dst' with
    | none => return false
    | some ch =>
      match scalarExprAny (← env) src with
      | some (m, e) =>
        match CTy.ofMode m with
        | some ty => emit s!"{ty.selSetFn}({ch.args}, {e});"; return true
        | none => return false
      | none => return false

partial def genNode (c : Core) : M Unit := do
  match c with
  | .lit v => genLit v
  | .loadCell d s =>
    match ← lvar d s with
    | some vv => emit s!"a68_v({vv.2.1.pushFn}({readVar vv}, W));"
    | none => emit s!"a68_v(a68rt_push_cell({← rtd d}, {s}, W));"
  | .refCell d s => emit s!"a68_v(a68rt_push_ref({← rtd d}, {s}, W));"
  | .deref e =>
    -- `f OF … OF x` of any mode: one call that pushes the field's value
    match fieldChain (← env) e with
    | some ch => emit s!"a68_v(a68rt_sel_push({ch.args}, W));"
    | none => do gen e; emit "a68_v(a68rt_deref(W));"
  | .deproc e => gen e; emit "a68_v(a68rt_deproc(W));"; jumpCheck
  | .widen a b e =>
    gen e
    emit s!"a68_v(a68rt_widen({← putMode a}, {← putMode b}, W));"
  | .rowOf e => gen e; emit "a68_v(a68rt_row_of(W));"
  | .unite m e => gen e; emit s!"a68_v(a68rt_unite({← putMode m}, W));"
  | .voiding e =>
    -- a VOIDing is a statement whose value happens to be wanted, and the escape analysis
    -- reads it that way (`slotEscapes` of a VOIDing is `slotEscapesV` of what it voids).
    -- Generating it any other way would build a reference to a slot that, because it does
    -- not escape, has been promoted to a C variable and has no cell.
    genVoid e
    emit "a68_v(a68rt_push_void(W));"
  | .assign d s flex =>
    -- `x := <scalar>` writes the cell directly, with nothing boxed and nothing pushed;
    -- the reference the assignment yields is only re-made when someone wants it.  Only a
    -- whole cell can be re-made that cheaply, so an assignment whose value is wanted and
    -- whose destination is a slice or a field goes the ordinary way.
    let direct ← match strip d with
      | .refCell dd ss => if (← storeScalar d s) then pure (some (dd, ss)) else pure none
      | _ => pure none
    match direct with
    | some (dd, ss) => emit s!"a68_v(a68rt_push_ref({← rtd dd}, {ss}, W));"
    | none => do
      gen d; gen s; emit s!"a68_v(a68rt_assign({if flex then 1 else 0}, W));"
  | .identRel l r isnt =>
    gen l; gen r
    emit s!"a68_v(a68rt_ident_rel({if isnt then 1 else 0}, W));"
  | .dyop op m1 m2 l r =>
    gen l; gen r
    emit s!"a68_v(a68rt_dyop({← putStr op}, {← putMode m1}, {← putMode m2}, W));"
  | .monop op m e =>
    gen e
    emit s!"a68_v(a68rt_monop({← putStr op}, {← putMode m}, W));"
  | .call f args =>
    gen f
    for a in args do gen a
    emit s!"a68_v(a68rt_call({args.length}, W));"
    jumpCheck
  | .routine nparams frameSize body =>
    let idx ← genFunction nparams frameSize body
    emit s!"a68_v(a68rt_push_proc({idx}, {nparams}, W));"
  | .slice arr idx viaRef =>
    gen arr
    let mut kinds : Nat := 0
    let mut i := 0
    for ix in idx do
      match ix with
      | .index e => gen e
      | .trim l u a =>
        let mut bits := 1
        match l with | some e => gen e; bits := bits + 2 | none => pure ()
        match u with | some e => gen e; bits := bits + 4 | none => pure ()
        match a with | some e => gen e; bits := bits + 8 | none => pure ()
        kinds := kinds + bits * 16 ^ i
      i := i + 1
    emit s!"a68_v(a68rt_slice({idx.length}, {kinds}ULL, {if viaRef then 1 else 0}, W));"
  | .select i e viaRef =>
    gen e
    emit s!"a68_v(a68rt_select({i}, {if viaRef then 1 else 0}, W));"
  | .newRow bounds init flex =>
    gen init
    for (l, u) in bounds do gen l; gen u
    emit s!"a68_v(a68rt_new_row({bounds.length}, {if flex then 1 else 0}, W));"
  | .gen init => gen init; emit "a68_v(a68rt_gen(W));"
  | .block size stmts labelBase nLabels => genBlock size stmts labelBase nLabels
  | .collateral es isStruct dims =>
    for e in es do gen e
    emit s!"a68_v(a68rt_collateral({es.length}, {if isStruct then 1 else 0}, {dims}, W));"
  | .cond c t e =>
    match scalarExpr (← env) .bool c with
    | some ce => emit ("if (" ++ ce ++ ") {")
    | none => do gen c; emit "if (a68_bool()) {"
    indent (gen t)
    emit "} else {"
    indent (gen e)
    emit "}"
  | .caseInt sel alts out =>
    gen sel
    emit ("switch (a68_case(" ++ toString alts.length ++ ")) {")
    let mut k := 1
    for a in alts do
      emit ("case " ++ toString k ++ ": {")
      indent (gen a)
      emit "} break;"
      k := k + 1
    emit "default: {"
    indent (gen out)
    emit "} }"
  | .caseConf sel alts out => genConformity sel alts out
  | .loop slot f b t w body => genLoop slot f b t w body
  | .goto l =>
    let s ← get
    if s.labels.contains l then emit s!"goto L{l};"
    else emit s!"a68_v(a68rt_raise_jump({l}, W)); {(← get).ret}"
  | .skip m => emit s!"a68_v(a68rt_push_skip({← putMode m}, W));"
  | .andThen l r =>
    gen l
    emit "if (a68_bool()) {"
    indent (gen r)
    emit "} else { a68_v(a68rt_push_bool(0, W)); }"
  | .orElse l r =>
    gen l
    emit "if (a68_bool()) { a68_v(a68rt_push_bool(1, W)); } else {"
    indent (gen r)
    emit "}"
  | .fmt items =>
    let items ← items.mapM genFmtItem
    emit s!"a68_v(a68rt_push_format({← putFmtList items}, W));"
  | .stop => emit "a68_v(a68rt_stop(W));"
  | .seq a b => genVoid a; gen b
  | .at p e => emit s!"a68_line({p.line});"; gen e
  | .hole _ _ => emit "a68_v(a68rt_push_void(W));"

partial def genLit (v : Value) : M Unit := do
  match v with
  | .int n =>
    if n ≥ -2147483647 && n ≤ 2147483647 then emit s!"a68_v(a68rt_push_int({n}LL, W));"
    else emit s!"a68_v(a68rt_push_bigint({← putStr (toString n)}, W));"
  | .real x => emit s!"a68_v(a68rt_push_real({creal x}, W));"
  | .bool b => emit s!"a68_v(a68rt_push_bool({if b then 1 else 0}, W));"
  | .char c => emit s!"a68_v(a68rt_push_char({c}, W));"
  | .bits b => emit s!"a68_v(a68rt_push_bits({b}ULL, W));"
  | .void => emit "a68_v(a68rt_push_void(W));"
  | .nil => emit "a68_v(a68rt_push_nil(W));"
  | .undef => emit "a68_v(a68rt_push_undef(W));"
  | .builtin n => emit s!"a68_v(a68rt_push_builtin({← putStr n}, W));"
  | .file id => emit s!"a68_v(a68rt_push_file({id}, W));"
  | .row _ _ es =>
    if es.all (fun e => match e with | .char _ => true | _ => false) then
      let str := String.ofList (es.toList.map fun e => match e with | .char c => Char.ofNat c | _ => '?')
      emit s!"a68_v(a68rt_push_str({← putStr str}, W));"
    else
      -- a row literal of non-characters: build it element by element
      for e in es do genLit e
      emit s!"a68_v(a68rt_collateral({es.size}, 0, 1, W));"
  | _ => emit "a68_v(a68rt_push_void(W));"

partial def genBlockAt (size : Nat) (stmts : Array CoreStmt) (labelBase nLabels : Nat)
    (wantValue : Bool) (dest : Option (CTy × String) := none) : M Unit := do
  let _ := labelBase
  let _ := nLabels
  let n ← fresh
  let modes : Array (Option Mode) := Id.run do
    let mut a : Array (Option Mode) := Array.replicate size none
    for st in stmts do
      match st with
      | .decl sl m _ => if sl < size then a := a.set! sl (some m)
      | _ => pure ()
    return a
  let fr := planFrame n size modes stmts wantValue (← get).modeTab
  -- Routines declared here that can also be plain C functions.  A routine's body sees those
  -- declared before it or in the same run of consecutive routine declarations, since no
  -- call can happen between two of them; the units of the block see a routine once its
  -- declaration has been passed.
  let mut procsAll : Array (Option ProcInfo) := Array.replicate size none
  let mut nats : Array (Nat × NatSig × Core × Nat) := #[]
  let mut runNo : Nat := 0
  let mut inRun := false
  for stx in stmts do
    match stx with
    | .decl sl dm init =>
      match strip init, dm with
      | .routine np fsz body, .proc _ _ =>
        if !inRun then runNo := runNo + 1
        inRun := true
        match natSigOf dm np fsz body with
        | some sg =>
          if sl < size && fr.pushed && (fr.vars[sl]?.join).isNone then
            let k ← reserveNative
            procsAll := procsAll.set! sl (some { nidx := k, sig := sg })
            nats := nats.push (sl, sg, body, runNo)
        | none => pure ()
      | _, _ => inRun := false
    | _ => inRun := false
  let procsFinal := procsAll
  let natsFinal := nats
  let afterDecl : Nat → M Unit := fun i => do
    if i == 0 then return
    match stmts[i - 1]? with
    | some (.decl sl _ _) =>
      match natsFinal.find? (fun (s2, _, _, _) => s2 == sl) with
      | some (_, sg, body, r) =>
        let pi := (procsFinal[sl]!).get!
        let vis := (Array.range size).map fun s3 =>
          if natsFinal.any (fun (s4, _, _, r4) => s4 == s3 && r4 ≤ r) then procsFinal[s3]! else none
        let outer : List Frame := match (← get).frames with
          | f :: rest => { f with procs := vis } :: rest
          | [] => []
        genNative pi.nidx sg body outer
        modify fun st => match st.frames with
          | f :: rest => { st with frames := { f with procs := f.procs.set! sl (some pi) } :: rest }
          | [] => st
      | none => pure ()
    | _ => pure ()
  let vp := voidPositions stmts wantValue
  -- with labels the block keeps its value on the operand stack, because a jump can land
  -- anywhere and EXIT leaves with whatever the last unit produced
  let onStack := wantValue && stmts.any fun st => match st with
    | .label _ | .exit => true | _ => false
  emit "{"
  indent do
    -- the depths are only wanted where a jump lands on one of this block's labels, and
    -- reading them is two calls into the runtime, so a block without labels skips them
    if stmts.any (fun st => match st with | .label _ => true | _ => false) then
      emit s!"uint32_t e{n} = a68_env_depth(); uint32_t s{n} = a68_stack_depth();"
    for i in [0:size] do
      match fr.vars[i]? with
      | some (some (v, ty, u)) =>
        emit (s!"{ty.name} {v} = 0;" ++ (if u then s!" uint8_t {v}_i = 0;" else ""))
      | _ => pure ()
    for i in [0:size] do
      match fr.rows[i]? with
      | some (some rv) =>
        emit s!"int64_t {rv.name}_l0 = 1, {rv.name}_u0 = 0, {rv.name}_l1 = 1, {rv.name}_u1 = 0; {rv.ty.name} *{rv.name}_p = NULL; uint8_t *{rv.name}_d = NULL;"
        for k in [0:rv.fields.size] do
          emit s!"{(rv.fields[k]!).name} *{rv.name}_p{k} = NULL; uint8_t *{rv.name}_d{k} = NULL;"
      | _ => pure ()
    if fr.pushed then emit s!"a68_v(a68rt_enter({size}, W));"
    modify fun st => { st with frames := { fr with procs := Array.replicate size none, modes := modes } :: st.frames }
    if onStack then emit "a68_v(a68rt_push_void(W));"
    let mut produced := false
    for i in [0:stmts.size] do
      afterDecl i
      match stmts[i]! with
      | .decl slot _ init =>
        match fr.vars[slot]? with
        | some (some (v, ty, u)) =>
          match strip init with
          | .lit .undef => pure ()          -- stays undefined; reads test the flag
          | i' =>
            match scalarExprAny (← env) i' with
            | some (m, e) =>
              if CTy.ofMode m == some ty then
                emit (if u then s!"{v} = {e}; {v}_i = 1;" else s!"{v} = {e};")
              else
                gen init
                emit (s!"{v} = {ty.popFn}();" ++ (if u then s!" {v}_i = 1;" else ""))
            | none =>
              gen init
              emit (s!"{v} = {ty.popFn}();" ++ (if u then s!" {v}_i = 1;" else ""))
        | _ =>
          match fr.rows[slot]? with
          | some (some rv) => genRowDecl rv init
          | _ =>
            -- a routine text: its boxed function learns its parameter modes, and when it has a
            -- plain entry point that needs no environment, the table of entry points records
            -- it for calls through procedure parameters
            let fb := (← get).fns.size
            match strip init, modes[slot]?.join with
            | .routine _ _ _, some pm@(.proc _ _) => modify fun st => { st with procMode := some pm }
            | _, _ => pure ()
            gen init
            modify fun st => { st with procMode := none }
            emit s!"a68_v(a68rt_store(0, {slot}, W));"
            match strip init, procsFinal[slot]?.join with
            | .routine _ _ body, some pi =>
              if !outerRef 1 body then
                modify fun st => { st with nativeOfFn := st.nativeOfFn.push (fb, pi.nidx) }
            | _, _ => pure ()
      | .unit e =>
        if vp[i]! == true then genVoid e
        else if onStack then do gen e; emit "a68_v(a68rt_nip(W));"
        else if wantValue then
          match dest with
          | some (ty, v) => do genInto ty v e; produced := true
          | none => do gen e; produced := true
        else genVoid e
      | .label id =>
        -- landing here ends the jump that brought us, so the pending flag is cleared: left
        -- set, the next call site would read it and jump away again
        emit s!"L{id}: a68_jump_clear(); a68_v(a68rt_env_truncate(e{n}+{if fr.pushed then 1 else 0}, W)); a68_v(a68rt_stack_truncate(s{n}, W));"
        if onStack then emit "a68_v(a68rt_push_void(W));"
      | .exit => emit s!"goto B{n};"
    afterDecl stmts.size
    if wantValue && !onStack && !produced && dest.isNone then emit "a68_v(a68rt_push_void(W));"
    modify fun st => { st with frames := st.frames.tail }
    emit s!"B{n}: {if fr.pushed then "a68_v(a68rt_leave(W));" else ";"}"
    -- the storage of promoted rows goes with the block; a jump out of the block leaves it
    for i in [0:size] do
      match fr.rows[i]? with
      | some (some rv) =>
        emit s!"free({rv.name}_p); free({rv.name}_d);"
        for k in [0:rv.fields.size] do
          emit s!"free({rv.name}_p{k}); free({rv.name}_d{k});"
      | _ => pure ()
    -- a block with labels keeps its value on the stack even when a variable was asked for
    match dest with
    | some (ty, v) => if onStack then emit s!"{v} = {ty.popFn}();"
    | none => pure ()
  emit "}"

partial def genBlock (size : Nat) (stmts : Array CoreStmt) (labelBase nLabels : Nat) : M Unit :=
  genBlockAt size stmts labelBase nLabels true

partial def genConformity (sel : Core) (alts : List (Mode × Option Nat × Core)) (out : Core) : M Unit := do
  gen sel
  let n ← fresh
  emit s!"int done{n} = 0;"
  for (m, slot, body) in alts do
    let mi ← putMode m
    emit ("if (!done" ++ toString n ++ " && a68_conform(" ++ toString mi ++ ", " ++ (if slot.isSome then "1" else "0") ++ ")) {")
    indent do
      emit s!"done{n} = 1;"
      -- as in the evaluator: a frame per alternative, empty when nothing is bound.  It is
      -- always a real frame, so the generator has to count it when translating depths.
      if slot.isSome then
        emit "a68_v(a68rt_enter(1, W));"
        emit "a68_v(a68rt_bind_cell(0, 0, W));"
      else emit "a68_v(a68rt_enter(0, W));"
      modify fun st => { st with frames := { vars := #[none], pushed := true } :: st.frames }
      gen body
      modify fun st => { st with frames := st.frames.tail }
      emit "a68_v(a68rt_nip(W));"
      emit "a68_v(a68rt_leave(W));"
    emit "}"
  emit ("if (!done" ++ toString n ++ ") {")
  indent do
    gen out
    emit "a68_v(a68rt_nip(W));"
  emit "}"

partial def genLoopAt (slot : Option Nat) (f b : Core) (t : Option Core) (w : Option Core)
    (body : Core) (wantValue : Bool) : M Unit := do
  let n ← fresh
  let bound (e : Core) : M String := do
    match scalarExpr (← env) (.int 0) e with
    | some ce => return ce
    | none => gen e; return "a68_int()"
  emit s!"int64_t from{n} = {← bound f};"
  emit s!"int64_t by{n} = {← bound b};"
  match t with
  | some tc => emit s!"int64_t to{n} = {← bound tc}; int has{n} = 1;"
  | none => emit s!"int64_t to{n} = 0; int has{n} = 0;"
  -- the counter can be the C induction variable itself when nothing inside needs a cell
  let others := hasOtherFn body || (match w with | some e => hasOtherFn e | none => false)
  let ok := assignsNatively CTy.i64
  let esc (sl : Nat) : Bool :=
    slotEscapesV ok 0 sl body || (match w with | some e => slotEscapes ok 0 sl e | none => false)
  let fr : Frame :=
    match slot with
    | some sl =>
      if !others && !esc sl && sl == 0 then
        { vars := #[some (s!"i{n}", CTy.i64, false)], pushed := false }
      else { vars := #[none], pushed := true }
    | none => { vars := #[], pushed := others }
  emit ("for (int64_t i" ++ toString n ++ " = from" ++ toString n ++ "; ; i" ++ toString n ++ " += by" ++ toString n ++ ") {")
  indent do
    emit s!"if (has{n} && ((by{n} > 0 && i{n} > to{n}) || (by{n} < 0 && i{n} < to{n}))) break;"
    -- the evaluator pushes a frame for every iteration, empty when there is no counter
    if fr.pushed then
      match slot with
      | some sl => emit "a68_v(a68rt_enter(1, W));"
                   emit s!"a68_v(a68rt_set_int(0, {sl}, i{n}, W));"
      | none => emit "a68_v(a68rt_enter(0, W));"
    modify fun st => { st with frames := fr :: st.frames }
    match w with
    | some wc =>
      match scalarExpr (← env) .bool wc with
      | some ce =>
        emit ("if (!(" ++ ce ++ ")) { " ++ (if fr.pushed then "a68_v(a68rt_leave(W)); " else "") ++ "break; }")
      | none =>
        emit s!"uint8_t cnd{n} = 0;"
        genInto .u8 s!"cnd{n}" wc
        emit ("if (!cnd" ++ toString n ++ ") { " ++ (if fr.pushed then "a68_v(a68rt_leave(W)); " else "") ++ "break; }")
    | none => pure ()
    genVoid body
    modify fun st => { st with frames := st.frames.tail }
    if fr.pushed then emit "a68_v(a68rt_leave(W));"
  emit "}"
  if wantValue then emit "a68_v(a68rt_push_void(W));"

partial def genLoop (slot : Option Nat) (f b : Core) (t : Option Core) (w : Option Core) (body : Core) : M Unit :=
  genLoopAt slot f b t w body true

/-- Compile a routine text into its own C function; returns its index. -/
partial def genFunction (nparams frameSize : Nat) (body : Core) : M Nat := do
  let s ← get
  let idx := s.fns.size
  -- reserve the slot so that nested routines get later indices
  set { s with fns := s.fns.push { name := s!"a68_fn{idx}" } }
  let savedCur := s.cur
  let savedLabels := s.labels
  let savedDepth := s.depth
  let savedFrames := s.frames
  -- a declared routine's parameter modes, so that calls through its procedure parameters
  -- know the C signature of a plain entry point
  let pmodes : Array (Option Mode) := match s.procMode with
    | some (.proc ps _) => (Array.range frameSize).map fun i => ps[i]?
    | _ => #[]
  -- A declared routine whose call cannot leave anything allocated during it reachable gives
  -- its cells back when it returns normally.  Without this, every boxed call adds its
  -- frame to a heap that only grows.  A jump out of the routine skips the release.
  let reclaim : Bool := match s.procMode with
    | some (.proc _ r) => !modeHoldsNames s.modeTab r && !cellsEscape body
    | _ => false
  modify fun st => { st with cur := #[], labels := labelsOf body, depth := 1, frames := [], ret := "return;", procMode := none }
  if reclaim then emit "uint32_t a68_hm = a68_u32(a68rt_heap_mark(W));"
  emit s!"a68_v(a68rt_enter_args({frameSize}, {nparams}, W));"
  modify fun st => { st with frames := [{ vars := Array.replicate frameSize none, modes := pmodes, pushed := true }] }
  gen body
  emit "a68_v(a68rt_leave(W));"
  if reclaim then emit "a68_v(a68rt_heap_release(a68_hm, W));"
  let st ← get
  let lines := st.cur
  let f : Fn := { name := s!"a68_fn{idx}", body := lines }
  set { st with cur := savedCur, labels := savedLabels, depth := savedDepth, fns := st.fns.set! idx f, frames := savedFrames, ret := s.ret }
  return idx

/-- Format items: the dynamic parts become holes evaluated by compiled code. -/
partial def genFmtItem (it : CoreFmt) : M CoreFmt := do
  match it with
  | .rep n dyn item =>
    let d ← match dyn with
      | some c => some <$> genHole c
      | none => pure none
    return .rep n d (← genFmtItem item)
  | .general args => return .general (← args.mapM genHole)
  | .group items => return .group (← items.mapM genFmtItem)
  | .include f => return .include (← genHole f)
  | other => return other

/-- Compile an expression embedded in a format text into a hole function. -/
partial def genHole (c : Core) : M Core := do
  let s ← get
  let idx := s.holes.size
  set { s with holes := s.holes.push { name := s!"a68_hole{idx}" } }
  let savedCur := s.cur
  let savedLabels := s.labels
  let savedDepth := s.depth
  let savedFrames := s.frames
  modify fun st => { st with cur := #[], labels := [], depth := 1, frames := [], ret := "return;" }
  gen c
  let st ← get
  let lines := st.cur
  let f : Fn := { name := s!"a68_hole{idx}", body := lines }
  set { st with cur := savedCur, labels := savedLabels, depth := savedDepth, holes := st.holes.set! idx f, frames := savedFrames, ret := s.ret }
  return .hole 0 idx

end

/-- The fixed part of every generated program. -/
def prelude : String := "
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define W lean_io_mk_world()


void lean_initialize_runtime_module(void);
void lean_io_mark_end_initialization(void);
void lean_init_task_manager(void);
char** lean_setup_args(int argc, char** argv);

lean_object* a68rt_boot(lean_object* blob, uint32_t ll, uint8_t reg, lean_object* args, lean_object* w);
lean_object* a68rt_finish(lean_object* w);
lean_object* a68rt_line(uint32_t l, lean_object* w);
extern uint32_t a68_line_no;
#define a68_line(n) (a68_line_no = (n))
lean_object* a68rt_jump_pending(lean_object* w);
extern uint32_t a68_jump_flag;
lean_object* a68rt_jump_clear(lean_object* w);
lean_object* a68rt_raise_jump(uint32_t l, lean_object* w);
lean_object* a68rt_stop(lean_object* w);
lean_object* a68rt_enter(uint32_t n, lean_object* w);
lean_object* a68rt_enter_args(uint32_t n, uint32_t k, lean_object* w);
lean_object* a68rt_leave(lean_object* w);
lean_object* a68rt_env_depth(lean_object* w);
lean_object* a68rt_env_truncate(uint32_t d, lean_object* w);
lean_object* a68rt_env_set(lean_object* env, lean_object* w);
lean_object* a68rt_env_restore(lean_object* w);
lean_object* a68rt_stack_depth(lean_object* w);
lean_object* a68rt_stack_truncate(uint32_t d, lean_object* w);
lean_object* a68rt_push_int(int64_t v, lean_object* w);
lean_object* a68rt_push_bigint(uint32_t i, lean_object* w);
lean_object* a68rt_push_real(double v, lean_object* w);
lean_object* a68rt_push_bool(uint8_t v, lean_object* w);
lean_object* a68rt_push_char(uint32_t v, lean_object* w);
lean_object* a68rt_push_bits(uint64_t v, lean_object* w);
lean_object* a68rt_push_str(uint32_t i, lean_object* w);
lean_object* a68rt_push_undef(lean_object* w);
lean_object* a68rt_push_nil(lean_object* w);
lean_object* a68rt_push_void(lean_object* w);
lean_object* a68rt_push_builtin(uint32_t i, lean_object* w);
lean_object* a68rt_push_file(uint32_t i, lean_object* w);
lean_object* a68rt_push_skip(uint32_t m, lean_object* w);
lean_object* a68rt_push_cell(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_push_ref(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_push_proc(uint32_t fn, uint32_t np, lean_object* w);
lean_object* a68rt_push_format(uint32_t k, lean_object* w);
lean_object* a68rt_push_array(lean_object* a, lean_object* w);
lean_object* a68rt_store(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_bind_cell(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_set_int(uint32_t d, uint32_t s, int64_t v, lean_object* w);
lean_object* a68rt_pop(lean_object* w);
lean_object* a68rt_nip(lean_object* w);
lean_object* a68rt_dup(lean_object* w);
lean_object* a68rt_pop_int(lean_object* w);
lean_object* a68rt_pop_bool(lean_object* w);
lean_object* a68rt_take_top(lean_object* w);
lean_object* a68rt_deref(lean_object* w);
lean_object* a68rt_deproc(lean_object* w);
lean_object* a68rt_widen(uint32_t a, uint32_t b, lean_object* w);
lean_object* a68rt_row_of(lean_object* w);
lean_object* a68rt_unite(uint32_t m, lean_object* w);
lean_object* a68rt_voiding(lean_object* w);
lean_object* a68rt_assign(uint8_t flex, lean_object* w);
lean_object* a68rt_ident_rel(uint8_t isnt, lean_object* w);
lean_object* a68rt_dyop(uint32_t op, uint32_t m1, uint32_t m2, lean_object* w);
lean_object* a68rt_monop(uint32_t op, uint32_t m, lean_object* w);
lean_object* a68rt_call(uint32_t n, lean_object* w);
lean_object* a68rt_select(uint32_t i, uint8_t viaRef, lean_object* w);
lean_object* a68rt_slice(uint32_t n, uint64_t kinds, uint8_t viaRef, lean_object* w);
lean_object* a68rt_new_row(uint32_t n, uint8_t flex, lean_object* w);
lean_object* a68rt_gen(lean_object* w);
lean_object* a68rt_collateral(uint32_t n, uint8_t st, uint32_t dims, lean_object* w);
lean_object* a68rt_case_index(uint32_t n, lean_object* w);
lean_object* a68rt_conform(uint32_t m, uint8_t bind, lean_object* w);
lean_object* initialize_algol68_A68_Runtime(uint8_t builtin);
void a68_set_state(lean_object* s);

static void a68_fail(lean_object* r) {
  lean_io_result_show_error(r);
  exit(1);
}
static inline lean_object* a68_take(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  lean_object* v = lean_io_result_take_value(r);
  return v;
}
static inline void a68_v(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  lean_dec_ref(r);
}
static inline uint32_t a68_u32(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  uint32_t v = lean_unbox_uint32(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}
static inline int64_t a68_i64(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  int64_t v = (int64_t) lean_unbox_uint64(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}
static inline uint8_t a68_u8(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  uint8_t v = lean_unbox(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}
#define a68_jump()        a68_jump_flag
#define a68_jump_clear()  (a68_jump_flag = 0)
#define a68_env_depth()   a68_u32(a68rt_env_depth(W))
#define a68_stack_depth() a68_u32(a68rt_stack_depth(W))
#define a68_bool()        (a68_u8(a68rt_pop_bool(W)) != 0)
#define a68_int()         a68_i64(a68rt_pop_int(W))
#define a68_case(n)       a68_u32(a68rt_case_index(n, W))
#define a68_conform(m,b)  (a68_u8(a68rt_conform(m, b, W)) != 0)

/* ---- native scalar arithmetic ----------------------------------------------
   Values of primitive mode are computed in C types here, so an expression like
   s + i * 3 allocates nothing and never touches the operand stack.  Each helper
   reproduces exactly the check its interpreted counterpart performs, and reports
   a failure through a68rt_arith_error, which prints and exits like any other
   runtime error. */

lean_object* a68rt_cell_int(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_cell_real(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_cell_bool(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_cell_char(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_cell_bits(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_set_cell_int(uint32_t d, uint32_t s, int64_t v, lean_object* w);
lean_object* a68rt_set_cell_real(uint32_t d, uint32_t s, double v, lean_object* w);
lean_object* a68rt_set_cell_bool(uint32_t d, uint32_t s, uint8_t v, lean_object* w);
lean_object* a68rt_set_cell_char(uint32_t d, uint32_t s, uint32_t v, lean_object* w);
lean_object* a68rt_set_cell_bits(uint32_t d, uint32_t s, uint64_t v, lean_object* w);
lean_object* a68rt_arith_error(uint32_t k, lean_object* w);

static inline double a68_f64(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  double v = lean_unbox_float(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}
static inline uint64_t a68_u64(lean_object* r) {
  if (lean_io_result_is_error(r)) a68_fail(r);
  uint64_t v = lean_unbox_uint64(lean_io_result_get_value(r));
  lean_dec_ref(r);
  return v;
}

#define a68_cell_i(d,s)   a68_i64(a68rt_cell_int(d, s, W))
#define a68_cell_r(d,s)   a68_f64(a68rt_cell_real(d, s, W))
#define a68_cell_b(d,s)   a68_u8(a68rt_cell_bool(d, s, W))
#define a68_cell_c(d,s)   a68_u32(a68rt_cell_char(d, s, W))
#define a68_cell_u(d,s)   a68_u64(a68rt_cell_bits(d, s, W))
#define a68_set_i(d,s,v)  a68_v(a68rt_set_cell_int(d, s, v, W))
#define a68_set_r(d,s,v)  a68_v(a68rt_set_cell_real(d, s, v, W))
#define a68_set_b(d,s,v)  a68_v(a68rt_set_cell_bool(d, s, v, W))
#define a68_set_c(d,s,v)  a68_v(a68rt_set_cell_char(d, s, v, W))
#define a68_set_u(d,s,v)  a68_v(a68rt_set_cell_bits(d, s, v, W))

lean_object* a68rt_pop_real(lean_object* w);
lean_object* a68rt_pop_char(lean_object* w);
lean_object* a68rt_pop_bits(lean_object* w);
lean_object* a68rt_undef_error(uint32_t k, lean_object* w);
lean_object* a68rt_row_int(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, lean_object* w);
lean_object* a68rt_row_real(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, lean_object* w);
lean_object* a68rt_row_bool(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, lean_object* w);
lean_object* a68rt_row_char(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, lean_object* w);
lean_object* a68rt_row_bits(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, lean_object* w);
lean_object* a68rt_set_row_int(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, int64_t v, lean_object* w);
lean_object* a68rt_set_row_real(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, double v, lean_object* w);
lean_object* a68rt_set_row_bool(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, uint8_t v, lean_object* w);
lean_object* a68rt_set_row_char(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, uint32_t v, lean_object* w);
lean_object* a68rt_set_row_bits(uint32_t d, uint32_t s, uint32_t r, int64_t i, int64_t j, uint64_t v, lean_object* w);

#define a68_row_i(d,s,r,i,j)  a68_i64(a68rt_row_int(d, s, r, i, j, W))
#define a68_row_r(d,s,r,i,j)  a68_f64(a68rt_row_real(d, s, r, i, j, W))
#define a68_row_b(d,s,r,i,j)  a68_u8(a68rt_row_bool(d, s, r, i, j, W))
#define a68_row_c(d,s,r,i,j)  a68_u32(a68rt_row_char(d, s, r, i, j, W))
#define a68_row_u(d,s,r,i,j)  a68_u64(a68rt_row_bits(d, s, r, i, j, W))
#define a68_set_row_i(d,s,r,i,j,v)  a68_v(a68rt_set_row_int(d, s, r, i, j, v, W))
#define a68_set_row_r(d,s,r,i,j,v)  a68_v(a68rt_set_row_real(d, s, r, i, j, v, W))
#define a68_set_row_b(d,s,r,i,j,v)  a68_v(a68rt_set_row_bool(d, s, r, i, j, v, W))
#define a68_set_row_c(d,s,r,i,j,v)  a68_v(a68rt_set_row_char(d, s, r, i, j, v, W))
#define a68_set_row_u(d,s,r,i,j,v)  a68_v(a68rt_set_row_bits(d, s, r, i, j, v, W))

/* One field of a structure a cell holds, or that is an element of a row a cell holds, or
   that a cell points at.  `spec` and `fields` describe the chain of selectors; see the
   runtime.  Anything that does not fit the shape falls back to the general machinery. */
lean_object* a68rt_sel_push(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, lean_object* w);
lean_object* a68rt_sel_int(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, lean_object* w);
lean_object* a68rt_sel_real(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, lean_object* w);
lean_object* a68rt_sel_bool(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, lean_object* w);
lean_object* a68rt_sel_char(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, lean_object* w);
lean_object* a68rt_sel_bits(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, lean_object* w);
lean_object* a68rt_set_sel_int(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, int64_t v, lean_object* w);
lean_object* a68rt_set_sel_real(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, double v, lean_object* w);
lean_object* a68rt_set_sel_bool(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, uint8_t v, lean_object* w);
lean_object* a68rt_set_sel_char(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, uint32_t v, lean_object* w);
lean_object* a68rt_set_sel_bits(uint32_t d, uint32_t s, uint32_t sp, int64_t i, int64_t j, uint32_t f, uint64_t v, lean_object* w);

#define a68_sel_i(d,s,sp,i,j,f)  a68_i64(a68rt_sel_int(d, s, sp, i, j, f, W))
#define a68_sel_r(d,s,sp,i,j,f)  a68_f64(a68rt_sel_real(d, s, sp, i, j, f, W))
#define a68_sel_b(d,s,sp,i,j,f)  a68_u8(a68rt_sel_bool(d, s, sp, i, j, f, W))
#define a68_sel_c(d,s,sp,i,j,f)  a68_u32(a68rt_sel_char(d, s, sp, i, j, f, W))
#define a68_sel_u(d,s,sp,i,j,f)  a68_u64(a68rt_sel_bits(d, s, sp, i, j, f, W))
#define a68_set_sel_i(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_int(d, s, sp, i, j, f, v, W))
#define a68_set_sel_r(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_real(d, s, sp, i, j, f, v, W))
#define a68_set_sel_b(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_bool(d, s, sp, i, j, f, v, W))
#define a68_set_sel_c(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_char(d, s, sp, i, j, f, v, W))
#define a68_set_sel_u(d,s,sp,i,j,f,v)  a68_v(a68rt_set_sel_bits(d, s, sp, i, j, f, v, W))

/* `s +:= c` and `s +:= t` where `s` is a row a cell holds: appended in place. */
lean_object* a68rt_append_char(uint32_t d, uint32_t s, uint32_t ch, lean_object* w);
lean_object* a68rt_append(uint32_t d, uint32_t s, lean_object* w);
#define a68_appendc(d,s,ch)  a68_v(a68rt_append_char(d, s, ch, W))

#define a68_pop_i()  a68_i64(a68rt_pop_int(W))
#define a68_pop_r()  a68_f64(a68rt_pop_real(W))
#define a68_pop_b()  a68_u8(a68rt_pop_bool(W))
#define a68_pop_c()  a68_u32(a68rt_pop_char(W))
#define a68_pop_u()  a68_u64(a68rt_pop_bits(W))

/* A promoted variable read before it was assigned: report exactly what the evaluator
   would have reported for an uninitialised cell of that mode. */
lean_object* a68rt_index_error(int64_t i, int64_t l, int64_t u, lean_object* w);
lean_object* a68rt_cell_cproc(uint32_t d, uint32_t s, lean_object* w);
lean_object* a68rt_heap_mark(lean_object* w);
lean_object* a68rt_heap_release(uint32_t m, lean_object* w);
static int64_t  a68_und_i(void) { a68_v(a68rt_undef_error(0, W)); return 0; }
static double   a68_und_r(void) { a68_v(a68rt_undef_error(1, W)); return 0.0; }
static uint8_t  a68_und_b(void) { a68_v(a68rt_undef_error(2, W)); return 0; }
static uint32_t a68_und_c(void) { a68_v(a68rt_undef_error(3, W)); return 0; }
static uint64_t a68_und_u(void) { a68_v(a68rt_undef_error(4, W)); return 0; }
/* Rows promoted to C arrays: bounds checks that report what the evaluator's subscripting
   reports, and element reads that apply its undefined test. */
static void a68_index_error(int64_t i, int64_t l, int64_t u) { a68_v(a68rt_index_error(i, l, u, W)); exit(1); }
static inline size_t a68_ao(int64_t l, int64_t u, int64_t i) {
  if (__builtin_expect(i < l || i > u, 0)) a68_index_error(i, l, u);
  return (size_t)(i - l);
}
static inline size_t a68_ao2(int64_t l0, int64_t u0, int64_t l1, int64_t u1, int64_t i, int64_t j) {
  if (__builtin_expect(i < l0 || i > u0, 0)) a68_index_error(i, l0, u0);
  if (__builtin_expect(j < l1 || j > u1, 0)) a68_index_error(j, l1, u1);
  return (size_t)((i - l0) * (u1 - l1 + 1) + (j - l1));
}
static void* a68_row_alloc(size_t n, size_t sz) {
  void* p = calloc(n ? n : 1, sz);
  if (!p) exit(1);
  return p;
}
#define A68_AR(S, T, UND) static inline T a68_ar_##S(T* p, uint8_t* d, int64_t l, int64_t u, int64_t i) { size_t o = a68_ao(l, u, i); return d[o] ? p[o] : UND(); } static inline T a68_ar2_##S(T* p, uint8_t* d, int64_t l0, int64_t u0, int64_t l1, int64_t u1, int64_t i, int64_t j) { size_t o = a68_ao2(l0, u0, l1, u1, i, j); return d[o] ? p[o] : UND(); }
A68_AR(i, int64_t, a68_und_i)
A68_AR(r, double, a68_und_r)
A68_AR(b, uint8_t, a68_und_b)
A68_AR(c, uint32_t, a68_und_c)
A68_AR(u, uint64_t, a68_und_u)

#define A68_INT_MAX 2147483647LL

static int64_t a68_die_i(uint32_t k) { a68_v(a68rt_arith_error(k, W)); return 0; }
static double  a68_die_r(uint32_t k) { a68_v(a68rt_arith_error(k, W)); return 0.0; }

/* INT is the range [-2147483647, 2147483647]; operands are always inside it, so the
   int64 intermediate of a sum or product cannot itself overflow. */
static inline int64_t a68_rng(int64_t v) {
  if (v > A68_INT_MAX || v < -A68_INT_MAX) return a68_die_i(0);
  return v;
}
static inline int64_t a68_add_i(int64_t a, int64_t b) { return a68_rng(a + b); }
static inline int64_t a68_sub_i(int64_t a, int64_t b) { return a68_rng(a - b); }
static inline int64_t a68_mul_i(int64_t a, int64_t b) { return a68_rng(a * b); }
static inline int64_t a68_neg_i(int64_t a)            { return a68_rng(-a); }
static inline int64_t a68_abs_i(int64_t a)            { return a68_rng(a < 0 ? -a : a); }
static inline int64_t a68_sign_i(int64_t a) { return a > 0 ? 1 : (a < 0 ? -1 : 0); }
static inline int64_t a68_sign_r(double a)  { return a > 0 ? 1 : (a < 0 ? -1 : 0); }

/* OVER truncates toward zero, which is C division. */
static inline int64_t a68_over_i(int64_t a, int64_t b) {
  if (b == 0) return a68_die_i(1);
  return a / b;
}
/* MOD is Euclidean against the absolute value of the right operand, so it is never
   negative; C remainder takes the sign of the left operand and has to be corrected. */
static inline int64_t a68_mod_i(int64_t a, int64_t b) {
  if (b == 0) return a68_die_i(1);
  int64_t m = b < 0 ? -b : b;
  int64_t r = a % m;
  return r < 0 ? r + m : r;
}
static inline double a68_chk_r(double x) {
  if (x != x) return a68_die_r(3);
  if (x > 1.7976931348623157e308 || x < -1.7976931348623157e308) return a68_die_r(2);
  return x;
}
/* REAL division checks the divisor, not the quotient, as a68g does: an infinite or NaN
   result is reported only by a later operation that checks.  `/:=` behaves the same. */
static inline double a68_div_r(double a, double b) {
  if (b == 0.0) return a68_die_r(3);
  return a / b;
}
static inline double a68_diveq_r(double a, double b) {
  if (b == 0.0) return a68_die_r(3);
  return a / b;
}
/* Exponentiation and the REAL standard functions, following the evaluator: INT ** INT and
   REAL ** INT by square-and-multiply with its checks, REAL ** REAL as exp (y ln x), and each
   function with its domain check and, except exp and exp2, a check of its result. */
static inline int64_t a68_pow_i(int64_t m, int64_t n) {
  if (n < 0) return a68_die_i(8);
  if (m == 0 && n == 0) return 1;
  if (m == 0 || m == 1) return m;
  if (m == -1) return (n % 2 == 0) ? 1 : -1;
  uint64_t nn = (uint64_t) n, bit = 1; int64_t mm = m, p = 1;
  for (;;) {
    if (nn & bit) p = a68_mul_i(p, mm);
    bit <<= 1;
    if (bit <= nn) mm = a68_mul_i(mm, mm);
    if (!(bit <= nn)) break;
  }
  return p;
}
static inline double a68_pow_ri(double x, int64_t n) {
  uint64_t nn = n < 0 ? (uint64_t)(-(n + 1)) + 1 : (uint64_t) n;
  double p;
  if (x == 0.0 && nn == 0) p = 1.0;
  else if (x == 0.0 || x == 1.0) p = x;
  else if (x == -1.0) p = (nn % 2 == 0) ? 1.0 : -1.0;
  else {
    uint64_t bit = 1; double mm = x; p = 1.0;
    for (;;) {
      if (nn & bit) p = p * mm;
      bit <<= 1;
      if (bit <= nn) mm = mm * mm;
      if (!(bit <= nn)) break;
    }
    if (p != p || p > 1.7976931348623157e308 || p < -1.7976931348623157e308) return a68_die_r(2);
  }
  return n < 0 ? 1.0 / p : p;
}
static inline double a68_pow_rr(double x, double y) {
  if (y == 0.0) return 1.0;
  if (x < 0.0) return a68_die_r(7);
  if (x == 0.0) { if (y < 0.0) return a68_die_r(7); return 0.0; }
  return exp(y * log(x));
}
static inline double a68_m_acos(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(acos(x)); }
static inline double a68_m_arccos(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(acos(x)); }
static inline double a68_m_arccosh(double x) { return a68_chk_r(acosh(x)); }
static inline double a68_m_arcsin(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(asin(x)); }
static inline double a68_m_arcsinh(double x) { return a68_chk_r(asinh(x)); }
static inline double a68_m_arctan(double x) { return a68_chk_r(atan(x)); }
static inline double a68_m_arctanh(double x) { return a68_chk_r(atanh(x)); }
static inline double a68_m_asin(double x) { if (x < -1.0 || x > 1.0) return a68_die_r(3); return a68_chk_r(asin(x)); }
static inline double a68_m_atan(double x) { return a68_chk_r(atan(x)); }
static inline double a68_m_cbrt(double x) { return a68_chk_r(cbrt(x)); }
static inline double a68_m_cos(double x) { return a68_chk_r(cos(x)); }
static inline double a68_m_cosh(double x) { return a68_chk_r(cosh(x)); }
static inline double a68_m_curt(double x) { return a68_chk_r(cbrt(x)); }
static inline double a68_m_exp(double x) { return exp(x); }
static inline double a68_m_exp2(double x) { return exp2(x); }
static inline double a68_m_ln(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(log(x)); }
static inline double a68_m_log(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(log10(x)); }
static inline double a68_m_log10(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(log10(x)); }
static inline double a68_m_log2(double x) { return a68_chk_r(log2(x)); }
static inline double a68_m_sin(double x) { return a68_chk_r(sin(x)); }
static inline double a68_m_sinh(double x) { return a68_chk_r(sinh(x)); }
static inline double a68_m_sqrt(double x) { if (x < 0.0) return a68_die_r(3); return a68_chk_r(sqrt(x)); }
static inline double a68_m_tan(double x) { return a68_chk_r(tan(x)); }
static inline double a68_m_tanh(double x) { return a68_chk_r(tanh(x)); }
static inline int64_t a68_entier(double x) {
  if (x < -2147483647.0 || x > 2147483647.0) return a68_die_i(4);
  return (int64_t) __builtin_floor(x);
}
static inline int64_t a68_round(double x) {
  if (x < -2147483647.0 || x > 2147483647.0) return a68_die_i(4);
  double ax = x < 0 ? -x : x;
  int64_t n = (int64_t) __builtin_floor(ax + 0.5);
  return x < 0 ? -n : n;
}
static inline double a68_fabs(double x) { return x < 0 ? -x : x; }
static inline uint32_t a68_repr(int64_t x) {
  if (x < 0 || x > 255) { a68_v(a68rt_arith_error(6, W)); return 0; }
  return (uint32_t) x;
}
"

/-- Emit the whole program. -/
def program (core : Core) (modes : Mode.Table) (ll : Nat) (regression : Bool) : String := Id.run do
  let (_, st) := (do
      let idx ← genFunction 0 0 core
      pure idx : M Nat).run { modeTab := modes }
  -- the mode declarations, sorted so that the emitted C does not depend on hash order
  let decls := modes.toArray.qsort (fun a b => a.1 < b.1)
  let st := decls.foldl (fun st (n, m) =>
      let (si, w) := st.w.str n
      let (mi, w) := Serial.putMode w m
      let (_, w) := w.add s!"n {si} {mi}"
      { st with w := w }) st
  let mut out := prelude
  out := out ++ "\nstatic const char* A68_BLOB =\n"
  -- the blob is emitted in chunks so that no C string literal grows too long
  for chunk in (st.w.render.splitOn "\n") do
    out := out ++ "  " ++ cstring (chunk ++ "\n") ++ "\n"
  out := out ++ ";\n\n"
  for (sg, _) in st.nfns do
    if sg != "" then out := out ++ sg ++ ";\n"
  for f in st.fns do
    out := out ++ s!"static void {f.name}(void);\n"
  -- the plain entry point of each compiled routine, indexed by boxed function index plus one,
  -- for calls through procedure parameters; NULL where there is none
  let natTab := (Array.range (st.fns.size + 1)).map fun i =>
    if i == 0 then "NULL" else
    match st.nativeOfFn.find? (fun (fi, _) => fi + 1 == i) with
    | some (_, k) => s!"(void*) a68_nf{k}"
    | none => "NULL"
  out := out ++ "static void* const a68_nf_of_fn[] = { " ++ ", ".intercalate natTab.toList ++ " };\n"
  for h in st.holes do
    out := out ++ s!"static void {h.name}(void);\n"
  out := out ++ "\n"
  for f in st.fns do
    out := out ++ "static void " ++ f.name ++ "(void) {\n" ++ "\n".intercalate f.body.toList ++ "\n}\n\n"
  for h in st.holes do
    out := out ++ "static void " ++ h.name ++ "(void) {\n" ++ "\n".intercalate h.body.toList ++ "\n}\n\n"
  for (sg, body) in st.nfns do
    if sg != "" then out := out ++ sg ++ " {\n" ++ "\n".intercalate body.toList ++ "\n}\n\n"
  -- dispatchers called from the runtime
  out := out ++ "lean_object* a68_dispatch_proc(size_t fn, lean_object* env, lean_object* args, lean_object* w) {\n"
  out := out ++ "  lean_inc(env);\n  a68_v(a68rt_env_set(env, W));\n"
  out := out ++ "  lean_inc(args);\n  a68_v(a68rt_push_array(args, W));\n  switch (fn) {\n"
  for i in [0:st.fns.size] do
    out := out ++ s!"    case {i}: a68_fn{i}(); break;\n"
  out := out ++ "    default: break;\n  }\n"
  out := out ++ "  lean_object* r = a68rt_take_top(lean_io_mk_world());\n  a68_v(a68rt_env_restore(W));\n  return r;\n}\n\n"
  out := out ++ "lean_object* a68_dispatch_hole(size_t fn, size_t idx, lean_object* env, lean_object* w) {\n"
  out := out ++ "  lean_inc(env);\n  a68_v(a68rt_env_set(env, W));\n  switch (idx) {\n"
  for i in [0:st.holes.size] do
    out := out ++ s!"    case {i}: a68_hole{i}(); break;\n"
  out := out ++ "    default: break;\n  }\n"
  out := out ++ "  lean_object* r = a68rt_take_top(lean_io_mk_world());\n  a68_v(a68rt_env_restore(W));\n  return r;\n}\n\n"
  -- main
  out := out ++ "int main(int argc, char** argv) {\n"
  out := out ++ "  argv = lean_setup_args(argc, argv);\n  lean_initialize_runtime_module();\n"
  out := out ++ "  lean_object* ir = initialize_algol68_A68_Runtime(1);\n"
  out := out ++ "  if (lean_io_result_is_error(ir)) { a68_fail(ir); }\n  lean_dec_ref(ir);\n"
  out := out ++ "  lean_io_mark_end_initialization();\n  lean_init_task_manager();\n"
  out := out ++ "  lean_object* args = lean_mk_empty_array();\n"
  out := out ++ "  for (int i = 0; i < argc; i++) args = lean_array_push(args, lean_mk_string(argv[i]));\n"
  out := out ++ s!"  a68_set_state(a68_take(a68rt_boot(lean_mk_string(A68_BLOB), {ll}, {if regression then 1 else 0}, args, W)));\n"
  out := out ++ "  a68_fn0();\n"
  out := out ++ "  uint32_t rc = a68_u32(a68rt_finish(W));\n  return (int) rc;\n}\n"
  return out

end A68.CodeGen
