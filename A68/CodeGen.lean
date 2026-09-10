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

/-- A frame as the generator sees it.  `vars` names the C variable a slot was promoted
    to, when it has one; `pushed` says whether a run-time frame was emitted for it at all.
    A frame every one of whose slots is a C variable needs no run-time frame, so the
    depths in `loadCell`/`refCell` — which count syntactic frames — have to be translated
    into run-time depths, which count only the frames that were actually pushed. -/
structure Frame where
  /-- per slot: C variable name, its type, and whether reads must test for undefined -/
  vars   : Array (Option (String × CTy × Bool)) := #[]
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
    emit "if (a68_jump()) return;"
  else
    emit "if (a68_jump()) { switch (a68_jump()-1) {"
    for l in s.labels do
      emit s!"  case {l}: goto L{l};"
    emit "  default: return; } }"

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
  if ["=", "/=", "<", "<=", ">", ">=", "AND", "OR", "XOR"].contains op then
    if ["AND", "OR", "XOR"].contains op then some m1 else some .bool
  else if ["+", "-", "*", "%", "%*", "**"].contains op then some m1
  else none

def monopResult (op : String) (m : Mode) : Option Mode :=
  match op, m with
  | "-", _ | "+", _ | "ABS", .int _ | "ABS", .real _ | "NOT", _ => some m
  | "SIGN", _ => some (.int 0)
  | "ODD", _ => some .bool
  | "ENTIER", .real n | "ROUND", .real n => some (.int n)
  | "REPR", _ => some .char
  | _, _ => none

mutual
/-- `a[i]` and `a[i, j]` where `a` is a row held directly in a cell: one call that returns
    a native value, instead of a reference built on the operand stack and then dereferenced. -/
partial def rowRead (env : List Frame) (ty : CTy) (base : Core) (idx : List CoreIdx) : Option String := do
  let (d, sl) ← match strip base with
    | .refCell d sl => some (d, sl)
    | .loadCell d sl => some (d, sl)
    | _ => none
  if (varOf env d sl).isSome then none else
  match idx with
  | [.index a] => do
    let ia ← scalarExpr env (.int 0) a
    some s!"{ty.rowFn}({rtDepthOf env d}, {sl}, 1, {ia}, 0)"
  | [.index a, .index b] => do
    let ia ← scalarExpr env (.int 0) a
    let ib ← scalarExpr env (.int 0) b
    some s!"{ty.rowFn}({rtDepthOf env d}, {sl}, 2, {ia}, {ib})"
  | _ => none

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
  | .deref (.slice base idx true) => rowRead env ty base idx
  | .slice base idx false => rowRead env ty base idx
  | .widen src dst e =>
    -- only the widenings that stay inside a native type
    match src, dst with
    | .int 0, .real 0 => do let x ← scalarExpr env (.int 0) e; some s!"((double)({x}))"
    | _, _ => none
  | .monop op mm e => do
    let r ← monopResult op mm
    if r != m then none else
    let x ← scalarExpr env mm e
    match op, (← CTy.ofMode mm) with
    | "-", .i64 => some s!"a68_neg_i({x})"
    | "-", .f64 => some s!"(-({x}))"
    | "+", _ => some x
    | "ABS", .i64 => some s!"a68_abs_i({x})"
    | "ABS", .f64 => some s!"a68_fabs({x})"
    | "SIGN", .i64 => some s!"a68_sign_i({x})"
    | "SIGN", .f64 => some s!"a68_sign_r({x})"
    | "ODD", .i64 => some s!"(uint8_t)((({x}) % 2) != 0)"
    | "NOT", .u8 => some s!"(uint8_t)(!({x}))"
    | "ENTIER", .f64 => some s!"a68_entier({x})"
    | "ROUND", .f64 => some s!"a68_round({x})"
    | _, _ => none
  | .dyop op m1 m2 l r => do
    if m1 != m2 then none else
    let opnd ← CTy.ofMode m1
    let res ← dyopResult op m1
    if res != m then none else
    let a ← scalarExpr env m1 l
    let b ← scalarExpr env m2 r
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
  | .dyop op m1 _ _ _ => dyopResult op m1
  | .monop op m _ => monopResult op m
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

/-- Which of a frame's slots can become C variables.  A slot qualifies when its declared
    mode is primitive and nothing inside the frame needs it to live in a cell.  If no
    routine text or format text occurs in the body — those compile to separate C functions
    that reach the frame through the run-time environment — and every slot qualifies, then
    no run-time frame is emitted for it at all. -/
def planFrame (tag : Nat) (size : Nat) (slotModes : Array (Option Mode))
    (stmts : Array CoreStmt) (wantValue : Bool) : Frame := Id.run do
  if stmts.toList.any hasOtherFnStmt then
    return { vars := Array.replicate size none, pushed := true }
  let mut vars : Array (Option (String × CTy × Bool)) := #[]
  let mut all := true
  for i in [0:size] do
    match (slotModes[i]?.join).bind CTy.ofMode with
    | some t =>
      if slotEscapesStmts (assignsNatively t) 0 i stmts wantValue then
        vars := vars.push none; all := false
      else
        vars := vars.push (some (s!"p{tag}_{i}", t, !slotInitialised stmts i))
    | none => vars := vars.push none; all := false
  return { vars := vars, pushed := !all }

def env : M (List Frame) := do return (← get).frames
def rtd (d : Nat) : M Nat := do return rtDepthOf (← env) d
def lvar (d s : Nat) : M (Option (String × CTy × Bool)) := do return varOf (← env) d s

mutual

/-- Emit code leaving the value of `c` on the operand stack. -/
partial def gen (c : Core) : M Unit := do
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
  | none => gen c; emit s!"{v} = {ty.popFn}();"

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
  | _ => gen c; emit "a68_v(a68rt_pop(W));"

/-- `x +:= e` in statement position: the variable or cell is updated in place, with
    nothing boxed and no reference built.  Returns whether it applied. -/
partial def assignOpVoid (op : String) (m1 m2 : Mode) (l r : Core) : M Bool := do
  match m1 with
  | .ref tm =>
    match CTy.ofMode tm, strip l with
    | some ty, .refCell dd ss =>
      let ev ← env
      match scalarExpr ev m2 r with
      | none => return false
      | some rs =>
        let cur := match varOf ev dd ss with
          | some vv => readVar vv
          | none => s!"{ty.cellFn}({rtDepthOf ev dd}, {ss})"
        match nativeAssignOp op ty cur rs with
        | none => return false
        | some e =>
          match varOf ev dd ss with
          | some (v, _, u) => emit (if u then s!"{v} = {e}; {v}_i = 1;" else s!"{v} = {e};")
          | none => emit s!"{ty.setFn}({rtDepthOf ev dd}, {ss}, {e});"
          return true
    | _, _ => return false
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
      | none => gen src; emit s!"{v} = {ty.popFn}();{setFlag}"
      return true
    | none =>
      match scalarExprAny (← env) src with
      | some (m, e) =>
        match CTy.ofMode m with
        | some ty => emit s!"{ty.setFn}({← rtd dd}, {ss}, {e});"; return true
        | none => return false
      | none => return false
  | .slice base idx true =>
    -- `a[i] := <scalar>` writes the element in place
    match strip base with
    | .refCell dd ss =>
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
  | _ => return false

partial def genNode (c : Core) : M Unit := do
  match c with
  | .lit v => genLit v
  | .loadCell d s =>
    match ← lvar d s with
    | some vv => emit s!"a68_v({vv.2.1.pushFn}({readVar vv}, W));"
    | none => emit s!"a68_v(a68rt_push_cell({← rtd d}, {s}, W));"
  | .refCell d s => emit s!"a68_v(a68rt_push_ref({← rtd d}, {s}, W));"
  | .deref e => gen e; emit "a68_v(a68rt_deref(W));"
  | .deproc e => gen e; emit "a68_v(a68rt_deproc(W));"; jumpCheck
  | .widen a b e =>
    gen e
    emit s!"a68_v(a68rt_widen({← putMode a}, {← putMode b}, W));"
  | .rowOf e => gen e; emit "a68_v(a68rt_row_of(W));"
  | .unite m e => gen e; emit s!"a68_v(a68rt_unite({← putMode m}, W));"
  | .voiding e => genVoid e; emit "a68_v(a68rt_push_void(W));"
  | .assign d s flex =>
    -- `x := <scalar>` writes the cell directly, with nothing boxed and nothing pushed;
    -- the reference the assignment yields is only re-made when someone wants it
    if (← storeScalar d s) then
      match strip d with
      | .refCell dd ss => emit s!"a68_v(a68rt_push_ref({← rtd dd}, {ss}, W));"
      | _ => emit "a68_v(a68rt_push_void(W));"
    else
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
    else emit s!"a68_v(a68rt_raise_jump({l}, W)); return;"
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
  let fr := planFrame n size modes stmts wantValue
  let vp := voidPositions stmts wantValue
  -- with labels the block keeps its value on the operand stack, because a jump can land
  -- anywhere and EXIT leaves with whatever the last unit produced
  let onStack := wantValue && stmts.any fun st => match st with
    | .label _ | .exit => true | _ => false
  emit "{"
  indent do
    emit s!"uint32_t e{n} = a68_env_depth(); uint32_t s{n} = a68_stack_depth();"
    for i in [0:size] do
      match fr.vars[i]? with
      | some (some (v, ty, u)) =>
        emit (s!"{ty.name} {v} = 0;" ++ (if u then s!" uint8_t {v}_i = 0;" else ""))
      | _ => pure ()
    if fr.pushed then emit s!"a68_v(a68rt_enter({size}, W));"
    modify fun st => { st with frames := fr :: st.frames }
    if onStack then emit "a68_v(a68rt_push_void(W));"
    let mut produced := false
    for i in [0:stmts.size] do
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
          gen init
          emit s!"a68_v(a68rt_store(0, {slot}, W));"
      | .unit e =>
        if vp[i]! == true then genVoid e
        else if onStack then do gen e; emit "a68_v(a68rt_nip(W));"
        else if wantValue then
          match dest with
          | some (ty, v) => do genInto ty v e; produced := true
          | none => do gen e; produced := true
        else genVoid e
      | .label id =>
        emit s!"L{id}: a68_v(a68rt_env_truncate(e{n}+{if fr.pushed then 1 else 0}, W)); a68_v(a68rt_stack_truncate(s{n}, W));"
        if onStack then emit "a68_v(a68rt_push_void(W));"
      | .exit => emit s!"goto B{n};"
    if wantValue && !onStack && !produced && dest.isNone then emit "a68_v(a68rt_push_void(W));"
    modify fun st => { st with frames := st.frames.tail }
    emit s!"B{n}: {if fr.pushed then "a68_v(a68rt_leave(W));" else ";"}"
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
  modify fun st => { st with cur := #[], labels := labelsOf body, depth := 1, frames := [] }
  emit s!"a68_v(a68rt_enter_args({frameSize}, {nparams}, W));"
  modify fun st => { st with frames := [{ vars := Array.replicate frameSize none, pushed := true }] }
  gen body
  emit "a68_v(a68rt_leave(W));"
  let st ← get
  let lines := st.cur
  let f : Fn := { name := s!"a68_fn{idx}", body := lines }
  set { st with cur := savedCur, labels := savedLabels, depth := savedDepth, fns := st.fns.set! idx f, frames := savedFrames }
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
  modify fun st => { st with cur := #[], labels := [], depth := 1, frames := [] }
  gen c
  let st ← get
  let lines := st.cur
  let f : Fn := { name := s!"a68_hole{idx}", body := lines }
  set { st with cur := savedCur, labels := savedLabels, depth := savedDepth, holes := st.holes.set! idx f, frames := savedFrames }
  return .hole 0 idx

end

/-- The fixed part of every generated program. -/
def prelude : String := "
#include <lean/lean.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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
#define a68_jump()        a68_u32(a68rt_jump_pending(W))
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

#define a68_pop_i()  a68_i64(a68rt_pop_int(W))
#define a68_pop_r()  a68_f64(a68rt_pop_real(W))
#define a68_pop_b()  a68_u8(a68rt_pop_bool(W))
#define a68_pop_c()  a68_u32(a68rt_pop_char(W))
#define a68_pop_u()  a68_u64(a68rt_pop_bits(W))

/* A promoted variable read before it was assigned: report exactly what the evaluator
   would have reported for an uninitialised cell of that mode. */
static int64_t  a68_und_i(void) { a68_v(a68rt_undef_error(0, W)); return 0; }
static double   a68_und_r(void) { a68_v(a68rt_undef_error(1, W)); return 0.0; }
static uint8_t  a68_und_b(void) { a68_v(a68rt_undef_error(2, W)); return 0; }
static uint32_t a68_und_c(void) { a68_v(a68rt_undef_error(3, W)); return 0; }
static uint64_t a68_und_u(void) { a68_v(a68rt_undef_error(4, W)); return 0; }

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
static inline double a68_div_r(double a, double b) {
  if (b == 0.0) return a68_die_r(3);
  return a68_chk_r(a / b);
}
/* `/:=` reports a different message from `/` when the divisor is zero. */
static inline double a68_diveq_r(double a, double b) {
  if (b == 0.0) return a68_die_r(5);
  return a68_chk_r(a / b);
}
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
"

/-- Emit the whole program. -/
def program (core : Core) (ll : Nat) (regression : Bool) : String := Id.run do
  let (_, st) := (do
      let idx ← genFunction 0 0 core
      pure idx : M Nat).run {}
  let mut out := prelude
  out := out ++ "\nstatic const char* A68_BLOB =\n"
  -- the blob is emitted in chunks so that no C string literal grows too long
  for chunk in (st.w.render.splitOn "\n") do
    out := out ++ "  " ++ cstring (chunk ++ "\n") ++ "\n"
  out := out ++ ";\n\n"
  for f in st.fns do
    out := out ++ s!"static void {f.name}(void);\n"
  for h in st.holes do
    out := out ++ s!"static void {h.name}(void);\n"
  out := out ++ "\n"
  for f in st.fns do
    out := out ++ "static void " ++ f.name ++ "(void) {\n" ++ "\n".intercalate f.body.toList ++ "\n}\n\n"
  for h in st.holes do
    out := out ++ "static void " ++ h.name ++ "(void) {\n" ++ "\n".intercalate h.body.toList ++ "\n}\n\n"
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
