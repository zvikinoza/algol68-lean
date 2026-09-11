import A68.Syntax
import A68.Mode
import A68.Core
import A68.Builtins
import A68.Numfmt

/-!
# A68.Elab — elaboration: mode checking, coercion insertion, name resolution

The elaborator turns the parse tree into `Core`:

* identifiers are resolved to `(depth, slot)` cells in lexically nested frames
  (every serial clause, routine text, loop and conformity alternative opens a frame);
* every unit is elaborated in a *context* (`Ctx`) of a given strength; the
  coercions permitted by that strength (deproceduring, dereferencing, uniting,
  widening, rowing, voiding) are inserted explicitly;
* operators are identified by first searching user-declared operators (innermost
  scope first, operands coerced firmly) and then the standard prelude;
* conditional and case clauses are *balanced* when no target mode is known.
-/
namespace A68

structure ElabError where
  msg : String
  pos : Pos
  deriving Repr, Inhabited

inductive BindKind where
  | var                     -- cell holds the value; identifier denotes REF (refCell)
  | ident                   -- cell holds the value; identifier denotes it (loadCell)
  | builtinConst (v : Value)
  | builtinProc (name : String)
  | label (id : Nat)
  deriving Inhabited

structure Binding where
  mode  : Mode
  depth : Nat        -- absolute frame depth where declared
  slot  : Nat
  kind  : BindKind
  deriving Inhabited

structure OpBinding where
  name  : String
  mode  : Mode       -- PROC mode of the operator routine
  depth : Nat
  slot  : Nat
  deriving Inhabited

structure Scope where
  names  : List (String × Binding) := []
  ops    : List OpBinding := []
  size   : Nat := 0
  deriving Inhabited

structure ElabState where
  scopes     : List Scope := []        -- innermost first
  modes      : Mode.Table := {}
  modeSyns   : Std.HashMap String ModeSyn := {}   -- declarers of MODE declarations (keep bounds)
  labelCount : Nat := 0
  curPos     : Pos := {}
  llDigits   : Nat := Numfmt.defaultLLDigits
  deriving Inhabited

abbrev Elab := StateT ElabState (Except ElabError)

instance : Inhabited (Elab α) := ⟨fun _ => .error default⟩

namespace Elab

/-- Elaboration contexts. -/
inductive Ctx where
  | strong (t : Mode)
  | meek (t : Mode)
  | firm            -- raw a priori mode (operand)
  | soft            -- deproceduring only
  | weak            -- dereference down to REF row/struct
  | meekAny         -- dereference and deprocedure fully, no target
  deriving Inhabited

def err (msg : String) : Elab α := do
  let s ← get
  throw { msg := msg, pos := s.curPos }

def tbl : Elab Mode.Table := do return (← get).modes
def depth : Elab Nat := do return (← get).scopes.length

def resolve (m : Mode) : Elab Mode := do return Mode.resolve (← tbl) m
def eqv (a b : Mode) : Elab Bool := do return Mode.eqv (← tbl) a b

def pushScope : Elab Unit := modify fun s => { s with scopes := {} :: s.scopes }
def popScope : Elab Scope := do
  let s ← get
  match s.scopes with
  | sc :: rest => set { s with scopes := rest }; return sc
  | [] => err "internal: scope underflow"

def modifyTop (f : Scope → Scope) : Elab Unit := modify fun s =>
  match s.scopes with
  | sc :: rest => { s with scopes := f sc :: rest }
  | [] => s

def newSlot : Elab Nat := do
  let s ← get
  match s.scopes with
  | sc :: rest =>
    set { s with scopes := { sc with size := sc.size + 1 } :: rest }
    return sc.size
  | [] => err "internal: no scope"

def declare (name : String) (mode : Mode) (kind : BindKind) : Elab Nat := do
  let slot ← newSlot
  let d ← depth
  modifyTop fun sc => { sc with names := (name, { mode := mode, depth := d - 1, slot := slot, kind := kind }) :: sc.names }
  return slot

def declareOp (name : String) (mode : Mode) : Elab Nat := do
  let slot ← newSlot
  let d ← depth
  modifyTop fun sc => { sc with ops := { name := name, mode := mode, depth := d - 1, slot := slot } :: sc.ops }
  return slot

def newLabel : Elab Nat := do
  let s ← get
  set { s with labelCount := s.labelCount + 1 }
  return s.labelCount

def lookup (name : String) : Elab (Option Binding) := do
  let s ← get
  for sc in s.scopes do
    match sc.names.lookup name with
    | some b => return some b
    | none => pure ()
  return none

/-- All user operators with a given name, innermost first. -/
def lookupOps (name : String) : Elab (List OpBinding) := do
  let s ← get
  return s.scopes.foldr (fun sc acc => acc ++ (sc.ops.filter (·.name == name))) []
  |>.reverse.reverse

def cellCore (b : Binding) : Elab Core := do
  let d ← depth
  let rel := d - 1 - b.depth
  match b.kind with
  | .var => return .refCell rel b.slot
  | .ident => return .loadCell rel b.slot
  | .builtinConst v => return .lit v
  | .builtinProc n => return .lit (.builtin n)
  | .label id => return .goto id

/-- Convert syntax mode to a semantic mode. -/
def modeOf (m : ModeSyn) : Mode := Mode.ofSyn m

-- ## Coercions

/-- Widening graph: one step. -/
def widenStep : Mode → List Mode
  | .int n => [.int (n + 1), .real n]
  | .real n => [.real (n + 1), .compl n]
  | .compl n => [.compl (n + 1)]
  | .bits n => [.bits (n + 1), .row 1 false .bool]
  | .bytes n => [.bytes (n + 1), .row 1 false .char]
  | _ => []

/-- Is `to` reachable from `from` by widening (bounded search)? -/
partial def widenable (src dst : Mode) (fuel : Nat := 6) : Bool :=
  if fuel = 0 then false
  else (widenStep src).any fun m => m == dst || widenable m dst (fuel - 1)

/-- Dereference and deprocedure fully ("meek" coercion with unknown target). -/
partial def meekCoerce (c : Core) (m : Mode) : Elab (Core × Mode) := do
  match (← resolve m) with
  | .ref x => meekCoerce (.deref c) x
  | .proc [] r => meekCoerce (.deproc c) r
  | _ => return (c, m)

/-- Weak coercion: dereference until a REF to a row/struct (or a non-REF) remains. -/
partial def weakCoerce (c : Core) (m : Mode) : Elab (Core × Mode) := do
  match (← resolve m) with
  | .proc [] r => weakCoerce (.deproc c) r
  | .ref x =>
    match (← resolve x) with
    | .ref _ => weakCoerce (.deref c) x
    | .proc [] _ => weakCoerce (.deref c) x
    | _ => return (c, m)
  | _ => return (c, m)

/-- Deprocedure only ("soft"). -/
partial def softCoerce (c : Core) (m : Mode) : Elab (Core × Mode) := do
  match (← resolve m) with
  | .proc [] r => softCoerce (.deproc c) r
  | _ => return (c, m)

inductive Strength where | strong | firm | meek | soft
  deriving BEq, Inhabited

/-- Try to coerce `c : from` to `to` with the given strength. -/
partial def coerce (s : Strength) (c : Core) (src dst : Mode) (fuel : Nat := 12) : Elab (Option Core) := do
  if fuel = 0 then return none
  if (← eqv src dst) then return some c
  let srcR ← resolve src
  let dstR ← resolve dst
  if s == .strong && dstR == .simplin then
    let (c', m') ← softCoerce c src
    return some (.unite m' c')
  if s == .strong && dstR == .row 1 false .simplin then
    -- a single name given to read/get: row it without dereferencing
    let (c', m') ← softCoerce c src
    match (← resolve m') with
    | .row 1 _ _ => pure ()   -- a row of names is passed as is (handled below)
    | _ => return some (.rowOf (.unite m' c'))
  if s == .strong && dstR == .void then
    -- voiding: deprocedure (through names) but do not dereference otherwise
    let rec strip (c : Core) (m : Mode) (fuel : Nat) : Elab Core := do
      if fuel = 0 then return c
      match (← resolve m) with
      | .proc [] r => strip (.deproc c) r (fuel - 1)
      | .ref x =>
        match (← resolve (Mode.stripRefs (← tbl) x)) with
        | .proc [] _ => strip (.deref c) x (fuel - 1)
        | _ => return c
      | _ => return c
    return some (.voiding (← strip c src 8))
  -- deproceduring / dereferencing first
  let viaDeproc ← match srcR with
    | .proc [] r => coerce s (.deproc c) r dst (fuel - 1)
    | _ => pure none
  if let some r := viaDeproc then return some r
  let viaDeref ← match srcR with
    | .ref x => if s != .soft then coerce s (.deref c) x dst (fuel - 1) else pure none
    | _ => pure none
  if let some r := viaDeref then return some r
  match s with
  | .strong =>
    match dstR with
    | .void => return some (.voiding c)
    | .union ms =>
      for m in ms do
        if let some c' ← coerce .firm c src m (fuel - 1) then return some (.unite m c')
      return none
    | .simplout =>
      let (c', m') ← meekCoerce c src
      return some (.unite m' c')
    | .simplin =>
      let (c', m') ← softCoerce c src
      return some (.unite m' c')
    | .number =>
      let (c', m') ← meekCoerce c src
      match (← resolve m') with
      | .int _ | .real _ => return some (.unite m' c')
      | _ => return none
    | .row 1 _ em =>
      -- rowing (a value M becomes [] M) — but not for REF sources handled below
      match srcR with
      | .ref _ => return none
      | _ =>
        if let some c' ← coerce .strong c src em (fuel - 1) then return some (.rowOf c')
        else
          -- widening to a row (BITS → [] BOOL)
          if widenable srcR dstR then return some (.widen srcR dstR c) else return none
    | .row d _ em =>
      -- rowing into a multi-dimensional row, as a68g does: a row of `d - 1` dimensions gains
      -- a first dimension `1:1`, and a value `M` becomes a `[1:1, …, 1:1] M`.  Both are
      -- one-element row displays, which both back ends already build.
      match srcR with
      | .ref _ => return none
      | .row k _ em' =>
        if k + 1 == d && (← eqv em' em) then return some (.collateral [c] false d)
        else return none
      | _ =>
        if let some c' ← coerce .strong c src em (fuel - 1) then
          return some ((List.range d).foldl (fun acc k => Core.collateral [acc] false (k + 1)) c')
        else return none
    | .ref (.row 1 _ em) =>
      match srcR with
      | .ref x => if (← eqv x em) then return some (.rowOf c) else return none
      | _ => return none
    | _ =>
      if widenable srcR dstR then return some (.widen srcR dstR c) else return none
  | .firm =>
    match dstR with
    | .union ms =>
      for m in ms do
        if let some c' ← coerce .firm c src m (fuel - 1) then return some (.unite m c')
      return none
    | _ => return none
  | _ => return none

def coerceStrong (c : Core) (src dst : Mode) : Elab Core := do
  match (← coerce .strong c src dst) with
  | some r => return r
  | none => err s!"{src} cannot be coerced to {dst} in a strong context"

/-- Apply a context to an a priori (core, mode). -/
def applyCtx (ctx : Ctx) (c : Core) (m : Mode) : Elab (Core × Mode) := do
  match ctx with
  | .strong t => return (← coerceStrong c m t, t)
  | .meek t =>
    match (← coerce .meek c m t) with
    | some r => return (r, t)
    | none => err s!"{m} cannot be coerced to {t} in a meek context"
  | .firm => return (c, m)
  | .soft => softCoerce c m
  | .weak => weakCoerce c m
  | .meekAny => meekCoerce c m

-- ## Standard operators

def isAssignOp (op : String) : Bool :=
  ["+:=", "-:=", "*:=", "/:=", "%:=", "%*:=", "+=:", "PLUSAB", "MINUSAB", "TIMESAB", "DIVAB",
   "OVERAB", "MODAB", "PLUSTO", "ANDAB", "ORAB"].contains op

def canonOp (op : String) : String :=
  match op with
  | "PLUSAB" => "+:=" | "MINUSAB" => "-:=" | "TIMESAB" => "*:=" | "DIVAB" => "/:="
  | "OVERAB" => "%:=" | "MODAB" => "%*:=" | "PLUSTO" => "+=:" | "ANDAB" => "&:=" | "ORAB" => "|:="
  | "EQ" => "=" | "NE" => "/=" | "~=" => "/=" | "LT" => "<" | "LE" => "<=" | "GT" => ">" | "GE" => ">="
  | "OVER" => "%" | "MOD" => "%*" | "^" => "**" | "UP" => "**" | "&" => "AND" | "+*" => "I"
  | "!" => "NOT" | "~" => "NOT"
  | _ => op

/-- Numeric join: the wider of two numeric modes. -/
def numJoin : Mode → Mode → Option Mode
  | .int a, .int b => some (.int (max a b))
  | .int a, .real b => some (.real (max a b))
  | .real a, .int b => some (.real (max a b))
  | .real a, .real b => some (.real (max a b))
  | .compl a, .compl b => some (.compl (max a b))
  | .compl a, .real b => some (.compl (max a b))
  | .real a, .compl b => some (.compl (max a b))
  | .compl a, .int b => some (.compl (max a b))
  | .int a, .compl b => some (.compl (max a b))
  | _, _ => none

def isStringMode (tb : Mode.Table) (m : Mode) : Bool :=
  match Mode.resolve tb m with
  | .row 1 _ e => (Mode.resolve tb e) == .char
  | _ => false

/-- Widen `c : from` to `to` (numeric), inserting a `widen` node if needed. -/
def widenTo (c : Core) (src dst : Mode) : Core :=
  if src == dst then c else .widen src dst c

/-- Resolve a builtin dyadic operator on meek-coerced operand modes. -/
def builtinDyadic (op : String) (l : Core) (ml : Mode) (r : Core) (mr : Mode) : Elab (Option (Core × Mode)) := do
  let tb ← tbl
  let ml ← resolve ml
  let mr ← resolve mr
  let op := canonOp op
  let asString (c : Core) (m : Mode) : Core := if m == .char then .rowOf c else c
  -- string / char operators
  let isCharish (m : Mode) := m == .char || isStringMode tb m
  if isCharish ml && isCharish mr then
    match op with
    | "+" => return some (.dyop "+" .string .string (asString l ml) (asString r mr), .string)
    | "=" | "/=" | "<" | "<=" | ">" | ">=" =>
      if ml == .char && mr == .char then
        return some (.dyop op .char .char l r, .bool)
      else
        return some (.dyop op .string .string (asString l ml) (asString r mr), .bool)
    | _ => pure ()
  match op, ml, mr with
  | "*", .int 0, _ => if isCharish mr then return some (.dyop "*" (.int 0) .string l (asString r mr), .string) else pure ()
  | "*", _, .int 0 => if isCharish ml then return some (.dyop "*" .string (.int 0) (asString l ml) r, .string) else pure ()
  | _, _, _ => pure ()
  -- numeric
  match numJoin ml mr with
  | some j =>
    match op with
    | "+" | "-" | "*" =>
      return some (.dyop op j j (widenTo l ml j) (widenTo r mr j), j)
    | "/" =>
      let j' := match j with | .int n => .real n | m => m
      return some (.dyop "/" j' j' (widenTo l ml j') (widenTo r mr j'), j')
    | "%" | "%*" =>
      match j with
      | .int _ => return some (.dyop op j j (widenTo l ml j) (widenTo r mr j), j)
      | _ => return none
    | "**" =>
      match ml, mr with
      | .int a, .int _ => return some (.dyop "**" (.int a) (.int 0) l r, .int a)
      | .real a, .int _ => return some (.dyop "**" (.real a) (.int 0) l r, .real a)
      | .compl a, .int _ => return some (.dyop "**" (.compl a) (.int 0) l r, .compl a)
      | _, _ =>
        let j' := match j with | .int n => .real n | m => m
        return some (.dyop "**" j' j' (widenTo l ml j') (widenTo r mr j'), j')
    | "=" | "/=" =>
      return some (.dyop op j j (widenTo l ml j) (widenTo r mr j), .bool)
    | "<" | "<=" | ">" | ">=" =>
      match j with
      | .compl _ => return none
      | _ => return some (.dyop op j j (widenTo l ml j) (widenTo r mr j), .bool)
    | "I" =>
      match j with
      | .int n | .real n => return some (.dyop "I" (.real n) (.real n) (widenTo l ml (.real n)) (widenTo r mr (.real n)), .compl n)
      | _ => return none
    | _ => pure ()
  | none => pure ()
  match op, ml, mr with
  | "AND", .bool, .bool | "OR", .bool, .bool | "XOR", .bool, .bool =>
    return some (.dyop op .bool .bool l r, .bool)
  | "=", .bool, .bool | "/=", .bool, .bool => return some (.dyop op .bool .bool l r, .bool)
  | "AND", .bits a, .bits b | "OR", .bits a, .bits b | "XOR", .bits a, .bits b
  | "=", .bits a, .bits b | "/=", .bits a, .bits b | "<=", .bits a, .bits b | ">=", .bits a, .bits b =>
    let j := Mode.bits (max a b)
    let res := if op == "=" || op == "/=" || op == "<=" || op == ">=" then Mode.bool else j
    return some (.dyop op j j l r, res)
  | "SHL", .bits a, .int _ | "SHR", .bits a, .int _ | "DOWN", .bits a, .int _ =>
    return some (.dyop op (.bits a) (.int 0) l r, .bits a)
  | "ELEM", .int _, .bits a => return some (.dyop "ELEM" (.int 0) (.bits a) l r, .bool)
  | "LWB", .int _, .row _ _ _ | "UPB", .int _, .row _ _ _ =>
    return some (.dyop op (.int 0) mr l r, .int 0)
  | "=", .row _ _ _, .row _ _ _ | "/=", .row _ _ _, .row _ _ _ =>
    return some (.dyop op ml mr l r, .bool)
  | _, _, _ => return none

/-- Resolve a builtin monadic operator on a meek-coerced operand. -/
def builtinMonadic (op : String) (e : Core) (m : Mode) : Elab (Option (Core × Mode)) := do
  let tb ← tbl
  let m ← resolve m
  let op := canonOp op
  match op, m with
  | "-", .int _ | "-", .real _ | "-", .compl _ | "+", .int _ | "+", .real _ | "+", .compl _ =>
    return some (.monop op m e, m)
  | "ABS", .int _ | "ABS", .real _ => return some (.monop "ABS" m e, m)
  | "ABS", .compl n => return some (.monop "ABS" m e, .real n)
  | "ABS", .char | "ABS", .bool | "ABS", .bits _ => return some (.monop "ABS" m e, .int 0)
  | "SIGN", .int _ | "SIGN", .real _ => return some (.monop "SIGN" m e, .int 0)
  | "ODD", .int _ => return some (.monop "ODD" m e, .bool)
  | "ENTIER", .real n | "ROUND", .real n => return some (.monop op m e, .int n)
  | "REPR", .int _ => return some (.monop "REPR" m e, .char)
  | "BIN", .int n => return some (.monop "BIN" m e, .bits n)
  | "NOT", .bool => return some (.monop "NOT" m e, .bool)
  | "NOT", .bits _ => return some (.monop "NOT" m e, m)
  | "LENG", .int n => return some (.widen m (.int (n+1)) e, .int (n+1))
  | "LENG", .real n => return some (.widen m (.real (n+1)) e, .real (n+1))
  | "LENG", .bits n => return some (.widen m (.bits (n+1)) e, .bits (n+1))
  | "LENG", .compl n => return some (.widen m (.compl (n+1)) e, .compl (n+1))
  | "SHORTEN", .int n => return some (.monop "SHORTEN" m e, .int (n-1))
  | "SHORTEN", .real n => return some (.monop "SHORTEN" m e, .real (n-1))
  | "SHORTEN", .bits n => return some (.monop "SHORTEN" m e, .bits (n-1))
  | "SHORTEN", .compl n => return some (.monop "SHORTEN" m e, .compl (n-1))
  | "RE", .compl n | "IM", .compl n | "ARG", .compl n => return some (.monop op m e, .real n)
  | "CONJ", .compl _ => return some (.monop "CONJ" m e, m)
  | "LWB", .row _ _ _ | "UPB", .row _ _ _ => return some (.monop op m e, .int 0)
  | "ELEMS", .row _ _ _ => return some (.monop op m e, .int 0)
  -- a SEMA is a name of an INT (a68g: `MODE SEMA = STRUCT (REF INT F)`): `LEVEL n` makes
  -- one holding `n`, and `LEVEL s` reads its level
  | "LEVEL", .int 0 => return some (.gen e, .sema)
  | "LEVEL", .sema => return some (.deref e, .int 0)
  | _, _ =>
    let _ := tb
    return none

-- ## Constants of the standard prelude

def constValue (name : String) (ll : Nat := Numfmt.defaultLLDigits) (fileName : String := "") : Value :=
  match name with
  | "programidf" => Value.ofString fileName
  | "maxint" => .int Numfmt.maxInt
  | "minint" => .int (-Numfmt.maxInt)
  | "maxreal" => .real 1.7976931348623157e308
  | "minreal" => .real 2.2250738585072014e-308
  | "smallreal" => .real 2.220446049250313e-16
  | "pi" => .real 3.141592653589793
  | "longpi" | "longlongpi" => .real 3.141592653589793
  | "longmaxint" => .int Numfmt.longMaxInt
  | "longlongmaxint" => .int (Numfmt.maxIntOf 2 ll)
  | "longmaxreal" | "longlongmaxreal" => .real 1.7976931348623157e308
  | "longsmallreal" => .real 1e-42
  | "longlongsmallreal" => .real 1e-70
  | "intwidth" => .int 10 | "realwidth" => .int 15 | "expwidth" => .int 3
  | "longintwidth" => .int 50 | "longrealwidth" => .int 42 | "longexpwidth" => .int 3
  | "longlongintwidth" => .int (Numfmt.intWidthOf 2 ll) | "longlongrealwidth" => .int (Numfmt.realWidthOf 2 ll)
  | "longlongexpwidth" => .int 3
  | "bitswidth" => .int 32 | "longbitswidth" => .int 64 | "byteswidth" => .int 32 | "maxabschar" => .int 255
  | "intlengths" => .int 3 | "intshorths" => .int 1 | "reallengths" => .int 3 | "realshorths" => .int 1
  | "bitslengths" => .int 3 | "byteslengths" => .int 2
  | "nullcharacter" | "nullchar" => .char 0 | "blank" => .char 32 | "flip" => .char 84 | "flop" => .char 70
  | "maxbits" => .bits 4294967295 | "bitsshorths" => .int 1
  | "errorchar" => .char 42
  | "standout" => .file 0 | "standin" => .file 1 | "standerror" => .file 2 | "standback" => .file 3
  | "standoutchannel" => .int 0 | "standinchannel" => .int 1 | "standbackchannel" => .int 3
  | "nil" => .nil
  | n => .builtin n

/-- Bits denotation value. -/
def bitsValue (radix : Nat) (digits : String) : Nat :=
  digits.foldl (fun acc c =>
    let d := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
    acc * radix + d) 0

def isFlexMode (tb : Mode.Table) (m : Mode) : Bool :=
  match Mode.resolve tb m with
  | .row _ true _ => true
  | _ => false

/-- The PROC mode of a routine text (or of an identifier denoting a routine). -/
def routineMode (e : Expr) : Elab Mode := do
  match e with
  | .routine params ret _ _ => return .proc (params.map fun (m, _) => modeOf m) (modeOf ret)
  | .ident n _ =>
    match (← lookup n) with
    | some b => return b.mode
    | none => err s!"identifier {n} has not been declared"
  | _ => err "routine text expected"

mutual

/-- Initial value of a generated/declared object of the given (actual) declarer. -/
partial def defaultValue (m : ModeSyn) : Elab Core := do
  match m with
  | .string => return .lit (.row #[1] #[0] #[])
  | .row bs flex elem =>
    let mut bcs : List (Core × Core) := []
    for b in bs do
      match b with
      | .mk l u =>
        let lc ← match l with
          | some e => (·.1) <$> elabUnit e (.meek (.int 0))
          | none => pure (.lit (.int 1))
        let uc ← match u with
          | some e => (·.1) <$> elabUnit e (.meek (.int 0))
          | none => pure (.lit (.int 0))
        bcs := bcs ++ [(lc, uc)]
    let ei ← defaultValue elem
    return .newRow bcs ei flex
  | .struct fs =>
    let inits ← fs.mapM fun (_, fm) => defaultValue fm
    return .collateral inits true 0
  | .ind n =>
    match (← get).modeSyns.get? n with
    | some syn => defaultValue syn
    | none =>
      match (← tbl).get? n with
      | some m' => defaultOfMode m'
      | none => return .lit .undef
  | .long _ inner => defaultValue inner
  | _ => return .lit .undef

/-- Default value from a semantic mode (no bounds information). -/
partial def defaultOfMode (m : Mode) (fuel : Nat := 8) : Elab Core := do
  if fuel = 0 then return .lit .undef
  match (← resolve m) with
  | .row d f e =>
    let ei ← defaultOfMode e (fuel - 1)
    return .newRow (List.replicate d (Core.lit (.int 1), Core.lit (.int 0))) ei f
  | .struct fs =>
    let inits ← fs.mapM fun (_, fm) => defaultOfMode fm (fuel - 1)
    return .collateral inits true 0
  | _ => return .lit .undef

partial def elabSerial (s : Serial) (ctx : Ctx) : Elab (Core × Mode) :=
  elabSerialK s ctx none

/-- Elaborate a serial clause; if `k` is given, the clause is an enquiry clause whose last
    unit is passed to `k` *inside* the clause's scope (so its declarations stay visible). -/
partial def elabSerialK (s : Serial) (ctx : Ctx) (k : Option (Core → Mode → Elab (Core × Mode))) : Elab (Core × Mode) := do
  pushScope
  let items := s.items
  -- pass 0: modes
  for st in items do
    match st with
    | .decl (.mode n m _) => modify fun es => { es with modes := es.modes.insert n (modeOf m), modeSyns := es.modeSyns.insert n m }
    | _ => pure ()
  -- pass 1: names, operators, labels
  let labelBase := (← get).labelCount
  let mut nLabels := 0
  for st in items do
    match st with
    | .decl (.var m _ vitems p) =>
      modify fun es => { es with curPos := p }
      for (n, init) in vitems do
        let mode ← match m, init with
          | .ind "", some e => do
            let rm ← routineMode e
            pure (Mode.ref rm)
          | _, _ => pure (Mode.ref (modeOf m))
        let _ ← declare n mode .var
    | .decl (.identity (some m) iitems p) =>
      modify fun es => { es with curPos := p }
      for (n, _) in iitems do
        let _ ← declare n (modeOf m) .ident
    | .decl (.identity none iitems p) =>
      modify fun es => { es with curPos := p }
      for (n, e) in iitems do
        let _ ← declare n (← routineMode e) .ident
    | .decl (.op name m body p) =>
      modify fun es => { es with curPos := p }
      let mode ← match m with
        | some m => pure (modeOf m)
        | none => routineMode body
      let _ ← declareOp name mode
    | .label n _ =>
      let id ← newLabel
      nLabels := nLabels + 1
      let _ ← declare n .void (.label id)
    | _ => pure ()
  -- which unit yields the value?
  let lastUnitIdx : Option Nat := match items.getLast? with
    | some (.unit _) => some (items.length - 1)
    | _ => none
  -- pass 2
  let itemsArr := items.toArray
  let mut stmts : List CoreStmt := []
  let mut hoisted : List CoreStmt := []   -- routine-text declarations, elaborated at block entry
  let mut resMode : Mode := .void
  let mut i := 0
  let isRoutineDecl : Decl → Bool
    | .identity _ ditems _ => ditems.all fun (_, e) => match e with | .routine .. => true | _ => false
    | .op _ _ (.routine ..) _ => true
    | _ => false
  for st in items do
    match st with
    | .decl d =>
      -- a68g lets a routine be applied before its declaration in the same clause: routine
      -- texts have no dynamic dependencies, so their declarations are moved to the front
      if isRoutineDecl d then hoisted := hoisted ++ (← elabDecl d)
      else stmts := stmts ++ (← elabDecl d)
    | .unit e =>
      modify fun es => { es with curPos := e.pos }
      let followedByExit := match itemsArr[i+1]? with | some (.exit _) => true | _ => false
      if followedByExit && lastUnitIdx != some i then
        -- completion point: the unit yields the value of the whole serial clause
        let (c, _) ← elabUnit e ctx
        stmts := stmts ++ [.unit (.at e.pos c)]
      else if lastUnitIdx == some i then
        let (c, m) ← elabUnit e ctx
        match k with
        | some kf =>
          let (c', m') ← kf (.at e.pos c) m
          resMode := m'
          stmts := stmts ++ [.unit c']
        | none =>
          resMode := m
          stmts := stmts ++ [.unit (.at e.pos c)]
      else
        let (c, _) ← elabUnit e (.strong .void)
        stmts := stmts ++ [.unit (.at e.pos c)]
    | .label n _ =>
      match (← lookup n) with
      | some { kind := .label id, .. } => stmts := stmts ++ [.label id]
      | _ => err "internal: label"
    | .exit _ => stmts := stmts ++ [.exit]
    i := i + 1
  let sc ← popScope
  let core := Core.block sc.size (hoisted ++ stmts).toArray labelBase nLabels
  if lastUnitIdx.isNone && k.isSome then err "enquiry clause does not yield a value"
  if lastUnitIdx.isNone then
    -- serial clause yielding VOID
    match ctx with
    | .strong t =>
      if (← eqv t .void) then return (core, .void)
      else err s!"serial clause yields VOID but {t} is required"
    | _ => return (core, .void)
  else
    return (core, resMode)

partial def elabDecl (d : Decl) : Elab (List CoreStmt) := do
  match d with
  | .mode _ _ _ | .prio _ _ _ => return []
  | .var m _ items p =>
    modify fun es => { es with curPos := p }
    let mut out : List CoreStmt := []
    for (n, init) in items do
      let some b ← lookup n | err "internal: var binding"
      let refM := b.mode
      let elemM ← match (← resolve refM) with
        | .ref x => pure x
        | _ => err "internal: var mode"
      let dflt ← match m with
        | .ind "" => pure (Core.lit .undef)
        | _ => defaultValue m
      out := out ++ [.decl b.slot elemM dflt]
      match init with
      | some e =>
        let (c, _) ← elabUnit e (.strong elemM)
        out := out ++ [.unit (.at p (.assign (.refCell 0 b.slot) c (isFlexMode (← tbl) elemM)))]
      | none => pure ()
    return out
  | .identity _ items p =>
    modify fun es => { es with curPos := p }
    let mut out : List CoreStmt := []
    for (n, e) in items do
      let some b ← lookup n | err "internal: identity binding"
      let (c, _) ← elabUnit e (.strong b.mode)
      out := out ++ [.decl b.slot b.mode (.at p c)]
    return out
  | .op name m body p =>
    modify fun es => { es with curPos := p }
    let mode ← match m with
      | some m => pure (modeOf m)
      | none => routineMode body
    let ops ← lookupOps name
    let d ← depth
    let mut chosen : Option OpBinding := none
    for ob in ops do
      if chosen.isNone && ob.depth == d - 1 && (← eqv ob.mode mode) then chosen := some ob
    let some ob := chosen | err "internal: op binding"
    let (c, _) ← elabUnit body (.strong ob.mode)
    return [.decl ob.slot ob.mode (.at p c)]

partial def elabUnit (e : Expr) (ctx : Ctx) : Elab (Core × Mode) := do
  modify fun es => { es with curPos := e.pos }
  match e with
  | .block (.mk []) _ =>
    match ctx with
    | .strong t =>
      match (← resolve t) with
      | .row d _ _ => return (.lit (.row (Array.replicate d 1) (Array.replicate d 0) #[]), t)
      | _ => elabSerial (.mk []) ctx
    | _ => elabSerial (.mk []) ctx
  | .block s _ => elabSerial s ctx
  | .cond branches els _ => elabCond branches els ctx
  | .caseInt sel alts out _ => elabCaseInt sel alts out ctx
  | .caseConf sel alts out _ => elabCaseConf sel alts out ctx
  | .loop var f b t w body _ => elabLoop var f b t w body ctx
  | .collateral es _ => elabCollateral es ctx
  | .skip _ =>
    match ctx with
    | .strong t => return (.skip t, t)
    | _ => return (.skip .void, .void)
  | .nil _ =>
    match ctx with
    | .strong t =>
      match (← resolve t) with
      | .ref _ => return (.lit .nil, t)
      | .union ms =>
        match ← ms.findM? (fun m => do return Mode.isRef (← tbl) m) with
        | some m => return (.unite m (.lit .nil), t)
        | none => err "NIL cannot be coerced to a non-REF mode"
      | _ => err s!"NIL cannot be coerced to {t}"
    | _ => return (.lit .nil, .ref .void)
  | .goto l _ =>
    match (← lookup l) with
    | some { kind := .label id, .. } =>
      match ctx with
      | .strong t => return (.goto id, t)
      | _ => return (.goto id, .void)
    | _ => err s!"label {l} has not been declared"
  | .ident "stop" _ =>
    let wantsProc ← match ctx with
      | .strong t => pure (Mode.isProc (← tbl) t)
      | .soft => pure true
      | _ => pure false
    match (← lookup "stop") with
    | some { depth := 0, .. } =>
      if wantsProc then
        applyCtx ctx (.lit (.builtin "stop")) (.proc [] .void)
      else
        match ctx with
        | .strong t => return (.stop, t)
        | _ => return (.stop, .void)
    | some b => applyCtx ctx (← cellCore b) b.mode
    | none => err "tag \"stop\" has not been declared"
  | .ident n _ =>
    match (← lookup n) with
    | some b =>
      match b.kind with
      | .label id =>
        match ctx with
        | .strong t => return (.goto id, t)
        | _ => return (.goto id, .void)
      | _ => applyCtx ctx (← cellCore b) b.mode
    | none => err s!"tag \"{n}\" has not been declared"
  | .routine params ret body _ =>
    let (c, m) ← elabRoutine params ret body
    applyCtx ctx c m
  | _ =>
    let (c, m) ← elabPrimary e
    applyCtx ctx c m

/-- A priori elaboration of context-free constructs. -/
partial def elabPrimary (e : Expr) : Elab (Core × Mode) := do
  match e with
  | .intLit v long _ => return (.lit (.int v), .int long)
  | .realLit t long _ => return (.lit (.real (Numfmt.parseFloat t)), .real long)
  | .bitsLit r d long _ => return (.lit (.bits (bitsValue r d)), .bits long)
  | .strLit s _ =>
    if s.length == 1 then return (.lit (.char s.front.toNat), .char)
    else return (.lit (Value.ofString s), .string)
  | .boolLit b _ => return (.lit (.bool b), .bool)
  | .empty _ => return (.lit .void, .void)
  | .dyadic op l r _ => elabDyadic op l r
  | .monadic op x _ => elabMonadic op x
  | .assign d s _ => elabAssign d s
  | .identity l r isnt _ => elabIdentity l r isnt
  | .call f args _ => elabCall f args
  | .slice arr idx _ => elabSlice arr idx
  | .select f x _ => elabSelect f x
  | .cast m x _ =>
    let target := modeOf m
    let (c, _) ← elabUnit x (.strong target)
    return (c, target)
  | .gen _ m _ =>
    let init ← defaultValue m
    return (.gen init, .ref (modeOf m))
  | .format items _ =>
    let cs ← items.mapM elabFormatItem
    return (.fmt cs, .format)
  | .vacant _ => err "an argument may only be omitted in the actual parameters of a call"
  | _ =>
    -- context-sensitive constructs reached without a context: use firm
    elabUnit e .firm

partial def elabFormatItem (it : FormatItem) : Elab CoreFmt := do
  match it with
  | .literal s => return .literal s
  | .newline => return .newline | .newpage => return .newpage | .space => return .space
  | .backspace => return .backspace
  | .rep n dyn item =>
    let d ← match dyn with
      | some e => some <$> ((·.1) <$> elabUnit e (.meek (.int 0)))
      | none => pure none
    return .rep n d (← elabFormatItem item)
  | .digit z => return .digit z
  | .sign p => return .sign p
  | .point => return .point | .exp => return .exp
  | .general args =>
    let cs ← args.mapM fun a => (·.1) <$> elabUnit a (.meek (.int 0))
    return .general cs
  | .bool_ f g => return .bool_ f g
  | .choice alts => return .choice alts
  | .char_ => return .char_ | .strings => return .strings
  | .group items => return .group (← items.mapM elabFormatItem)
  | .include f => return .include (← (·.1) <$> elabUnit f (.meek .format))
  | .sep => return .sep
  | .col => return .col

partial def elabRoutine (params : List (ModeSyn × String)) (ret : ModeSyn) (body : Expr) : Elab (Core × Mode) := do
  pushScope
  for (m, n) in params do
    let _ ← declare n (modeOf m) .ident
  let retM := modeOf ret
  let (bc, _) ← elabUnit body (.strong retM)
  let sc ← popScope
  return (.routine params.length sc.size bc, .proc (params.map fun (m, _) => modeOf m) retM)

partial def elabAssign (d s : Expr) : Elab (Core × Mode) := do
  let (dc, dm) ← elabUnit d .soft
  match (← resolve dm) with
  | .ref m =>
    let (sc, _) ← elabUnit s (.strong m)
    return (.assign dc sc (isFlexMode (← tbl) m), dm)
  | _ => err s!"cannot assign to a value of mode {dm}"

partial def elabIdentity (l r : Expr) (isnt : Bool) : Elab (Core × Mode) := do
  let isNil : Expr → Bool | .nil _ => true | _ => false
  if isNil r then
    let (lc, lm) ← elabUnit l .soft
    return (.identRel lc (.lit .nil) isnt, .bool)
  if isNil l then
    let (rc, rm) ← elabUnit r .soft
    let _ := rm
    return (.identRel (.lit .nil) rc isnt, .bool)
  let (lc, lm) ← elabUnit l .soft
  let (rc, rm) ← elabUnit r .soft
  let lr ← resolve lm
  let rr ← resolve rm
  match lr, rr with
  | .ref _, .ref _ =>
    if (← eqv lm rm) then return (.identRel lc rc isnt, .bool)
    else if let some rc' ← coerce .strong rc rm lm then return (.identRel lc rc' isnt, .bool)
    else if let some lc' ← coerce .strong lc lm rm then return (.identRel lc' rc isnt, .bool)
    else err s!"identity relation between {lm} and {rm}"
  | _, _ => err s!"identity relation requires REF operands ({lm}, {rm})"

partial def elabCall (f : Expr) (args : List Expr) : Elab (Core × Mode) := do
  -- a68g accepts `a(i)` as a subscript when `a` is a row
  let (wc, wm) ← elabUnit f .weak
  let isRowish ← match (← resolve wm) with
    | .row _ _ _ => pure true
    | .ref x => pure (Mode.isRow (← tbl) x)
    | _ => pure false
  if isRowish then
    let _ := wc
    return ← elabSlice f (args.map fun a => Indexer.index a)
  let (fc, fm) ← elabUnit f .meekAny
  -- a68g accepts `establish (file, name, channel)` without page/line/char bounds
  let args := match fc, args with
    | .lit (.builtin "establish"), [a, b, c] => [a, b, c, .intLit 0 0 f.pos, .intLit 0 0 f.pos, .intLit 0 0 f.pos]
    | _, _ => args
  match (← resolve fm) with
  | .proc ps r =>
    if ps.length != args.length then
      err s!"procedure expects {ps.length} arguments, {args.length} given"
    if args.any (fun a => match a with | .vacant _ => true | _ => false) then
      return ← elabPartialCall f args ps r
    let mut cs : List Core := []
    for (a, p) in args.zip ps do
      let (c, _) ← elabUnit a (.strong p)
      cs := cs ++ [c]
    return (.call fc cs, r)
  | _ => err s!"call of a non-procedure of mode {fm}"

/-- Partial parametrisation (a68g implements Lindsey's proposal): `f (a, , c)` with
    `f : PROC (A, B, C) R` yields a `PROC (B) R`.  The procedure and the arguments that are
    given are evaluated at the call, in that order, and kept; the omitted ones become the
    parameters of the new procedure, in their original order.  This is elaborated as a
    block whose frame holds those values and which yields a routine text over the omitted
    parameters:

        ( PROC (A, B, C) R p = f; A a = …; C c = …; (B b) R: p (a, b, c) )

    so both back ends need nothing new.  A partial call of a partial procedure composes. -/
partial def elabPartialCall (f : Expr) (args : List Expr) (ps : List Mode) (r : Mode) : Elab (Core × Mode) := do
  pushScope
  let (fc, fm) ← elabUnit f .meekAny
  let fSlot ← newSlot
  let mut stmts : List CoreStmt := [.decl fSlot fm fc]
  let mut given : List (Option Nat) := []    -- the slot holding each given argument
  let mut missing : List Mode := []
  for (a, p) in args.zip ps do
    match a with
    | .vacant _ =>
      given := given ++ [none]
      missing := missing ++ [p]
    | _ =>
      let (c, _) ← elabUnit a (.strong p)
      let s ← newSlot
      stmts := stmts ++ [.decl s p (.at a.pos c)]
      given := given ++ [some s]
  let mut k := 0
  let mut callArgs : List Core := []
  for g in given do
    match g with
    | some s => callArgs := callArgs ++ [.loadCell 1 s]
    | none =>
      callArgs := callArgs ++ [.loadCell 0 k]
      k := k + 1
  let body := Core.call (.loadCell 1 fSlot) callArgs
  let routine := Core.routine missing.length missing.length body
  let sc ← popScope
  let labelBase := (← get).labelCount
  return (.block sc.size (stmts ++ [CoreStmt.unit routine]).toArray labelBase 0, .proc missing r)

partial def elabSlice (arr : Expr) (idx : List Indexer) : Elab (Core × Mode) := do
  let (ac, am) ← elabUnit arr .weak
  let (viaRef, rowM) ← match (← resolve am) with
    | .ref x => pure (true, ← resolve x)
    | x => pure (false, x)
  match rowM with
  | .row d _ em =>
    if idx.length != d then err s!"row has {d} dimensions, {idx.length} indexers given"
    let mut cs : List CoreIdx := []
    let mut nTrims := 0
    for ix in idx do
      match ix with
      | .index e =>
        let (c, _) ← elabUnit e (.meek (.int 0))
        cs := cs ++ [.index c]
      | .trim l u at_ =>
        let lc ← l.mapM fun e => (·.1) <$> elabUnit e (.meek (.int 0))
        let uc ← u.mapM fun e => (·.1) <$> elabUnit e (.meek (.int 0))
        let atc ← at_.mapM fun e => (·.1) <$> elabUnit e (.meek (.int 0))
        cs := cs ++ [.trim lc uc atc]
        nTrims := nTrims + 1
    let resM := if nTrims == 0 then em else Mode.row nTrims false em
    return (.slice ac cs viaRef, if viaRef then .ref resM else resM)
  | _ => err s!"cannot slice a value of mode {am}"

partial def elabSelect (field : String) (x : Expr) : Elab (Core × Mode) := do
  let (xc, xm) ← elabUnit x .weak
  let (viaRef, sm) ← match (← resolve xm) with
    | .ref y => pure (true, ← resolve y)
    | y => pure (false, y)
  let asStruct (m : Mode) : Mode := match m with
    | .compl n => Mode.struct [("re", .real n), ("im", .real n)]   -- COMPL is STRUCT (REAL re, im)
    | m => m
  match asStruct sm with
  | .struct fs =>
    match fs.findIdx? (·.1 == field) with
    | some i =>
      let fm := (fs[i]!).2
      return (.select i xc viaRef, if viaRef then .ref fm else fm)
    | none => err s!"no field {field} in {sm}"
  | .row d fl em =>
    -- multiple selection: a field of every element of a row of structures
    match asStruct (← resolve em) with
    | .struct fs =>
      match fs.findIdx? (·.1 == field) with
      | some i =>
        let fm := (fs[i]!).2
        let rm := Mode.row d fl fm
        return (.select i xc viaRef, if viaRef then .ref rm else rm)
      | none => err s!"no field {field} in {em}"
    | _ => err s!"cannot select {field} from a value of mode {xm}"
  | _ => err s!"cannot select {field} from a value of mode {xm}"

partial def elabDyadic (op : String) (l r : Expr) : Elab (Core × Mode) := do
  if ["ANDF", "ANDTH", "THEF"].contains op then
    let (lc, _) ← elabUnit l (.meek .bool)
    let (rc, _) ← elabUnit r (.meek .bool)
    return (.andThen lc rc, .bool)
  if ["OREL", "ORF"].contains op then
    let (lc, _) ← elabUnit l (.meek .bool)
    let (rc, _) ← elabUnit r (.meek .bool)
    return (.orElse lc rc, .bool)
  let (lc, lm) ← elabUnit l .firm
  let (rc, rm) ← elabUnit r .firm
  -- user-defined operators first
  for ob in (← lookupOps op) do
    match (← resolve ob.mode) with
    | .proc [p1, p2] res =>
      if let some lc' ← coerce .firm lc lm p1 then
        if let some rc' ← coerce .firm rc rm p2 then
          let d ← depth
          return (.call (.loadCell (d - 1 - ob.depth) ob.slot) [lc', rc'], res)
    | _ => pure ()
  let cop := canonOp op
  if isAssignOp op then
    if cop == "+=:" then
      -- value +=: REF STRING
      let (rc', rm') ← softCoerce rc rm
      match (← resolve rm') with
      | .ref m =>
        let (lc', lm') ← meekCoerce lc lm
        let lm'' ← resolve lm'
        let lc'' := if lm'' == .char then Core.rowOf lc' else lc'
        return (.dyop "+=:" .string (.ref m) lc'' rc', rm')
      | _ => err "+=: requires a REF STRING right operand"
    let (lc', lm') ← softCoerce lc lm
    match (← resolve lm') with
    | .ref m =>
      let mR ← resolve m
      let (rc', rm') ← meekCoerce rc rm
      let rmR ← resolve rm'
      let tb ← tbl
      if isStringMode tb mR then
        let rc'' := if rmR == .char then Core.rowOf rc' else rc'
        if cop == "+:=" then return (.dyop "+:=" (.ref .string) .string lc' rc'', lm')
        else if cop == "*:=" then
          match rmR with
          | .int _ => return (.dyop "*:=" (.ref .string) (.int 0) lc' rc', lm')
          | _ => err s!"operator {op} on {lm} and {rm}"
        else err s!"operator {op} on {lm} and {rm}"
      match mR, rmR with
      | .bits a, .bits _ =>
        if cop == "&:=" || cop == "|:=" then return (.dyop cop (.ref (.bits a)) (.bits a) lc' rc', lm')
        else err s!"operator {op} on {lm} and {rm}"
      | _, _ =>
        match numJoin mR rmR with
        | some j =>
          if j == mR || (mR == .real 0 && rmR == .int 0) || widenable rmR mR then
            let rc'' := widenTo rc' rmR mR
            -- INT %:= / %*:= need INT; REAL /:= etc fine
            return (.dyop cop (.ref mR) mR lc' rc'', lm')
          else err s!"{rm} cannot be coerced to {m} in operator {op}"
        | none => err s!"operator {op} has not been declared for {lm} and {rm}"
    | _ => err s!"operator {op} requires a REF left operand, found {lm}"
  let (lc', lm') ← meekCoerce lc lm
  let (rc', rm') ← meekCoerce rc rm
  match (← builtinDyadic op lc' lm' rc' rm') with
  | some res => return res
  | none => err s!"dyadic operator {lm} \"{op}\" {rm} has not been declared"

partial def elabMonadic (op : String) (x : Expr) : Elab (Core × Mode) := do
  let (xc, xm) ← elabUnit x .firm
  for ob in (← lookupOps op) do
    match (← resolve ob.mode) with
    | .proc [p] res =>
      if let some xc' ← coerce .firm xc xm p then
        let d ← depth
        return (.call (.loadCell (d - 1 - ob.depth) ob.slot) [xc'], res)
    | _ => pure ()
  let (xc', xm') ← meekCoerce xc xm
  match (← builtinMonadic op xc' xm') with
  | some res => return res
  | none => err s!"monadic operator \"{op}\" {xm} has not been declared"

/-- Does a core never yield a value (jump / stop)? Such branches do not take part in balancing. -/
partial def isWild : Core → Bool
  | .stop | .goto _ | .skip _ => true
  | .at _ e => isWild e
  | .voiding e => isWild e
  | .block _ stmts _ _ => match stmts.toList with
    | [.unit e] => isWild e
    | _ => false
  | _ => false

/-- Balance a list of (core, mode) so that all have a common mode. -/
partial def balance (parts : List (Core × Mode)) : Elab (List Core × Mode) := do
  let live := parts.filter fun (c, _) => !isWild c
  if live.length < parts.length && !live.isEmpty then
    let (_, m) ← balance live
    let cs ← parts.mapM fun (c, cm) => do
      if isWild c then pure c else
      match (← coerce .strong c cm m) with
      | some c' => pure c'
      | none => err s!"cannot balance {cm} with {m}"
    return (cs, m)
  match parts with
  | [] => return ([], .void)
  | (c0, m0) :: rest =>
    let mut allEq := true
    for (_, m) in rest do
      if !(← eqv m m0) then allEq := false
    if allEq then return (parts.map (·.1), m0)
    -- try each candidate mode: the branches' a priori modes, then their meekly coerced modes
    let mut cands : List Mode := parts.map (·.2)
    for (c, m) in parts do
      let (_, m') ← meekCoerce c m
      cands := cands ++ [m']
    for cand in cands do
      let mut ok := true
      let mut cs : List Core := []
      for (c, m) in parts do
        match (← coerce .strong c m cand) with
        | some c' => cs := cs ++ [c']
        | none => ok := false
      if ok then return (cs, cand)
    -- last resort: void
    let cs ← parts.mapM fun (c, m) => coerceStrong c m .void
    let _ := c0
    return (cs, .void)

/-- Elaborate branches in a context; balance if the context has no target. -/
partial def elabBranches (fs : List (Elab (Core × Mode))) (ctx : Ctx) : Elab (List Core × Mode) := do
  let parts ← fs.mapM id
  match ctx with
  | .strong t => return (parts.map (·.1), t)
  | .meek t => return (parts.map (·.1), t)
  | _ => balance parts

partial def elabCond (branches : List (Serial × Serial)) (els : Option Serial) (ctx : Ctx) : Elab (Core × Mode) := do
  match branches with
  | [] =>
    match els with
    | some e => elabSerial e ctx
    | none =>
      match ctx with
      | .strong t => return (.skip t, t)
      | _ => return (.skip .void, .void)
  | (c, t) :: rest =>
    elabSerialK c (.meek .bool) (some fun cc _ => do
      let (parts, m) ← elabBranches [elabSerial t ctx, elabCond rest els ctx] ctx
      match parts with
      | [tc, ec] => return (.cond cc tc ec, m)
      | _ => err "internal: cond")

partial def elabCaseInt (sel : Serial) (alts : List Expr) (out : Option Serial) (ctx : Ctx) : Elab (Core × Mode) := do
  elabSerialK sel (.meek (.int 0)) (some fun sc _ => do
    let outE : Elab (Core × Mode) := match out with
      | some o => elabSerial o ctx
      | none => match ctx with
        | .strong t => pure (.skip t, t)
        | _ => pure (.skip .void, .void)
    let (parts, m) ← elabBranches (alts.map (fun a => elabUnit a ctx) ++ [outE]) ctx
    match parts.reverse with
    | oc :: revAlts => return (.caseInt sc revAlts.reverse oc, m)
    | _ => err "internal: case")

partial def elabCaseConf (sel : Serial) (alts : List (ModeSyn × Option String × Expr)) (out : Option Serial) (ctx : Ctx) : Elab (Core × Mode) := do
  elabSerialK sel .meekAny (some fun sc _ => elabCaseConfBody sc alts out ctx)

partial def elabCaseConfBody (sc : Core) (alts : List (ModeSyn × Option String × Expr)) (out : Option Serial) (ctx : Ctx) : Elab (Core × Mode) := do
  let altE (a : ModeSyn × Option String × Expr) : Elab (Core × Mode) := do
    let (msyn, name, body) := a
    let m := modeOf msyn
    pushScope
    match name with
    | some n => let _ ← declare n m .ident
    | none => pure ()
    let (bc, bm) ← elabUnit body ctx
    let _ ← popScope
    return (bc, bm)
  let outE : Elab (Core × Mode) := match out with
    | some o => elabSerial o ctx
    | none => match ctx with
      | .strong t => pure (.skip t, t)
      | _ => pure (.skip .void, .void)
  let (parts, m) ← elabBranches (alts.map altE ++ [outE]) ctx
  match parts.reverse with
  | oc :: revAlts =>
    let altCores := revAlts.reverse
    let mut coreAlts : List (Mode × Option Nat × Core) := []
    for (a, c) in alts.zip altCores do
      let (msyn, name, _) := a
      coreAlts := coreAlts ++ [(modeOf msyn, if name.isSome then some 0 else none, c)]
    return (.caseConf sc coreAlts oc, m)
  | _ => err "internal: conformity case"

partial def elabLoop (var : Option String) (f b t : Option Expr) (w : Option Serial) (body : Serial) (ctx : Ctx) : Elab (Core × Mode) := do
  let fc ← match f with
    | some e => (·.1) <$> elabUnit e (.meek (.int 0))
    | none => pure (Core.lit (.int 1))
  let bc ← match b with
    | some e => (·.1) <$> elabUnit e (.meek (.int 0))
    | none => pure (Core.lit (.int 1))
  let tc ← match t with
    | some e => some <$> ((·.1) <$> elabUnit e (.meek (.int 0)))
    | none => pure none
  pushScope
  let slot ← match var with
    | some n => some <$> declare n (.int 0) .ident
    | none => pure none
  let (wc, bodyC) ← match w with
    | some s =>
      -- WHILE w DO body OD  ≡  WHILE (w-decls; IF w THEN body; TRUE ELSE FALSE FI) DO SKIP OD
      let (c, _) ← elabSerialK s (.meek .bool) (some fun cc _ => do
        let (bodyC, _) ← elabSerial body (.strong .void)
        return (Core.cond cc (.seq bodyC (.lit (.bool true))) (.lit (.bool false)), .bool))
      pure (some c, Core.lit .void)
    | none =>
      let (bodyC, _) ← elabSerial body (.strong .void)
      pure (none, bodyC)
  let _ ← popScope
  applyCtx ctx (.loop slot fc bc tc wc bodyC) .void

partial def elabCollateral (es : List Expr) (ctx : Ctx) : Elab (Core × Mode) := do
  match ctx with
  | .strong t =>
    match (← resolve t) with
    | .row d _ em =>
      let elemTarget := if d == 1 then em else Mode.row (d - 1) false em
      let cs ← es.mapM fun e => (·.1) <$> elabUnit e (.strong elemTarget)
      return (.collateral cs false d, t)
    | .struct fs =>
      if fs.length != es.length then err s!"struct display: {fs.length} fields expected, {es.length} given"
      let cs ← (es.zip fs).mapM fun (e, (_, fm)) => (·.1) <$> elabUnit e (.strong fm)
      return (.collateral cs true 0, t)
    | .compl n =>
      match es with
      | [re, im] =>
        let (rc, _) ← elabUnit re (.strong (.real n))
        let (ic, _) ← elabUnit im (.strong (.real n))
        return (.collateral [rc, ic] true 0, t)
      | _ => err "COMPL display needs two elements"
    | .void =>
      let cs ← es.mapM fun e => (·.1) <$> elabUnit e (.strong .void)
      return (.voiding (.collateral cs false 1), .void)
    | .union ms =>
      for m in ms do
        match (← resolve m) with
        | .row _ _ _ | .struct _ =>
          let (c, _) ← elabCollateral es (.strong m)
          return (.unite m c, t)
        | _ => pure ()
      err s!"collateral clause cannot be coerced to {t}"
    | _ => err s!"collateral clause cannot be coerced to {t}"
  | _ =>
    let parts ← es.mapM fun e => elabUnit e .meekAny
    let (cs, m) ← balance parts
    return (.collateral cs false 1, .row 1 false m)

end

/-- Elaborate a whole program. -/
def elabProgram (s : Serial) : Except ElabError (Core × Nat) :=
  let base : Scope := {
    names := (Builtins.consts.map fun (n, m) =>
                (n, { mode := m, depth := 0, slot := 0, kind := .builtinConst (constValue n) }))
             ++ (Builtins.procs.map fun (n, m) =>
                (n, { mode := m, depth := 0, slot := 0, kind := .builtinProc n })),
    ops := [], size := 0 }
  let st : ElabState := { scopes := [base] }
  match (elabSerial s (.strong .void)).run st with
  | .ok ((c, _), st') => .ok (c, st'.labelCount)
  | .error e => .error e

/-- Elaborate a whole program, returning the core and the mode table (needed at run time). -/
def elabProgramWithModes (s : Serial) (ll : Nat := Numfmt.defaultLLDigits) (fileName : String := "") : Except ElabError (Core × Mode.Table) :=
  let base : Scope := {
    names := (Builtins.consts.map fun (n, m) =>
                (n, { mode := m, depth := 0, slot := 0, kind := .builtinConst (constValue n ll fileName) }))
             ++ (Builtins.procs.map fun (n, m) =>
                (n, { mode := m, depth := 0, slot := 0, kind := .builtinProc n })),
    ops := [], size := 0 }
  let st : ElabState := { scopes := [base], llDigits := ll }
  match (elabSerial s (.strong .void)).run st with
  | .ok ((c, _), st') => .ok (c, st'.modes)
  | .error e => .error e

end Elab
end A68
