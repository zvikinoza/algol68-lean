import A68.Mode
import A68.MP

/-!
# A68.Core — runtime values and the elaborated intermediate representation

The elaborator turns `Syntax` into `Core`, where

* every identifier is resolved to a frame `(depth, slot)`,
* every coercion (dereferencing, deproceduring, widening, rowing, uniting,
  voiding) is an explicit node,
* every operator is resolved either to a builtin (by name and operand modes)
  or to a user routine stored in a cell.

Runtime values (`Value`) and `Core` are mutually recursive because closures
(routine texts) capture an environment of frames of cells.
-/
namespace A68

/-- One step in a path from a cell to a sub-value. -/
inductive Sel where
  | field (i : Nat)                              -- struct field
  | elem (i : Nat)                               -- flat row element index
  | sub (lwb upb : Array Int) (offs : Array Nat) -- trimmed/sliced sub-row view (element offsets)
  deriving Repr, BEq, Inhabited

mutual
inductive Value where
  | undef
  | int (v : Int)
  | real (v : Float)
  | mp (x : MP.MP)                              -- LONG / LONG LONG REAL (a68g multi-precision)
  | bool (b : Bool)
  | char (c : Nat)                               -- a byte 0..255
  | bits (v : Nat)
  | compl (re im : Float)
  | void
  | nil
  | ref (cell : Nat) (path : List Sel)
  | row (lwb upb : Array Int) (elems : Array Value)
  | struct (fs : Array Value)
  | union (m : Mode) (v : Value)
  | proc (env : List (Array Nat)) (nparams frameSize : Nat) (body : Core)
  | builtin (name : String)
  | cproc (fn : Nat) (nparams : Nat) (env : List (Array Nat))   -- compiled procedure
  | fmt (env : List (Array Nat)) (items : List CoreFmt)
  | file (id : Nat)
  deriving Inhabited, Repr

/-- An indexer whose bounds have already been evaluated. -/
inductive IdxVal where
  | index (v : Value)
  | trim (lo hi at_ : Option Value)
  deriving Inhabited

inductive CoreIdx where
  | index (e : Core)
  | trim (lwb upb : Option Core) (at_ : Option Core)
  deriving Inhabited, Repr

inductive CoreFmt where
  | literal (s : String)
  | newline | newpage | space | backspace
  | rep (n : Nat) (dyn : Option Core) (item : CoreFmt)
  | digit (zero : Bool)
  | sign (plus : Bool)
  | point
  | exp
  | general (args : List Core)
  | bool_ (flip flop : Option String)
  | choice (alts : List String)
  | char_
  | strings
  | group (items : List CoreFmt)
  | include (f : Core)
  | sep
  | col
  deriving Inhabited, Repr

inductive CoreStmt where
  | decl (slot : Nat) (mode : Mode) (init : Core)
  | unit (e : Core)
  | label (id : Nat)
  | exit
  deriving Inhabited, Repr

inductive Core where
  | lit (v : Value)
  | loadCell (depth slot : Nat)
  | refCell (depth slot : Nat)
  | deref (e : Core)
  | deproc (e : Core)
  | widen (src dst : Mode) (e : Core)
  | rowOf (e : Core)                            -- value M → [] M  (or REF M → REF [] M)
  | unite (m : Mode) (e : Core)
  | voiding (e : Core)
  | assign (dest src : Core) (flex : Bool)
  | identRel (l r : Core) (isnt : Bool)
  | dyop (op : String) (m1 m2 : Mode) (l r : Core)
  | monop (op : String) (m : Mode) (e : Core)
  | call (f : Core) (args : List Core)
  | routine (nparams frameSize : Nat) (body : Core)
  | slice (arr : Core) (idx : List CoreIdx) (viaRef : Bool)
  | select (idx : Nat) (e : Core) (viaRef : Bool)
  | newRow (bounds : List (Core × Core)) (elemInit : Core) (flex : Bool)
  | gen (init : Core)                           -- allocate a cell, yield REF
  | block (frameSize : Nat) (stmts : Array CoreStmt) (labelBase : Nat) (nLabels : Nat)
  | collateral (es : List Core) (isStruct : Bool) (dims : Nat)   -- row display (dims ≥ 1) or struct display
  | cond (c t e : Core)
  | caseInt (sel : Core) (alts : List Core) (out : Core)
  | caseConf (sel : Core) (alts : List (Mode × Option Nat × Core)) (out : Core)
  | loop (slot : Option Nat) (from_ by_ : Core) (to_ : Option Core) (whileC : Option Core) (body : Core)
  | goto (label : Nat)
  | skip (m : Mode)
  | andThen (l r : Core)
  | orElse (l r : Core)
  | fmt (items : List CoreFmt)
  | stop
  | seq (a b : Core)                            -- evaluate a, then b (no new frame)
  | hole (fn : Nat) (idx : Nat)                 -- compiled code: evaluate via the C dispatcher
  | at (p : Pos) (e : Core)
  deriving Inhabited, Repr
end

namespace Value

def isUndef : Value → Bool
  | undef => true
  | _ => false

/-- Build a row value with bounds `1:n` from a list of elements. -/
def rowOfList (xs : List Value) : Value :=
  .row #[1] #[xs.length] xs.toArray

/-- Build a STRING (FLEX [] CHAR) value from a byte-string. -/
def ofString (s : String) : Value :=
  rowOfList (s.toList.map fun c => .char c.toNat)

/-- Extract a string from a `[] CHAR` value (undefined characters become `?`). -/
def charOf : Value → Char
  | .char c => Char.ofNat c
  | _ => '?'

def toStr : Value → String
  | .row _ _ es => String.ofList (es.toList.map charOf)
  | .char c => String.singleton (Char.ofNat c)
  | _ => ""

end Value

end A68
