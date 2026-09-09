import A68.Syntax
import Std.Data.HashMap

/-!
# A68.Mode — modes (types) of Algol 68

`Mode` is the semantic counterpart of `ModeSyn`: bounds are dropped, `STRING`
is `FLEX [] CHAR`, and user mode indicants are kept as `named` references into
a `ModeTable` so that recursive modes (`MODE NODE = STRUCT (INT v, REF NODE next)`)
are representable.  Mode equivalence unfolds indicants with a fuel bound.
-/
namespace A68

inductive Mode where
  | int (n : Int)          -- 0 = INT, 1 = LONG INT, 2 = LONG LONG INT, -1 = SHORT INT
  | real (n : Int)
  | bool | char | void
  | bits (n : Int)
  | bytes (n : Int)
  | compl (n : Int)
  | ref (m : Mode)
  | row (dims : Nat) (flex : Bool) (m : Mode)
  | proc (ps : List Mode) (r : Mode)
  | struct (fs : List (String × Mode))
  | union (ms : List Mode)
  | named (n : String)
  | format | file | channel | sema
  | simplout               -- pseudo-union accepted by print/printf (any straightenable mode)
  | simplin                -- pseudo-union accepted by read/get (names, not dereferenced)
  | number                 -- pseudo-union for whole/fixed/float: any INT or REAL of any length
  deriving Repr, BEq, Inhabited, Hashable

namespace Mode

def string : Mode := row 1 true char
def rowOf (m : Mode) : Mode := row 1 false m

abbrev Table := Std.HashMap String Mode

/-- Unfold a named mode once (if known). -/
def unfold (tbl : Table) : Mode → Option Mode
  | named n => tbl.get? n
  | _ => none

/-- Mode equivalence, ignoring `flex`, unfolding indicants with fuel. -/
partial def eqv (tbl : Table) (a b : Mode) (fuel : Nat := 64) : Bool :=
  if fuel = 0 then false else
  match a, b with
  | named x, named y => x == y || (match tbl.get? x, tbl.get? y with
      | some a', some b' => eqv tbl a' b' (fuel - 1)
      | _, _ => false)
  | named x, _ => match tbl.get? x with
      | some a' => eqv tbl a' b (fuel - 1)
      | none => false
  | _, named y => match tbl.get? y with
      | some b' => eqv tbl a b' (fuel - 1)
      | none => false
  | int n, int m => n == m
  | real n, real m => n == m
  | bool, bool | char, char | void, void => true
  | bits n, bits m => n == m
  | bytes n, bytes m => n == m
  | compl n, compl m => n == m
  | ref x, ref y => eqv tbl x y (fuel - 1)
  | row d1 _ x, row d2 _ y => d1 == d2 && eqv tbl x y (fuel - 1)
  | proc ps r, proc qs s => ps.length == qs.length &&
      (List.zip ps qs).all (fun (p, q) => eqv tbl p q (fuel - 1)) && eqv tbl r s (fuel - 1)
  | struct fs, struct gs => fs.length == gs.length &&
      (List.zip fs gs).all (fun ((n1, m1), (n2, m2)) => n1 == n2 && eqv tbl m1 m2 (fuel - 1))
  | union ms, union ns => ms.length == ns.length &&
      ms.all (fun m => ns.any (fun n => eqv tbl m n (fuel - 1)))
  | format, format | file, file | channel, channel | sema, sema => true
  | simplout, simplout | number, number | simplin, simplin => true
  | _, _ => false

/-- Resolve a named mode to its structure (one or more unfoldings). -/
partial def resolve (tbl : Table) (m : Mode) (fuel : Nat := 32) : Mode :=
  match m with
  | named n => if fuel = 0 then m else match tbl.get? n with
      | some m' => resolve tbl m' (fuel - 1)
      | none => m
  | _ => m

def isRef (tbl : Table) (m : Mode) : Bool :=
  match resolve tbl m with | ref _ => true | _ => false

def isProc (tbl : Table) (m : Mode) : Bool :=
  match resolve tbl m with | proc _ _ => true | _ => false

def isRow (tbl : Table) (m : Mode) : Bool :=
  match resolve tbl m with | row _ _ _ => true | _ => false

def isUnion (tbl : Table) (m : Mode) : Bool :=
  match resolve tbl m with | union _ => true | _ => false

def isNumeric : Mode → Bool
  | int _ | real _ => true
  | _ => false

/-- Strip all leading REFs. -/
partial def stripRefs (tbl : Table) (m : Mode) : Mode :=
  match resolve tbl m with
  | ref x => stripRefs tbl x
  | m' => m'

/-- Pretty printer using Algol 68 notation (for diagnostics). -/
partial def toString : Mode → String
  | int n => longPrefix n ++ "INT"
  | real n => longPrefix n ++ "REAL"
  | bool => "BOOL" | char => "CHAR" | void => "VOID"
  | bits n => longPrefix n ++ "BITS"
  | bytes n => longPrefix n ++ "BYTES"
  | compl n => longPrefix n ++ "COMPL"
  | ref m => "REF " ++ toString m
  | row d f m => (if f then "FLEX " else "") ++ "[" ++ String.ofList (List.replicate (d - 1) ',') ++ "] " ++ toString m
  | proc ps r => "PROC " ++ (if ps.isEmpty then "" else "(" ++ ", ".intercalate (ps.map toString) ++ ") ") ++ toString r
  | struct fs => "STRUCT (" ++ ", ".intercalate (fs.map fun (n, m) => toString m ++ " " ++ n) ++ ")"
  | union ms => "UNION (" ++ ", ".intercalate (ms.map toString) ++ ")"
  | named n => n
  | format => "FORMAT" | file => "FILE" | channel => "CHANNEL" | sema => "SEMA"
  | simplout => "SIMPLOUT" | number => "NUMBER" | simplin => "SIMPLIN"
where
  longPrefix (n : Int) : String :=
    if n > 0 then String.join (List.replicate n.toNat "LONG ")
    else if n < 0 then String.join (List.replicate (-n).toNat "SHORT ")
    else ""

instance : ToString Mode := ⟨toString⟩

/-- Convert syntax to a mode (bounds dropped). `STRING` becomes `FLEX [] CHAR`. -/
partial def ofSyn : ModeSyn → Mode
  | .int => int 0 | .real => real 0 | .bool => bool | .char => char | .void => void
  | .bits => bits 0 | .bytes => bytes 0 | .compl => compl 0
  | .string => string
  | .format => format | .file => file | .channel => channel | .sema => sema
  | .long n m =>
    let clamp (k : Int) : Int := if k < 0 then 0 else k   -- a68g: SHORT modes equal the base mode
    match ofSyn m with
    | int k => int (clamp (k + n)) | real k => real (clamp (k + n)) | bits k => bits (clamp (k + n))
    | bytes k => bytes (clamp (k + n)) | compl k => compl (clamp (k + n))
    | other => other
  | .ref m => ref (ofSyn m)
  | .row bs f m => row bs.length f (ofSyn m)
  | .proc ps r => proc (ps.map ofSyn) (ofSyn r)
  | .struct fs => struct (fs.map fun (n, m) => (n, ofSyn m))
  | .union ms => union (ms.map ofSyn)
  | .ind n => named n

end Mode
end A68
