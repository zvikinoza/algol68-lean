import A68.Mode
import A68.Core

/-!
# A68.Serial — serialisation of the tables a compiled program needs at run time

A program compiled to C keeps its *structure* in C (control flow, calls,
operators) but shares the runtime with the interpreter, so a few tables have to
be rebuilt when the compiled program starts:

* the **mode table** — modes tag united values, drive the layout of `print`,
  select conformity alternatives and name modes in diagnostics;
* the **format table** — format texts, whose dynamic parts (`n(expr)`,
  `g(w,a)`, `f(fmt)`) are `Core.hole` nodes that call back into the compiled
  code.

Both are written as a single text blob that the C program carries as a string
literal and hands to `a68rt_boot`. The encoding is line-based and index-based;
strings are hex-encoded so that a line never contains a delimiter.
-/
namespace A68.Serial

/-- Hex-encode a byte string (each character is taken modulo 256, as elsewhere). -/
def hexEncode (s : String) : String :=
  let digits := "0123456789abcdef"
  String.ofList (s.toList.flatMap fun c =>
    let n := c.toNat % 256
    [digits.get ⟨n / 16⟩, digits.get ⟨n % 16⟩])

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if c ≥ 'a' && c ≤ 'f' then 10 + c.toNat - 'a'.toNat
  else 0

def hexDecode (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i + 1 < cs.size do
    out := out.push (Char.ofNat (hexVal cs[i]! * 16 + hexVal cs[i+1]!))
    i := i + 2
  return out

/-- Writer state: tables built while serialising, with hash-consing by rendered line. -/
structure Writer where
  lines : Array String := #[]
  index : Std.HashMap String Nat := {}
  deriving Inhabited

def Writer.add (w : Writer) (line : String) : Nat × Writer :=
  match w.index.get? line with
  | some i => (i, w)
  | none =>
    let i := w.lines.size
    (i, { lines := w.lines.push line, index := w.index.insert line i })

def Writer.str (w : Writer) (s : String) : Nat × Writer := w.add ("s " ++ hexEncode s)

/-- Serialise a mode, returning its table index. -/
partial def putMode (w : Writer) : Mode → Nat × Writer
  | .int n => w.add s!"m int {n}"
  | .real n => w.add s!"m real {n}"
  | .bool => w.add "m bool"
  | .char => w.add "m char"
  | .void => w.add "m void"
  | .bits n => w.add s!"m bits {n}"
  | .bytes n => w.add s!"m bytes {n}"
  | .compl n => w.add s!"m compl {n}"
  | .ref m => let (i, w) := putMode w m; w.add s!"m ref {i}"
  | .row d f m => let (i, w) := putMode w m; w.add s!"m row {d} {if f then 1 else 0} {i}"
  | .proc ps r =>
    let (is, w) := ps.foldl (fun (acc, w) p => let (i, w) := putMode w p; (acc ++ [i], w)) ([], w)
    let (ri, w) := putMode w r
    w.add s!"m proc {ri} {is.length}{String.join (is.map fun i => " " ++ toString i)}"
  | .struct fs =>
    let (is, w) := fs.foldl (fun (acc, w) (n, m) =>
      let (si, w) := w.str n
      let (mi, w) := putMode w m
      (acc ++ [(si, mi)], w)) ([], w)
    w.add s!"m struct {is.length}{String.join (is.map fun (a, b) => s!" {a} {b}")}"
  | .union ms =>
    let (is, w) := ms.foldl (fun (acc, w) m => let (i, w) := putMode w m; (acc ++ [i], w)) ([], w)
    w.add s!"m union {is.length}{String.join (is.map fun i => " " ++ toString i)}"
  | .named n => let (i, w) := w.str n; w.add s!"m named {i}"
  | .format => w.add "m format"
  | .file => w.add "m file"
  | .channel => w.add "m channel"
  | .sema => w.add "m sema"
  | .simplout => w.add "m simplout"
  | .simplin => w.add "m simplin"
  | .number => w.add "m number"

/-- Serialise a `Core` that occurs inside a format text. Only `hole` nodes and
    literals can occur there in compiled code. -/
partial def putFmtCore (w : Writer) : Core → Nat × Writer
  | .hole fn idx => w.add s!"c hole {fn} {idx}"
  | .lit (.int n) => w.add s!"c int {n}"
  | .at _ e => putFmtCore w e
  | _ => w.add "c bad"

partial def putFmt (w : Writer) : CoreFmt → Nat × Writer
  | .literal s => let (i, w) := w.str s; w.add s!"f lit {i}"
  | .newline => w.add "f nl"
  | .newpage => w.add "f np"
  | .space => w.add "f sp"
  | .backspace => w.add "f bs"
  | .rep n dyn item =>
    let (di, w) := match dyn with
      | some c => let (i, w) := putFmtCore w c; (i + 1, w)
      | none => (0, w)
    let (ii, w) := putFmt w item
    w.add s!"f rep {n} {di} {ii}"
  | .digit z => w.add s!"f dig {if z then 1 else 0}"
  | .sign p => w.add s!"f sign {if p then 1 else 0}"
  | .point => w.add "f point"
  | .exp => w.add "f exp"
  | .general args =>
    let (is, w) := args.foldl (fun (acc, w) a => let (i, w) := putFmtCore w a; (acc ++ [i], w)) ([], w)
    w.add s!"f gen {is.length}{String.join (is.map fun i => " " ++ toString i)}"
  | .bool_ f g =>
    match f, g with
    | some a, some b =>
      let (ai, w) := w.str a
      let (bi, w) := w.str b
      w.add s!"f bool 1 {ai} {bi}"
    | _, _ => w.add "f bool 0"
  | .choice alts =>
    let (is, w) := alts.foldl (fun (acc, w) a => let (i, w) := w.str a; (acc ++ [i], w)) ([], w)
    w.add s!"f choice {is.length}{String.join (is.map fun i => " " ++ toString i)}"
  | .char_ => w.add "f char"
  | .strings => w.add "f strings"
  | .group items =>
    let (is, w) := items.foldl (fun (acc, w) it => let (i, w) := putFmt w it; (acc ++ [i], w)) ([], w)
    w.add s!"f group {is.length}{String.join (is.map fun i => " " ++ toString i)}"
  | .include f => let (i, w) := putFmtCore w f; w.add s!"f incl {i}"
  | .sep => w.add "f sep"
  | .col => w.add "f col"

/-- Serialise a format text (a list of items) as one entry. -/
def putFmtList (w : Writer) (items : List CoreFmt) : Nat × Writer :=
  let (is, w) := items.foldl (fun (acc, w) it => let (i, w) := putFmt w it; (acc ++ [i], w)) ([], w)
  w.add s!"k {is.length}{String.join (is.map fun i => " " ++ toString i)}"

/-- The blob handed to the runtime. -/
def Writer.render (w : Writer) : String := "\n".intercalate w.lines.toList

-- ## Reading back

structure Reader where
  modes : Array Mode := #[]
  fmts  : Array CoreFmt := #[]
  lists : Array (List CoreFmt) := #[]
  cores : Array Core := #[]
  strs  : Array String := #[]
  /-- The program's mode declarations, `MODE YEAR = INT`, so that the run time can resolve
      a mode indicant exactly as the evaluator does. Not index-aligned with the tables. -/
  decls : Array (String × Mode) := #[]
  deriving Inhabited

private def field (fs : Array String) (i : Nat) : Nat := (fs[i]?.getD "0").toNat!
private def fieldI (fs : Array String) (i : Nat) : Int :=
  let s := fs[i]?.getD "0"
  if s.startsWith "-" then -((String.ofList (s.toList.drop 1)).toNat! : Int) else (s.toNat! : Int)

/-- Rebuild the tables from the blob. Every entry only refers to earlier entries,
    so one pass suffices. -/
def parse (blob : String) : Reader := Id.run do
  let mut r : Reader := {}
  -- slot i of each table is written for every line so that indices stay aligned
  for line in blob.splitOn "\n" do
    let fs := (line.splitOn " ").filter (· ≠ "") |>.toArray
    let kind := fs[0]?.getD ""
    let sub := fs[1]?.getD ""
    let mut m : Mode := .void
    let mut f : CoreFmt := .sep
    let mut l : List CoreFmt := []
    let mut c : Core := .stop
    let mut s : String := ""
    if kind == "s" then
      s := hexDecode (fs[1]?.getD "")
    else if kind == "m" then
      m := match sub with
        | "int" => .int (fieldI fs 2) | "real" => .real (fieldI fs 2)
        | "bool" => .bool | "char" => .char | "void" => .void
        | "bits" => .bits (fieldI fs 2) | "bytes" => .bytes (fieldI fs 2)
        | "compl" => .compl (fieldI fs 2)
        | "ref" => .ref (r.modes[field fs 2]!)
        | "row" => .row (field fs 2) (field fs 3 == 1) (r.modes[field fs 4]!)
        | "proc" =>
          let n := field fs 3
          .proc ((List.range n).map fun k => r.modes[field fs (4 + k)]!) (r.modes[field fs 2]!)
        | "struct" =>
          let n := field fs 2
          .struct ((List.range n).map fun k => (r.strs[field fs (3 + 2*k)]!, r.modes[field fs (4 + 2*k)]!))
        | "union" =>
          let n := field fs 2
          .union ((List.range n).map fun k => r.modes[field fs (3 + k)]!)
        | "named" => .named r.strs[field fs 2]!
        | "format" => .format | "file" => .file | "channel" => .channel | "sema" => .sema
        | "simplout" => .simplout | "simplin" => .simplin | "number" => .number
        | _ => .void
    else if kind == "c" then
      c := match sub with
        | "hole" => .hole (field fs 2) (field fs 3)
        | "int" => .lit (.int (fieldI fs 2))
        | _ => .stop
    else if kind == "f" then
      f := match sub with
        | "lit" => .literal r.strs[field fs 2]!
        | "nl" => .newline | "np" => .newpage | "sp" => .space | "bs" => .backspace
        | "rep" =>
          let d := field fs 3
          .rep (field fs 2) (if d == 0 then none else some r.cores[d - 1]!) r.fmts[field fs 4]!
        | "dig" => .digit (field fs 2 == 1)
        | "sign" => .sign (field fs 2 == 1)
        | "point" => .point | "exp" => .exp
        | "gen" =>
          let n := field fs 2
          .general ((List.range n).map fun k => r.cores[field fs (3 + k)]!)
        | "bool" =>
          if field fs 2 == 1 then .bool_ (some r.strs[field fs 3]!) (some r.strs[field fs 4]!)
          else .bool_ none none
        | "choice" =>
          let n := field fs 2
          .choice ((List.range n).map fun k => r.strs[field fs (3 + k)]!)
        | "char" => .char_ | "strings" => .strings
        | "group" =>
          let n := field fs 2
          .group ((List.range n).map fun k => r.fmts[field fs (3 + k)]!)
        | "incl" => .include r.cores[field fs 2]!
        | "col" => .col
        | _ => .sep
    else if kind == "n" then
      r := { r with decls := r.decls.push (r.strs[field fs 1]!, r.modes[field fs 2]!) }
    else if kind == "k" then
      let n := field fs 1
      l := (List.range n).map fun k => r.fmts[field fs (2 + k)]!
    r := { modes := r.modes.push m, fmts := r.fmts.push f, lists := r.lists.push l,
           cores := r.cores.push c, strs := r.strs.push s }
  return r

end A68.Serial
