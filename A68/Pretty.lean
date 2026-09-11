import A68.Core

/-!
# A68.Pretty — readable rendering of the compiled core representation

`a68lean dump file.a68` prints the elaborated program in this notation. It is
an S-expression-like tree: every coercion inserted by the elaborator is a
visible node (`deref`, `deproc`, `widen`, `row-of`, `unite`, `void`), names
are `cell[depth.slot]` (a value) or `&cell[depth.slot]` (a REF to the cell),
builtin operators carry the operand modes they were resolved to, and blocks
show their frame size and label range.
-/
namespace A68.Pretty

def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

def valueStr : Value → String
  | .undef => "undef"
  | .int n => toString n
  | .real x => toString x
  | .mp x =>
    let (m, e) := MP.toDecParts x x.size
    s!"long {m}e{e}"
  | .bool b => if b then "TRUE" else "FALSE"
  | .char c => s!"'{Char.ofNat c}'"
  | .bits b => s!"bits {b}"
  | .compl a b => s!"compl {a} {b}"
  | .void => "EMPTY"
  | .nil => "NIL"
  | .ref c _ => s!"ref#{c}"
  | .row _ _ es =>
    if es.all (fun e => match e with | .char _ => true | _ => false) then
      "\"" ++ String.ofList (es.toList.map fun e => match e with | .char c => Char.ofNat c | _ => '?') ++ "\""
    else s!"row[{es.size}]"
  | .struct fs => s!"struct[{fs.size}]"
  | .union m _ => s!"union {m}"
  | .proc .. => "proc"
  | .builtin n => s!"builtin {n}"
  | .cproc fn np _ => s!"cproc#{fn}/{np}"
  | .fmt .. => "format"
  | .file id => s!"file {id}"

mutual
partial def core (n : Nat) : Core → String
  | .lit v => valueStr v
  | .loadCell d s => s!"cell[{d}.{s}]"
  | .refCell d s => s!"&cell[{d}.{s}]"
  | .deref e => s!"(deref {core n e})"
  | .deproc e => s!"(deproc {core n e})"
  | .widen a b e => s!"(widen {a}→{b} {core n e})"
  | .rowOf e => s!"(row-of {core n e})"
  | .unite m e => s!"(unite {m} {core n e})"
  | .voiding e => s!"(void {core n e})"
  | .assign d s flex => s!"(assign{if flex then "-flex" else ""} {core n d} {core n s})"
  | .identRel l r isnt => s!"({if isnt then "isnt" else "is"} {core n l} {core n r})"
  | .dyop op m1 m2 l r => s!"({op} :{m1},{m2} {core n l} {core n r})"
  | .monop op m e => s!"({op} :{m} {core n e})"
  | .call f args => s!"(call {core n f}{String.join (args.map fun a => " " ++ core n a)})"
  | .routine np fs body => s!"(routine params={np} frame={fs}\n{indent (n+1)}{core (n+1) body})"
  | .slice arr idx viaRef =>
    let ix := idx.map fun
      | .index e => core n e
      | .trim l u a => s!"[{(l.map (core n)).getD ""}:{(u.map (core n)).getD ""}{match a with | some x => " AT " ++ core n x | none => ""}]"
    s!"(slice{if viaRef then "-ref" else ""} {core n arr} {" ".intercalate ix})"
  | .select i e viaRef => s!"(select{if viaRef then "-ref" else ""} #{i} {core n e})"
  | .newRow bs init flex =>
    let bounds := bs.map fun (l, u) => s!"{core n l}:{core n u}"
    s!"(new-row{if flex then "-flex" else ""} [{", ".intercalate bounds}] {core n init})"
  | .gen init => s!"(generator {core n init})"
  | .block size stmts lb nl =>
    let body := stmts.toList.map fun st => indent (n+1) ++ stmt (n+1) st
    s!"(block frame={size}{if nl > 0 then s!" labels={lb}..{lb+nl-1}" else ""}\n{"\n".intercalate body})"
  | .collateral es isStruct dims =>
    s!"({if isStruct then "struct-display" else s!"row-display dims={dims}"}{String.join (es.map fun e => " " ++ core n e)})"
  | .cond c t e => s!"(if {core n c}\n{indent (n+1)}then {core (n+1) t}\n{indent (n+1)}else {core (n+1) e})"
  | .caseInt sel alts out =>
    s!"(case {core n sel}{String.join (alts.map fun a => "\n" ++ indent (n+1) ++ core (n+1) a)}\n{indent (n+1)}out {core (n+1) out})"
  | .caseConf sel alts out =>
    let as := alts.map fun (m, slot, c) => "\n" ++ indent (n+1) ++ s!"({m}{match slot with | some s => s!" → cell[0.{s}]" | none => ""}) {core (n+1) c}"
    s!"(conformity {core n sel}{String.join as}\n{indent (n+1)}out {core (n+1) out})"
  | .loop slot f b t w body =>
    s!"(loop{match slot with | some s => s!" var=cell[0.{s}]" | none => ""} from={core n f} by={core n b}{match t with | some tc => " to=" ++ core n tc | none => ""}{match w with | some wc => "\n" ++ indent (n+1) ++ "while " ++ core (n+1) wc | none => ""}\n{indent (n+1)}do {core (n+1) body})"
  | .goto l => s!"(goto L{l})"
  | .skip m => s!"(skip :{m})"
  | .andThen l r => s!"(andf {core n l} {core n r})"
  | .orElse l r => s!"(orel {core n l} {core n r})"
  | .fmt items => s!"(format {" ".intercalate (items.map (fmtItem n))})"
  | .stop => "(stop)"
  | .seq a b => s!"(seq {core n a} {core n b})"
  | .at _ e => core n e
  | .hole fn idx => s!"(hole {fn}.{idx})"

partial def stmt (n : Nat) : CoreStmt → String
  | .decl slot _ init => s!"cell[0.{slot}] := {core n init}"
  | .unit e => core n e
  | .label id => s!"L{id}:"
  | .exit => "EXIT"

partial def fmtItem (n : Nat) : CoreFmt → String
  | .literal s => s!"\"{s}\""
  | .newline => "l" | .newpage => "p" | .space => "x" | .backspace => "q"
  | .rep k dyn it => s!"{match dyn with | some e => "n(" ++ core n e ++ ")" | none => toString k}{fmtItem n it}"
  | .digit z => if z then "z" else "d"
  | .sign p => if p then "+" else "-"
  | .point => "." | .exp => "e"
  | .general args => if args.isEmpty then "g" else s!"g({", ".intercalate (args.map (core n))})"
  | .bool_ (some a) (some b) => s!"b(\"{a}\",\"{b}\")"
  | .bool_ _ _ => "b"
  | .choice alts => s!"c({", ".intercalate (alts.map fun a => "\"" ++ a ++ "\"")})"
  | .char_ => "a" | .strings => "s"
  | .group items => s!"({" ".intercalate (items.map (fmtItem n))})"
  | .include f => s!"f({core n f})"
  | .sep => "," | .col => "k"
  | .radix => "r" | .hmark => "h" | .cpat s => "%" ++ s | .cwidth => "<w>" | .cafter => "<a>"
end

/-- Render a whole program. -/
def program (c : Core) : String := core 0 c

end A68.Pretty
