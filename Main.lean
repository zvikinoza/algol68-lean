import A68.Parser
import A68.Numfmt
import A68.Elab
import A68.Interp

open A68

def pf (x : String) : Float :=
  if x.startsWith "-" then -(Numfmt.parseFloat (String.ofList (x.toList.drop 1))) else Numfmt.parseFloat x

def fmtLine (line : String) : String :=
  match line.splitOn " " |>.filter (· ≠ "") with
  | ["w", n, w] => Numfmt.whole n.toInt! w.toInt!
  | ["fr", x, w, a] => Numfmt.fixedReal (pf x) w.toInt! a.toInt!
  | ["fi", n, w, a] => Numfmt.fixedInt n.toInt! w.toInt! a.toInt!
  | ["fl", x, w, a, e] => Numfmt.floatReal (pf x) w.toInt! a.toInt! e.toInt!
  | ["fli", n, w, a, e] => Numfmt.floatInt n.toInt! w.toInt! a.toInt! e.toInt!
  | ["pi", n] => Numfmt.printInt n.toInt! 0
  | ["pr", x] => Numfmt.printReal (pf x) 0
  | ["wr", x, w] => Numfmt.wholeReal (pf x) w.toInt!
  | _ => "?"

/-- Read a source file as bytes; each byte becomes one character (a68g treats CHAR as a byte). -/
def readSource (file : String) : IO String := do
  let bytes ← IO.FS.readBinFile file
  return String.ofList (bytes.toList.map fun b => Char.ofNat b.toNat)

/-- Parse and elaborate; report errors in a68g-like style on stderr. -/
def compile (file : String) : IO (Option (Core × Mode.Table × Nat)) := do
  let src ← readSource file
  let ll := match A68.precisionOf (A68.lex src) with
    | some n => Numfmt.llDigitsOfPrecision n
    | none => Numfmt.defaultLLDigits
  let fileName := file
  match A68.parse src with
  | .error e =>
    IO.eprintln s!"a68lean: syntax error: {file}:{e.pos.line}:{e.pos.col}: {e.msg}."
    return none
  | .ok ast =>
    match Elab.elabProgramWithModes ast ll fileName with
    | .error e =>
      IO.eprintln s!"a68lean: error: {file}:{e.pos.line}:{e.pos.col}: {e.msg}."
      return none
    | .ok (core, modes) => return some (core, modes, ll)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["parse", file] =>
    let src ← readSource file
    match A68.parse src with
    | .ok _ => IO.println "OK"; return 0
    | .error e => IO.println s!"{file}:{e.pos.line}:{e.pos.col}: {e.msg}"; return 1
  | ["check", file] =>
    match (← compile file) with
    | some _ => IO.println "OK"; return 0
    | none => return 1
  | "run" :: file :: rest =>
    match (← compile file) with
    | some (core, modes, ll) =>
      let toks := A68.lex (← readSource file)
      for e in A68.echoesOf toks do IO.println e
      Interp.run core modes ("a68g" :: file :: rest).toArray ll (A68.isRegression toks)
    | none => return 1
  | ["dump", file] =>
    match (← compile file) with
    | some (core, _, _) => IO.println (repr core); return 0
    | none => return 1
  | ["lex", file] =>
    let src ← readSource file
    for t in A68.lex src do
      IO.println s!"{t.pos.line}:{t.pos.col} {repr t.tok}"
    return 0
  | ["fmttest", file] =>
    let src ← IO.FS.readFile file
    for line in src.splitOn "\n" do
      if line ≠ "" then IO.println (fmtLine line)
    return 0
  | file :: rest =>
    match (← compile file) with
    | some (core, modes, ll) =>
      let toks := A68.lex (← readSource file)
      for e in A68.echoesOf toks do IO.println e
      Interp.run core modes ("a68g" :: file :: rest).toArray ll (A68.isRegression toks)
    | none => return 1
  | _ => IO.println "usage: a68lean [run|check|parse|lex] file.a68"; return 2
