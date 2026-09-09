import A68.Syntax
/-!
# A68.Lexer — tokeniser for upper-stropped Algol 68 (a68g dialect)

Conventions implemented (matching Algol 68 Genie):
* bold words are runs of upper-case letters (`INT`, `PROC`, `MODE`, user modes/ops);
* tags (identifiers) are lower-case and may contain insignificant spaces (`new line`);
* digits inside numerals may be separated by spaces (`10 000`);
* comments: `# … #`, `CO … CO`, `COMMENT … COMMENT`; pragmats `PR … PR`, `PRAGMAT … PRAGMAT`;
* strings use `""` for an embedded quote; formats are `$ … $` and are kept raw.

All functions are total: the main loop recurses on the remaining input length.
-/

namespace A68

inductive Tok where
  | bold (s : String)
  | ident (s : String)
  | int (digits : String)
  | real (text : String)
  | bits (radix : Nat) (digits : String)
  | str (s : String)
  | sym (s : String)
  | format (raw : String)
  | pragmat (text : String)
  | eof
  deriving Repr, BEq, Inhabited

structure Token where
  tok : Tok
  pos : Pos
  deriving Repr, Inhabited

namespace Lexer

structure St where
  src   : Array Char
  line  : Nat := 1
  col   : Nat := 1

def isUpper (c : Char) : Bool := 'A' ≤ c ∧ c ≤ 'Z'
def isLower (c : Char) : Bool := 'a' ≤ c ∧ c ≤ 'z'
def isDigit (c : Char) : Bool := '0' ≤ c ∧ c ≤ '9'
def isTagCont (c : Char) : Bool := isLower c || isDigit c || c == '_'
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

def isMonad (c : Char) : Bool := "%^&+-~!?".contains c
def isNomad (c : Char) : Bool := "></=*".contains c

/-- Unicode operator aliases. -/
def uniSym (c : Char) : Option String :=
  match c with
  | '≤' => some "<=" | '≥' => some ">=" | '≠' => some "/=" | '×' => some "*"
  | '÷' => some "%"  | '↑' => some "**" | '¬' => some "NOT" | '∧' => some "AND"
  | '∨' => some "OR" | '→' => some "OF" | _ => none


def charAt (a : Array Char) (i : Nat) : Char := if h : i < a.size then a[i] else '\x00'

/-- Advance a position over character `c`. -/
def advance (p : Pos) (c : Char) : Pos :=
  if c == '\n' then { line := p.line + 1, col := 1 } else { p with col := p.col + 1 }

/-- Position after consuming `src[i..j)`. -/
def advanceRange (src : Array Char) (p : Pos) (i j : Nat) : Pos := Id.run do
  let mut q := p
  for k in [i:j] do
    q := advance q (charAt src k)
  return q

/-- Scan while predicate holds, returning the end index (≥ i). -/
def scanWhile (src : Array Char) (pred : Char → Bool) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < src.size && pred (charAt src j) do
    j := j + 1
  return j

/-- Find next occurrence of `c` at or after `i`; returns `src.size` if none. -/
def findChar (src : Array Char) (c : Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < src.size && charAt src j != c do
    j := j + 1
  return j

/-- Skip a bold-word delimited comment/pragmat: find the next occurrence of bold word `w`. -/
def findBold (src : Array Char) (w : String) (i : Nat) : Nat := Id.run do
  let mut j := i
  let ws := w.toList.toArray
  while j < src.size do
    -- a bold word starts here if previous char is not upper
    if isUpper (charAt src j) && !(isUpper (charAt src (j - 1)) && j > 0) then
      let e := scanWhile src isUpper j
      if (src.extract j e) == ws then
        return e
      j := e
    else
      j := j + 1
  return src.size

/-- Read a tag: lower-case letters/digits/underscores with insignificant spaces. -/
def scanTag (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  let mut out : String := ""
  while j < src.size do
    let c := charAt src j
    if isTagCont c then
      out := out.push c; j := j + 1
    else if c == ' ' then
      -- spaces are allowed inside a tag if followed by a tag character
      let k := scanWhile src (· == ' ') j
      if k < src.size && isTagCont (charAt src k) then
        j := k
      else
        break
    else
      break
  return (out, j)

/-- Read a run of digits with optional embedded spaces. -/
def scanDigits (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  let mut out : String := ""
  while j < src.size do
    let c := charAt src j
    if isDigit c then
      out := out.push c; j := j + 1
    else if c == ' ' then
      let k := scanWhile src (· == ' ') j
      if k < src.size && isDigit (charAt src k) then j := k else break
    else break
  return (out, j)

/-- Numeric denotation starting at `i` (a digit, or '.' followed by a digit). -/
def scanNumber (src : Array Char) (i : Nat) : Tok × Nat := Id.run do
  let (intPart, j0) := scanDigits src i
  let mut j := j0
  -- radix denotation: 2r1010, 16rff
  if intPart != "" && charAt src j == 'r' && (isDigit (charAt src (j+1)) || ('a' ≤ charAt src (j+1) && charAt src (j+1) ≤ 'f')) then
    let e := scanWhile src (fun c => isDigit c || ('a' ≤ c && c ≤ 'f')) (j+1)
    let digits := String.ofList (src.extract (j+1) e).toList
    return (.bits intPart.toNat! digits, e)
  let mut isReal := false
  let mut text := intPart
  if charAt src j == '.' && isDigit (charAt src (j+1)) then
    let (frac, j2) := scanDigits src (j+1)
    text := text ++ "." ++ frac; j := j2; isReal := true
  -- exponent
  let ec := charAt src j
  if (ec == 'e' || ec == 'E' || ec == '\\') then
    let mut k := j + 1
    let mut sign := ""
    if charAt src k == '+' || charAt src k == '-' then
      sign := String.singleton (charAt src k); k := k + 1
    if isDigit (charAt src k) then
      let (ex, k2) := scanDigits src k
      text := text ++ "e" ++ sign ++ ex; j := k2; isReal := true
  if isReal then return (.real text, j) else return (.int text, j)

/-- String denotation body starting after the opening quote at `i`. -/
def scanString (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  let mut out := ""
  while j < src.size do
    let c := charAt src j
    if c == '"' then
      if charAt src (j+1) == '"' then
        out := out.push '"'; j := j + 2
      else
        return (out, j + 1)
    else if c == '\\' && charAt src (j+1) == '\n' then
      j := j + 2   -- a68g: backslash-newline continues the string
    else
      out := out.push c; j := j + 1
  return (out, j)

/-- Format text body starting after the opening `$` at `i`; strings inside may contain `$`. -/
def scanFormat (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  let mut out := ""
  while j < src.size do
    let c := charAt src j
    if c == '$' then return (out, j + 1)
    if c == '"' then
      out := out.push c; j := j + 1
      while j < src.size && charAt src j != '"' do
        out := out.push (charAt src j); j := j + 1
      if j < src.size then out := out.push '"'; j := j + 1
    else
      out := out.push c; j := j + 1
  return (out, j)

/-- Operator / punctuation symbol scanning, following the Algol 68 Genie scanner:
    `:` forms `: := :=: :/=: :: ::=`; `|` forms `| |:`; an operator is a monad or nomad,
    optionally followed by one nomad, then optionally `= [: [=]]` or `: [=]`. -/
def scanSymbol (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let c := charAt src i
  let at_ (k : Nat) := charAt src k
  if c == ':' then
    if at_ (i+1) == '=' then
      if at_ (i+2) == ':' then return (":=:", i+3) else return (":=", i+2)
    else if at_ (i+1) == '/' && at_ (i+2) == '=' then
      if at_ (i+3) == ':' then return (":/=:", i+4) else return (":/=", i+3)
    else if at_ (i+1) == ':' then
      if at_ (i+2) == '=' then return ("::=", i+3) else return ("::", i+2)
    else return (":", i+1)
  else if c == '|' then
    if at_ (i+1) == ':' then return ("|:", i+2) else return ("|", i+1)
  else if c == '=' || isMonad c || isNomad c then
    let mut j := i + 1
    let mut sym := String.singleton c
    if isNomad (at_ j) then
      sym := sym.push (at_ j); j := j + 1
    if at_ j == '=' then
      sym := sym.push '='; j := j + 1
      if at_ j == ':' then
        sym := sym.push ':'; j := j + 1
        if sym.length < 4 && at_ j == '=' then
          sym := sym.push '='; j := j + 1
    else if at_ j == ':' then
      sym := sym.push ':'; j := j + 1
      if at_ j == '=' then
        sym := sym.push '='; j := j + 1
    return (sym, j)
  else
    return (String.singleton c, i + 1)

/-- Produce one token starting at `i` (assumed not whitespace). Returns `none` for skipped
    text (comments/pragmats) with the index after it. -/
def next (src : Array Char) (i : Nat) : Option Tok × Nat :=
  let c := charAt src i
  if c == '#' then
    (none, findChar src '#' (i+1) + 1)
  else if c == '¢' then
    (none, findChar src '¢' (i+1) + 1)
  else if isUpper c then
    let e := scanWhile src (fun c => isUpper c || c == '_') i
    let w := String.ofList (src.extract i e).toList
    if w == "CO" || w == "COMMENT" || w == "PR" || w == "PRAGMAT" then
      let e' := findBold src w e
      if w == "PR" || w == "PRAGMAT" then
        -- keep pragmat text as a token so that `PR precision N PR` can be honoured
        (some (.pragmat (String.ofList (src.extract e (e' - w.length)).toList)), e')
      else (none, e')
    else (some (.bold w), e)
  else if isLower c then
    let (t, e) := scanTag src i
    (some (.ident t), e)
  else if isDigit c || (c == '.' && isDigit (charAt src (i+1))) then
    let (t, e) := scanNumber src i
    (some t, e)
  else if c == '"' then
    let (s, e) := scanString src (i+1)
    (some (.str s), e)
  else if c == '$' then
    let (s, e) := scanFormat src (i+1)
    (some (.format s), e)
  else match uniSym c with
  | some s => if s.all isUpper then (some (.bold s), i+1) else (some (.sym s), i+1)
  | none =>
    let (sym, j) := scanSymbol src i
    (some (.sym sym), j)

/-- Main loop. Total: recursion measure is the remaining input. -/
def loop (src : Array Char) (i : Nat) (pos : Pos) (acc : Array Token) : Array Token :=
  if h : i < src.size then
    let c := src[i]
    if isSpace c then
      loop src (i+1) (advance pos c) acc
    else
      let (t, j) := next src i
      let acc := match t with
        | some t => acc.push { tok := t, pos := pos }
        | none => acc
      let pos' := advanceRange src pos i j
      if hj : i < j then
        loop src j pos' acc
      else
        acc.push { tok := .sym (String.singleton c), pos := pos }  -- cannot happen; keeps totality
  else acc.push { tok := .eof, pos := pos }
termination_by src.size - i

end Lexer

/-- Tokenise a whole program. -/
def lex (s : String) : Array Token :=
  Lexer.loop s.toList.toArray 0 { line := 1, col := 1 } #[]

end A68
