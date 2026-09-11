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

/-- White space that a68g's scanner skips inside tags and numerals (`next_char` with
    `allow_typo`): blanks, tabs, line ends, vertical tabs and form feeds. -/
def isTypoSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

/-- Index of the first character at or after `i` that is not typographical white space. -/
def skipTypo (src : Array Char) (i : Nat) : Nat := scanWhile src isTypoSpace i

/-- Read a tag: lower-case letters/digits/underscores with insignificant white space
    (a68g joins a tag across blanks and line ends: `new line`, or a tag split over lines). -/
def scanTag (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  let mut out : String := ""
  while j < src.size do
    let c := charAt src j
    if isTagCont c then
      out := out.push c; j := j + 1
    else if isTypoSpace c then
      -- white space is allowed inside a tag if a tag character follows
      let k := skipTypo src j
      if k < src.size && isTagCont (charAt src k) then
        j := k
      else
        break
    else
      break
  return (out, j)

/-- Read a run of digits with optional embedded white space. -/
def scanDigits (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  let mut out : String := ""
  while j < src.size do
    let c := charAt src j
    if isDigit c then
      out := out.push c; j := j + 1
    else if isTypoSpace c then
      let k := skipTypo src j
      if k < src.size && isDigit (charAt src k) then j := k else break
    else break
  return (out, j)

/-- Numeric denotation starting at `i` (a digit, or '.' followed by a digit). -/
def scanNumber (src : Array Char) (i : Nat) : Tok × Nat := Id.run do
  -- a68g's scanner reads the characters after a digit with `next_char (…, allow_typo)`, so
  -- white space may separate the digits, the point, the exponent and the radix digits:
  -- `3 . 14`, `1 e 3`, `2r 0 1 1`, `16r 44 ff` are all denotations
  let (intPart, j0) := scanDigits src i
  let mut j := j0
  let isHex (c : Char) := isDigit c || ('a' ≤ c && c ≤ 'f')
  let isExpChar (c : Char) := c == 'e' || c == 'E' || c == '\\'
  -- the first character after the digits, skipping white space
  let k0 := skipTypo src j
  -- radix denotation: 2r1010, 16rff
  if intPart != "" && charAt src k0 == 'r' && isHex (charAt src (skipTypo src (k0+1))) then
    let mut e := skipTypo src (k0+1)
    let mut digits := ""
    while e < src.size && isHex (charAt src e) do
      digits := digits.push (charAt src e)
      let e' := skipTypo src (e+1)
      e := if e' < src.size && isHex (charAt src e') then e' else e + 1
    return (.bits intPart.toNat! digits, e)
  let mut isReal := false
  let mut text := intPart
  -- is there an exponent at `k` (an exponent character followed by a sign or a digit)?
  let expAt (k : Nat) : Bool :=
    isExpChar (charAt src k) && "+-0123456789".contains (charAt src (skipTypo src (k+1)))
  if charAt src k0 == '.' then
    let k1 := skipTypo src (k0+1)
    if isDigit (charAt src k1) then
      let (frac, j2) := scanDigits src k1
      text := text ++ "." ++ frac; j := j2; isReal := true
    else if expAt k1 then
      -- `1.e5`: a point followed directly by an exponent
      text := text ++ ".0"; j := k1; isReal := true
  -- exponent
  let ke := skipTypo src j
  if expAt ke then
    let mut k := skipTypo src (ke + 1)
    let mut sign := ""
    if charAt src k == '+' || charAt src k == '-' then
      sign := String.singleton (charAt src k); k := skipTypo src (k + 1)
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

/-- Format text body starting after the opening `$` at `i`; returns the raw text (without the
    outer delimiters) and the index after the closing `$`.

    a68g's tokeniser is recursive (`tokenise_source`): after an `n`, `g`, `h` or `f` item an
    opening parenthesis switches to ordinary program text until the matching closing
    parenthesis, and in program text a `$` opens a nested format text.  So
    `$f(c | $"a"$ | $"b"$)$` is one format whose inclusion holds two formats.  The same
    nesting is tracked here with an explicit stack: `0` is format text, `d ≥ 1` is program
    text at parenthesis depth `d`. -/
def scanFormat (src : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut j := i
  let mut out := ""
  let mut stack : Array Nat := #[0]
  let mut lastItem := false     -- the previous format token was `n`, `g`, `h` or `f`
  while j < src.size do
    let c := charAt src j
    let top := stack.back?.getD 0
    if c == '"' then
      -- a string (format literal or string denotation); `""` is two adjacent strings/an
      -- embedded quote, which copying character by character preserves
      out := out.push c; j := j + 1
      while j < src.size && charAt src j != '"' do
        out := out.push (charAt src j); j := j + 1
      if j < src.size then out := out.push '"'; j := j + 1
      lastItem := false
    else if top == 0 then
      if c == '$' then
        stack := stack.pop
        if stack.isEmpty then return (out, j + 1)
        out := out.push c; j := j + 1
      else if c == '(' && lastItem then
        stack := stack.push 1
        out := out.push c; j := j + 1
        lastItem := false
      else
        if !isTypoSpace c then lastItem := c == 'n' || c == 'g' || c == 'h' || c == 'f'
        out := out.push c; j := j + 1
    else
      if c == '$' then
        stack := stack.push 0
        lastItem := false
      else if c == '#' then
        -- a comment in program text: copy it whole
        out := out.push c; j := j + 1
        while j < src.size && charAt src j != '#' do
          out := out.push (charAt src j); j := j + 1
        if j >= src.size then return (out, j)
      else if c == '(' || c == '[' then
        stack := stack.set! (stack.size - 1) (top + 1)
      else if c == ')' || c == ']' then
        if top == 1 then stack := stack.pop
        else stack := stack.set! (stack.size - 1) (top - 1)
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

/-- Refinements, an a68g extension (`parser-refinement.c`).  A program may be followed by
    refinements: after the point that ends it come definitions `name : text .`, and each
    identifier `name` in the program, or in a refinement applied in it, is replaced by the
    tokens of `text`.  Every refinement must be applied exactly once.

    The program ends at the first point followed by an identifier and a colon; a point
    followed by the end of the text (`END.`) means there are no refinements.  The result is
    the substituted program tokens followed by `eof`; an error carries a message and the
    position a68g reports it at. -/
def applyRefinements (toks : Array Token) : Except (String × Pos) (Array Token) := Id.run do
  let n := toks.size
  let tokAt (k : Nat) : Tok := (toks[k]?.map (·.tok)).getD .eof
  let isIdent (t : Tok) : Bool := match t with | .ident _ => true | _ => false
  -- find the point that ends the program
  let mut p := 0
  let mut found := false
  while p < n do
    if tokAt p == .sym "." then
      if tokAt (p+1) == .eof then break
      if isIdent (tokAt (p+1)) && tokAt (p+2) == .sym ":" then
        found := true
        break
    p := p + 1
  if !found then return .ok toks
  let mainEnd := p
  -- the definitions: name, position, and the token range of the text
  let mut defs : Array (String × Pos × Nat × Nat) := #[]
  let mut q := p + 1
  while q < n && isIdent (tokAt q) && tokAt (q+1) == .sym ":" do
    let name := match tokAt q with | .ident s => s | _ => ""
    let pos := toks[q]!.pos
    let b := q + 2
    let mut e := b
    while e < n && tokAt e != .sym "." && tokAt e != .eof do
      e := e + 1
    if tokAt e != .sym "." then return .error ("invalid refinement", pos)
    if b == e then return .error ("refinement is empty", pos)
    if defs.any (·.1 == name) then return .error ("refinement already defined", pos)
    defs := defs.push (name, pos, b, e)
    q := e + 1
  if tokAt q != .eof then
    return .error ("invalid refinement", (toks[q]?.map (·.pos)).getD {})
  -- substitute, innermost first; a refinement applied a second time is an error, so the
  -- expansion is bounded by the number of refinements
  let mut out : Array Token := #[]
  let mut applied : Array Bool := Array.replicate defs.size false
  let mut stack : List (Nat × Nat) := [(0, mainEnd)]
  while !stack.isEmpty do
    match stack with
    | [] => pure ()
    | (i, e) :: rest =>
      if i >= e then
        stack := rest
      else
        stack := (i + 1, e) :: rest
        let t := toks[i]!
        match t.tok with
        | .ident nm =>
          match defs.findIdx? (·.1 == nm) with
          | some k =>
            let (_, pos, b, e') := defs[k]!
            if applied[k]! then return .error ("refinement is applied more than once", pos)
            applied := applied.set! k true
            stack := (b, e') :: stack
          | none => out := out.push t
        | _ => out := out.push t
  for k in [0:defs.size] do
    if !applied[k]! then return .error ("refinement is not applied", defs[k]!.2.1)
  let endPos := (toks.back?.map (·.pos)).getD {}
  return .ok (out.push { tok := .eof, pos := endPos })

end A68
