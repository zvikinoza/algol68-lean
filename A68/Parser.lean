import A68.Syntax
import A68.Lexer
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# A68.Parser — recursive-descent parser for Algol 68

Algol 68 cannot be parsed without knowing which bold words are mode indicants
and which are operators (and their priorities), so `prescan` walks the token
stream first, collecting `MODE`, `OP` and `PRIO` declarations.  Formulas are
parsed by precedence climbing (all dyadic operators are left associative;
monadic operators bind tightest).  Routine texts, conformity alternatives and
declarations are recognised by speculative parsing with backtracking.
-/
namespace A68

structure PError where
  msg : String
  pos : Pos
  deriving Repr, Inhabited

structure PState where
  toks   : Array Token
  i      : Nat := 0
  modes  : Std.HashSet String := {}          -- user mode indicants
  prios  : Std.HashMap String Nat := {}      -- dyadic operator priorities (std + user)
  monops : Std.HashSet String := {}          -- bold monadic operators (std + user)

abbrev P := StateT PState (Except PError)

instance : Inhabited (P α) := ⟨fun _ => .error default⟩

namespace Parser

def stdPrios : List (String × Nat) :=
  [("+:=",1),("-:=",1),("*:=",1),("/:=",1),("%:=",1),("%*:=",1),("+=:",1),
   ("PLUSAB",1),("MINUSAB",1),("TIMESAB",1),("DIVAB",1),("OVERAB",1),("MODAB",1),("PLUSTO",1),
   ("ANDAB",1),("ORAB",1),
   ("OR",2),("OREL",2),("ORF",2),("AND",3),("&",3),("XOR",3),("ANDF",3),("ANDTH",3),("THEF",3),
   ("=",4),("/=",4),("~=",4),("EQ",4),("NE",4),
   ("<",5),("<=",5),(">",5),(">=",5),("LT",5),("LE",5),("GT",5),("GE",5),
   ("+",6),("-",6),
   ("*",7),("/",7),("%",7),("OVER",7),("%*",7),("MOD",7),("ELEM",7),
   ("**",8),("^",8),("UP",8),("DOWN",8),("SHL",8),("SHR",8),("LWB",8),("UPB",8),
   ("I",9),("+*",9)]

def stdMonops : List String :=
  ["ABS","SIGN","ODD","ENTIER","ROUND","REPR","BIN","NOT","LENG","SHORTEN","RE","IM","CONJ",
   "ARG","UPB","LWB","ELEMS","LEVEL","UP","DOWN"]

def keywords : List String :=
  ["BEGIN","END","IF","THEN","ELIF","ELSE","FI","CASE","IN","OUSE","OUT","ESAC","FOR","FROM",
   "BY","TO","WHILE","DO","OD","PROC","OP","PRIO","MODE","REF","STRUCT","UNION","FLEX","HEAP",
   "LOC","LONG","SHORT","INT","REAL","BOOL","CHAR","STRING","BITS","BYTES","VOID","COMPL",
   "FORMAT","FILE","CHANNEL","SEMA","SKIP","NIL","EMPTY","TRUE","FALSE","GOTO","GO","IS","ISNT","COMPLEX",
   "AT","OF","EXIT","PAR","CO","COMMENT","PR","PRAGMAT","NEW","UNTIL"]

def baseModes : List (String × ModeSyn) :=
  [("INT",.int),("REAL",.real),("BOOL",.bool),("CHAR",.char),("STRING",.string),("BITS",.bits),
   ("BYTES",.bytes),("VOID",.void),("COMPL",.compl),("COMPLEX",.compl),("FORMAT",.format),("FILE",.file),
   ("CHANNEL",.channel),("SEMA",.sema)]

/-- Mode indicants declared by a68g's standard environ (`a68g-environ.h`):
    `MODE ZAHL = LONG INT, DOUBLE = LONG REAL, QUAD = LONG LONG REAL`.  Unlike the base
    modes they are not keywords, so a program may declare them itself. -/
def environModes : List (String × ModeSyn) :=
  [("ZAHL", .long 1 .int), ("DOUBLE", .long 1 .real), ("QUAD", .long 1 (.long 1 .real))]

/-- Is a symbol token an operator symbol (made of a68g's monad and nomad characters, with
    the `=`/`:` tails of assigning operators), rather than punctuation? -/
def isOperatorSymbol (w : String) : Bool :=
  w != "" && w != ":" && w != ":=" && w.toList.all fun (c : Char) => "%^&+-~!?></=*:".toList.contains c

/-- The operator a defining occurrence names when a68g's scanner has glued the `=` of the
    declaration onto the operator symbol (`OP!=(INT c)CHAR: …` is `OP ! = …`). -/
def splitDefiningOp (w : String) : Option String :=
  if w.length > 1 && w.endsWith "=" then some (String.ofList w.toList.dropLast) else none

/-- Collect user `MODE`, `OP` and `PRIO` names before parsing. -/
def prescan (toks : Array Token) : Std.HashSet String × Std.HashMap String Nat × Std.HashSet String := Id.run do
  let mut modes : Std.HashSet String := {}
  let mut prios : Std.HashMap String Nat := Std.HashMap.ofList stdPrios
  let mut monops : Std.HashSet String := Std.HashSet.ofList stdMonops
  let mut kind : Option (String × Nat) := none   -- ("MODE"/"OP"/"PRIO", depth)
  let mut depth := 0
  let n := toks.size
  for k in [0:n] do
    let t := toks[k]!.tok
    let prev := if k > 0 then toks[k-1]!.tok else .eof
    let nxt := if k+1 < n then toks[k+1]!.tok else .eof
    let nxt2 := if k+2 < n then toks[k+2]!.tok else .eof
    match t with
    | .sym "(" | .sym "[" => depth := depth + 1
    | .sym ")" | .sym "]" => depth := depth - 1
    | .bold "BEGIN" | .bold "IF" | .bold "CASE" | .bold "DO" => depth := depth + 1
    | .bold "END" | .bold "FI" | .bold "ESAC" | .bold "OD" => depth := depth - 1
    | .sym ";" =>
      match kind with
      | some (_, d) => if depth ≤ d then kind := none
      | none => pure ()
    | .bold "MODE" => kind := some ("MODE", depth)
    | .bold "OP" => kind := some ("OP", depth)
    | .bold "PRIO" => kind := some ("PRIO", depth)
    | _ => pure ()
    match kind, t, nxt with
    | some ("MODE", d), .bold w, .sym "=" => if depth == d then modes := modes.insert w
    -- every declared operator may be applied monadically: a68g identifies the operator by
    -- its operands, so one bold word can be both a dyadic (with a PRIO) and a monadic one
    | some ("OP", d), .bold w, .sym "=" =>
      if depth == d then monops := monops.insert w
    | some ("OP", d), .sym w, .sym "=" =>
      -- only an operator symbol can be defined, not the `)` of `(a) = b` in a routine text
      if depth == d && isOperatorSymbol w then monops := monops.insert w
    | some ("OP", d), .sym w, _ =>
      if depth == d && isOperatorSymbol w && (prev == .bold "OP" || prev == .sym ",") then
        if let some w' := splitDefiningOp w then monops := monops.insert w'
    | some ("PRIO", d), .bold w, .sym "=" =>
      if depth == d then
        match nxt2 with
        | .int s => prios := prios.insert w s.toNat!
        | _ => pure ()
    | some ("PRIO", d), .sym w, .sym "=" =>
      if depth == d then
        match nxt2 with
        | .int s => prios := prios.insert w s.toNat!
        | _ => pure ()
    | _, _, _ => pure ()
  return (modes, prios, monops)

-- ## Basic combinators

def cur : P Token := do
  let s ← get
  return if h : s.i < s.toks.size then s.toks[s.i] else { tok := .eof, pos := {} }

def peek : P Tok := do return (← cur).tok
def peekAt (n : Nat) : P Tok := do
  let s ← get
  return if h : s.i + n < s.toks.size then (s.toks[s.i + n]).tok else .eof
def curPos : P Pos := do return (← cur).pos
def adv : P Unit := modify fun s => { s with i := s.i + 1 }

def fail (msg : String) : P α := do
  let p ← curPos
  throw { msg := msg, pos := p }

/-- Speculative parse: returns `none` (with state restored) on failure. -/
def attempt (p : P α) : P (Option α) := fun s =>
  match p s with
  | .ok (r, s') => .ok (some r, s')
  | .error _ => .ok (none, s)

def isSym (s : String) : P Bool := do return (← peek) == .sym s
def isBold (w : String) : P Bool := do return (← peek) == .bold w
def expectSym (s : String) : P Unit := do
  if (← isSym s) then adv else fail s!"expected '{s}'"
def expectBold (w : String) : P Unit := do
  if (← isBold w) then adv else fail s!"expected {w}"
def acceptSym (s : String) : P Bool := do
  if (← isSym s) then adv; return true else return false
def acceptBold (w : String) : P Bool := do
  if (← isBold w) then adv; return true else return false

def expectIdent : P String := do
  match (← peek) with
  | .ident s => adv; return s
  | _ => fail "expected identifier"

def isIdentTok : Tok → Bool
  | .ident _ => true
  | _ => false

def isModeIndicant (w : String) : P Bool := do
  let s ← get
  return s.modes.contains w || (!(keywords.contains w) && !(s.prios.contains w) && !(s.monops.contains w))

/-- Is `w` one of the environ's mode indicants (`ZAHL`, `DOUBLE`, `QUAD`) in its standard
    meaning, i.e. not declared by the program as a mode or an operator? -/
def isEnvironMode (s : PState) (w : String) : Bool :=
  (environModes.lookup w).isSome && !s.modes.contains w && !s.prios.contains w && !s.monops.contains w

/-- Does a token start a declarer, not looking past it? -/
def tokStartsDeclarer (s : PState) : Tok → Bool
  | .bold w => (baseModes.map (·.1)).contains w
      || ["LONG","SHORT","REF","FLEX","PROC","STRUCT","UNION"].contains w
      || s.modes.contains w || isEnvironMode s w
  | .sym "[" => true
  | _ => false

/-- At an opening parenthesis: is it the bounds bracket of a declarer, as in `(1:n)INT a`
    or `REF ()REAL`?  a68g accepts parentheses for the brackets of a row declarer; they are
    told apart from an enclosed clause by what follows the matching closing parenthesis. -/
def parenBoundsAhead : P Bool := do
  let s ← get
  if s.toks[s.i]?.map (·.tok) != some (.sym "(") then return false
  let mut depth : Nat := 0
  let mut k := s.i
  while k < s.toks.size do
    match s.toks[k]!.tok with
    | .sym "(" | .sym "[" => depth := depth + 1
    | .sym ")" | .sym "]" =>
      depth := depth - 1
      if depth == 0 then
        let nxt := (s.toks[k+1]?.map (·.tok)).getD .eof
        return tokStartsDeclarer s nxt || nxt == .sym "("
    | .sym ";" | .eof => return false
    | _ => pure ()
    k := k + 1
  return false

def isDeclarerStart : P Bool := do
  let s ← get
  let t ← peek
  if tokStartsDeclarer s t then return true
  if t == .sym "(" then parenBoundsAhead else return false

def isDyadicOp : P (Option (String × Nat)) := do
  let s ← get
  match (← peek) with
  | .bold w => return (s.prios.get? w).map (w, ·)
  | .sym w => return (s.prios.get? w).map (w, ·)
  | _ => return none

def isMonadicOp : P (Option String) := do
  let s ← get
  match (← peek) with
  | .bold w => return if s.monops.contains w then some w else none
  | .sym "-" => return some "-"
  | .sym "+" => return some "+"
  | .sym "!" => return some "!"
  | .sym "~" => return some "NOT"
  -- a monadic operator declared by the program (`OP +> = (…)…`, `OP -=: = (REF …)…`)
  | .sym w => return if s.monops.contains w then some w else none
  | _ => return none

-- ## Grammar

mutual

/-- declarer (formal or actual). -/
partial def parseDeclarer : P ModeSyn := do
  match (← peek) with
  | .bold "LONG" => adv; return .long 1 (← parseDeclarer)
  | .bold "SHORT" => adv; return .long (-1) (← parseDeclarer)
  | .bold "REF" => adv; return .ref (← parseDeclarer)
  | .bold "FLEX" =>
    adv
    expectSym "["
    let bs ← parseBounds
    expectSym "]"
    return .row bs true (← parseDeclarer)
  | .sym "[" =>
    adv
    let bs ← parseBounds
    expectSym "]"
    return .row bs false (← parseDeclarer)
  | .sym "(" =>
    -- a68g: parentheses may bracket the bounds of a row declarer, `(1:n)INT`, `REF ()REAL`
    if !(← parenBoundsAhead) then fail "expected declarer"
    adv
    let bs ← if (← isSym ")") then pure [Bound.mk none none] else parseBoundsUntil ")"
    expectSym ")"
    return .row bs false (← parseDeclarer)
  | .bold "PROC" =>
    adv
    if (← acceptSym "(") then
      let mut ps : List ModeSyn := []
      if !(← isSym ")") then
        repeat
          let m ← parseDeclarer
          -- optional parameter names in formal declarers
          let mut count := 1
          if isIdentTok (← peek) then
            adv
            while (← isSym ",") && isIdentTok (← peekAt 1)
                  && ((← peekAt 2) == .sym "," || (← peekAt 2) == .sym ")") do
              adv; adv; count := count + 1
          ps := ps ++ List.replicate count m
          if !(← acceptSym ",") then break
      expectSym ")"
      return .proc ps (← parseDeclarer)
    else
      return .proc [] (← parseDeclarer)
  | .bold "STRUCT" =>
    adv
    expectSym "("
    let mut fs : List (String × ModeSyn) := []
    repeat
      let m ← parseDeclarer
      let n ← expectIdent
      fs := fs ++ [(n, m)]
      while (← isSym ",") && isIdentTok (← peekAt 1)
            && ((← peekAt 2) == .sym "," || (← peekAt 2) == .sym ")") do
        adv
        let n2 ← expectIdent
        fs := fs ++ [(n2, m)]
      if !(← acceptSym ",") then break
    expectSym ")"
    return .struct fs
  | .bold "UNION" =>
    adv
    expectSym "("
    let mut ms : List ModeSyn := []
    repeat
      ms := ms ++ [← parseDeclarer]
      if !(← acceptSym ",") then break
    expectSym ")"
    return .union ms
  | .bold w =>
    match baseModes.lookup w with
    | some m => adv; return m
    | none =>
      let s ← get
      match environModes.lookup w with
      | some m =>
        if isEnvironMode s w then adv; return m
        else if (← isModeIndicant w) then adv; return .ind w
        else fail s!"expected declarer, found {w}"
      | none =>
        if (← isModeIndicant w) then adv; return .ind w
        else fail s!"expected declarer, found {w}"
  | _ => fail "expected declarer"

partial def acceptColon : P Bool := do
  if (← acceptSym ":") then return true
  if (← isSym ".") && (← peekAt 1) == .sym "." then adv; adv; return true
  return false

partial def parseBounds : P (List Bound) := parseBoundsUntil "]"

/-- Bounds of a row declarer up to the closing bracket `close` (not consumed). -/
partial def parseBoundsUntil (close : String) : P (List Bound) := do
  let mut bs : List Bound := []
  repeat
    if (← isSym close) || (← isSym ",") then
      bs := bs ++ [.mk none none]
    else if (← acceptColon) then
      let u ← if (← isSym close) || (← isSym ",") then pure none else some <$> parseUnit
      bs := bs ++ [.mk none u]
    else
      let e ← parseUnit
      if (← acceptColon) then
        let u ← if (← isSym close) || (← isSym ",") then pure none else some <$> parseUnit
        bs := bs ++ [.mk (some e) u]
      else
        bs := bs ++ [.mk none (some e)]
    -- ignore FLEX inside bounds (old style)
    let _ ← acceptBold "FLEX"
    if !(← acceptSym ",") then break
  return bs

/-- Serial clause until one of the stop tokens (not consumed). -/
partial def parseSerial (stops : List Tok) : P Serial := do
  let mut items : List Stmt := []
  let isStop : P Bool := do return stops.contains (← peek)
  if (← isStop) then return .mk []
  let mut labelSeen := false
  repeat
    -- label?
    match (← peek), (← peekAt 1) with
    | .ident l, .sym ":" =>
      let p ← curPos
      adv; adv
      items := items ++ [.label l p]
      labelSeen := true
      if (← isStop) then break
      continue
    | _, _ => pure ()
    let stPos ← curPos
    let st ← parseStatement
    -- a68g (`reduce_serial_clauses`): labels belong to the units after the last declaration
    let isDeclStmt := match st with | .decl _ :: _ => true | _ => false
    if isDeclStmt && labelSeen then
      throw { msg := "declaration cannot follow a labeled unit", pos := stPos }
    items := items ++ st
    -- collateral declarations: `INT a = 1, STRING s := "x"`
    if isDeclStmt then
      while (← isSym ",") do
        adv
        let st2 ← parseStatement
        items := items ++ st2
    if (← acceptSym ";") then
      if (← isStop) then break   -- trailing ';' before END etc. (a68g tolerates)
      continue
    -- EXIT completer: `unit EXIT`
    if (← isBold "EXIT") then
      let p ← curPos
      adv
      items := items ++ [.exit p]
      continue
    break
  return .mk items

/-- A statement: declaration(s) or a unit. May yield several statements. -/
partial def parseStatement : P (List Stmt) := do
  let p ← curPos
  match (← peek) with
  | .bold "MODE" =>
    adv
    let mut ds : List Stmt := []
    repeat
      match (← peek) with
      | .bold n =>
        adv
        expectSym "="
        let m ← parseDeclarer
        ds := ds ++ [.decl (.mode n m p)]
      | _ => fail "expected mode indicant"
      if !(← acceptSym ",") then break
    return ds
  | .bold "PRIO" =>
    adv
    let mut ds : List Stmt := []
    repeat
      let n ← match (← peek) with
        | .bold n => adv; pure n
        | .sym n => adv; pure n
        | _ => fail "expected operator"
      expectSym "="
      match (← peek) with
      | .int s => adv; ds := ds ++ [.decl (.prio n s.toNat! p)]
      | _ => fail "expected priority"
      if !(← acceptSym ",") then break
    return ds
  | .bold "OP" =>
    adv
    -- OP (INT,INT) INT + = ... (with declarer)  or  OP + = routine
    let m ← if (← isSym "(") then
        adv
        let mut ps : List ModeSyn := []
        if !(← isSym ")") then
          repeat
            ps := ps ++ [← parseDeclarer]
            if !(← acceptSym ",") then break
        expectSym ")"
        pure (some (ModeSyn.proc ps (← parseDeclarer)))
      else if (← isDeclarerStart) then some <$> parseDeclarer else pure none
    let mut ds : List Stmt := []
    repeat
      -- a68g's scanner glues the `=` of the declaration onto a symbol (`OP!=(INT c)…` scans
      -- as `!=`); like a68g's `extract_operators`, split it off when no `=` follows
      let glued ← match (← peek), (← peekAt 1) with
        | .sym n, nxt => pure (if nxt != .sym "=" && nxt != .sym ":=" then splitDefiningOp n else none)
        | _, _ => pure none
      let n ← match glued, (← peek) with
        | some n', _ => adv; pure n'
        | none, .bold n => adv; pure n
        | none, .sym n => adv; pure n
        | _, _ => fail "expected operator symbol"
      if glued.isSome || (← acceptSym "=") then
        let body ← parseUnit
        ds := ds ++ [.decl (.op n m body p)]
      else if (← acceptSym ":=") then
        let body ← parseUnit
        ds := ds ++ [.decl (.op n m body p)]
      else fail "expected '=' in operator declaration"
      let isOpNext := (match (← peekAt 1) with | .bold _ => true | .sym _ => true | _ => false)
                      && ((← peekAt 2) == .sym "=" || (← peekAt 2) == .sym ":=")
      if (← isSym ",") && isOpNext then adv else break
    return ds
  | .bold "PROC" =>
    if isIdentTok (← peekAt 1) then
      adv
      let mut ds : List Stmt := []
      let mut items : List (String × Expr) := []
      let mut varItems : List (String × Expr) := []
      let mut isVar := false
      repeat
        let n ← expectIdent
        if (← acceptSym "=") then
          items := items ++ [(n, ← parseUnit)]
        else if (← acceptSym ":=") then
          isVar := true
          varItems := varItems ++ [(n, ← parseUnit)]
        else fail "expected '=' in procedure declaration"
        -- continue the list only if another identifier follows (`PROC a = …, PROC b = …` is
        -- a collateral declaration handled by the serial-clause parser)
        if (← isSym ",") && isIdentTok (← peekAt 1) then adv else break
      if isVar then
        -- PROC f := routine : a variable whose mode is inferred from the routine text
        for (n, e) in varItems do
          ds := ds ++ [.decl (.var (.ind "") false [(n, some e)] p)]
      else
        ds := [.decl (.identity none items p)]
      return ds
    else parseDeclarationOrUnit p
  | .bold "HEAP" | .bold "LOC" | .bold "NEW" =>
    parseDeclarationOrUnit p
  | _ =>
    if (← isDeclarerStart) then parseDeclarationOrUnit p
    else return [.unit (← parseUnit)]

/-- Something starting with a declarer: a declaration if an identifier follows the declarer. -/
partial def parseDeclarationOrUnit (p : Pos) : P (List Stmt) := do
  let hdr ← attempt do
    -- a68g's `NEW` is a synonym of `HEAP`
    let heap ← do pure ((← acceptBold "HEAP") || (← acceptBold "NEW"))
    let _ ← if heap then pure false else acceptBold "LOC"
    let m ← parseDeclarer
    if isIdentTok (← peek) && (← peekAt 1) != .bold "OF" then return (heap, m)
    else fail "not a declaration"
  match hdr with
  | none => return [.unit (← parseUnit)]
  | some (heap, m) =>
    let mut idItems : List (String × Expr) := []
    let mut varItems : List (String × Option Expr) := []
    let mut isVar : Option Bool := none
    repeat
      let n ← expectIdent
      if (← acceptSym "=") then
        if isVar == some true then fail "mixed declaration"
        isVar := some false
        idItems := idItems ++ [(n, ← parseUnit)]
      else if (← acceptSym ":=") then
        if isVar == some false then fail "mixed declaration"
        isVar := some true
        varItems := varItems ++ [(n, some (← parseUnit))]
      else
        if isVar == some false then fail "mixed declaration"
        isVar := some true
        varItems := varItems ++ [(n, none)]
      -- continue only if next is ',' followed by an identifier
      if (← isSym ",") && isIdentTok (← peekAt 1) then adv else break
    if isVar == some false then return [Stmt.decl (.identity (some m) idItems p)]
    else return [Stmt.decl (.var m heap varItems p)]

/-- Routine text header: `( params ) declarer :` or `declarer :`. -/
partial def parseRoutineHeader : P (List (ModeSyn × String) × ModeSyn) := do
  let mut params : List (ModeSyn × String) := []
  if (← isSym "(") then
    adv
    if !(← isSym ")") then
      repeat
        let m ← parseDeclarer
        let n ← expectIdent
        params := params ++ [(m, n)]
        while (← isSym ",") && isIdentTok (← peekAt 1)
              && ((← peekAt 2) == .sym "," || (← peekAt 2) == .sym ")") do
          adv
          let n2 ← expectIdent
          params := params ++ [(m, n2)]
        if !(← acceptSym ",") then break
    expectSym ")"
  let ret ← parseDeclarer
  expectSym ":"
  return (params, ret)

partial def parseUnit : P Expr := do
  let p ← curPos
  -- routine text? (header is speculative; once seen, the body is committed)
  match (← attempt parseRoutineHeader) with
  | some (params, ret) =>
    let body ← parseUnit
    return .routine params ret body p
  | none => pure ()
  let t ← parseTertiary
  match (← peek) with
  | .sym ":=" => adv; return .assign t (← parseUnit) p
  | .sym ":=:" => adv; return .identity t (← parseTertiary) false p
  | .bold "IS" => adv; return .identity t (← parseTertiary) false p
  | .sym ":/=:" => adv; return .identity t (← parseTertiary) true p
  | .bold "ISNT" => adv; return .identity t (← parseTertiary) true p
  | _ => return t

partial def parseTertiary : P Expr := parseFormula 1

partial def parseFormula (minPrio : Nat) : P Expr := do
  let mut lhs ← parseOperand
  repeat
    match (← isDyadicOp) with
    | some (op, prio) =>
      if prio < minPrio then break
      let p ← curPos
      adv
      let rhs ← parseFormula (prio + 1)
      lhs := .dyadic op lhs rhs p
    | none => break
  return lhs

partial def parseOperand : P Expr := do
  if (← isSym "~") then
    -- `~` is SKIP unless an operand follows (then it is NOT)
    let p ← curPos
    let followsOperand := match (← peekAt 1) with
      | .sym s => s == "(" || s == "["
      | .eof => false
      | .bold w => !(["END","FI","OD","ESAC","THEN","ELSE","ELIF","IN","OUT","OUSE","DO","TO","BY","WHILE","EXIT","AT"].contains w)
      | _ => true
    if !followsOperand then
      adv
      return .skip p
  match (← isMonadicOp) with
  | some op =>
    let p ← curPos
    adv
    let e ← parseOperand
    return .monadic op e p
  | none => parseSecondary

partial def parseSecondary : P Expr := do
  let p ← curPos
  match (← peek) with
  | .bold "HEAP" | .bold "NEW" => adv; return .gen true (← parseDeclarer) p
  | .bold "LOC" => adv; return .gen false (← parseDeclarer) p
  | .ident f =>
    if (← peekAt 1) == .bold "OF" then
      adv; adv
      let e ← parseSecondary
      return .select f e p
    else parsePrimary
  | _ => parsePrimary

partial def parsePrimary : P Expr := do
  let mut e ← parsePrimaryBase
  repeat
    let p ← curPos
    match (← peek) with
    | .sym "(" =>
      adv
      let mut args : List Expr := []
      if !(← isSym ")") then
        repeat
          -- partial parametrisation: an argument may be left out, `f (x, )`
          if (← isSym ",") || (← isSym ")") then args := args ++ [.vacant (← curPos)]
          else args := args ++ [← parseUnit]
          if !(← acceptSym ",") then break
      expectSym ")"
      e := .call e args p
    | .sym "[" =>
      adv
      let idx ← parseIndexers
      expectSym "]"
      e := .slice e idx p
    | _ => break
  return e

partial def parseIndexers : P (List Indexer) := do
  let mut ix : List Indexer := []
  let isEnd : P Bool := do return (← isSym "]") || (← isSym ",") || (← isBold "AT") || (← isSym "@")
  repeat
    if (← acceptColon) then
      let u ← if (← isEnd) then pure none else some <$> parseUnit
      let at_ ← parseAt
      ix := ix ++ [.trim none u at_]
    else if (← isEnd) then
      let at_ ← parseAt
      ix := ix ++ [.trim none none at_]
    else
      let e ← parseUnit
      if (← acceptColon) then
        let u ← if (← isEnd) then pure none else some <$> parseUnit
        let at_ ← parseAt
        ix := ix ++ [.trim (some e) u at_]
      else
        ix := ix ++ [.index e]
    if !(← acceptSym ",") then break
  return ix

partial def parseAt : P (Option Expr) := do
  if (← acceptBold "AT") || (← acceptSym "@") then some <$> parseUnit else pure none

partial def parsePrimaryBase : P Expr := do
  let p ← curPos
  match (← peek) with
  | .int s => adv; return .intLit s.toNat! 0 p
  | .real s => adv; return .realLit s 0 p
  | .bits r d => adv; return .bitsLit r d 0 p
  | .str s => adv; return .strLit s p
  | .format raw => adv; parseFormatText raw p
  | .bold "TRUE" => adv; return .boolLit true p
  | .bold "FALSE" => adv; return .boolLit false p
  | .bold "NIL" => adv; return .nil p
  | .bold "SKIP" => adv; return .skip p
  | .bold "EMPTY" => adv; return .empty p
  | .bold "GOTO" => adv; return .goto (← expectIdent) p
  | .bold "GO" => adv; expectBold "TO"; return .goto (← expectIdent) p
  | .ident n => adv; return .ident n p
  | .sym "(" => parseParen
  | .bold "BEGIN" =>
    adv
    let s ← parseSerial [.bold "END", .sym ","]
    if (← isSym ",") then
      let first ← match s with
        | .mk [.unit e] => pure e
        | _ => fail "invalid collateral clause"
      let mut es := [first]
      while (← acceptSym ",") do
        es := es ++ [← parseUnit]
      expectBold "END"
      return .collateral es p
    expectBold "END"
    return .block s p
  | .bold "IF" => parseIf
  | .bold "CASE" => parseCase
  | .bold "FOR" | .bold "FROM" | .bold "BY" | .bold "TO" | .bold "WHILE" | .bold "DO" => parseLoop
  | .bold "PAR" => adv; parsePrimaryBase
  | .bold "LONG" | .bold "SHORT" =>
    -- long denotation or declarer (cast)
    let mut n : Int := 0
    while (← isBold "LONG") || (← isBold "SHORT") do
      n := n + (if (← isBold "LONG") then 1 else -1)
      adv
    match (← peek) with
    | .int s => adv; return .intLit s.toNat! n p
    | .real s => adv; return .realLit s n p
    | .bits r d => adv; return .bitsLit r d n p
    | _ =>
      let m ← parseDeclarer
      let m := (List.range n.natAbs).foldl (fun acc _ => ModeSyn.long (if n > 0 then 1 else -1) acc) m
      parseCastBody m p
  | _ =>
    if (← isDeclarerStart) then
      let m ← parseDeclarer
      parseCastBody m p
    else
      fail s!"unexpected token {repr (← peek)}"

partial def parseCastBody (m : ModeSyn) (p : Pos) : P Expr := do
  match (← peek) with
  | .sym "(" => return .cast m (← parseParen) p
  | .bold "BEGIN" =>
    adv
    let s ← parseSerial [.bold "END"]
    expectBold "END"
    return .cast m (.block s p) p
  | .bold "IF" => return .cast m (← parseIf) p
  | .bold "CASE" => return .cast m (← parseCase) p
  | _ => fail "expected enclosed clause after declarer (cast)"

/-- Conformity alternative: `( declarer [ident] ) : unit` -/
partial def parseConformityAlt : P (ModeSyn × Option String × Expr) := do
  expectSym "("
  let m ← parseDeclarer
  let n ← match (← peek) with
    | .ident n => adv; pure (some n)
    | _ => pure none
  expectSym ")"
  expectSym ":"
  let e ← parseUnit
  return (m, n, e)

/-- Parse alternatives after `IN`: either conformity alternatives or a unit list. -/
partial def parseAlternatives : P (Sum (List Expr) (List (ModeSyn × Option String × Expr))) := do
  match (← attempt parseConformityAlt) with
  | some a =>
    let mut alts := [a]
    while (← acceptSym ",") do
      alts := alts ++ [← parseConformityAlt]
    return .inr alts
  | none =>
    let mut us : List Expr := []
    repeat
      us := us ++ [← parseUnit]
      if !(← acceptSym ",") then break
    return .inl us

partial def parseParen : P Expr := do
  let p ← curPos
  expectSym "("
  let stops : List Tok := [.sym ")", .sym "|", .sym "|:", .sym ","]
  let s ← parseSerial stops
  match (← peek) with
  | .sym ")" => adv; return .block s p
  | .sym "," =>
    -- collateral
    let first ← match s with
      | .mk [.unit e] => pure e
      | _ => fail "invalid collateral clause"
    let mut es := [first]
    while (← acceptSym ",") do
      es := es ++ [← parseUnit]
    expectSym ")"
    return .collateral es p
  | .sym "|" =>
    adv
    parseBriefAlternatives s p
  | _ => fail "expected ')'"

/-- After `( enquiry |` : conditional or case. -/
partial def parseBriefAlternatives (enq : Serial) (p : Pos) : P Expr := do
  -- conformity?
  match (← attempt parseConformityAlt) with
  | some a =>
    let mut alts := [a]
    while (← acceptSym ",") do
      alts := alts ++ [← parseConformityAlt]
    let out ← parseBriefOut
    return .caseConf enq alts out p
  | none => pure ()
  -- first alternative is a serial clause (conditional) or a unit (case)
  let s1 ← parseSerial [.sym ")", .sym "|", .sym "|:", .sym ","]
  if (← isSym ",") then
    let first ← match s1 with
      | .mk [.unit e] => pure e
      | _ => fail "invalid case alternative"
    let mut alts := [first]
    while (← acceptSym ",") do
      alts := alts ++ [← parseUnit]
    let out ← parseBriefOut
    return .caseInt enq alts out p
  else
    -- conditional
    match (← peek) with
    | .sym ")" => adv; return .cond [(enq, s1)] none p
    | .sym "|" =>
      adv
      let els ← parseSerial [.sym ")"]
      expectSym ")"
      return .cond [(enq, s1)] (some els) p
    | .sym "|:" =>
      adv
      let enq2 ← parseSerial [.sym "|"]
      expectSym "|"
      let rest ← parseBriefAlternatives enq2 p
      return .cond [(enq, s1)] (some (.mk [.unit rest])) p
    | _ => fail "expected '|' or ')'"

partial def parseBriefOut : P (Option Serial) := do
  match (← peek) with
  | .sym ")" => adv; return none
  | .sym "|" =>
    adv
    let s ← parseSerial [.sym ")"]
    expectSym ")"
    return some s
  | .sym "|:" =>
    adv
    let p ← curPos
    let enq2 ← parseSerial [.sym "|"]
    expectSym "|"
    let rest ← parseBriefAlternatives enq2 p
    return some (.mk [.unit rest])
  | _ => fail "expected '|' or ')'"

partial def parseIf : P Expr := do
  let p ← curPos
  expectBold "IF"
  let mut branches : List (Serial × Serial) := []
  let mut els : Option Serial := none
  repeat
    let c ← parseSerial [.bold "THEN"]
    expectBold "THEN"
    let t ← parseSerial [.bold "ELIF", .bold "ELSE", .bold "FI"]
    branches := branches ++ [(c, t)]
    if (← acceptBold "ELIF") then continue
    if (← acceptBold "ELSE") then
      els := some (← parseSerial [.bold "FI"])
    break
  expectBold "FI"
  return .cond branches els p

partial def parseCase : P Expr := do
  let p ← curPos
  expectBold "CASE"
  parseCaseBody p

partial def parseCaseBody (p : Pos) : P Expr := do
  let sel ← parseSerial [.bold "IN"]
  expectBold "IN"
  let alts ← parseAlternatives
  let out ← if (← acceptBold "OUSE") then
      let p2 ← curPos
      let inner ← parseCaseBody p2
      pure (some (Serial.mk [.unit inner]))
    else if (← acceptBold "OUT") then
      let s ← parseSerial [.bold "ESAC"]
      expectBold "ESAC"
      pure (some s)
    else
      expectBold "ESAC"
      pure none
  match alts with
  | .inl us => return .caseInt sel us out p
  | .inr cs => return .caseConf sel cs out p

partial def parseLoop : P Expr := do
  let p ← curPos
  let mut var : Option String := none
  let mut from_ : Option Expr := none
  let mut by_ : Option Expr := none
  let mut to_ : Option Expr := none
  let mut while_ : Option Serial := none
  if (← acceptBold "FOR") then var := some (← expectIdent)
  if (← acceptBold "FROM") then from_ := some (← parseUnit)
  if (← acceptBold "BY") then by_ := some (← parseUnit)
  if (← acceptBold "TO") then to_ := some (← parseUnit)
  else if (← isBold "DOWNTO") then
    let p2 ← curPos
    adv
    to_ := some (← parseUnit)
    by_ := some (.intLit 1 0 p2 |> fun e => .monadic "-" e p2)
  if (← acceptBold "WHILE") then while_ := some (← parseSerial [.bold "DO"])
  expectBold "DO"
  let body ← parseSerial [.bold "OD", .bold "UNTIL"]
  if (← isBold "UNTIL") then
    -- a68g extension `DO s UNTIL u OD`: after the body in every iteration the loop stops
    -- when `u` holds; `u` sees the declarations of the body (genie-enclosed.c).  This is
    -- `WHILE [w; IF w' THEN] s; NOT u [ELSE FALSE FI] DO SKIP OD`, the until part being an
    -- enquiry clause of its own.
    let pu ← curPos
    adv
    if (match body.items.getLast? with | some (.decl _) => true | _ => false) then
      fail "a serial clause before UNTIL must end with a unit"
    let u ← parseSerial [.bold "OD"]
    expectBold "OD"
    let notU : Expr := .cond [(u, .mk [.unit (.boolLit false pu)])] (some (.mk [.unit (.boolLit true pu)])) pu
    let cont : Serial := .mk (body.items ++ [.unit notU])
    let whileC : Serial := match while_ with
      | none => cont
      | some w =>
        match w.items.reverse with
        | .unit wl :: restRev =>
          .mk (restRev.reverse ++
            [.unit (.cond [(.mk [.unit wl], cont)] (some (.mk [.unit (.boolLit false pu)])) pu)])
        | _ => .mk (w.items ++ [.unit (.cond [(.mk [], cont)] none pu)])   -- rejected later: no value
    return .loop var from_ by_ to_ (some whileC) (.mk []) p
  expectBold "OD"
  return .loop var from_ by_ to_ while_ body p

-- ## Format texts

/-- Run a sub-parser over a token array, restoring the outer position afterwards. -/
partial def subParse (toks : Array Token) (q : P α) : P α := do
  let s ← get
  set { s with toks := toks, i := 0 }
  let r ← q
  let s' ← get
  set { s' with toks := s.toks, i := s.i }
  return r

partial def parseFormatText (raw : String) (p : Pos) : P Expr := do
  let cs := raw.toList.toArray
  let (items, _) ← parseFormatItems cs 0 p
  return .format items p

/-- Scan a string literal inside a format (after the opening quote); `""` is an embedded quote.
    Returns the text and the index after the closing quote. -/
partial def scanFmtLiteral (cs : Array Char) (start : Nat) : String × Nat := Id.run do
  let mut j := start
  let mut s := ""
  while j < cs.size do
    if cs[j]! == '"' then
      if j + 1 < cs.size && cs[j+1]! == '"' then
        s := s.push '"'; j := j + 2
      else
        return (s, j + 1)
    else if cs[j]! == '\\' && j + 1 < cs.size && cs[j+1]! == '\n' then
      -- a backslash at the end of a line continues the string on the next
      j := j + 2
    else
      s := s.push cs[j]!; j := j + 1
  return (s, j)

/-- The index of the first character at or after `i` that is not a space. -/
partial def fmtSkipSpaces (cs : Array Char) (i : Nat) : Nat :=
  if i < cs.size && (cs[i]! == ' ' || cs[i]! == '\n' || cs[i]! == '\t') then fmtSkipSpaces cs (i + 1) else i

/-- Parse a balanced `( ... )` starting at index `i` (which must be '('); returns inner text and index after ')'. -/
partial def balanced (cs : Array Char) (i : Nat) : String × Nat := Id.run do
  let mut depth := 0
  let mut j := i
  let mut out := ""
  let mut inStr := false
  while j < cs.size do
    let c := cs[j]!
    if inStr then
      out := out.push c
      if c == '"' then inStr := false
    else if c == '"' then
      out := out.push c; inStr := true
    else if c == '(' then
      depth := depth + 1
      if depth > 1 then out := out.push c
    else if c == ')' then
      depth := depth - 1
      if depth == 0 then return (out, j + 1)
      out := out.push c
    else out := out.push c
    j := j + 1
  return (out, j)

partial def parseUnitFromString (s : String) : P Expr :=
  -- the text was inside parentheses: parse it as an enclosed clause so that brief
  -- conditionals such as `f(cond | fmt1 | fmt2)` keep their meaning
  subParse (lex ("(" ++ s ++ ")")) parseUnit

/-- Split a string on top-level commas (outside quotes/parentheses). -/
partial def splitTop (s : String) : List String := Id.run do
  let mut parts : List String := []
  let mut cur := ""
  let mut depth := 0
  let mut inStr := false
  for c in s.toList do
    if inStr then
      cur := cur.push c
      if c == '"' then inStr := false
    else if c == '"' then cur := cur.push c; inStr := true
    else if c == '(' then depth := depth + 1; cur := cur.push c
    else if c == ')' then depth := depth - 1; cur := cur.push c
    else if c == ',' && depth == 0 then parts := parts ++ [cur]; cur := ""
    else cur := cur.push c
  return parts ++ [cur]

partial def unquote (s : String) : String :=
  let cs := s.toList
  let blank (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'
  let cs := (cs.dropWhile blank).reverse.dropWhile blank |>.reverse
  match cs with
  | '"' :: rest => if rest.getLast? == some '"' then String.ofList rest.dropLast else String.ofList cs
  | _ => String.ofList cs

partial def parseFormatItems (cs : Array Char) (start : Nat) (p : Pos) : P (List FormatItem × Nat) := do
  let mut items : List FormatItem := []
  let mut i := start
  while i < cs.size do
    let c := cs[i]!
    if c == ' ' || c == '\n' || c == '\t' then
      i := i + 1
    else if c == ',' then
      items := items ++ [.sep]
      i := i + 1
    else if c == ')' then
      return (items, i + 1)
    else if c == '"' then
      let (s, j) := scanFmtLiteral cs (i + 1)
      items := items ++ [.literal s]
      i := j
    else if c == '(' then
      let (sub, j) ← parseFormatItems cs (i + 1) p
      items := items ++ [.group sub]
      i := j
    else if Lexer.isDigit c then
      -- replicator
      let mut j := i
      let mut n := 0
      while j < cs.size && Lexer.isDigit cs[j]! do
        n := n * 10 + (cs[j]!.toNat - '0'.toNat); j := j + 1
      let (item, k) ← parseOneFormatItem cs j p
      items := items ++ [.rep n none item]
      i := k
    else if c == 'n' && fmtSkipSpaces cs (i + 1) < cs.size && cs[fmtSkipSpaces cs (i + 1)]! == '(' then
      let (inner, j) := balanced cs (fmtSkipSpaces cs (i + 1))
      let e ← parseUnitFromString inner
      let (item, k) ← parseOneFormatItem cs j p
      items := items ++ [.rep 0 (some e) item]
      i := k
    else
      let (item, k) ← parseOneFormatItem cs i p
      items := items ++ [item]
      i := k
  return (items, i)

partial def parseOneFormatItem (cs : Array Char) (i : Nat) (p : Pos) : P (FormatItem × Nat) := do
  -- skip spaces
  let mut i := i
  while i < cs.size && (cs[i]! == ' ') do i := i + 1
  if i ≥ cs.size then fail "bad format"
  let c := cs[i]!
  let next := if i + 1 < cs.size then cs[i+1]! else ' '
  match c with
  | 'd' => return (.digit false, i + 1)
  | 'z' => return (.digit true, i + 1)
  | '+' => return (.sign true, i + 1)
  | '-' => return (.sign false, i + 1)
  | '.' => return (.point, i + 1)
  | 'e' => return (.exp, i + 1)
  | 'l' => return (.newline, i + 1)
  | 'p' => return (.newpage, i + 1)
  | 'x' => return (.space, i + 1)
  | 'q' => return (.backspace, i + 1)
  | 'k' => return (.col, i + 1)
  | 'a' => return (.char_, i + 1)
  | 's' => return (.strings, i + 1)
  | 'g' =>
    if next == '(' then
      let (inner, j) := balanced cs (i + 1)
      let args ← (splitTop inner).mapM parseUnitFromString
      return (.general args, j)
    else return (.general [], i + 1)
  | 'b' =>
    if next == '(' then
      let (inner, j) := balanced cs (i + 1)
      match splitTop inner with
      | [t, f] => return (.bool_ (some (unquote t)) (some (unquote f)), j)
      | _ => fail "bad boolean pattern"
    else return (.bool_ none none, i + 1)
  | 'c' =>
    if next == '(' then
      let (inner, j) := balanced cs (i + 1)
      return (.choice ((splitTop inner).map unquote), j)
    else fail "bad choice pattern"
  | 'f' =>
    if next == '(' then
      let (inner, j) := balanced cs (i + 1)
      let e ← parseUnitFromString inner
      return (.include e, j)
    else fail "bad format inclusion"
  | '"' =>
    let (s, j) := scanFmtLiteral cs (i + 1)
    return (.literal s, j)
  | '(' =>
    let (sub, j) ← parseFormatItems cs (i + 1) p
    return (.group sub, j)
  | 'r' => return (.radix, i + 1)
  | 'h' =>
    if next == '(' then
      let (inner, j) := balanced cs (i + 1)
      let args ← (splitTop inner).mapM parseUnitFromString
      return (.hpat args, j)
    else return (.hpat [], i + 1)
  | '%' =>
    -- %[-][+][replicator][.replicator]letter
    let mut j := i + 1
    let mut flags := ""
    if j < cs.size && cs[j]! == '-' then flags := flags.push '-'; j := j + 1
    if j < cs.size && cs[j]! == '+' then flags := flags.push '+'; j := j + 1
    let (w, j1) ← fmtReplicator cs j
    j := j1
    let mut a : Option (Nat × Option Expr) := none
    if j < cs.size && cs[j]! == '.' then
      let (a', j2) ← fmtReplicator cs (j + 1)
      if a'.isNone then fail "bad C-style format pattern"
      a := a'; j := j2
    if j < cs.size && "boxcfegdis".toList.contains cs[j]! then
      return (.cpat (flags.push cs[j]!) w a, j + 1)
    else fail "bad C-style format pattern"
  | _ => fail s!"unsupported format item '{c}'"

/-- An optional replicator at `i`: digits, or `n` followed by an enclosed clause. -/
partial def fmtReplicator (cs : Array Char) (i : Nat) : P (Option (Nat × Option Expr) × Nat) := do
  if i < cs.size && Lexer.isDigit cs[i]! then
    let mut j := i
    let mut n := 0
    while j < cs.size && Lexer.isDigit cs[j]! do
      n := n * 10 + (cs[j]!.toNat - '0'.toNat); j := j + 1
    return (some (n, none), j)
  else if i < cs.size && cs[i]! == 'n' && fmtSkipSpaces cs (i + 1) < cs.size
      && cs[fmtSkipSpaces cs (i + 1)]! == '(' then
    let (inner, j) := balanced cs (fmtSkipSpaces cs (i + 1))
    return (some (0, some (← parseUnitFromString inner)), j)
  else return (none, i)

end

/-- Parse a whole program (a serial clause, possibly enclosed). -/
partial def parseProgram : P Serial := do
  let s ← parseSerial [.eof, .sym "."]
  let _ ← acceptSym "."
  match (← peek) with
  | .eof => return s
  | t => fail s!"unexpected token {repr t}"

end Parser

/-- Texts of `PR echo "..." PR` pragmats, in order. -/
def echoesOf (toks : Array Token) : List String := Id.run do
  let mut out : List String := []
  for t in toks do
    match t.tok with
    | .pragmat text =>
      let tt := String.ofList (text.toList.dropWhile (· == ' '))
      if tt.startsWith "echo" then
        match tt.toList.dropWhile (· != '"') with
        | '"' :: rest => out := out ++ [String.ofList (rest.takeWhile (· != '"'))]
        | _ => pure ()
    | _ => pure ()
  -- a68g ends one echo's line when it prints the next, and that strips its trailing
  -- blanks; the last echo's line is ended by the program's own output, which does not
  let n := out.length
  let mut res : List String := []
  let mut i := 0
  for e in out do
    res := res ++ [if i + 1 < n then String.ofList (e.toList.reverse.dropWhile (· == ' ')).reverse else e]
    i := i + 1
  return res

/-- Is a `PR regression PR` (or `quiet regression`) pragmat present? -/
def isRegression (toks : Array Token) : Bool :=
  toks.any fun t => match t.tok with
    | .pragmat text => (text.splitOn " ").contains "regression"
    | _ => false

/-- `PR precision N PR` value, if any. -/
def precisionOf (toks : Array Token) : Option Nat := Id.run do
  for t in toks do
    match t.tok with
    | .pragmat text =>
      let ws := (text.replace "=" " ").splitOn " " |>.filter (· ≠ "")
      match ws with
      | w :: n :: _ => if w.toLower == "precision" then if let some k := n.toNat? then return some k
      | _ => pure ()
    | _ => pure ()
  return none

/-- Parse source text into a `Serial`. -/
def parse (src : String) : Except PError Serial :=
  let toks := (lex src).filter fun t => match t.tok with | .pragmat _ => false | _ => true
  match applyRefinements toks with
  | .error (msg, pos) => .error { msg := msg, pos := pos }
  | .ok toks =>
  let (modes, prios, monops) := Parser.prescan toks
  match Parser.parseProgram { toks := toks, modes := modes, prios := prios, monops := monops } with
  | .ok (s, _) => .ok s
  | .error e => .error e

end A68
