/-!
# A68.Syntax — abstract syntax of Algol 68 (as accepted by a68lean)

The parser produces these trees; the elaborator (`A68.Elab`) checks modes,
resolves operators and inserts coercions, producing `A68.Core` terms.
-/
namespace A68

/-- Source position (1-based line and column). -/
structure Pos where
  line : Nat := 0
  col  : Nat := 0
  deriving Repr, Inhabited, BEq

mutual
/-- Items of a format text (`$ ... $`). -/
inductive FormatItem where
  | literal (s : String)                             -- "text"
  | newline | newpage | space | backspace            -- l p x q
  | rep (n : Nat) (dyn : Option Expr) (item : FormatItem)   -- 3d  /  n(k)d
  | digit (zero : Bool)                              -- d / z
  | sign (plus : Bool)                               -- + / -
  | point                                            -- .
  | exp                                              -- e
  | general (args : List Expr)                       -- g, g(w), g(w,a), g(w,a,e)
  | bool_ (flip flop : Option String)                -- b, b("t","f")
  | choice (alts : List String)                      -- c("a","b")
  | char_                                            -- a
  | strings                                          -- s
  | group (items : List FormatItem)                  -- ( ... )
  | include (f : Expr)                               -- f(format)  (a68g: user format inclusion)
  | sep                                              -- picture separator (",")
  | col                                              -- k: alignment to a column (with replicator)
  | radix                                            -- r: radix frame of a bits pattern (with replicator)
  | hpat (args : List Expr)                          -- h, h(a), h(a,m), h(w,a,m), h(w,a,e,m)
  -- a68g C-style pattern %[-][+][w][.a]letter; `flags` holds the '-' and '+' given and ends
  -- with the letter; width and after are replicators (static, or dynamic with an expression)
  | cpat (flags : String) (width after : Option (Nat × Option Expr))
  deriving Repr, Inhabited

/-- Mode syntax (declarers) as written in source. Bounds appear only in actual declarers. -/
inductive ModeSyn where
  | int | real | bool | char | void | bits | bytes | compl
  | string                                           -- STRING = FLEX []CHAR
  | format | file | channel | sema
  | long (n : Int) (m : ModeSyn)                     -- LONG (n>0) / SHORT (n<0)
  | ref (m : ModeSyn)
  | row (bounds : List Bound) (flex : Bool) (m : ModeSyn)
  | proc (params : List ModeSyn) (ret : ModeSyn)
  | struct (fields : List (String × ModeSyn))
  | union (alts : List ModeSyn)
  | ind (name : String)                               -- mode indicant
  deriving Repr, Inhabited

/-- One dimension of a row declarer: `[]` (None,None), `[u]`, `[l:u]`. -/
inductive Bound where
  | mk (lwb : Option Expr) (upb : Option Expr)
  deriving Repr, Inhabited

inductive Indexer where
  | index (e : Expr)                                          -- [i]
  | trim (lwb upb : Option Expr) (at_ : Option Expr)          -- [l:u AT k]
  deriving Repr, Inhabited

inductive Expr where
  | intLit (v : Nat) (long : Int) (pos : Pos)
  | realLit (text : String) (long : Int) (pos : Pos)
  | bitsLit (radix : Nat) (digits : String) (long : Int) (pos : Pos)
  | strLit (s : String) (pos : Pos)
  | boolLit (b : Bool) (pos : Pos)
  | nil (pos : Pos)
  | skip (pos : Pos)
  | empty (pos : Pos)
  | ident (name : String) (pos : Pos)
  | dyadic (op : String) (l r : Expr) (pos : Pos)
  | monadic (op : String) (e : Expr) (pos : Pos)
  | assign (dest src : Expr) (pos : Pos)
  | identity (l r : Expr) (isnt : Bool) (pos : Pos)
  | call (f : Expr) (args : List Expr) (pos : Pos)
  | slice (arr : Expr) (idx : List Indexer) (pos : Pos)
  | select (field : String) (e : Expr) (pos : Pos)
  | cast (m : ModeSyn) (e : Expr) (pos : Pos)
  | gen (heap : Bool) (m : ModeSyn) (pos : Pos)
  | routine (params : List (ModeSyn × String)) (ret : ModeSyn) (body : Expr) (pos : Pos)
  | goto (label : String) (pos : Pos)
  | block (s : Serial) (pos : Pos)                     -- ( s ) / BEGIN s END
  | collateral (es : List Expr) (pos : Pos)            -- ( a, b, c )
  | cond (branches : List (Serial × Serial)) (els : Option Serial) (pos : Pos)
  | caseInt (sel : Serial) (alts : List Expr) (out : Option Serial) (pos : Pos)
  | caseConf (sel : Serial) (alts : List (ModeSyn × Option String × Expr)) (out : Option Serial) (pos : Pos)
  | loop (var : Option String) (from_ by_ to_ : Option Expr) (while_ : Option Serial)
         (body : Serial) (pos : Pos)
  | format (items : List FormatItem) (pos : Pos)
  | vacant (pos : Pos)                                 -- omitted argument of a partial call `f (x, )`
  deriving Repr, Inhabited

inductive Decl where
  | var (m : ModeSyn) (heap : Bool) (items : List (String × Option Expr)) (pos : Pos)
  | identity (m : Option ModeSyn) (items : List (String × Expr)) (pos : Pos)   -- None: PROC f = routine
  | op (name : String) (m : Option ModeSyn) (body : Expr) (pos : Pos)
  | prio (name : String) (n : Nat) (pos : Pos)
  | mode (name : String) (m : ModeSyn) (pos : Pos)
  deriving Repr, Inhabited

inductive Stmt where
  | decl (d : Decl)
  | unit (e : Expr)
  | label (name : String) (pos : Pos)
  | exit (pos : Pos)                       -- `unit EXIT`: complete the enclosing serial clause
  deriving Repr, Inhabited

/-- A serial clause: statements separated by `;`. -/
inductive Serial where
  | mk (items : List Stmt)
  deriving Repr, Inhabited
end

def Serial.items : Serial → List Stmt
  | .mk xs => xs

def Expr.pos : Expr → Pos
  | .intLit _ _ p | .realLit _ _ p | .bitsLit _ _ _ p | .strLit _ p | .boolLit _ p
  | .nil p | .skip p | .empty p | .ident _ p | .dyadic _ _ _ p | .monadic _ _ p
  | .assign _ _ p | .identity _ _ _ p | .call _ _ p | .slice _ _ p | .select _ _ p
  | .cast _ _ p | .gen _ _ p | .routine _ _ _ p | .goto _ p | .block _ p
  | .collateral _ p | .cond _ _ p | .caseInt _ _ _ p | .caseConf _ _ _ p
  | .loop _ _ _ _ _ _ p | .format _ p | .vacant p => p

end A68
