import A68.MIR.Sem

/-!
# A68.MIR.Opt — optimisation passes on MIR

Every pass is a total, structural function `Func → Func`; `A68.Verified.MIR` proves each
one preserves `A68.MIR.Sem.run` for every fuel, runtime and runtime state.  The pipeline
is `Opt.run`.

The passes, in the order of the pipeline:

1. **Copy propagation** (`copyProp`): within a block, after `set x (opnd y)` a use of
   `x` reads `y` instead, until `x` or the variable of `y` is assigned again.  Since a
   constant is an operand, this is also constant propagation.
2. **Constant folding** (`constFold`): a scalar operation whose operands are constants
   and whose check passes becomes the constant it evaluates to.  An operation whose check
   fails — an overflowing addition, a division by zero — is left in place, so that the
   program traps where it did.
3. **Branch folding** (`foldBranches`): a `condBr` on a constant becomes `br`; a
   `switch` on a constant becomes `br` to the case it selects.
4. **Dead assignment elimination** (`dropDead`): an assignment to a variable no operand
   of the function reads is dropped when its right-hand side cannot trap (an operand), or
   demoted to a plain call when it is a call.  A scalar operation with a dead result stays,
   because its check may fail.
5. **Unreachable block removal** (`pruneUnreachable`): a block no path from the entry
   reaches is replaced by an empty `unreachable` block.  Blocks are not renumbered, so
   the correctness theorem needs no simulation of block indices; the printer emits one
   `unreachable` line per pruned block, which LLVM discards.

The two checks a pass performs on its own analysis (`funcNoDead`, `closedUnder`) make
the theorems unconditional: a pass whose analysis had gone wrong would leave the function
alone rather than produce an incorrect one.  `A68.Verified.MIR.funcNoDead_deadVar` proves
the first check always passes; that `reachable` is closed under successors is checked at
run time, not proved.
-/
namespace A68.MIR.Opt
open Sem

-- ## Variables an operand reads

def opndReads : Opnd → List Nat
  | .v x => [x.id]
  | .k _ _ => []

def rhsReads : Rhs → List Nat
  | .opnd o => opndReads o
  | .bin _ a b => opndReads a ++ opndReads b
  | .un _ a => opndReads a
  | .call _ args => args.toList.flatMap opndReads
  | .natTab i => opndReads i
  | .select c a b => opndReads c ++ opndReads a ++ opndReads b

def instrReads : Instr → List Nat
  | .set _ r => rhsReads r
  | .call _ args => args.toList.flatMap opndReads
  | .line _ => []

def termReads : Term → List Nat
  | .condBr c _ _ => opndReads c
  | .switch o _ _ => opndReads o
  | .retVal o => opndReads o
  | _ => []

def blockReads (b : Block) : List Nat := b.instrs.toList.flatMap instrReads ++ termReads b.term

/-- Every variable some operand of the function reads. -/
def readVars (f : Func) : List Nat := f.blocks.toList.flatMap blockReads

-- ## 1. Copy propagation

/-- The copies in force: `x` currently holds the value of the operand. -/
abbrev Copies := List (Var × Opnd)

/-- The operand a variable read stands for. -/
def substOpnd (m : Copies) : Opnd → Opnd
  | .v x =>
    match m.find? (fun e => decide (e.1.id = x.id ∧ e.1.ty = x.ty)) with
    | some e => e.2
    | none => .v x
  | o => o

def substRhs (m : Copies) : Rhs → Rhs
  | .opnd o => .opnd (substOpnd m o)
  | .bin op a b => .bin op (substOpnd m a) (substOpnd m b)
  | .un op a => .un op (substOpnd m a)
  | .call f args => .call f (args.map (substOpnd m))
  | .natTab i => .natTab (substOpnd m i)
  | .select c a b => .select (substOpnd m c) (substOpnd m a) (substOpnd m b)

def substTerm (m : Copies) : Term → Term
  | .condBr c t f => .condBr (substOpnd m c) t f
  | .switch o cs d => .switch (substOpnd m o) cs d
  | .retVal o => .retVal (substOpnd m o)
  | t => t

/-- Assigning `id` invalidates the copies of it and the copies from it. -/
def killVar (id : Nat) (m : Copies) : Copies :=
  m.filter fun e => decide (e.1.id ≠ id) && !((opndReads e.2).contains id)

/-- The copies in force after `set d rhs` (with `rhs` already substituted): a copy of an
    operand of `d`'s own type that does not mention `d` is recorded. -/
def addCopy (d : Var) (rhs : Rhs) (m : Copies) : Copies :=
  match rhs with
  | .opnd y => if y.ty = d.ty ∧ !((opndReads y).contains d.id) then (d, y) :: m else m
  | _ => m

/-- Propagate through a block's instructions, returning them and the copies in force at
    the terminator. -/
def copyPropInstrs (m : Copies) : List Instr → List Instr × Copies
  | [] => ([], m)
  | .set d rhs :: is =>
    let rhs' := substRhs m rhs
    let r := copyPropInstrs (addCopy d rhs' (killVar d.id m)) is
    (.set d rhs' :: r.1, r.2)
  | .call f args :: is =>
    let r := copyPropInstrs m is
    (.call f (args.map (substOpnd m)) :: r.1, r.2)
  | .line n :: is =>
    let r := copyPropInstrs m is
    (.line n :: r.1, r.2)

def copyPropBlock (b : Block) : Block :=
  let r := copyPropInstrs [] b.instrs.toList
  ⟨r.1.toArray, substTerm r.2 b.term⟩

def copyProp (f : Func) : Func := { f with blocks := f.blocks.map copyPropBlock }

-- ## 2. Constant folding

/-- The constant denoting a value. -/
def valToConst : Val → Const
  | .i n => .i n
  | .f x => .f x
  | .b t => .i (if t then 1 else 0)

/-- Is the value of the representation a variable of this type holds?  Only then does
    `constVal ty v.toConst` give `v` back. -/
def valFits : Ty → Val → Bool
  | .i1, .b _ => true
  | .i64, .i _ => true
  | .i32, .i _ => true
  | .f64, .f _ => true
  | _, _ => false

/-- Fold a right-hand side assigned to `d`: an operation on constants whose check passes
    becomes the constant.  The mathematical functions are unknown here (`noMath`), so a
    `math` operation is never folded. -/
def foldRhs (d : Var) : Rhs → Rhs
  | .bin op (.k ta ca) (.k tb cb) =>
    match binSem op (constVal ta ca) (constVal tb cb) with
    | some v => if valFits d.ty v then .opnd (.k d.ty (valToConst v)) else .bin op (.k ta ca) (.k tb cb)
    | none => .bin op (.k ta ca) (.k tb cb)
  | .un op (.k ta ca) =>
    match unSem noMath op (constVal ta ca) with
    | some v => if valFits d.ty v then .opnd (.k d.ty (valToConst v)) else .un op (.k ta ca)
    | none => .un op (.k ta ca)
  | r => r

def foldInstr : Instr → Instr
  | .set d r => .set d (foldRhs d r)
  | i => i

def foldBlock (b : Block) : Block := { b with instrs := b.instrs.map foldInstr }

def constFold (f : Func) : Func := { f with blocks := f.blocks.map foldBlock }

-- ## 3. Branch folding

def foldTerm : Term → Term
  | .condBr (.k ty c) t f => .br (if (constVal ty c).truthy then t else f)
  | .switch (.k ty c) cs d => .br (selectCase (constVal ty c) cs.toList d)
  | t => t

def foldBranchBlock (b : Block) : Block := { b with term := foldTerm b.term }

def foldBranches (f : Func) : Func := { f with blocks := f.blocks.map foldBranchBlock }

-- ## 4. Dead assignment elimination

/-- Drop or demote the assignments to dead variables. -/
def dropDeadInstrs (dead : Nat → Bool) : List Instr → List Instr
  | [] => []
  | .set d (.opnd o) :: is =>
    if dead d.id then dropDeadInstrs dead is else .set d (.opnd o) :: dropDeadInstrs dead is
  | .set d (.call f args) :: is =>
    if dead d.id then .call f args :: dropDeadInstrs dead is
    else .set d (.call f args) :: dropDeadInstrs dead is
  | i :: is => i :: dropDeadInstrs dead is

def dropDeadBlock (dead : Nat → Bool) (b : Block) : Block :=
  { b with instrs := (dropDeadInstrs dead b.instrs.toList).toArray }

/-- Does no operand read a dead variable?  The check the pass makes of its own analysis. -/
def opndNoDead (dead : Nat → Bool) : Opnd → Bool
  | .v x => !dead x.id
  | .k _ _ => true

def rhsNoDead (dead : Nat → Bool) : Rhs → Bool
  | .opnd o => opndNoDead dead o
  | .bin _ a b => opndNoDead dead a && opndNoDead dead b
  | .un _ a => opndNoDead dead a
  | .call _ args => args.toList.all (opndNoDead dead)
  | .natTab i => opndNoDead dead i
  | .select c a b => opndNoDead dead c && opndNoDead dead a && opndNoDead dead b

def instrNoDead (dead : Nat → Bool) : Instr → Bool
  | .set _ r => rhsNoDead dead r
  | .call _ args => args.toList.all (opndNoDead dead)
  | .line _ => true

def termNoDead (dead : Nat → Bool) : Term → Bool
  | .condBr c _ _ => opndNoDead dead c
  | .switch o _ _ => opndNoDead dead o
  | .retVal o => opndNoDead dead o
  | _ => true

def blockNoDead (dead : Nat → Bool) (b : Block) : Bool :=
  b.instrs.toList.all (instrNoDead dead) && termNoDead dead b.term

def funcNoDead (dead : Nat → Bool) (f : Func) : Bool :=
  f.blocks.toList.all (blockNoDead dead)

/-- A variable is dead when no operand of the function reads it. -/
def deadVar (f : Func) (id : Nat) : Bool := !((readVars f).contains id)

def dropDead (f : Func) : Func :=
  let dead := deadVar f
  if funcNoDead dead f then { f with blocks := f.blocks.map (dropDeadBlock dead) } else f

-- ## 5. Unreachable block removal

/-- The successors of block `b`. -/
def blockSuccs (f : Func) (b : Nat) : List Nat :=
  match f.blocks[b]? with
  | some blk => termSuccs blk.term
  | none => []

/-- One round of the reachability closure. -/
def reachStep (f : Func) (r : List Nat) : List Nat :=
  r.foldl (fun acc b => (blockSuccs f b).foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) acc) r

/-- The blocks reachable from the entry, by iterating the closure as many times as there
    are blocks. -/
def reachable (f : Func) : List Nat :=
  (List.range (f.blocks.size + 1)).foldl (fun r _ => reachStep f r) [0]

/-- Is the set closed under successors and does it contain the entry? -/
def closedUnder (f : Func) (r : List Nat) : Bool :=
  r.contains 0 && r.all fun b => (blockSuccs f b).all r.contains

/-- The block an unreachable one becomes. -/
def unreachableBlock : Block := ⟨#[], .unreachable⟩

def pruneBlocks (r : List Nat) (bs : Array Block) : Array Block :=
  bs.mapIdx fun i b => if r.contains i then b else unreachableBlock

def pruneUnreachable (f : Func) : Func :=
  let r := reachable f
  if closedUnder f r then { f with blocks := pruneBlocks r f.blocks } else f

-- ## The pipeline

/-- One round of propagation and folding: folding creates new copies, propagation new
    constants. -/
def simplify (f : Func) : Func := constFold (copyProp f)

def simplifyN : Nat → Func → Func
  | 0, f => f
  | n + 1, f => simplifyN n (simplify f)

/-- Three rounds of simplification, a last propagation so that the constants reach the
    terminators, then branch folding, dead assignment elimination and unreachable block
    removal. -/
def run (f : Func) : Func :=
  f |> simplifyN 3 |> copyProp |> foldBranches |> dropDead |> pruneUnreachable

end A68.MIR.Opt
