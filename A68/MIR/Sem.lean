import A68.MIR

/-!
# A68.MIR.Sem — the semantics of MIR

An executable, fuel-bounded semantics of `A68.MIR` (docs/LLVM-DESIGN.md §2, §4).  It is
the reference the MIR optimisations are proved against (`A68.Verified.MIR`) and doubles
as an interpreter for differential testing of the LLVM printer.

* **Values** are untyped: an `Int` (INT, BITS and the code of a CHAR), a `Float` (REAL)
  or a `Bool`.  A variable environment is a total function with the default `.i 0`.
* **Scalar operations** are partial functions that are `none` exactly when a68g's check
  of the operation fails — the LLVM printer expands each into that check and a branch to
  `a68rt_arith_error` — or when the operands are not of the operation's type, which
  the lowering never produces.  INT arithmetic is checked against ±2147483647, REAL
  results against NaN and infinity, `powI` is `Interp.powIntInt` transcribed.
  Float arithmetic is Lean's `Float`, opaque to every theorem.
* **The runtime** is a parameter: a type of runtime states and a step function per kind
  of callee.  A call the runtime answers with `none` aborts the program (as
  `a68rt_arith_error` and the other fatal entry points do).  The mathematical
  functions `math name` are likewise a parameter of the runtime.
* **Observable behaviour** is the trace of calls (with their arguments and results) and
  of `line` markers, plus how the run ended: returned, trapped, aborted in the runtime,
  or ran out of fuel.  Fuel counts block transitions, so `run` is structural recursion
  on it and every block body is executed to its end without fuel.

Reading a variable coerces the stored value to the variable's declared type
(`coerceTo`), which models the `zext`/`icmp ne` the printer emits when an operand of
one type is assigned to a variable of another; the coercion is the identity on values
of the right type, so a well-typed program never observes it.
-/
namespace A68.MIR.Sem

/-- A scalar value.  `i` carries INT, BITS and CHAR (the i32 code), `f` REAL, `b` BOOL. -/
inductive Val where
  | i (n : Int)
  | f (x : Float)
  | b (t : Bool)
  deriving Repr, Inhabited

/-- The value a scalar denotes as a truth value: what `condBr` tests. -/
def Val.truthy : Val → Bool
  | .b t => t
  | .i n => decide (n ≠ 0)
  | .f _ => false

/-- The value seen through a variable (or constant) of type `ty`: `i1` reads a truth
    value, the integer types read a BOOL as 0/1 (LLVM's `zext`), the rest is unchanged. -/
def coerceTo : Ty → Val → Val
  | .i1, v => .b v.truthy
  | .f64, v => v
  | _, .b b => .i (if b then 1 else 0)
  | _, v => v

/-- The raw value of a constant, before its type is applied. -/
def rawVal : Const → Val
  | .i n => .i n
  | .f x => .f x

/-- The value of a constant of type `ty`. -/
def constVal (ty : Ty) (c : Const) : Val := coerceTo ty (rawVal c)

/-- A variable environment: total, unset variables read as `.i 0`. -/
abbrev Env := Nat → Val

def Env.init : Env := fun _ => .i 0

def Env.set (env : Env) (id : Nat) (v : Val) : Env := fun j => if j = id then v else env j

/-- The value of an operand. -/
def evalOpnd (env : Env) : Opnd → Val
  | .v x => coerceTo x.ty (env x.id)
  | .k ty c => constVal ty c

-- ## The scalar operations

/-- INT results must lie in [-2147483647, 2147483647] (a68g's `A68_MAX_INT`). -/
def maxInt : Int := 2147483647

def inRange (n : Int) : Bool := decide (-maxInt ≤ n ∧ n ≤ maxInt)

def checkInt (n : Int) : Option Val := if inRange n then some (.i n) else none

/-- A REAL result may be neither NaN nor infinite (`a68_chk_r`). -/
def checkReal (x : Float) : Option Val := if x.isNaN || x.isInf then none else some (.f x)

/-- The mask a BITS value is reduced to (32 bits). -/
def bitsMask : Nat := 4294967295

/-- The square-and-multiply loop of `Interp.powIntInt`: `bit` doubles at every round and
    the loop ends once it exceeds `nn`, so `nn + 1` rounds always suffice; the fuel is only
    what makes the recursion structural. -/
def powILoop : Nat → Nat → Nat → Int → Int → Option Int
  | 0, _, _, _, p => some p
  | k + 1, nn, bit, mm, p =>
    let p' := if nn &&& bit != 0 then (if inRange (p * mm) then some (p * mm) else none) else some p
    match p' with
    | none => none
    | some p =>
      let bit := bit <<< 1
      if bit ≤ nn then
        if inRange (mm * mm) then powILoop k nn bit (mm * mm) p else none
      else some p

/-- INT ** INT as a68g computes it (`Interp.powIntInt`): a negative exponent traps, the
    trivial bases short-cut, and every intermediate product is range-checked. -/
def powI (m n : Int) : Option Int :=
  if n < 0 then none
  else if m = 0 ∧ n = 0 then some 1
  else if m = 0 ∨ m = 1 then some m
  else if m = -1 then some (if n % 2 = 0 then 1 else -1)
  else powILoop (n.toNat + 1) n.toNat 1 m 1

/-- The loop of `Interp.powRealIntPos`, unchecked until the end. -/
def powFLoop : Nat → Nat → Nat → Float → Float → Float
  | 0, _, _, _, p => p
  | k + 1, nn, bit, mm, p =>
    let p := if nn &&& bit != 0 then p * mm else p
    let bit := bit <<< 1
    if bit ≤ nn then powFLoop k nn bit (mm * mm) p else p

/-- REAL ** INT with a non-negative exponent (`a68g_x_up_n_real`). -/
def powFNat (x : Float) (nn : Nat) : Option Float :=
  if x == 0.0 && nn == 0 then some 1.0
  else if x == 0.0 || x == 1.0 then some x
  else if x == -1.0 then some (if nn % 2 == 0 then 1.0 else -1.0)
  else
    let p := powFLoop (nn + 1) nn 1 x 1.0
    if p.isInf || p.isNaN then none else some p

/-- REAL ** INT (`Interp.powRealInt`, `a68n_pow_ri`). -/
def powFI (x : Float) (n : Int) : Option Float :=
  if n < 0 then (powFNat x n.natAbs).map (fun p => 1.0 / p) else powFNat x n.toNat

/-- REAL ** REAL (`a68n_pow_rr`): a negative base or a zero base with a negative
    exponent is a math error; the result is not checked. -/
def powFF (x y : Float) : Option Float :=
  if y == 0.0 then some 1.0
  else if x < 0.0 then none
  else if x == 0.0 then (if y < 0.0 then none else some 0.0)
  else some (Float.exp (y * Float.log x))

/-- The bound of ENTIER and ROUND, as a REAL. -/
def intLimit : Float := 2147483647.0

/-- ENTIER: traps outside ±2147483647, then floors (`Interp` and `a68n_entier`). -/
def entier (x : Float) : Option Int :=
  if x < -intLimit || x > intLimit then none
  else
    let f := Float.floor x
    some (if f < 0.0 then -((-f).toUInt64.toNat : Int) else (f.toUInt64.toNat : Int))

/-- ROUND: half away from zero (`Interp.roundReal`, `a68n_round`). -/
def round (x : Float) : Option Int :=
  if x < -intLimit || x > intLimit then none
  else
    let r := Float.floor (Float.abs x + 0.5)
    let n : Int := r.toUInt64.toNat
    some (if x < 0.0 then -n else n)

/-- The comparisons on INT, BITS and CHAR. -/
def cmpI : BinOp → Int → Int → Option Val
  | .eq, a, b => some (.b (decide (a = b)))
  | .ne, a, b => some (.b (decide (a ≠ b)))
  | .lt, a, b => some (.b (decide (a < b)))
  | .le, a, b => some (.b (decide (a ≤ b)))
  | .gt, a, b => some (.b (decide (a > b)))
  | .ge, a, b => some (.b (decide (a ≥ b)))
  | _, _, _ => none

/-- The comparisons on REAL (IEEE: every comparison with a NaN is false). -/
def cmpF : BinOp → Float → Float → Option Val
  | .eq, a, b => some (.b (a == b))
  | .ne, a, b => some (.b (a != b))
  | .lt, a, b => some (.b (decide (a < b)))
  | .le, a, b => some (.b (decide (a ≤ b)))
  | .gt, a, b => some (.b (decide (a > b)))
  | .ge, a, b => some (.b (decide (a ≥ b)))
  | _, _, _ => none

/-- The comparisons on BOOL: only `=` and `/=` exist. -/
def cmpB : BinOp → Bool → Bool → Option Val
  | .eq, a, b => some (.b (decide (a = b)))
  | .ne, a, b => some (.b (decide (a ≠ b)))
  | _, _, _ => none

/-- The meaning of a dyadic operation: `none` when its check fails (or its operands are
    of the wrong type). -/
def binSem : BinOp → Val → Val → Option Val
  | .addI, .i a, .i b => checkInt (a + b)
  | .subI, .i a, .i b => checkInt (a - b)
  | .mulI, .i a, .i b => checkInt (a * b)
  | .overI, .i a, .i b => if b = 0 then none else some (.i (Int.tdiv a b))
  | .modI, .i a, .i b => if b = 0 then none else some (.i (a % (b.natAbs : Int)))
  | .powI, .i a, .i b => (powI a b).map .i
  | .addF, .f a, .f b => checkReal (a + b)
  | .subF, .f a, .f b => checkReal (a - b)
  | .mulF, .f a, .f b => checkReal (a * b)
  | .divF, .f a, .f b => if b == 0.0 then none else some (.f (a / b))
  | .powFI, .f a, .i b => (powFI a b).map .f
  | .powFF, .f a, .f b => (powFF a b).map .f
  | .andB, .b a, .b b => some (.b (a && b))
  | .orB, .b a, .b b => some (.b (a || b))
  | .xorB, .b a, .b b => some (.b (a != b))
  | .andU, .i a, .i b => some (.i ((a.toNat &&& b.toNat : Nat) : Int))
  | .orU, .i a, .i b => some (.i (((a.toNat ||| b.toNat) &&& bitsMask : Nat) : Int))
  | .xorU, .i a, .i b => some (.i (((a.toNat ^^^ b.toNat) &&& bitsMask : Nat) : Int))
  | op, .i a, .i b => cmpI op a b
  | op, .f a, .f b => cmpF op a b
  | op, .b a, .b b => cmpB op a b
  | _, _, _ => none

/-- The mathematical functions of the runtime support (`a68n_m_<name>`), abstract:
    `none` is a domain error or an unchecked result. -/
abbrev MathFns := String → Float → Option Float

/-- The meaning of a monadic operation, given the mathematical functions. -/
def unSem (math : MathFns) : UnOp → Val → Option Val
  | .negI, .i n => checkInt (-n)
  | .absI, .i n => some (.i (n.natAbs : Int))
  | .signI, .i n => some (.i (if n > 0 then 1 else if n < 0 then -1 else 0))
  | .oddI, .i n => some (.b (decide (n % 2 ≠ 0)))
  | .reprI, .i n => if n < 0 ∨ n > 255 then none else some (.i n)
  | .negF, .f x => some (.f (-x))
  | .absF, .f x => some (.f (Float.abs x))
  | .signF, .f x => some (.i (if x > 0.0 then 1 else if x < 0.0 then -1 else 0))
  | .entier, .f x => (entier x).map .i
  | .round, .f x => (round x).map .i
  | .notB, .b b => some (.b (!b))
  | .absB, .b b => some (.i (if b then 1 else 0))
  | .absC, .i n => some (.i n)
  | .i2f, .i n => some (.f (Float.ofInt n))
  | .math name, .f x => (math name x).map .f
  | _, _ => none

/-- No mathematical function is known: what an optimiser may assume. -/
def noMath : MathFns := fun _ _ => none

-- ## The runtime, the events, the states

/-- The runtime a MIR program calls, abstractly: a state `R` and, per kind of callee, a
    step function from arguments and state to the new state and the result, or `none`
    when the call does not return (the runtime aborts the program). -/
structure Runtime (R : Type) where
  rt   : String → List Val → R → Option (R × Option Val)
  fn   : Nat → List Val → R → Option (R × Option Val)
  hole : Nat → List Val → R → Option (R × Option Val)
  nat  : String → List Val → R → Option (R × Option Val)
  nfn  : Nat → List Val → R → Option (R × Option Val)
  /-- An indirect call: the pointer (the value of the first argument) then the arguments. -/
  ind  : Array Ty → Option Ty → List Val → R → Option (R × Option Val)
  math : MathFns

def Runtime.call (rt : Runtime R) : Callee → List Val → R → Option (R × Option Val)
  | .rt name => rt.rt name
  | .fn i => rt.fn i
  | .hole i => rt.hole i
  | .nat name => rt.nat name
  | .nfn i => rt.nfn i
  | .ind ptys rty => rt.ind ptys rty

/-- What a run makes observable. -/
inductive Event where
  | call (f : Callee) (args : List Val) (ret : Option Val)
  | line (n : Nat)
  | ret (v : Val)
  deriving Repr

/-- How a run ended. -/
inductive Status where
  | done        -- the function returned
  | trap        -- a check failed, `unreachable` was reached, or a block index is out of range
  | abort       -- the runtime did not return from a call
  | outOfFuel
  deriving Repr, DecidableEq

/-- The observable behaviour of a run: the events in order, and the end. -/
structure Outcome where
  trace  : List Event
  status : Status
  deriving Repr

/-- The state during a run; the trace is kept most recent first. -/
structure State (R : Type) where
  env   : Env
  rt    : R
  trace : List Event

/-- The result of executing instructions: the next state, or the trace so far and why
    execution stopped. -/
inductive Res (R : Type) where
  | ok (s : State R)
  | stop (trace : List Event) (st : Status)

-- ## Instructions

/-- The value of a scalar right-hand side (`none`: its check failed). -/
def evalRhs (math : MathFns) (env : Env) : Rhs → Option Val
  | .opnd o => some (evalOpnd env o)
  | .bin op a b => binSem op (evalOpnd env a) (evalOpnd env b)
  | .un op a => unSem math op (evalOpnd env a)
  | .call _ _ => none
  | .natTab i => some (evalOpnd env i)   -- a pointer is identified by its routine index

/-- A call: the arguments are evaluated, the runtime steps, the call is recorded. -/
def execCall (rt : Runtime R) (f : Callee) (args : Array Opnd) (s : State R) :
    Option (State R × Option Val) :=
  let vs := args.toList.map (evalOpnd s.env)
  match rt.call f vs s.rt with
  | none => none
  | some (r', ret) => some (⟨s.env, r', .call f vs ret :: s.trace⟩, ret)

/-- One instruction.  A void call whose result is assigned stores `.i 0`. -/
def execInstr (rt : Runtime R) : Instr → State R → Res R
  | .line n, s => .ok { s with trace := .line n :: s.trace }
  | .call f args, s =>
    match execCall rt f args s with
    | none => .stop s.trace .abort
    | some (s', _) => .ok s'
  | .set d (.call f args), s =>
    match execCall rt f args s with
    | none => .stop s.trace .abort
    | some (s', ret) => .ok { s' with env := s'.env.set d.id (ret.getD (.i 0)) }
  | .set d rhs, s =>
    match evalRhs rt.math s.env rhs with
    | none => .stop s.trace .trap
    | some v => .ok { s with env := s.env.set d.id v }

/-- A sequence of instructions, stopping at the first that does not complete. -/
def execInstrs (rt : Runtime R) : List Instr → State R → Res R
  | [], s => .ok s
  | i :: is, s =>
    match execInstr rt i s with
    | .ok s' => execInstrs rt is s'
    | .stop tr st => .stop tr st

-- ## Blocks and functions

/-- The case of a `switch` a value selects. -/
def selectCase (v : Val) : List (Int × Nat) → Nat → Nat
  | [], d => d
  | (k, b) :: cs, d => match v with
    | .i n => if n = k then b else selectCase v cs d
    | _ => selectCase v cs d

/-- The blocks a terminator may transfer to. -/
def termSuccs : Term → List Nat
  | .br b => [b]
  | .condBr _ t f => [t, f]
  | .switch _ cs d => d :: cs.toList.map (·.2)
  | .ret => []
  | .retVal _ => []
  | .unreachable => []

/-- The result of executing one block: the block to continue with, or the end. -/
inductive BlockOut (R : Type) where
  | next (b : Nat) (s : State R)
  | stop (trace : List Event) (st : Status)

/-- One block: its instructions, then its terminator. -/
def stepBlock (rt : Runtime R) (blk : Block) (s : State R) : BlockOut R :=
  match execInstrs rt blk.instrs.toList s with
  | .stop tr st => .stop tr st
  | .ok s' =>
    match blk.term with
    | .ret => .stop s'.trace .done
    | .retVal o => .stop (.ret (evalOpnd s'.env o) :: s'.trace) .done
    | .unreachable => .stop s'.trace .trap
    | .br b => .next b s'
    | .condBr c t f => .next (if (evalOpnd s'.env c).truthy then t else f) s'
    | .switch o cs d => .next (selectCase (evalOpnd s'.env o) cs.toList d) s'

/-- Run from block `b` with `fuel` block transitions left. -/
def runFrom (rt : Runtime R) (f : Func) : Nat → Nat → State R → Outcome
  | 0, _, s => ⟨s.trace.reverse, .outOfFuel⟩
  | fuel + 1, b, s =>
    match f.blocks[b]? with
    | none => ⟨s.trace.reverse, .trap⟩
    | some blk =>
      match stepBlock rt blk s with
      | .stop tr st => ⟨tr.reverse, st⟩
      | .next b' s' => runFrom rt f fuel b' s'

/-- **The semantics of a function**: run it from its entry block on runtime state `r`,
    every variable initially `.i 0`. -/
def run (rt : Runtime R) (fuel : Nat) (f : Func) (r : R) : Outcome :=
  runFrom rt f fuel 0 ⟨Env.init, r, []⟩

end A68.MIR.Sem
