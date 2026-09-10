/-!
# A68.Verified.StackMachine — a verified compiler for the expression core

This module isolates the compilation strategy used for Algol 68 *formulas*
(integer arithmetic over let-bound identifiers, i.e. identity declarations)
and proves it correct: compiling an expression and running the resulting
code on the stack machine leaves exactly the expression's value on top of
the stack, for every environment and initial stack.

All definitions here are total and structural, so the theorems are checked
by Lean's kernel with no axioms beyond the standard ones.
-/
namespace A68.Verified

/-- Expression core: integer denotations, identifiers (de Bruijn indices into an
    environment of identity declarations), the standard dyadic operators `+ - *`,
    monadic minus, and `let` (an identity declaration whose range is `b`). -/
inductive Expr where
  | lit (n : Int)
  | var (i : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  | letE (a b : Expr)
  deriving Repr, DecidableEq

/-- Denotational semantics. Unknown identifiers evaluate to 0 (the elaborator
    rejects them statically; this keeps `eval` total). -/
def Expr.eval (env : List Int) : Expr → Int
  | .lit n => n
  | .var i => env.getD i 0
  | .add a b => eval env a + eval env b
  | .sub a b => eval env a - eval env b
  | .mul a b => eval env a * eval env b
  | .neg a => - eval env a
  | .letE a b => eval (eval env a :: env) b

/-- Instructions of the stack machine. -/
inductive Instr where
  | push (n : Int)
  | load (i : Nat)
  | add | sub | mul | neg
  | enter      -- move the top of the stack into a new innermost environment slot
  | leave      -- discard the innermost environment slot
  deriving Repr

/-- Machine state: an operand stack and an environment (innermost first). -/
structure State where
  stack : List Int
  env   : List Int
  deriving Repr

/-- One step. Ill-formed states (stack underflow) are left unchanged, which keeps
    `step` total; the correctness theorem shows compiled code never reaches them. -/
def step : Instr → State → State
  | .push n, ⟨st, env⟩ => ⟨n :: st, env⟩
  | .load i, ⟨st, env⟩ => ⟨env.getD i 0 :: st, env⟩
  | .add, ⟨b :: a :: st, env⟩ => ⟨(a + b) :: st, env⟩
  | .sub, ⟨b :: a :: st, env⟩ => ⟨(a - b) :: st, env⟩
  | .mul, ⟨b :: a :: st, env⟩ => ⟨(a * b) :: st, env⟩
  | .neg, ⟨a :: st, env⟩ => ⟨(-a) :: st, env⟩
  | .enter, ⟨a :: st, env⟩ => ⟨st, a :: env⟩
  | .leave, ⟨st, _ :: env⟩ => ⟨st, env⟩
  | _, s => s

/-- Run a code sequence. -/
def exec : List Instr → State → State
  | [], s => s
  | i :: is, s => exec is (step i s)

/-- The compiler. -/
def compile : Expr → List Instr
  | .lit n => [.push n]
  | .var i => [.load i]
  | .add a b => compile a ++ compile b ++ [.add]
  | .sub a b => compile a ++ compile b ++ [.sub]
  | .mul a b => compile a ++ compile b ++ [.mul]
  | .neg a => compile a ++ [.neg]
  | .letE a b => compile a ++ [.enter] ++ compile b ++ [.leave]

theorem exec_append (p q : List Instr) (s : State) : exec (p ++ q) s = exec q (exec p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons i is ih => simp [exec, ih]

/-- **Compiler correctness.** Running the code of `e` on any stack and environment
    pushes exactly `e.eval env` and leaves the environment unchanged. -/
theorem compile_correct (e : Expr) (st env : List Int) :
    exec (compile e) ⟨st, env⟩ = ⟨e.eval env :: st, env⟩ := by
  induction e generalizing st env with
  | lit n => rfl
  | var i => rfl
  | add a b iha ihb => simp [compile, exec_append, iha, ihb, exec, step, Expr.eval]
  | sub a b iha ihb => simp [compile, exec_append, iha, ihb, exec, step, Expr.eval]
  | mul a b iha ihb => simp [compile, exec_append, iha, ihb, exec, step, Expr.eval]
  | neg a iha => simp [compile, exec_append, iha, exec, step, Expr.eval]
  | letE a b iha ihb => simp [compile, exec_append, iha, ihb, exec, step, Expr.eval]

/-- Corollary: evaluating from the empty machine yields a singleton stack. -/
theorem run_compile (e : Expr) : (exec (compile e) ⟨[], []⟩).stack = [e.eval []] := by
  simp [compile_correct]

/-- Compiled code is deterministic and its length is linear in the expression size. -/
def Expr.size : Expr → Nat
  | .lit _ | .var _ => 1
  | .add a b | .sub a b | .mul a b => a.size + b.size + 1
  | .neg a => a.size + 1
  | .letE a b => a.size + b.size + 2

theorem compile_length (e : Expr) : (compile e).length = e.size := by
  induction e <;> simp_all [compile, Expr.size] <;> omega

end A68.Verified
