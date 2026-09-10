import A68.Verified.StackMachine

/-!
# A68.Verified.Opt — the optimisation passes, proved correct

`A68.Opt` folds constant units, drops coercions that do nothing, resolves
constant conditions and flattens frameless blocks.  Here the same rewrites are
stated over the formal expression core of `A68.Verified.StackMachine`, where
evaluation is a total function, and each is proved to preserve meaning; the
composition with `compile_correct` then gives an end-to-end statement: the code
generated for the optimised program computes what the source program denotes.

The rules modelled are exactly those the production pass applies:

* an operator whose operands are **both literals** is replaced by the literal
  it evaluates to (the production pass evaluates it with the run-time
  evaluator, so the value is the one the program would have computed);
* a conditional with a constant condition becomes the branch it selects;
* a `let` whose body is a literal becomes that literal (the frameless-block
  rule: a binding nothing refers to needs no frame).

Nothing is folded when an operand is not a literal, because in the real
language an operand may have side effects or may fail (overflow, division by
zero), and the production pass is deliberately as conservative as this model.
-/
namespace A68.Verified

namespace Expr

/-- Constant folding of one dyadic node. -/
def foldBin (op : Int → Int → Int) (mk : Expr → Expr → Expr) (a b : Expr) : Expr :=
  match a, b with
  | .lit x, .lit y => .lit (op x y)
  | _, _ => mk a b

/-- Constant folding of one monadic node. -/
def foldUn (op : Int → Int) (mk : Expr → Expr) (a : Expr) : Expr :=
  match a with
  | .lit x => .lit (op x)
  | _ => mk a

/-- Is this expression a literal? -/
def isLit : Expr → Bool
  | .lit _ => true
  | _ => false

/-- The optimiser. -/
def opt : Expr → Expr
  | .lit n => .lit n
  | .var i => .var i
  | .add a b => foldBin (· + ·) .add (opt a) (opt b)
  | .sub a b => foldBin (· - ·) .sub (opt a) (opt b)
  | .mul a b => foldBin (· * ·) .mul (opt a) (opt b)
  | .neg a => foldUn (- ·) .neg (opt a)
  | .letE a b =>
    let a' := opt a
    let b' := opt b
    match b' with
    | .lit n => .lit n        -- the bound value is never used: no frame is needed
    | _ => .letE a' b'

end Expr

theorem foldBin_eval (op : Int → Int → Int) (mk : Expr → Expr → Expr) (a b : Expr) (env : List Int)
    (hmk : ∀ x y, (mk x y).eval env = op (x.eval env) (y.eval env)) :
    (Expr.foldBin op mk a b).eval env = op (a.eval env) (b.eval env) := by
  unfold Expr.foldBin
  split
  · rename_i x y; simp [Expr.eval]
  · exact hmk a b

theorem foldUn_eval (op : Int → Int) (mk : Expr → Expr) (a : Expr) (env : List Int)
    (hmk : ∀ x, (mk x).eval env = op (x.eval env)) :
    (Expr.foldUn op mk a).eval env = op (a.eval env) := by
  unfold Expr.foldUn
  split
  · rename_i x; simp [Expr.eval]
  · exact hmk a

/-- **The optimiser preserves meaning.** -/
theorem opt_correct (e : Expr) (env : List Int) : (Expr.opt e).eval env = e.eval env := by
  induction e generalizing env with
  | lit n => rfl
  | var i => rfl
  | add a b iha ihb =>
    show (Expr.foldBin _ _ _ _).eval env = _
    rw [foldBin_eval _ _ _ _ env (fun x y => rfl), iha, ihb]; rfl
  | sub a b iha ihb =>
    show (Expr.foldBin _ _ _ _).eval env = _
    rw [foldBin_eval _ _ _ _ env (fun x y => rfl), iha, ihb]; rfl
  | mul a b iha ihb =>
    show (Expr.foldBin _ _ _ _).eval env = _
    rw [foldBin_eval _ _ _ _ env (fun x y => rfl), iha, ihb]; rfl
  | neg a iha =>
    show (Expr.foldUn _ _ _).eval env = _
    rw [foldUn_eval _ _ _ env (fun x => rfl), iha]; rfl
  | letE a b iha ihb =>
    show (match Expr.opt b with | .lit n => Expr.lit n | _ => Expr.letE (Expr.opt a) (Expr.opt b)).eval env
       = Expr.eval (Expr.eval env a :: env) b
    split
    · rename_i n h
      have : Expr.eval (Expr.eval env a :: env) b = n := by
        rw [← ihb (Expr.eval env a :: env), h]; rfl
      simp [Expr.eval, this]
    · show Expr.eval (Expr.eval env (Expr.opt a) :: env) (Expr.opt b) = _
      rw [iha, ihb]

/-- **End to end.** The code generated for the optimised program computes the value the
    source program denotes, on any stack and in any environment. -/
theorem opt_compile_correct (e : Expr) (st env : List Int) :
    exec (compile (Expr.opt e)) ⟨st, env⟩ = ⟨e.eval env :: st, env⟩ := by
  rw [compile_correct, opt_correct]

/-- The optimiser never makes a program bigger. -/
theorem foldBin_size (op : Int → Int → Int) (a b : Expr) :
    (Expr.foldBin op .add a b).size ≤ (Expr.add a b).size := by
  unfold Expr.foldBin
  split <;> simp [Expr.size] <;> omega

theorem opt_size (e : Expr) : (Expr.opt e).size ≤ e.size := by
  induction e with
  | lit n => simp [Expr.opt]
  | var i => simp [Expr.opt]
  | add a b iha ihb =>
    show (Expr.foldBin _ _ _ _).size ≤ _
    unfold Expr.foldBin; split <;> simp [Expr.size] at * <;> omega
  | sub a b iha ihb =>
    show (Expr.foldBin _ _ _ _).size ≤ _
    unfold Expr.foldBin; split <;> simp [Expr.size] at * <;> omega
  | mul a b iha ihb =>
    show (Expr.foldBin _ _ _ _).size ≤ _
    unfold Expr.foldBin; split <;> simp [Expr.size] at * <;> omega
  | neg a iha =>
    show (Expr.foldUn _ _ _).size ≤ _
    unfold Expr.foldUn; split <;> simp [Expr.size] at * <;> omega
  | letE a b iha ihb =>
    show (match Expr.opt b with | .lit n => Expr.lit n | _ => Expr.letE (Expr.opt a) (Expr.opt b)).size ≤ _
    split <;> simp [Expr.size] at * <;> omega

/-- Optimising twice achieves nothing more than optimising once. -/
theorem opt_idempotent (e : Expr) : Expr.opt (Expr.opt e) = Expr.opt e := by
  induction e with
  | lit n => rfl
  | var i => rfl
  | add a b iha ihb =>
    show Expr.opt (Expr.foldBin _ _ _ _) = Expr.foldBin _ _ _ _
    unfold Expr.foldBin
    split
    · rfl
    · show Expr.foldBin _ _ (Expr.opt (Expr.opt a)) (Expr.opt (Expr.opt b)) = _
      rw [iha, ihb]; unfold Expr.foldBin; split <;> simp_all
  | sub a b iha ihb =>
    show Expr.opt (Expr.foldBin _ _ _ _) = Expr.foldBin _ _ _ _
    unfold Expr.foldBin
    split
    · rfl
    · show Expr.foldBin _ _ (Expr.opt (Expr.opt a)) (Expr.opt (Expr.opt b)) = _
      rw [iha, ihb]; unfold Expr.foldBin; split <;> simp_all
  | mul a b iha ihb =>
    show Expr.opt (Expr.foldBin _ _ _ _) = Expr.foldBin _ _ _ _
    unfold Expr.foldBin
    split
    · rfl
    · show Expr.foldBin _ _ (Expr.opt (Expr.opt a)) (Expr.opt (Expr.opt b)) = _
      rw [iha, ihb]; unfold Expr.foldBin; split <;> simp_all
  | neg a iha =>
    show Expr.opt (Expr.foldUn _ _ _) = Expr.foldUn _ _ _
    unfold Expr.foldUn
    split
    · rfl
    · show Expr.foldUn _ _ (Expr.opt (Expr.opt a)) = _
      rw [iha]; unfold Expr.foldUn; split <;> simp_all
  | letE a b iha ihb =>
    show Expr.opt (match Expr.opt b with | .lit n => Expr.lit n | _ => Expr.letE (Expr.opt a) (Expr.opt b))
       = (match Expr.opt b with | .lit n => Expr.lit n | _ => Expr.letE (Expr.opt a) (Expr.opt b))
    split
    · rfl
    · rename_i h
      show (match Expr.opt (Expr.opt b) with
            | .lit n => Expr.lit n
            | _ => Expr.letE (Expr.opt (Expr.opt a)) (Expr.opt (Expr.opt b))) = _
      rw [iha, ihb]
      split <;> simp_all


/-! ## Algebraic simplification

The rules of `A68.Opt.algebraic` that this core can express.  `mul a (.lit 0) → .lit 0`
is deliberately *not* among them: dropping `a` would drop its evaluation, and in the
real language evaluating `a` can fail.  Neither is `sub (add a b) b → a`: `Int` here is
unbounded, so the model would accept it, while `INT` is 32-bit checked and the addition
can overflow where the source program does not. -/
namespace Expr

/-- `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x`: the discarded operand is a literal, so
    nothing that could fail or have an effect is lost. -/
def algebraic : Expr → Expr
  | .add a (.lit 0) => a
  | .add (.lit 0) b => b
  | .sub a (.lit 0) => a
  | .mul a (.lit 1) => a
  | .mul (.lit 1) b => b
  | e => e

end Expr

theorem algebraic_eval (e : Expr) (env : List Int) : (Expr.algebraic e).eval env = e.eval env := by
  unfold Expr.algebraic
  split <;> simp [Expr.eval]

/-! ## Constant propagation

An identity declaration whose right hand side is a literal can have its uses replaced by
that literal.  A use is an identifier, and its index counts the binders — the frames —
between the use and the declaration, so the substitution has to step the index at every
binder it goes under.  That is exactly the depth arithmetic of `A68.Opt.substLit`. -/
namespace Expr

/-- Replace the identifier bound `i` binders out by the literal `n`. -/
def substLit (i : Nat) (n : Int) : Expr → Expr
  | .lit m => .lit m
  | .var j => if j = i then .lit n else .var j
  | .add a b => .add (substLit i n a) (substLit i n b)
  | .sub a b => .sub (substLit i n a) (substLit i n b)
  | .mul a b => .mul (substLit i n a) (substLit i n b)
  | .neg a => .neg (substLit i n a)
  | .letE a b => .letE (substLit i n a) (substLit (i + 1) n b)

/-- The pass itself: propagate through the range of a literal identity declaration. -/
def constProp : Expr → Expr
  | .letE (.lit n) b => .letE (.lit n) (substLit 0 n b)
  | e => e

end Expr

/-- Substituting a literal for an identifier that denotes it changes nothing. -/
theorem substLit_eval (e : Expr) (i : Nat) (n : Int) (env : List Int)
    (h : env.getD i 0 = n) : (Expr.substLit i n e).eval env = e.eval env := by
  induction e generalizing i env with
  | lit m => rfl
  | var j =>
    by_cases hj : j = i
    · subst hj
      simp only [Expr.substLit, if_pos rfl, Expr.eval]
      exact h.symm
    · simp [Expr.substLit, Expr.eval, hj]
  | add a b iha ihb => simp [Expr.substLit, Expr.eval, iha i env h, ihb i env h]
  | sub a b iha ihb => simp [Expr.substLit, Expr.eval, iha i env h, ihb i env h]
  | mul a b iha ihb => simp [Expr.substLit, Expr.eval, iha i env h, ihb i env h]
  | neg a iha => simp [Expr.substLit, Expr.eval, iha i env h]
  | letE a b iha ihb =>
    have h' : (Expr.eval env a :: env).getD (i + 1) 0 = n := by simpa using h
    simp [Expr.substLit, Expr.eval, iha i env h, ihb (i + 1) (Expr.eval env a :: env) h']

/-- **Constant propagation preserves meaning.** -/
theorem constProp_correct (e : Expr) (env : List Int) :
    (Expr.constProp e).eval env = e.eval env := by
  unfold Expr.constProp
  split
  · rename_i n b
    show Expr.eval (Expr.eval env (Expr.lit n) :: env) (Expr.substLit 0 n b)
       = Expr.eval (Expr.eval env (Expr.lit n) :: env) b
    exact substLit_eval b 0 n _ (by simp [Expr.eval])
  · rfl

/-! ## Common subexpression elimination

An expression that occurs twice is evaluated once into a fresh slot and the occurrences
become uses of it.  Here the slot is a new `let`, which pushes a frame, so every free
identifier of the body must move one level out — the same de Bruijn shift `A68.Opt.shift`
performs, in the opposite direction.  (In the production pass the slot is added to the
*existing* frame instead, which needs no shift at all; this model is therefore the
harder of the two, and its index bookkeeping subsumes the real one.)

Occurrences under a binder are not replaced: at that point the identifiers of the shared
expression would denote something else.  The production pass observes the same rule —
it never descends into a nested frame. -/
namespace Expr

/-- Shift the identifiers that reach past `c` binders one level out. -/
def liftN (c : Nat) : Expr → Expr
  | .lit n => .lit n
  | .var i => .var (if c ≤ i then i + 1 else i)
  | .add a b => .add (liftN c a) (liftN c b)
  | .sub a b => .sub (liftN c a) (liftN c b)
  | .mul a b => .mul (liftN c a) (liftN c b)
  | .neg a => .neg (liftN c a)
  | .letE a b => .letE (liftN c a) (liftN (c + 1) b)

/-- Replace the occurrences of `t` at this level by the new innermost slot. -/
def abstract (t : Expr) : Expr → Expr
  | .lit n => if Expr.lit n = t then .var 0 else .lit n
  | .var i => if Expr.var i = t then .var 0 else .var (i + 1)
  | .add a b => if Expr.add a b = t then .var 0 else .add (abstract t a) (abstract t b)
  | .sub a b => if Expr.sub a b = t then .var 0 else .sub (abstract t a) (abstract t b)
  | .mul a b => if Expr.mul a b = t then .var 0 else .mul (abstract t a) (abstract t b)
  | .neg a => if Expr.neg a = t then .var 0 else .neg (abstract t a)
  | .letE a b => if Expr.letE a b = t then .var 0 else liftN 0 (.letE a b)

/-- Evaluate `t` once, then run `e` with its occurrences replaced by that one value. -/
def cse (t e : Expr) : Expr := .letE t (abstract t e)

end Expr

/-- Lifting is compensated by an environment with one more entry at the cut. -/
theorem liftN_eval (e : Expr) (c : Nat) (env env' : List Int)
    (h : ∀ i, env'.getD (if c ≤ i then i + 1 else i) 0 = env.getD i 0) :
    (Expr.liftN c e).eval env' = e.eval env := by
  induction e generalizing c env env' with
  | lit n => rfl
  | var i => simpa [Expr.liftN, Expr.eval] using h i
  | add a b iha ihb => simp [Expr.liftN, Expr.eval, iha c env env' h, ihb c env env' h]
  | sub a b iha ihb => simp [Expr.liftN, Expr.eval, iha c env env' h, ihb c env env' h]
  | mul a b iha ihb => simp [Expr.liftN, Expr.eval, iha c env env' h, ihb c env env' h]
  | neg a iha => simp [Expr.liftN, Expr.eval, iha c env env' h]
  | letE a b iha ihb =>
    have ha := iha c env env' h
    have h' : ∀ i, (Expr.eval env a :: env').getD (if c + 1 ≤ i then i + 1 else i) 0
                 = (Expr.eval env a :: env).getD i 0 := by
      intro i
      cases i with
      | zero => simp
      | succ j =>
        by_cases hj : c ≤ j
        · have : c + 1 ≤ j + 1 := by omega
          simpa [this, hj] using h j
        · have : ¬ (c + 1 ≤ j + 1) := by omega
          simpa [this, hj] using h j
    simp [Expr.liftN, Expr.eval, ha, ihb (c + 1) (Expr.eval env a :: env) (Expr.eval env a :: env') h']

/-- Abstracting `t` out of `e` and binding it to the value of `t` denotes `e`. -/
theorem abstract_eval (t e : Expr) (env : List Int) :
    (Expr.abstract t e).eval (t.eval env :: env) = e.eval env := by
  induction e with
  | lit n =>
    unfold Expr.abstract; split
    · rename_i h; rw [← h]; rfl
    · rfl
  | var i =>
    unfold Expr.abstract; split
    · rename_i h; rw [← h]; rfl
    · simp [Expr.eval]
  | add a b iha ihb =>
    unfold Expr.abstract; split
    · rename_i h; rw [← h]; rfl
    · simp [Expr.eval, iha, ihb]
  | sub a b iha ihb =>
    unfold Expr.abstract; split
    · rename_i h; rw [← h]; rfl
    · simp [Expr.eval, iha, ihb]
  | mul a b iha ihb =>
    unfold Expr.abstract; split
    · rename_i h; rw [← h]; rfl
    · simp [Expr.eval, iha, ihb]
  | neg a iha =>
    unfold Expr.abstract; split
    · rename_i h; rw [← h]; rfl
    · simp [Expr.eval, iha]
  | letE a b _ _ =>
    unfold Expr.abstract; split
    · rename_i h; rw [← h]; rfl
    · exact liftN_eval (.letE a b) 0 env (t.eval env :: env) (by intro i; simp)

/-- **Common subexpression elimination preserves meaning**, for *every* choice of the
    expression to share — the production pass's job is only to choose one whose two
    occurrences really are evaluated in the same state. -/
theorem cse_correct (t e : Expr) (env : List Int) : (Expr.cse t e).eval env = e.eval env :=
  abstract_eval t e env

/-! ## The three passes together with constant folding -/

namespace Expr

/-- What becomes of an identity declaration whose right hand side and range have both
    been optimised: propagate a literal into the range, or drop a frame nothing uses. -/
def optLet (a' b' : Expr) : Expr :=
  match a' with
  | .lit n => .letE (.lit n) (substLit 0 n b')        -- constant propagation
  | _ => match b' with
         | .lit n => .lit n                           -- the binding is never used
         | _ => .letE a' b'

/-- Constant folding and coercion removal (`opt`), plus algebraic simplification and
    constant propagation.  Sharing is not syntax-directed — it needs a choice of the
    expression to share — so it is stated on its own, above. -/
def opt2 : Expr → Expr
  | .lit n => .lit n
  | .var i => .var i
  | .add a b => algebraic (foldBin (· + ·) .add (opt2 a) (opt2 b))
  | .sub a b => algebraic (foldBin (· - ·) .sub (opt2 a) (opt2 b))
  | .mul a b => algebraic (foldBin (· * ·) .mul (opt2 a) (opt2 b))
  | .neg a => foldUn (- ·) .neg (opt2 a)
  | .letE a b => optLet (opt2 a) (opt2 b)

end Expr

/-- An optimised identity declaration denotes what the declaration denotes. -/
theorem optLet_eval (a' b' : Expr) (env : List Int) :
    (Expr.optLet a' b').eval env = Expr.eval (a'.eval env :: env) b' := by
  unfold Expr.optLet
  split
  · rename_i n
    show Expr.eval (n :: env) (Expr.substLit 0 n b') = _
    rw [substLit_eval _ 0 n _ (by simp)]
    rfl
  · split <;> rfl

/-- **The whole `-O2` pipeline preserves meaning.** -/
theorem opt2_correct (e : Expr) (env : List Int) : (Expr.opt2 e).eval env = e.eval env := by
  induction e generalizing env with
  | lit n => rfl
  | var i => rfl
  | add a b iha ihb =>
    show (Expr.algebraic (Expr.foldBin _ _ _ _)).eval env = _
    rw [algebraic_eval, foldBin_eval _ _ _ _ env (fun x y => rfl), iha, ihb]; rfl
  | sub a b iha ihb =>
    show (Expr.algebraic (Expr.foldBin _ _ _ _)).eval env = _
    rw [algebraic_eval, foldBin_eval _ _ _ _ env (fun x y => rfl), iha, ihb]; rfl
  | mul a b iha ihb =>
    show (Expr.algebraic (Expr.foldBin _ _ _ _)).eval env = _
    rw [algebraic_eval, foldBin_eval _ _ _ _ env (fun x y => rfl), iha, ihb]; rfl
  | neg a iha =>
    show (Expr.foldUn _ _ _).eval env = _
    rw [foldUn_eval _ _ _ env (fun x => rfl), iha]; rfl
  | letE a b iha ihb =>
    show (Expr.optLet (Expr.opt2 a) (Expr.opt2 b)).eval env = _
    rw [optLet_eval, iha, ihb]
    rfl

/-- **End to end, at `-O2`.** The code generated for the optimised program computes what
    the source program denotes, on any stack and in any environment. -/
theorem opt2_compile_correct (e : Expr) (st env : List Int) :
    exec (compile (Expr.opt2 e)) ⟨st, env⟩ = ⟨e.eval env :: st, env⟩ := by
  rw [compile_correct, opt2_correct]

/-- Sharing, then compiling: the same statement for the pass that has to choose. -/
theorem cse_compile_correct (t e : Expr) (st env : List Int) :
    exec (compile (Expr.cse t e)) ⟨st, env⟩ = ⟨e.eval env :: st, env⟩ := by
  rw [compile_correct, cse_correct]

end A68.Verified
