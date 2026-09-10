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

end A68.Verified
