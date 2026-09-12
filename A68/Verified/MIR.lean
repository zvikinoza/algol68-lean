import A68.MIR.Opt

/-!
# A68.Verified.MIR — the MIR optimisations, proved correct

For every pass `P` of `A68.MIR.Opt`, for every runtime, runtime state and fuel,
`run rt fuel (P f) r = run rt fuel f r`: the optimised function makes the same calls
with the same arguments, reaches the same lines, and ends the same way — returned,
trapped, aborted or out of fuel — as the function it came from.  Fuel counts block
transitions and no pass changes the blocks a run passes through, so the equalities are
exact rather than refinements.

All definitions are total and structural and the proofs use no axioms beyond the
standard ones (`propext`, `Quot.sound`, `Classical.choice`).

Not proved, and not needed for the correctness statements: that `Opt.reachable` is
closed under successors (the pass checks it and keeps the function unchanged otherwise),
and that any pass makes a function smaller or faster.
-/
namespace A68.Verified.MIR
open A68.MIR A68.MIR.Sem

variable {R : Type} (rt : Runtime R)

/-! ## A pass that rewrites every block independently

Copy propagation, constant folding and branch folding change nothing but the contents
of each block, and each rewritten block executes exactly as the original does; that
suffices for the whole function. -/

/-- Running a function whose blocks are rewritten one by one, when each rewritten block
    executes as the original does, runs as the original does. -/
theorem runFrom_map (g : Block → Block) (hg : ∀ blk (s : State R), stepBlock rt (g blk) s = stepBlock rt blk s)
    (f : Func) : ∀ (fuel b : Nat) (s : State R),
      runFrom rt { f with blocks := f.blocks.map g } fuel b s = runFrom rt f fuel b s := by
  intro fuel
  induction fuel with
  | zero => intro b s; rfl
  | succ fuel ih =>
    intro b s
    simp only [runFrom, Array.getElem?_map]
    cases f.blocks[b]? with
    | none => rfl
    | some blk =>
      simp only [Option.map_some, hg]
      cases stepBlock rt blk s with
      | stop tr st => rfl
      | next b' s' => exact ih b' s'

theorem run_map (g : Block → Block) (hg : ∀ blk (s : State R), stepBlock rt (g blk) s = stepBlock rt blk s)
    (fuel : Nat) (f : Func) (r : R) : run rt fuel { f with blocks := f.blocks.map g } r = run rt fuel f r :=
  runFrom_map rt g hg f fuel 0 _

/-! ## Constant folding -/

/-- The constant of a value that fits the type denotes the value. -/
theorem constVal_valToConst (ty : Ty) (v : Val) (h : Opt.valFits ty v = true) :
    constVal ty (Opt.valToConst v) = v := by
  cases ty <;> cases v <;> simp [Opt.valFits] at h <;> first | rfl | (rename_i t; cases t <;> rfl)

/-- What a monadic operation computes without the mathematical functions, it computes
    with any of them. -/
theorem unSem_noMath (m : MathFns) (op : UnOp) (v w : Val) (h : unSem noMath op v = some w) :
    unSem m op v = some w := by
  cases op <;> cases v <;> simp_all [unSem, noMath]

/-- A folded right-hand side denotes what the original does. -/
theorem evalRhs_foldRhs (m : MathFns) (env : Env) (d : Var) (r : Rhs) :
    evalRhs m env (Opt.foldRhs d r) = evalRhs m env r := by
  cases r with
  | opnd o => rfl
  | call f args => rfl
  | natTab i => rfl
  | select c a b => rfl
  | bin op a b =>
    cases a <;> cases b <;> try rfl
    simp only [Opt.foldRhs]
    split
    · rename_i v hv
      split
      · rename_i hfit
        simp [evalRhs, evalOpnd, hv, constVal_valToConst _ _ hfit]
      · rfl
    · rfl
  | un op a =>
    cases a <;> try rfl
    simp only [Opt.foldRhs]
    split
    · rename_i v hv
      split
      · rename_i hfit
        simp [evalRhs, evalOpnd, unSem_noMath m _ _ _ hv, constVal_valToConst _ _ hfit]
      · rfl
    · rfl

/-- A folded instruction executes as the original does. -/
theorem execInstr_foldInstr (i : Instr) (s : State R) :
    execInstr rt (Opt.foldInstr i) s = execInstr rt i s := by
  cases i with
  | line n => rfl
  | call f args => rfl
  | set d r =>
    cases r with
    | opnd o => rfl
    | call f args => rfl
    | natTab i => rfl
    | select c a b => rfl
    | bin op a b =>
      simp only [Opt.foldInstr]
      cases a <;> cases b <;> try rfl
      simp only [Opt.foldRhs]
      split
      · rename_i v hv
        split
        · rename_i hfit
          simp [execInstr, evalRhs, evalOpnd, hv, constVal_valToConst _ _ hfit]
        · rfl
      · rfl
    | un op a =>
      simp only [Opt.foldInstr]
      cases a <;> try rfl
      simp only [Opt.foldRhs]
      split
      · rename_i v hv
        split
        · rename_i hfit
          simp [execInstr, evalRhs, evalOpnd, unSem_noMath rt.math _ _ _ hv, constVal_valToConst _ _ hfit]
        · rfl
      · rfl

/-- A block with folded instructions executes as the original does. -/
theorem execInstrs_map_foldInstr (is : List Instr) (s : State R) :
    execInstrs rt (is.map Opt.foldInstr) s = execInstrs rt is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map, execInstrs, execInstr_foldInstr]
    cases execInstr rt i s with
    | ok s' => exact ih s'
    | stop tr st => rfl

theorem stepBlock_foldBlock (blk : Block) (s : State R) :
    stepBlock rt (Opt.foldBlock blk) s = stepBlock rt blk s := by
  simp only [stepBlock, Opt.foldBlock, Array.toList_map, execInstrs_map_foldInstr]

/-- **Constant folding preserves behaviour.** -/
theorem constFold_correct (fuel : Nat) (f : Func) (r : R) :
    run rt fuel (Opt.constFold f) r = run rt fuel f r :=
  run_map rt Opt.foldBlock (stepBlock_foldBlock rt) fuel f r

/-! ## Branch folding -/

theorem stepBlock_foldBranchBlock (blk : Block) (s : State R) :
    stepBlock rt (Opt.foldBranchBlock blk) s = stepBlock rt blk s := by
  obtain ⟨is, t⟩ := blk
  simp only [stepBlock, Opt.foldBranchBlock]
  cases execInstrs rt is.toList s with
  | stop tr st => rfl
  | ok s' =>
    cases t with
    | condBr c t f => cases c <;> rfl
    | switch o cs d => cases o <;> rfl
    | _ => rfl

/-- **Branch folding preserves behaviour.** -/
theorem foldBranches_correct (fuel : Nat) (f : Func) (r : R) :
    run rt fuel (Opt.foldBranches f) r = run rt fuel f r :=
  run_map rt Opt.foldBranchBlock (stepBlock_foldBranchBlock rt) fuel f r

/-! ## Copy propagation

The copies in force are sound in an environment when every recorded variable reads as
the operand it was copied from; the pass keeps that invariant across every instruction
of a block, and substituting under it changes no value. -/

/-- The recorded copies hold in the environment. -/
def CopiesValid (env : Env) (m : Opt.Copies) : Prop :=
  ∀ e ∈ m, evalOpnd env (.v e.1) = evalOpnd env e.2

/-- Coercing to a type twice is coercing once. -/
theorem coerceTo_idem (ty : Ty) (v : Val) : coerceTo ty (coerceTo ty v) = coerceTo ty v := by
  cases ty <;> cases v <;> rfl

/-- An operand's value is already of the operand's type. -/
theorem coerceTo_evalOpnd (env : Env) (o : Opnd) : coerceTo o.ty (evalOpnd env o) = evalOpnd env o := by
  cases o <;> simp [evalOpnd, constVal, Opnd.ty, coerceTo_idem]

/-- Assigning a variable an operand does not read leaves the operand's value alone. -/
theorem evalOpnd_set_of_not_read (env : Env) (id : Nat) (v : Val) (o : Opnd)
    (h : ¬ (Opt.opndReads o).contains id) : evalOpnd (env.set id v) o = evalOpnd env o := by
  cases o with
  | k ty c => rfl
  | v x =>
    have hne : x.id ≠ id := by
      intro heq; apply h; simp [Opt.opndReads, heq]
    simp [evalOpnd, Env.set, hne]

/-- Substituting a valid copy for a use gives the same value. -/
theorem evalOpnd_substOpnd (env : Env) (m : Opt.Copies) (h : CopiesValid env m) (o : Opnd) :
    evalOpnd env (Opt.substOpnd m o) = evalOpnd env o := by
  cases o with
  | k ty c => rfl
  | v x =>
    simp only [Opt.substOpnd]
    split
    · rename_i e he
      have hm := List.mem_of_find?_eq_some he
      have hp0 := List.find?_some he
      have hp : e.1.id = x.id ∧ e.1.ty = x.ty := of_decide_eq_true hp0
      rw [← h e hm]
      simp [evalOpnd, hp.1, hp.2]
    · rfl

theorem evalRhs_substRhs (mf : MathFns) (env : Env) (m : Opt.Copies) (h : CopiesValid env m) (r : Rhs) :
    evalRhs mf env (Opt.substRhs m r) = evalRhs mf env r := by
  cases r <;> simp [Opt.substRhs, evalRhs, evalOpnd_substOpnd env m h]

theorem execCall_subst (f : Callee) (args : Array Opnd) (s : State R) (m : Opt.Copies)
    (h : CopiesValid s.env m) :
    execCall rt f (args.map (Opt.substOpnd m)) s = execCall rt f args s := by
  have hargs : List.map (evalOpnd s.env ∘ Opt.substOpnd m) args.toList = List.map (evalOpnd s.env) args.toList :=
    List.map_congr_left (fun o _ => evalOpnd_substOpnd s.env m h o)
  simp only [execCall, Array.toList_map, List.map_map, hargs]

/-- Assigning a variable keeps the copies that mention neither it nor its source. -/
theorem copiesValid_killVar (env : Env) (m : Opt.Copies) (h : CopiesValid env m) (id : Nat) (v : Val) :
    CopiesValid (env.set id v) (Opt.killVar id m) := by
  intro e he
  simp only [Opt.killVar, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he
  obtain ⟨hm, hne, hread⟩ := he
  have h1 : evalOpnd (env.set id v) e.2 = evalOpnd env e.2 :=
    evalOpnd_set_of_not_read env id v e.2 (by simpa using hread)
  have h2 : evalOpnd (env.set id v) (.v e.1) = evalOpnd env (.v e.1) := by
    simp [evalOpnd, Env.set, hne]
  rw [h1, h2]
  exact h e hm

/-- After `set d y` the copy `d ↦ y` holds, when `y` has `d`'s type and does not read `d`. -/
theorem copiesValid_addCopy (env : Env) (m : Opt.Copies) (d : Var) (rhs : Rhs) (v : Val)
    (hm : CopiesValid (env.set d.id v) m)
    (hv : ∀ y, rhs = .opnd y → v = evalOpnd env y) :
    CopiesValid (env.set d.id v) (Opt.addCopy d rhs m) := by
  cases rhs with
  | opnd y =>
    simp only [Opt.addCopy]
    split
    · rename_i hc
      obtain ⟨hty, hread⟩ := hc
      intro e he
      rw [List.mem_cons] at he
      rcases he with rfl | he
      · have h1 : evalOpnd (env.set d.id v) y = evalOpnd env y :=
          evalOpnd_set_of_not_read env d.id v y (by simpa using hread)
        rw [h1, hv y rfl]
        simp only [evalOpnd, Env.set, if_true]
        rw [← hty]
        exact coerceTo_evalOpnd env y
      · exact hm e he
    · exact hm
  | bin op a b => exact hm
  | un op a => exact hm
  | call f args => exact hm
  | natTab i => exact hm
  | select c a b => exact hm

/-- A call leaves the variables alone. -/
theorem execCall_env (f : Callee) (args : Array Opnd) (s s' : State R) (ret : Option Val)
    (h : execCall rt f args s = some (s', ret)) : s'.env = s.env := by
  simp only [execCall] at h
  split at h
  · cases h
  · cases h; rfl

/-- Every assignment ends with the target set to some value. -/
theorem execInstr_set_ok (d : Var) (rhs : Rhs) (s s' : State R)
    (h : execInstr rt (.set d rhs) s = .ok s') : ∃ v, s'.env = s.env.set d.id v := by
  cases rhs with
  | call f args =>
    simp only [execInstr] at h
    split at h
    · cases h
    · rename_i s₁ ret hc
      cases h
      refine ⟨ret.getD (.i 0), ?_⟩
      show s₁.env.set d.id _ = s.env.set d.id _
      rw [execCall_env rt f args s s₁ ret hc]
  | opnd o =>
    simp only [execInstr, evalRhs] at h
    cases h; exact ⟨_, rfl⟩
  | natTab i =>
    simp only [execInstr, evalRhs] at h
    cases h; exact ⟨_, rfl⟩
  | select c a b =>
    simp only [execInstr, evalRhs] at h
    cases h; exact ⟨_, rfl⟩
  | bin op a b =>
    simp only [execInstr] at h
    split at h
    · cases h
    · cases h; exact ⟨_, rfl⟩
  | un op a =>
    simp only [execInstr] at h
    split at h
    · cases h
    · cases h; exact ⟨_, rfl⟩

/-- An assignment with substituted operands executes as the original does. -/
theorem execInstr_set_subst (d : Var) (rhs : Rhs) (s : State R) (m : Opt.Copies) (h : CopiesValid s.env m) :
    execInstr rt (.set d (Opt.substRhs m rhs)) s = execInstr rt (.set d rhs) s := by
  cases rhs with
  | call f args => simp only [Opt.substRhs, execInstr, execCall_subst rt f args s m h]
  | opnd o => simp only [Opt.substRhs, execInstr, evalRhs, evalOpnd_substOpnd s.env m h]
  | bin op a b => simp only [Opt.substRhs, execInstr, evalRhs, evalOpnd_substOpnd s.env m h]
  | un op a => simp only [Opt.substRhs, execInstr, evalRhs, evalOpnd_substOpnd s.env m h]
  | natTab i => simp only [Opt.substRhs, execInstr, evalRhs, evalOpnd_substOpnd s.env m h]
  | select c a b => simp only [Opt.substRhs, execInstr, evalRhs, evalOpnd_substOpnd s.env m h]

/-- **Copy propagation within a block**: the propagated instructions execute as the
    originals do, and the copies in force at the end hold in the final environment. -/
theorem copyPropInstrs_correct (is : List Instr) : ∀ (m : Opt.Copies) (s : State R), CopiesValid s.env m →
    execInstrs rt (Opt.copyPropInstrs m is).1 s = execInstrs rt is s ∧
    ∀ s', execInstrs rt is s = .ok s' → CopiesValid s'.env (Opt.copyPropInstrs m is).2 := by
  induction is with
  | nil =>
    intro m s h
    refine ⟨rfl, fun s' hs' => ?_⟩
    simp only [execInstrs] at hs'
    cases hs'; exact h
  | cons i is ih =>
    intro m s h
    cases i with
    | line n =>
      simp only [Opt.copyPropInstrs, execInstrs, execInstr]
      exact ih m _ h
    | call f args =>
      simp only [Opt.copyPropInstrs, execInstrs, execInstr, execCall_subst rt f args s m h]
      cases hc : execCall rt f args s with
      | none => simp
      | some p =>
        obtain ⟨s₁, ret⟩ := p
        have henv : s₁.env = s.env := execCall_env rt f args s s₁ ret hc
        exact ih m s₁ (by rw [henv]; exact h)
    | set d rhs =>
      simp only [Opt.copyPropInstrs, execInstrs, execInstr_set_subst rt d rhs s m h]
      cases hx : execInstr rt (.set d rhs) s with
      | stop tr st => simp
      | ok s₁ =>
        obtain ⟨v, hv⟩ := execInstr_set_ok rt d rhs s s₁ hx
        have hval : CopiesValid s₁.env (Opt.addCopy d (Opt.substRhs m rhs) (Opt.killVar d.id m)) := by
          rw [hv]
          apply copiesValid_addCopy
          · exact copiesValid_killVar s.env m h d.id v
          · intro y hy
            cases rhs with
            | opnd o =>
              simp only [Opt.substRhs, Rhs.opnd.injEq] at hy
              subst hy
              simp only [execInstr, evalRhs, Res.ok.injEq] at hx
              subst hx
              have hd := congrFun hv d.id
              simp [Env.set] at hd
              rw [evalOpnd_substOpnd s.env m h o]
              exact hd.symm
            | bin op a b => simp [Opt.substRhs] at hy
            | un op a => simp [Opt.substRhs] at hy
            | call f args => simp [Opt.substRhs] at hy
            | natTab i => simp [Opt.substRhs] at hy
            | select c a b => simp [Opt.substRhs] at hy
        exact ih _ s₁ hval

/-- A propagated block executes as the original does. -/
theorem stepBlock_copyPropBlock (blk : Block) (s : State R) :
    stepBlock rt (Opt.copyPropBlock blk) s = stepBlock rt blk s := by
  obtain ⟨is, t⟩ := blk
  have hnil : CopiesValid s.env [] := fun e he => by cases he
  obtain ⟨h1, h2⟩ := copyPropInstrs_correct rt is.toList [] s hnil
  simp only [stepBlock, Opt.copyPropBlock, List.toList_toArray, h1]
  cases hx : execInstrs rt is.toList s with
  | stop tr st => rfl
  | ok s' =>
    have hv := h2 s' hx
    cases t with
    | condBr c t f => simp [Opt.substTerm, evalOpnd_substOpnd s'.env _ hv]
    | switch o cs d => simp [Opt.substTerm, evalOpnd_substOpnd s'.env _ hv]
    | retVal o => simp [Opt.substTerm, evalOpnd_substOpnd s'.env _ hv]
    | _ => rfl

/-- **Copy propagation preserves behaviour.** -/
theorem copyProp_correct (fuel : Nat) (f : Func) (r : R) :
    run rt fuel (Opt.copyProp f) r = run rt fuel f r :=
  run_map rt Opt.copyPropBlock (stepBlock_copyPropBlock rt) fuel f r

/-! ## Dead assignment elimination

The optimised function and the original run in lock step with environments that agree
on every variable that is not dead; since no operand reads a dead variable — which the
pass checks — every value computed, every call made and every branch taken is the same. -/

/-- Environments that agree outside the dead variables. -/
def EnvEq (dead : Nat → Bool) (e₁ e₂ : Env) : Prop := ∀ id, dead id = false → e₁ id = e₂ id

def StateEq (dead : Nat → Bool) (s₁ s₂ : State R) : Prop :=
  EnvEq dead s₁.env s₂.env ∧ s₁.rt = s₂.rt ∧ s₁.trace = s₂.trace

def ResEq (dead : Nat → Bool) : Res R → Res R → Prop
  | .ok s₁, .ok s₂ => StateEq dead s₁ s₂
  | .stop tr₁ st₁, .stop tr₂ st₂ => tr₁ = tr₂ ∧ st₁ = st₂
  | _, _ => False

def OutEq (dead : Nat → Bool) : BlockOut R → BlockOut R → Prop
  | .next b₁ s₁, .next b₂ s₂ => b₁ = b₂ ∧ StateEq dead s₁ s₂
  | .stop tr₁ st₁, .stop tr₂ st₂ => tr₁ = tr₂ ∧ st₁ = st₂
  | _, _ => False

theorem envEq_set (dead : Nat → Bool) (e₁ e₂ : Env) (h : EnvEq dead e₁ e₂) (id : Nat) (v : Val) :
    EnvEq dead (e₁.set id v) (e₂.set id v) := by
  intro j hj
  simp only [Env.set]
  split
  · rfl
  · exact h j hj

/-- Assigning a dead variable on one side only keeps the environments in agreement. -/
theorem envEq_set_dead (dead : Nat → Bool) (e₁ e₂ : Env) (h : EnvEq dead e₁ e₂) (id : Nat)
    (hd : dead id = true) (v : Val) : EnvEq dead e₁ (e₂.set id v) := by
  intro j hj
  have hne : j ≠ id := by intro heq; rw [heq, hd] at hj; cases hj
  simp only [Env.set, hne, if_false]
  exact h j hj

theorem evalOpnd_envEq (dead : Nat → Bool) (e₁ e₂ : Env) (h : EnvEq dead e₁ e₂) (o : Opnd)
    (ho : Opt.opndNoDead dead o = true) : evalOpnd e₁ o = evalOpnd e₂ o := by
  cases o with
  | k ty c => rfl
  | v x =>
    simp only [Opt.opndNoDead, Bool.not_eq_true'] at ho
    simp [evalOpnd, h x.id ho]

theorem evalRhs_envEq (mf : MathFns) (dead : Nat → Bool) (e₁ e₂ : Env) (h : EnvEq dead e₁ e₂) (r : Rhs)
    (hr : Opt.rhsNoDead dead r = true) : evalRhs mf e₁ r = evalRhs mf e₂ r := by
  cases r with
  | opnd o => simp [evalRhs, evalOpnd_envEq dead e₁ e₂ h o hr]
  | bin op a b =>
    simp only [Opt.rhsNoDead, Bool.and_eq_true] at hr
    simp [evalRhs, evalOpnd_envEq dead e₁ e₂ h a hr.1, evalOpnd_envEq dead e₁ e₂ h b hr.2]
  | un op a => simp [evalRhs, evalOpnd_envEq dead e₁ e₂ h a hr]
  | natTab i => simp [evalRhs, evalOpnd_envEq dead e₁ e₂ h i hr]
  | select c a b =>
    simp only [Opt.rhsNoDead, Bool.and_eq_true] at hr
    simp [evalRhs, evalOpnd_envEq dead e₁ e₂ h c hr.1.1, evalOpnd_envEq dead e₁ e₂ h a hr.1.2,
          evalOpnd_envEq dead e₁ e₂ h b hr.2]
  | call f args => rfl

theorem args_envEq (dead : Nat → Bool) (e₁ e₂ : Env) (h : EnvEq dead e₁ e₂) (args : Array Opnd)
    (ha : args.toList.all (Opt.opndNoDead dead) = true) :
    args.toList.map (evalOpnd e₁) = args.toList.map (evalOpnd e₂) :=
  List.map_congr_left fun o ho => evalOpnd_envEq dead e₁ e₂ h o (List.all_eq_true.mp ha o ho)

/-- A call from related states either aborts in both or returns the same result into
    related states. -/
theorem execCall_envEq (dead : Nat → Bool) (f : Callee) (args : Array Opnd) (s₁ s₂ : State R)
    (h : StateEq dead s₁ s₂) (ha : args.toList.all (Opt.opndNoDead dead) = true) :
    (execCall rt f args s₁ = none ∧ execCall rt f args s₂ = none) ∨
    ∃ s₁' s₂' ret, execCall rt f args s₁ = some (s₁', ret) ∧ execCall rt f args s₂ = some (s₂', ret) ∧
      StateEq dead s₁' s₂' := by
  obtain ⟨henv, hrt, htr⟩ := h
  simp only [execCall, args_envEq dead s₁.env s₂.env henv args ha, hrt, htr]
  cases rt.call f (args.toList.map (evalOpnd s₂.env)) s₂.rt with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some p => exact Or.inr ⟨_, _, p.2, rfl, rfl, henv, rfl, rfl⟩

/-- One instruction, from related states, gives related results. -/
theorem execInstr_envEq (dead : Nat → Bool) (i : Instr) (s₁ s₂ : State R) (h : StateEq dead s₁ s₂)
    (hi : Opt.instrNoDead dead i = true) : ResEq dead (execInstr rt i s₁) (execInstr rt i s₂) := by
  obtain ⟨henv, hrt, htr⟩ := h
  cases i with
  | line n => exact ⟨henv, hrt, by simp [htr]⟩
  | call f args =>
    rcases execCall_envEq rt dead f args s₁ s₂ ⟨henv, hrt, htr⟩ hi with ⟨h1, h2⟩ | ⟨s₁', s₂', ret, h1, h2, hs⟩
    · simp [execInstr, h1, h2, ResEq, htr]
    · simp only [execInstr, h1, h2]; exact hs
  | set d rhs =>
    cases rhs with
    | call f args =>
      rcases execCall_envEq rt dead f args s₁ s₂ ⟨henv, hrt, htr⟩ hi with ⟨h1, h2⟩ | ⟨s₁', s₂', ret, h1, h2, hs⟩
      · simp [execInstr, h1, h2, ResEq, htr]
      · simp only [execInstr, h1, h2]
        exact ⟨envEq_set dead _ _ hs.1 _ _, hs.2.1, hs.2.2⟩
    | opnd o =>
      simp only [execInstr, evalRhs]
      rw [evalOpnd_envEq dead _ _ henv o hi]
      exact ⟨envEq_set dead _ _ henv _ _, hrt, htr⟩
    | natTab i =>
      simp only [execInstr, evalRhs]
      rw [evalOpnd_envEq dead _ _ henv i hi]
      exact ⟨envEq_set dead _ _ henv _ _, hrt, htr⟩
    | select c a b =>
      simp only [execInstr, evalRhs_envEq rt.math dead s₁.env s₂.env henv (.select c a b) hi]
      cases evalRhs rt.math s₂.env (.select c a b) with
      | none => exact ⟨htr, rfl⟩
      | some v => exact ⟨envEq_set dead _ _ henv _ _, hrt, htr⟩
    | bin op a b =>
      simp only [execInstr, evalRhs_envEq rt.math dead s₁.env s₂.env henv (.bin op a b) hi]
      cases evalRhs rt.math s₂.env (.bin op a b) with
      | none => exact ⟨htr, rfl⟩
      | some v => exact ⟨envEq_set dead _ _ henv _ _, hrt, htr⟩
    | un op a =>
      simp only [execInstr, evalRhs_envEq rt.math dead s₁.env s₂.env henv (.un op a) hi]
      cases evalRhs rt.math s₂.env (.un op a) with
      | none => exact ⟨htr, rfl⟩
      | some v => exact ⟨envEq_set dead _ _ henv _ _, hrt, htr⟩

/-- Related first steps followed by related continuations give related results. -/
theorem execInstrs_cons_envEq (dead : Nat → Bool) (i : Instr) (is₁ is₂ : List Instr) (s₁ s₂ : State R)
    (h : ResEq dead (execInstr rt i s₁) (execInstr rt i s₂))
    (ih : ∀ s₁ s₂, StateEq dead s₁ s₂ → ResEq dead (execInstrs rt is₁ s₁) (execInstrs rt is₂ s₂)) :
    ResEq dead (execInstrs rt (i :: is₁) s₁) (execInstrs rt (i :: is₂) s₂) := by
  simp only [execInstrs]
  revert h
  cases execInstr rt i s₁ <;> cases execInstr rt i s₂ <;> intro h
  · exact ih _ _ h
  · exact h.elim
  · exact h.elim
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- **Dead assignment elimination within a block**: from related states, the pruned
    instructions and the originals give related results. -/
theorem execInstrs_dropDead (dead : Nat → Bool) (is : List Instr) : ∀ (s₁ s₂ : State R), StateEq dead s₁ s₂ →
    is.all (Opt.instrNoDead dead) = true →
    ResEq dead (execInstrs rt (Opt.dropDeadInstrs dead is) s₁) (execInstrs rt is s₂) := by
  induction is with
  | nil => intro s₁ s₂ h _; exact h
  | cons i is ih =>
    intro s₁ s₂ h hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hi, hrest⟩ := hall
    have keep : ResEq dead (execInstrs rt (i :: Opt.dropDeadInstrs dead is) s₁) (execInstrs rt (i :: is) s₂) :=
      execInstrs_cons_envEq rt dead i _ _ s₁ s₂ (execInstr_envEq rt dead i s₁ s₂ h hi)
        (fun s₁ s₂ hs => ih s₁ s₂ hs hrest)
    cases i with
    | line n => exact keep
    | call f args => exact keep
    | set d rhs =>
      cases rhs with
      | bin op a b => exact keep
      | un op a => exact keep
      | natTab i => exact keep
      | select c a b => exact keep
      | opnd o =>
        simp only [Opt.dropDeadInstrs]
        split
        · rename_i hd
          simp only [execInstrs, execInstr, evalRhs]
          apply ih s₁ _ _ hrest
          exact ⟨envEq_set_dead dead _ _ h.1 d.id hd _, h.2.1, h.2.2⟩
        · exact keep
      | call f args =>
        simp only [Opt.dropDeadInstrs]
        split
        · rename_i hd
          simp only [execInstrs, execInstr]
          rcases execCall_envEq rt dead f args s₁ s₂ h hi with ⟨h1, h2⟩ | ⟨s₁', s₂', ret, h1, h2, hs⟩
          · simp only [h1, h2]; exact ⟨h.2.2, rfl⟩
          · simp only [h1, h2]
            apply ih s₁' _ _ hrest
            exact ⟨envEq_set_dead dead _ _ hs.1 d.id hd _, hs.2.1, hs.2.2⟩
        · exact keep

theorem stepBlock_dropDeadBlock (dead : Nat → Bool) (blk : Block) (s₁ s₂ : State R) (h : StateEq dead s₁ s₂)
    (hb : Opt.blockNoDead dead blk = true) :
    OutEq dead (stepBlock rt (Opt.dropDeadBlock dead blk) s₁) (stepBlock rt blk s₂) := by
  obtain ⟨is, t⟩ := blk
  simp only [Opt.blockNoDead, Bool.and_eq_true] at hb
  obtain ⟨hi, ht⟩ := hb
  have hr := execInstrs_dropDead rt dead is.toList s₁ s₂ h hi
  simp only [stepBlock, Opt.dropDeadBlock, List.toList_toArray]
  revert hr
  cases execInstrs rt (Opt.dropDeadInstrs dead is.toList) s₁ <;> cases execInstrs rt is.toList s₂ <;> intro hr
  · rename_i s₁' s₂'
    obtain ⟨henv, hrt, htr⟩ := hr
    cases t with
    | ret => exact ⟨htr, rfl⟩
    | retVal o => exact ⟨by simp [evalOpnd_envEq dead _ _ henv o ht, htr], rfl⟩
    | unreachable => exact ⟨htr, rfl⟩
    | br b => exact ⟨rfl, henv, hrt, htr⟩
    | condBr c t f => exact ⟨by simp [evalOpnd_envEq dead _ _ henv c ht], henv, hrt, htr⟩
    | switch o cs d => exact ⟨by simp [evalOpnd_envEq dead _ _ henv o ht], henv, hrt, htr⟩
  · exact hr.elim
  · exact hr.elim
  · obtain ⟨rfl, rfl⟩ := hr; exact ⟨rfl, rfl⟩

theorem runFrom_dropDead (dead : Nat → Bool) (f : Func) (hf : Opt.funcNoDead dead f = true) :
    ∀ (fuel b : Nat) (s₁ s₂ : State R), StateEq dead s₁ s₂ →
      runFrom rt { f with blocks := f.blocks.map (Opt.dropDeadBlock dead) } fuel b s₁ = runFrom rt f fuel b s₂ := by
  intro fuel
  induction fuel with
  | zero => intro b s₁ s₂ h; simp [runFrom, h.2.2]
  | succ fuel ih =>
    intro b s₁ s₂ h
    simp only [runFrom, Array.getElem?_map]
    cases hb : f.blocks[b]? with
    | none => simp [h.2.2]
    | some blk =>
      have hblk : Opt.blockNoDead dead blk = true :=
        List.all_eq_true.mp hf blk (List.mem_of_getElem? (Array.getElem?_toList.trans hb))
      have hs := stepBlock_dropDeadBlock rt dead blk s₁ s₂ h hblk
      simp only [Option.map_some]
      revert hs
      cases stepBlock rt (Opt.dropDeadBlock dead blk) s₁ <;> cases stepBlock rt blk s₂ <;> intro hs
      · obtain ⟨rfl, hs⟩ := hs; exact ih _ _ _ hs
      · exact hs.elim
      · exact hs.elim
      · obtain ⟨rfl, rfl⟩ := hs; rfl

/-- **Dead assignment elimination preserves behaviour.** -/
theorem dropDead_correct (fuel : Nat) (f : Func) (r : R) :
    run rt fuel (Opt.dropDead f) r = run rt fuel f r := by
  simp only [Opt.dropDead]
  split
  · rename_i hf
    exact runFrom_dropDead rt _ f hf fuel 0 _ _ ⟨fun _ _ => rfl, rfl, rfl⟩
  · rfl

/-- No operand reads a variable outside the variables the function reads: the check
    `funcNoDead` makes of `deadVar` always passes, so `dropDead` never falls back to the
    unoptimised function. -/
theorem opndNoDead_deadVar (f : Func) (o : Opnd) (h : ∀ id ∈ Opt.opndReads o, id ∈ Opt.readVars f) :
    Opt.opndNoDead (Opt.deadVar f) o = true := by
  cases o with
  | k ty c => rfl
  | v x =>
    have hx : x.id ∈ Opt.readVars f := h x.id (by simp [Opt.opndReads])
    simp [Opt.opndNoDead, Opt.deadVar, hx]

theorem rhsNoDead_deadVar (f : Func) (r : Rhs) (h : ∀ id ∈ Opt.rhsReads r, id ∈ Opt.readVars f) :
    Opt.rhsNoDead (Opt.deadVar f) r = true := by
  cases r with
  | opnd o => exact opndNoDead_deadVar f o h
  | bin op a b =>
    simp only [Opt.rhsReads, List.mem_append] at h
    simp only [Opt.rhsNoDead, Bool.and_eq_true]
    exact ⟨opndNoDead_deadVar f a (fun id hid => h id (Or.inl hid)),
           opndNoDead_deadVar f b (fun id hid => h id (Or.inr hid))⟩
  | un op a => exact opndNoDead_deadVar f a h
  | natTab i => exact opndNoDead_deadVar f i h
  | select c a b =>
    simp only [Opt.rhsReads, List.mem_append] at h
    simp only [Opt.rhsNoDead, Bool.and_eq_true]
    exact ⟨⟨opndNoDead_deadVar f c (fun id hid => h id (Or.inl (Or.inl hid))),
            opndNoDead_deadVar f a (fun id hid => h id (Or.inl (Or.inr hid)))⟩,
           opndNoDead_deadVar f b (fun id hid => h id (Or.inr hid))⟩
  | call g args =>
    simp only [Opt.rhsReads, List.mem_flatMap] at h
    simp only [Opt.rhsNoDead, List.all_eq_true]
    exact fun o ho => opndNoDead_deadVar f o (fun id hid => h id ⟨o, ho, hid⟩)

theorem instrNoDead_deadVar (f : Func) (i : Instr) (h : ∀ id ∈ Opt.instrReads i, id ∈ Opt.readVars f) :
    Opt.instrNoDead (Opt.deadVar f) i = true := by
  cases i with
  | set d r => exact rhsNoDead_deadVar f r h
  | call g args =>
    simp only [Opt.instrReads, List.mem_flatMap] at h
    simp only [Opt.instrNoDead, List.all_eq_true]
    exact fun o ho => opndNoDead_deadVar f o (fun id hid => h id ⟨o, ho, hid⟩)
  | line n => rfl

theorem termNoDead_deadVar (f : Func) (t : Term) (h : ∀ id ∈ Opt.termReads t, id ∈ Opt.readVars f) :
    Opt.termNoDead (Opt.deadVar f) t = true := by
  cases t with
  | condBr c t e => exact opndNoDead_deadVar f c h
  | switch o cs d => exact opndNoDead_deadVar f o h
  | retVal o => exact opndNoDead_deadVar f o h
  | _ => rfl

theorem blockNoDead_deadVar (f : Func) (b : Block) (h : ∀ id ∈ Opt.blockReads b, id ∈ Opt.readVars f) :
    Opt.blockNoDead (Opt.deadVar f) b = true := by
  simp only [Opt.blockReads, List.mem_append, List.mem_flatMap] at h
  simp only [Opt.blockNoDead, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun i hi => instrNoDead_deadVar f i (fun id hid => h id (Or.inl ⟨i, hi, hid⟩)),
         termNoDead_deadVar f b.term (fun id hid => h id (Or.inr hid))⟩

/-- **The check of `dropDead` always passes.** -/
theorem funcNoDead_deadVar (f : Func) : Opt.funcNoDead (Opt.deadVar f) f = true := by
  simp only [Opt.funcNoDead, List.all_eq_true]
  intro b hb
  apply blockNoDead_deadVar
  intro id hid
  simp only [Opt.readVars, List.mem_flatMap]
  exact ⟨b, hb, hid⟩

/-! ## Unreachable block removal

A run only ever visits blocks in the reachable set — the entry is in it and it is closed
under successors, which the pass checks — and those blocks are untouched. -/

/-- The successor a block transfers to is one of its terminator's successors. -/
theorem selectCase_mem (v : Val) (cs : List (Int × Nat)) (d : Nat) : selectCase v cs d ∈ d :: cs.map (·.2) := by
  induction cs with
  | nil => simp [selectCase]
  | cons c cs ih =>
    obtain ⟨k, b⟩ := c
    have step : selectCase v cs d ∈ d :: List.map (·.2) ((k, b) :: cs) := by
      simp only [List.map_cons]
      rcases List.mem_cons.mp ih with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h)))
    cases v with
    | i n =>
      simp only [selectCase]
      split
      · simp
      · exact step
    | f x => exact step
    | b t => exact step

theorem stepBlock_next_mem (blk : Block) (s s' : State R) (b' : Nat)
    (h : stepBlock rt blk s = .next b' s') : b' ∈ termSuccs blk.term := by
  obtain ⟨is, t⟩ := blk
  simp only [stepBlock] at h
  split at h
  · cases h
  · cases t with
    | ret => cases h
    | retVal o => cases h
    | unreachable => cases h
    | br b => cases h; simp [termSuccs]
    | condBr c t f =>
      cases h
      simp only [termSuccs]
      split <;> simp
    | switch o cs d =>
      cases h
      exact selectCase_mem _ _ _

/-- The pruned blocks are the original ones at every reachable index. -/
theorem pruneBlocks_get (r : List Nat) (bs : Array Block) (b : Nat) (hb : b ∈ r) :
    (Opt.pruneBlocks r bs)[b]? = bs[b]? := by
  have hc : r.contains b = true := List.contains_iff_mem.mpr hb
  simp only [Opt.pruneBlocks, Array.getElem?_mapIdx, hc, if_true]
  cases bs[b]? <;> rfl

/-- What the closure check guarantees. -/
theorem closedUnder_succ (f : Func) (r : List Nat) (h : Opt.closedUnder f r = true) (b : Nat) (hb : b ∈ r)
    (blk : Block) (hblk : f.blocks[b]? = some blk) (b' : Nat) (hb' : b' ∈ termSuccs blk.term) : b' ∈ r := by
  simp only [Opt.closedUnder, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 b hb
  simp only [Opt.blockSuccs, hblk] at this
  exact List.contains_iff_mem.mp (this b' hb')

theorem runFrom_prune (f : Func) (r : List Nat) (h : Opt.closedUnder f r = true) :
    ∀ (fuel b : Nat) (s : State R), b ∈ r →
      runFrom rt { f with blocks := Opt.pruneBlocks r f.blocks } fuel b s = runFrom rt f fuel b s := by
  intro fuel
  induction fuel with
  | zero => intro b s _; rfl
  | succ fuel ih =>
    intro b s hb
    simp only [runFrom, pruneBlocks_get r f.blocks b hb]
    cases hblk : f.blocks[b]? with
    | none => rfl
    | some blk =>
      dsimp only
      cases hs : stepBlock rt blk s with
      | stop tr st => rfl
      | next b' s' =>
        exact ih b' s' (closedUnder_succ f r h b hb blk hblk b' (stepBlock_next_mem rt blk s s' b' hs))

/-- **Unreachable block removal preserves behaviour.** -/
theorem pruneUnreachable_correct (fuel : Nat) (f : Func) (r : R) :
    run rt fuel (Opt.pruneUnreachable f) r = run rt fuel f r := by
  simp only [Opt.pruneUnreachable]
  split
  · rename_i h
    have h0 : 0 ∈ Opt.reachable f := by
      simp only [Opt.closedUnder, Bool.and_eq_true] at h
      exact List.contains_iff_mem.mp h.1
    exact runFrom_prune rt f _ h fuel 0 _ h0
  · rfl

/-! ## The pipeline -/

theorem simplify_correct (fuel : Nat) (f : Func) (r : R) :
    run rt fuel (Opt.simplify f) r = run rt fuel f r := by
  simp only [Opt.simplify]
  rw [constFold_correct, copyProp_correct]

theorem simplifyN_correct (n : Nat) (fuel : Nat) (f : Func) (r : R) :
    run rt fuel (Opt.simplifyN n f) r = run rt fuel f r := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [Opt.simplifyN]; rw [ih, simplify_correct]

/-- **The whole MIR optimiser preserves behaviour**: for every runtime, fuel and runtime
    state, the optimised function makes the same calls, reaches the same lines and ends
    the same way as the original. -/
theorem run_correct (fuel : Nat) (f : Func) (r : R) : run rt fuel (Opt.run f) r = run rt fuel f r := by
  simp only [Opt.run]
  rw [pruneUnreachable_correct, dropDead_correct, foldBranches_correct, copyProp_correct, simplifyN_correct]

end A68.Verified.MIR
