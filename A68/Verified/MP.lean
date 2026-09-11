import A68.MP

/-!
# A68.Verified.MP — what the multi-precision kernel preserves

`A68.MP` reproduces a68g's multi-precision routines step by step, including their
rounding quirks, so its specification *is* a68g's behaviour and is checked by
differential testing.  What can be proved is that the steps a68g relies on to be
exact are exact.  With `digVal a n` the integer that positions `0 … n` of a digit
array denote in radix `R = 10⁷` (position 0 most significant):

* a carry step of `norm_mp` and the whole normalisation loop preserve `digVal`
  (`carryAt_digVal`, `normFrom_digVal`, `normDigits_digVal`);
* the double arithmetic of a68g's scratch computations is exact below 2⁵³
  (`dblOfInt_exact`, `fma_exact`);
* the aligned digit sum that `add_mp` and `sub_mp` normalise and round is the exact
  sum `R · (X + s·Y)` of the operands' digit values when their exponents agree
  (`alignedSum_equal_exponents`), and otherwise holds the digits of the larger operand
  and the shifted, truncated digits of the other (`alignedSum_digit`);
* the digit value is linear, so digit-wise sums add values (`dv_linear`);
* the mantissa that decimal conversion starts from is the digit value itself, and one
  digit is exactly seven decimal digits (`toDecParts_mant`, `mantOf_succ`, `R_eq`).
-/
namespace A68.Verified.MPProofs

open A68.MP

theorem R_eq : R = 10 ^ logR := by decide

-- ## Array updates

theorem getD_setIfInBounds (a : Array Int) (i j : Nat) (v : Int) :
    (a.setIfInBounds i v).getD j 0 = if i = j ∧ i < a.size then v else a.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
  · simp [h]

-- ## The value of a digit array

/-- Positions `0 … n` of `a` read in radix `R`, position 0 most significant. -/
def digVal (a : Array Int) : Nat → Int
  | 0 => a.getD 0 0
  | n + 1 => digVal a n * R + a.getD (n + 1) 0

theorem digVal_congr (a b : Array Int) (n : Nat) (h : ∀ i, i ≤ n → a.getD i 0 = b.getD i 0) :
    digVal a n = digVal b n := by
  induction n with
  | zero => simp [digVal, h 0 (Nat.le_refl 0)]
  | succ n ih =>
    simp only [digVal]
    rw [ih (fun i hi => h i (Nat.le_succ_of_le hi)), h (n + 1) (Nat.le_refl _)]

/-- Changing only position `m` changes the value at `m` by the difference there. -/
theorem digVal_last (a b : Array Int) (m : Nat) (h : ∀ i, i < m → a.getD i 0 = b.getD i 0) :
    digVal b m - digVal a m = b.getD m 0 - a.getD m 0 := by
  cases m with
  | zero => simp [digVal]
  | succ m =>
    simp only [digVal]
    rw [digVal_congr a b m (fun i hi => h i (Nat.lt_succ_of_le hi))]
    omega

/-- Two arrays that agree except at positions `j - 1` and `j`, where they hold the same
    two-digit value, have the same value at every `n ≥ j`. -/
theorem digVal_pair (a b : Array Int) (j n : Nat) (hj : 1 ≤ j) (hn : j ≤ n)
    (hsame : ∀ i, i ≠ j - 1 → i ≠ j → a.getD i 0 = b.getD i 0)
    (hpair : b.getD (j - 1) 0 * R + b.getD j 0 = a.getD (j - 1) 0 * R + a.getD j 0) :
    digVal b n = digVal a n := by
  revert hn
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn
    by_cases hjn : j ≤ n
    · simp only [digVal]
      rw [ih hjn, hsame (n + 1) (by omega) (by omega)]
    · have hjeq : j = n + 1 := by omega
      subst hjeq
      simp only [digVal]
      have hk := digVal_last a b n (fun i hi => hsame i (by omega) (by omega))
      simp only [Nat.add_sub_cancel] at hpair
      unfold R at hpair ⊢
      omega

theorem carryAt_size (a : Array Int) (j : Nat) : (carryAt a j).size = a.size := by
  simp only [carryAt]
  split
  · simp [Array.size_setIfInBounds]
  · split <;> simp [Array.size_setIfInBounds]

/-- Writing `v` at position `j` and `w` at position `j - 1` keeps the value when the two
    positions still denote the same two-digit number. -/
theorem digVal_carry (a : Array Int) (j n : Nat) (v w : Int) (hj : 1 ≤ j) (hn : j ≤ n)
    (hs : j < a.size) (hv : w * R + v = a.getD (j - 1) 0 * R + a.getD j 0) :
    digVal ((a.setIfInBounds j v).setIfInBounds (j - 1) w) n = digVal a n := by
  have hs1 : j - 1 < a.size := by omega
  have hne : j - 1 ≠ j := by omega
  apply digVal_pair a _ j n hj hn
  · intro i h1 h2
    rw [getD_setIfInBounds, if_neg (fun h => h1 h.1.symm), getD_setIfInBounds,
      if_neg (fun h => h2 h.1.symm)]
  · rw [getD_setIfInBounds, if_pos ⟨rfl, by rw [Array.size_setIfInBounds]; exact hs1⟩,
      getD_setIfInBounds, if_neg (fun h => hne h.1), getD_setIfInBounds, if_pos ⟨rfl, hs⟩]
    exact hv

theorem carryAt_ge (a : Array Int) (j : Nat) (h : a.getD j 0 ≥ R) :
    carryAt a j = (a.setIfInBounds j (a.getD j 0 - a.getD j 0 / R * R)).setIfInBounds (j - 1)
      (a.getD (j - 1) 0 + a.getD j 0 / R) := by
  unfold carryAt
  simp only [if_pos h]

theorem carryAt_neg (a : Array Int) (j : Nat) (h1 : ¬ a.getD j 0 ≥ R) (h2 : a.getD j 0 < 0) :
    carryAt a j = (a.setIfInBounds j (a.getD j 0 + (1 + (-a.getD j 0 - 1) / R) * R)).setIfInBounds (j - 1)
      (a.getD (j - 1) 0 - (1 + (-a.getD j 0 - 1) / R)) := by
  unfold carryAt
  simp only [if_neg h1, if_pos h2]

theorem carryAt_mid (a : Array Int) (j : Nat) (h1 : ¬ a.getD j 0 ≥ R) (h2 : ¬ a.getD j 0 < 0) :
    carryAt a j = a := by
  unfold carryAt
  simp only [if_neg h1, if_neg h2]

/-- **A carry preserves the value.** -/
theorem carryAt_digVal (a : Array Int) (j n : Nat) (hj : 1 ≤ j) (hn : j ≤ n) (hs : j < a.size) :
    digVal (carryAt a j) n = digVal a n := by
  by_cases h1 : a.getD j 0 ≥ R
  · rw [carryAt_ge a j h1]
    apply digVal_carry a j n _ _ hj hn hs
    unfold R
    omega
  · by_cases h2 : a.getD j 0 < 0
    · rw [carryAt_neg a j h1 h2]
      apply digVal_carry a j n _ _ hj hn hs
      unfold R
      omega
    · rw [carryAt_mid a j h1 h2]

theorem normFrom_size (a : Array Int) (k j : Nat) : (normFrom a k j).size = a.size := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    simp only [normFrom]
    split
    · rfl
    · rw [ih, carryAt_size]

/-- **Normalisation preserves the value**: `norm_mp`'s carries from position `j` down to
    `k` (never below 1) leave the number denoted by positions `0 … n` unchanged. -/
theorem normFrom_digVal (a : Array Int) (k j n : Nat) (hn : j ≤ n) (hs : j < a.size) :
    digVal (normFrom a k j) n = digVal a n := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    simp only [normFrom]
    split
    · rfl
    · rw [ih (carryAt a (j + 1)) (by omega) (by rw [carryAt_size]; omega)]
      exact carryAt_digVal a (j + 1) n (by omega) hn hs

theorem grow_getD (a : Array Int) (n i : Nat) : (grow a n).getD i 0 = a.getD i 0 := by
  unfold grow
  split
  · rfl
  · simp only [Array.getD_eq_getD_getElem?]
    by_cases h : i < a.size
    · simp [Array.getElem?_append_left h]
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]
      by_cases h2 : i < a.size + (n - a.size)
      · rw [Array.getElem?_append_right (Nat.le_of_not_lt h)]
        simp only [Array.getElem?_replicate]
        split <;> rfl
      · rw [Array.getElem?_eq_none (by simp; omega)]

theorem grow_size (a : Array Int) (n : Nat) : n ≤ (grow a n).size := by
  unfold grow
  split
  · omega
  · simp; omega

/-- `normDigits w k digs` — the scratch normalisation every operation performs — does not
    change the value of positions `0 … digs`. -/
theorem normDigits_digVal (w : Array Int) (k digs : Nat) :
    digVal (normDigits w k digs) digs = digVal w digs := by
  unfold normDigits
  rw [normFrom_digVal _ k digs digs (Nat.le_refl _) (by have := grow_size w (digs + 1); omega)]
  exact digVal_congr _ _ digs (fun i _ => grow_getD w (digs + 1) i)

-- ## Exactness of a68g's double arithmetic on scratch digits

/-- Every integer below 2⁵³ in magnitude is a double. -/
theorem dblOfInt_exact (n : Int) (h : n.natAbs < 2 ^ 53) : dblOfInt n = n := by
  unfold dblOfInt
  simp [h]

/-- A fused multiply-add of integer-valued doubles is exact when its result is below 2⁵³. -/
theorem fma_exact (a b c : Int) (h : (a * b + c).natAbs < 2 ^ 53) : fma a b c = a * b + c := by
  unfold fma
  exact dblOfInt_exact _ h

-- ## Addition before rounding

/-- Positions `1 … n` of a digit function read in radix `R`. -/
def dv (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => dv f n * R + f (n + 1)

/-- **The digit value is linear**: adding digit by digit (without carries) adds the values. -/
theorem dv_linear (f g : Nat → Int) (s : Int) (n : Nat) :
    dv (fun i => f i + s * g i) n = dv f n + s * dv g n := by
  induction n with
  | zero => simp [dv]
  | succ n ih =>
    simp only [dv, ih]
    simp only [Int.add_mul, Int.mul_add, Int.mul_assoc]
    omega

theorem digitOr0_in (a : Array Int) (digs j : Nat) (h1 : 1 ≤ j) (h2 : j ≤ digs) :
    digitOr0 a digs (j : Int) = a.getD j 0 := by
  unfold digitOr0
  have hc : ((j : Int) ≤ 0 || (j : Int) > (digs : Int)) = false := by simp <;> omega
  simp only [hc, Bool.false_eq_true, if_false, Int.toNat_natCast]

theorem digitOr0_out (a : Array Int) (digs j : Nat) (h : digs < j) :
    digitOr0 a digs (j : Int) = 0 := by
  unfold digitOr0
  have hc : ((j : Int) ≤ 0 || (j : Int) > (digs : Int)) = true := by simp <;> omega
  simp only [hc, if_true]

/-- Digit `i ∈ [2, digs + 2]` of the scratch number of `add_mp` / `sub_mp` is the digit of
    the first operand plus `s` times the digit of the second, each shifted by its alignment. -/
theorem alignedSum_digit (x y : Array Int) (xex yex : Int) (digs : Nat) (s : Int) (i : Nat)
    (hi : 2 ≤ i) (hi2 : i ≤ digs + 2) :
    (alignedSum x y xex yex digs s).1.getD i 0 =
      digitOr0 x digs ((i : Int) - 1 - (if yex > xex then yex - xex else 0)) +
      s * digitOr0 y digs ((i : Int) - 1 - (if xex > yex then xex - yex else 0)) := by
  unfold alignedSum
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_ofFn]
  simp [show i < digs + 2 + 1 by omega, show ¬ i < 2 by omega]

/-- The scratch digits below position 2 are zero. -/
theorem alignedSum_low (x y : Array Int) (xex yex : Int) (digs : Nat) (s : Int) (i : Nat)
    (hi : i < 2) : (alignedSum x y xex yex digs s).1.getD i 0 = 0 := by
  unfold alignedSum
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_ofFn]
  simp [show i < digs + 2 + 1 by omega, hi]

/-- **Addition before rounding is exact.**  With equal exponents the scratch number of
    `add_mp` / `sub_mp` is `x + s·y` one digit to the right: its value is `R · (X + s·Y)`
    for the digit values `X`, `Y` of the operands. -/
theorem alignedSum_equal_exponents (x y : Array Int) (e : Int) (digs : Nat) (s : Int) :
    digVal (alignedSum x y e e digs s).1 (digs + 2) =
      R * (dv (fun j => x.getD j 0) digs + s * dv (fun j => y.getD j 0) digs) := by
  have hlow : ∀ i, i < 2 → (alignedSum x y e e digs s).1.getD i 0 = 0 :=
    fun i hi => alignedSum_low x y e e digs s i hi
  have hmid : ∀ j, 1 ≤ j → j ≤ digs + 1 →
      (alignedSum x y e e digs s).1.getD (j + 1) 0 =
        (if j ≤ digs then x.getD j 0 else 0) + s * (if j ≤ digs then y.getD j 0 else 0) := by
    intro j hj hj2
    rw [alignedSum_digit x y e e digs s (j + 1) (by omega) (by omega)]
    simp only [Int.lt_irrefl, if_false, Int.sub_zero]
    have h1 : ((j + 1 : Nat) : Int) - 1 = (j : Int) := by omega
    rw [h1]
    by_cases h : j ≤ digs
    · rw [digitOr0_in x digs j hj h, digitOr0_in y digs j hj h]
      simp [h]
    · rw [digitOr0_out x digs j (by omega), digitOr0_out y digs j (by omega)]
      simp [h]
  have key : ∀ m, m ≤ digs →
      digVal (alignedSum x y e e digs s).1 (m + 1) =
        dv (fun j => x.getD j 0) m + s * dv (fun j => y.getD j 0) m := by
    intro m hm
    induction m with
    | zero =>
      simp only [digVal, hlow 0 (by omega), hlow 1 (by omega), dv]
      simp
    | succ m ih =>
      have ih' := ih (by omega)
      have hm' := hmid (m + 1) (by omega) (by omega)
      simp only [show m + 1 ≤ digs by omega, if_true] at hm'
      show digVal _ (m + 1) * R + _ = _
      rw [ih', hm']
      simp only [dv, Int.add_mul, Int.mul_add, Int.mul_assoc]
      omega
  have hlast := hmid (digs + 1) (by omega) (by omega)
  simp only [show ¬ (digs + 1 ≤ digs) by omega, if_false, Int.mul_zero, Int.add_zero] at hlast
  show digVal _ (digs + 1) * R + _ = _
  rw [key digs (Nat.le_refl _), hlast, Int.add_zero, Int.mul_comm]

-- ## Decimal conversion

/-- The mantissa of `toDecParts` is `|d₁| d₂ … d_digs` in radix `R`, and its exponent is
    seven decimal places per digit, so `value = mant · 10^exp` exactly. -/
theorem toDecParts_mant (z : MP) (digs : Nat) :
    toDecParts z digs =
      (if z.dig 1 < 0 then -(mantOf z digs) else mantOf z digs, (z.ex - digs + 1) * logR) := rfl

theorem mantOf_succ (z : MP) (k : Nat) (hk : 1 ≤ k) :
    mantOf z (k + 1) = mantOf z k * R + z.dig (k + 1) := by
  simp only [mantOf]
  have : (k + 1 == 1) = false := by simp; omega
  simp [this]

end A68.Verified.MPProofs
