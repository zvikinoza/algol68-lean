import A68.Numfmt

/-!
# A68.Verified.Numfmt — properties of the exact-decimal formatting kernel

`A68.Numfmt.Dec` represents `mant * 10^exp` exactly.  The formatting routines
(`fixed`, `float`, `whole`) only ever add, subtract, halve, scale by ten and
compare such numbers, so the byte-exact output of the formatter rests on these
operations being exact.  We prove that here with respect to an integer
semantics `valAt`: the value of a decimal scaled to a common exponent `e`.

We also prove the basic length invariants of the string builders.
-/
namespace A68.Verified
open A68.Numfmt

/-- The integer value of `d` scaled to exponent `e` (meaningful when `e ≤ d.exp`):
    `valAt d e = d.mant * 10^(d.exp - e)`. -/
def Dec.valAt (d : Dec) (e : Int) : Int := d.mant * (10 : Int) ^ (d.exp - e).toNat

theorem Dec.valAt_self (d : Dec) : Dec.valAt d d.exp = d.mant := by
  simp [Dec.valAt]

/-- Rescaling: the value at a lower exponent is the value at a higher one times a power of ten. -/
theorem Dec.valAt_rescale (d : Dec) (e f : Int) (he : e ≤ f) (hf : f ≤ d.exp) :
    Dec.valAt d e = Dec.valAt d f * (10 : Int) ^ (f - e).toNat := by
  unfold Dec.valAt
  have h : (d.exp - e).toNat = (d.exp - f).toNat + (f - e).toNat := by omega
  rw [h, Int.pow_add, Int.mul_assoc]

/-- **Addition is exact.** -/
theorem Dec.valAt_add (a b : Dec) (e : Int) (ha : e ≤ a.exp) (hb : e ≤ b.exp) :
    Dec.valAt (Dec.add a b) e = Dec.valAt a e + Dec.valAt b e := by
  unfold Dec.add Dec.align
  simp only [Dec.valAt, Dec.pow10]
  have hm : min a.exp b.exp ≤ a.exp := by omega
  have hm' : min a.exp b.exp ≤ b.exp := by omega
  have h1 : (a.exp - e).toNat = (a.exp - min a.exp b.exp).toNat + (min a.exp b.exp - e).toNat := by omega
  have h2 : (b.exp - e).toNat = (b.exp - min a.exp b.exp).toNat + (min a.exp b.exp - e).toNat := by omega
  rw [h1, h2, Int.pow_add, Int.pow_add, Int.add_mul, Int.mul_assoc, Int.mul_assoc]

/-- **Subtraction is exact.** -/
theorem Dec.valAt_sub (a b : Dec) (e : Int) (ha : e ≤ a.exp) (hb : e ≤ b.exp) :
    Dec.valAt (Dec.sub a b) e = Dec.valAt a e - Dec.valAt b e := by
  unfold Dec.sub Dec.align
  simp only [Dec.valAt, Dec.pow10]
  have h1 : (a.exp - e).toNat = (a.exp - min a.exp b.exp).toNat + (min a.exp b.exp - e).toNat := by omega
  have h2 : (b.exp - e).toNat = (b.exp - min a.exp b.exp).toNat + (min a.exp b.exp - e).toNat := by omega
  rw [h1, h2, Int.pow_add, Int.pow_add, Int.sub_mul, Int.mul_assoc, Int.mul_assoc]

/-- **Scaling by ten is exact.** -/
theorem Dec.valAt_mul10 (a : Dec) (e : Int) (ha : e ≤ a.exp) :
    Dec.valAt (Dec.mul10 a) e = 10 * Dec.valAt a e := by
  unfold Dec.mul10
  simp only [Dec.valAt]
  have h : (a.exp + 1 - e).toNat = (a.exp - e).toNat + 1 := by omega
  rw [h, Int.pow_succ]
  ac_rfl

/-- **Division by ten is exact** (it only lowers the exponent). -/
theorem Dec.valAt_div10 (a : Dec) (e : Int) (ha : e ≤ a.exp - 1) :
    10 * Dec.valAt (Dec.div10 a) e = Dec.valAt a e := by
  unfold Dec.div10
  simp only [Dec.valAt]
  have h : (a.exp - e).toNat = (a.exp - 1 - e).toNat + 1 := by omega
  rw [h, Int.pow_succ]
  ac_rfl

/-- **Halving is exact:** `2 * half a = a`. -/
theorem Dec.valAt_half (a : Dec) (e : Int) (ha : e ≤ a.exp - 1) :
    2 * Dec.valAt (Dec.half a) e = Dec.valAt a e := by
  unfold Dec.half
  simp only [Dec.valAt]
  have h : (a.exp - e).toNat = (a.exp - 1 - e).toNat + 1 := by omega
  rw [h, Int.pow_succ]
  calc 2 * (a.mant * 5 * 10 ^ (a.exp - 1 - e).toNat)
      = a.mant * (10 ^ (a.exp - 1 - e).toNat * (2 * 5)) := by ac_rfl
    _ = a.mant * (10 ^ (a.exp - 1 - e).toNat * 10) := by simp

/-- `sign (a - b)` decides the order of the represented values. -/
theorem Dec.cmp_spec (a b : Dec) :
    Dec.cmp a b = (Dec.valAt a (min a.exp b.exp) - Dec.valAt b (min a.exp b.exp)).sign := by
  unfold Dec.cmp Dec.sign
  have h := Dec.valAt_sub a b (min a.exp b.exp) (by omega) (by omega)
  have hs : Dec.valAt (Dec.sub a b) (min a.exp b.exp) = (Dec.sub a b).mant := by
    unfold Dec.sub Dec.align
    simp [Dec.valAt]
  rw [← h, hs]
  rcases Int.lt_trichotomy (Dec.sub a b).mant 0 with hlt | heq | hgt
  · have hn : ¬ (0 < (Dec.sub a b).mant) := Int.not_lt.mpr (Int.le_of_lt hlt)
    simp [Int.sign_eq_neg_one_of_neg hlt, hlt, hn]
  · simp [heq]
  · have hn : ¬ ((Dec.sub a b).mant < 0) := Int.not_lt.mpr (Int.le_of_lt hgt)
    simp [Int.sign_eq_one_of_pos hgt, hgt, hn]

-- ## Length invariants of the string builders

theorem errorChars_length (w : Int) :
    (errorChars w).length = if w = 0 then 1 else w.natAbs := by
  unfold errorChars
  split <;> simp_all

theorem leadingSpaces_length (s : String) (w : Nat) :
    (leadingSpaces s w).length = max s.length w := by
  unfold leadingSpaces
  split <;> simp_all <;> omega

end A68.Verified
