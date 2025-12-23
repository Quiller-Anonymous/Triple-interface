/-
  Goldbach/PPNumerics.lean
  Small numeric lemmas used by prime-power counting on the inner band.
-/
import Mathlib

namespace Goldbach.PPNumerics

/-- Our canonical constants. -/
def X0 : Nat := 1_000_000
def H  : Nat := 10_000

lemma half_H : H / 2 = 5_000 := by decide
lemma X0_div2 : X0 / 2 = 500_000 := by decide

/-- Algebraic identity in `ℕ`: `(t+1)^2 - t^2 = t + t + 1`. -/
lemma sq_succ_sub_sq (t : Nat) : (t+1)^2 - t^2 = t + t + 1 := by
  -- expand `(t+1)^2 = t^2 + t + t + 1` then cancel `t^2`
  have : (t+1)^2 = t * t + t + t + 1 := by
    -- `(t+1)^2 = (t+1)*(t+1) = t*(t+1) + (t+1) = t*t + t + t + 1`
    simp [pow_two, Nat.succ_mul, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  calc
    (t+1)^2 - t^2
        = (t * t + t + t + 1) - t^2 := by simpa [this]
    _   = t + t + 1 := by
      -- `(t*t + (t + t + 1)) - t*t = t + t + 1`
      simpa [Nat.add_assoc, pow_two] using (Nat.add_sub_cancel (t * t) (t + t + 1))

/-- For `t ≥ 704`, consecutive squares are at least `1409` apart:
    `(t+1)^2 - t^2 ≥ 1409`. -/
lemma square_gap_ge_1409 {t : Nat} (ht : 704 ≤ t) :
    (t+1)^2 - t^2 ≥ 1409 := by
  -- Using `sq_succ_sub_sq` and monotonicity of addition
  have hsum : t + t ≥ 704 + 704 := Nat.add_le_add ht ht
  have : t + t + 1 ≥ (704 + 704) + 1 := Nat.add_le_add_right hsum 1
  -- `704+704+1 = 1409`
  simpa [sq_succ_sub_sq, Nat.add_assoc] using this

/-- Eight such gaps already exceed the inner-band width `H = 10_000`. -/
lemma eight_gaps_exceed_10k : 8 * 1409 > 10_000 := by norm_num

/-- For `N ≥ X0`, the inner-band left endpoint
    `A := N/2 - H/2` satisfies `A ≥ 495000`. -/
lemma inner_left_endpoint_lower (N : Nat) (hN : X0 ≤ N) :
    495_000 ≤ N/2 - H/2 := by
  -- divide `hN` by 2 and subtract `H/2 = 5000`
  have hdiv : X0 / 2 ≤ N / 2 := Nat.div_le_div_right hN
  have : X0 / 2 - H / 2 ≤ N / 2 - H / 2 := Nat.sub_le_sub_right hdiv (H/2)
  simpa [X0_div2, half_H, Nat.sub_eq, Nat.add_comm] using this

/-- If `t^2 ≥ 495000`, then `t ≥ 704`.  (Since `703^2 = 494209`.) -/
lemma t_ge_704_of_square_ge_495k {t : Nat} (h : 495_000 ≤ t*t) : 704 ≤ t := by
  -- contrapositive: if `t ≤ 703` then `t*t ≤ 703*703 = 494209 < 495000`
  by_contra hlt
  have hlt' : t < 704 := Nat.lt_of_not_ge hlt
  have hle : t ≤ 703 := Nat.lt_succ_iff.mp hlt'
  have sq_le : t * t ≤ 703 * 703 := Nat.mul_le_mul hle hle
  have : t * t ≤ 494_209 := by simpa using sq_le
  exact (not_le.mpr (lt_of_le_of_lt this (by decide : 494_209 < 495_000))) h

end Goldbach.PPNumerics
