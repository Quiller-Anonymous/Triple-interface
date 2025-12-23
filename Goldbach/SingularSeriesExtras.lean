import Mathlib
import Goldbach.SingularSeries

open scoped BigOperators

namespace Goldbach
namespace Singular

/-- If `p` is an odd prime then `(p-1)/(p-2) ≥ 1`. -/
lemma oddFactor_ge_one_of_prime_ne_two
    {p : ℕ} (hp : Nat.Prime p) (hne2 : p ≠ 2) :
    (1 : ℝ) ≤ oddFactor p := by
  -- `2 < p` since `p` is prime and `p ≠ 2`.
  have h2le : 2 ≤ p := hp.two_le
  have h2lt : 2 < p := lt_of_le_of_ne h2le (by symm; exact hne2)
  have h1le : 1 ≤ p := le_trans (by decide : 1 ≤ 2) h2le
  -- Denominator positivity: `0 < (p - 2 : ℝ)`.
  have hden_pos_nat : 0 < p - 2 := Nat.sub_pos_of_lt h2lt
  have hden_pos : (0 : ℝ) < (p - 2 : ℝ) := by exact_mod_cast hden_pos_nat
  -- Show `(p-2) ≤ (p-1)` in ℝ and use `one_le_div_iff`.
  have num_ge : ((p - 2 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    have : (p : ℝ) - 2 ≤ (p : ℝ) - 1 := by linarith
    simpa [Nat.cast_sub h2le, Nat.cast_sub h1le] using this
  have : (1 : ℝ) ≤ (p - 1 : ℝ) / (p - 2 : ℝ) := (one_le_div_iff hden_pos).2 num_ge
  simpa [oddFactor] using this

/-- Every factor in the finite product over odd prime divisors is ≥ 1. -/
lemma oddFactor_ge_one_on_support {n p : ℕ}
    (hp : p ∈ oddPrimeSupport n) : (1 : ℝ) ≤ oddFactor p := by
  rcases Finset.mem_filter.mp hp with ⟨_, hpr⟩
  rcases hpr with ⟨hp_prime, hp_ne2⟩
  exact oddFactor_ge_one_of_prime_ne_two hp_prime hp_ne2

/-- The finite product of odd prime local factors is ≥ 1. -/
lemma prod_oddFactor_ge_one (n : ℕ) :
  (1 : ℝ) ≤ ∏ p in oddPrimeSupport n, oddFactor p := by
  classical
  refine Finset.induction_on (oddPrimeSupport n) ?base ?step
  · simp
  · intro a s ha hIH
    have ha1 : (1 : ℝ) ≤ oddFactor a := oddFactor_ge_one_on_support (by simpa using ha)
    have hs_nonneg : 0 ≤ ∏ p in s, oddFactor p := by
      -- each factor in s is ≥ 1, so the product is ≥ 0
      have htail : (1 : ℝ) ≤ ∏ p in s, oddFactor p := by simpa using hIH
      exact le_trans (by norm_num) htail
    have hprod_full : (1 : ℝ) ≤ oddFactor a * ∏ p in s, oddFactor p := by
      nlinarith
    simpa [Finset.prod_insert ha, one_mul] using hprod_full

/-- Uniform positive floor for σ on even `n`: `σ(n) ≥ 2*C2`. -/
lemma sigma_floor_even {C : C2Const} {n : ℕ} (he : Even n) :
  (2 : ℝ) * C.C2 ≤ sigma C n := by
  have hprod := prod_oddFactor_ge_one n
  have hnonneg : 0 ≤ (2 : ℝ) * C.C2 := by
    have : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg this (le_of_lt C.pos)
  have := mul_le_mul_of_nonneg_left hprod hnonneg
  simpa [sigma_even_expand (C:=C) he, mul_assoc, mul_left_comm, mul_comm] using this

end Singular
end Goldbach
