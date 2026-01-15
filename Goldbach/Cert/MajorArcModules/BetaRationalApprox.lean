import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Real.Pi.Bounds

/-!
`MajorArcModules/BetaRationalApprox` provides a small, self-contained lemma for approximating
`β : ℝ` by rationals with a prescribed denominator.

This is intended as a helper for “Option (2)” style bookkeeping, where one wants to replace a
real offset by a nearby rational offset (to be later absorbed into a major-arc rational phase),
while keeping the certificate side free of `Real.log`/analysis.
-/

namespace Goldbach.Cert.MajorArcModules.BetaRationalApprox

noncomputable section

open scoped Real

open Real

/--
Rational approximation with a prescribed denominator:
for `q > 0`, there exists `z : ℤ` with `|β - z/q| ≤ 1/(2q)`.

We take `z = round (q * β)`.
-/
theorem exists_int_close_div_nat (β : ℝ) {q : ℕ} (hq : 0 < q) :
    ∃ z : ℤ, |β - (z : ℝ) / (q : ℝ)| ≤ (1 : ℝ) / (2 * (q : ℝ)) := by
  classical
  -- Use rounding at scale `q`.
  let z : ℤ := round ((q : ℝ) * β)
  refine ⟨z, ?_⟩

  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos

  -- Rounding error: `|(q*β) - z| ≤ 1/2`.
  have hz : |(q : ℝ) * β - (z : ℝ)| ≤ (1 : ℝ) / 2 := by
    simpa [z] using (abs_sub_round ((q : ℝ) * β))

  -- Rewrite the target as a scaled version of the rounding error.
  have hrew : β - (z : ℝ) / (q : ℝ) = ((q : ℝ) * β - (z : ℝ)) / (q : ℝ) := by
    field_simp [hq0]
  have habs :
      |β - (z : ℝ) / (q : ℝ)| = |(q : ℝ) * β - (z : ℝ)| / (q : ℝ) := by
    -- `|t / q| = |t| / q` for `q > 0`.
    simp [hrew, abs_div, abs_of_pos hqpos]

  -- Divide by `q`.
  have hz' : |(q : ℝ) * β - (z : ℝ)| / (q : ℝ) ≤ ((1 : ℝ) / 2) / (q : ℝ) := by
    exact (div_le_div_of_nonneg_right hz (le_of_lt hqpos))

  -- Finish.
  have hz'' :
      |(q : ℝ) * β - (z : ℝ)| / (q : ℝ) ≤ (1 : ℝ) / (2 * (q : ℝ)) := by
    -- First normalize `hz'` to the form `… ≤ (2⁻¹)/q`.
    have hz1 : |(q : ℝ) * β - (z : ℝ)| / (q : ℝ) ≤ (2 : ℝ)⁻¹ / (q : ℝ) := by
      simpa using hz'
    -- Rewrite the RHS as `q⁻¹ * 2⁻¹`.
    have hcomm : (2 : ℝ)⁻¹ / (q : ℝ) = (q : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by
      simp [div_eq_mul_inv, mul_comm]
    have hz2 : |(q : ℝ) * β - (z : ℝ)| / (q : ℝ) ≤ (q : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by
      simpa [hcomm] using hz1
    -- Now rewrite the goal’s RHS to the same normal form.
    simpa [div_eq_mul_inv, mul_comm] using hz2
  simpa [habs] using hz''

/-!
### Simple corollaries for the `|2π⋅|` smallness regime
-/

theorem exists_int_close_div_nat_abs_two_pi_mul_le_pi_div (β : ℝ) {q : ℕ} (hq : 0 < q) :
    ∃ z : ℤ, |2 * Real.pi * (β - (z : ℝ) / (q : ℝ))| ≤ Real.pi / (q : ℝ) := by
  rcases exists_int_close_div_nat (β := β) (q := q) hq with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htwopi_nonneg : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
  have hz' : |β - (z : ℝ) / (q : ℝ)| ≤ (q : ℝ)⁻¹ * (2 : ℝ)⁻¹ := by
    -- Rewrite the `1/(2*q)`-style bound into `q⁻¹ * 2⁻¹`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hz
  have hmul : (2 * Real.pi) * |β - (z : ℝ) / (q : ℝ)|
        ≤ (2 * Real.pi) * ((q : ℝ)⁻¹ * (2 : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hz' htwopi_nonneg
  have habs :
      |2 * Real.pi * (β - (z : ℝ) / (q : ℝ))|
        = (2 * Real.pi) * |β - (z : ℝ) / (q : ℝ)| := by
    -- `|c*t| = |c|*|t|` and `|2π| = 2π`.
    have : |(2 * Real.pi : ℝ) * (β - (z : ℝ) / (q : ℝ))|
        = |2 * Real.pi| * |β - (z : ℝ) / (q : ℝ)| := by
      simp
    simpa [mul_assoc, abs_of_nonneg htwopi_nonneg] using this
  have hconst : (2 * Real.pi) * ((q : ℝ)⁻¹ * (2 : ℝ)⁻¹) = Real.pi / (q : ℝ) := by
    field_simp [hqpos.ne']
  -- Combine the three rewrites.
  have : |2 * Real.pi * (β - (z : ℝ) / (q : ℝ))| ≤ Real.pi / (q : ℝ) := by
    -- Rewrite the LHS of `hmul` into `|2π⋅|`, then simplify the RHS using `hconst`.
    have hmul_abs :
        |2 * Real.pi * (β - (z : ℝ) / (q : ℝ))|
          ≤ (2 * Real.pi) * ((q : ℝ)⁻¹ * (2 : ℝ)⁻¹) := by
      simpa [habs] using hmul
    simpa [hconst] using hmul_abs
  exact this

theorem exists_int_close_div_nat_abs_two_pi_mul_le_one_of_four_le (β : ℝ) {q : ℕ} (hq : 0 < q)
    (hq4 : 4 ≤ q) :
    ∃ z : ℤ, |2 * Real.pi * (β - (z : ℝ) / (q : ℝ))| ≤ 1 := by
  rcases exists_int_close_div_nat_abs_two_pi_mul_le_pi_div (β := β) (q := q) hq with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq4R : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
  have hpi_le : Real.pi ≤ (4 : ℝ) := le_of_lt Real.pi_lt_four
  have hpi_div : Real.pi / (q : ℝ) ≤ 1 := by
    -- `π/q ≤ 4/q ≤ 1` since `q ≥ 4`.
    have h1 : Real.pi / (q : ℝ) ≤ (4 : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right hpi_le (le_of_lt hqpos)
    have h2 : (4 : ℝ) / (q : ℝ) ≤ 1 := by
      -- `4/q ≤ 1` ↔ `4 ≤ q`.
      have : (4 : ℝ) ≤ (q : ℝ) := hq4R
      exact (div_le_one hqpos).2 this
    exact le_trans h1 h2
  exact le_trans hz hpi_div

end

end Goldbach.Cert.MajorArcModules.BetaRationalApprox
