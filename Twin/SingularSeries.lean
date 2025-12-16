/-
  Twin/SingularSeries.lean
  Local factor and truncated singular series, with positivity lemmas.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace Twin

/-- Local twin-prime factor at a (natural) prime `p`:
    \( 1 - \frac{1}{(p-1)^2} \).
    We define it for all `p : ℕ`; in applications we use it for `p ≥ 3`. -/
def twinFactor (p : ℕ) : ℝ :=
  1 - 1 / ((p - 1 : ℝ) ^ 2)

/-- The truncated singular series over a finite set `S` of naturals
    (intended: odd primes). -/
def truncSingularSeries (S : Finset ℕ) : ℝ :=
  ∏ p ∈ S, twinFactor p

/-- For every `p ≥ 3`, the local factor is strictly positive (indeed ≥ 3/4). -/
lemma twinFactor_pos_of_three_le {p : ℕ} (hp3 : 3 ≤ p) :
  0 < twinFactor p := by
  -- From 3 ≤ p, get 2 ≤ p-1 (in ℕ), then cast to ℝ.
  have h2ltp : 2 < p := Nat.lt_of_lt_of_le (by decide : 2 < 3) hp3
  have h2le_pred : 2 ≤ p - 1 := Nat.le_pred_of_lt h2ltp
  have h2leR : (2 : ℝ) ≤ (p - 1 : ℝ) := by
    have : (p - 1 : ℝ) = ((p - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_one, (Nat.cast_sub (Nat.one_le_of_lt h2ltp)).symm]
    rw [this]
    exact Nat.cast_le.mpr h2le_pred
  -- Nonnegativity of (p - 1 : ℝ)
  have hx_nonneg : 0 ≤ (p - 1 : ℝ) := le_trans (by norm_num) h2leR
  -- Hence 4 ≤ (p - 1)^2 via `mul_le_mul` with hypotheses in the correct slots
  have two_mul_two : (2 : ℝ) * 2 = 4 := by norm_num
  have hx_sq_ge4 : (4 : ℝ) ≤ (p - 1 : ℝ) ^ 2 := by
    have hmul : (2 : ℝ) * 2 ≤ (p - 1 : ℝ) * (p - 1) :=
      mul_le_mul h2leR h2leR (by norm_num) hx_nonneg
    simpa [two_mul_two, pow_two] using hmul
  -- Then 1/((p-1)^2) ≤ 1/4 (monotonicity of 1/x on (0,∞))
  have inv_le : 1 / ((p - 1 : ℝ) ^ 2) ≤ 1 / 4 := by
    have h4_pos : 0 < (4 : ℝ) := by norm_num
    -- one_div_le_one_div_of_le: 0 < a → a ≤ b → 1/b ≤ 1/a
    simpa [one_div] using one_div_le_one_div_of_le h4_pos hx_sq_ge4
  -- So 1 - 1/((p-1)^2) ≥ 1 - 1/4 = 3/4 > 0
  have h_ge : (3 : ℝ) / 4 ≤ 1 - 1 / ((p - 1 : ℝ) ^ 2) := by
    have : 1 / ((p - 1 : ℝ) ^ 2) ≤ (1 : ℝ) / 4 := by simpa using inv_le
    linarith
  -- Conclude positivity and unfold the definition
  have : 0 < 1 - 1 / ((p - 1 : ℝ) ^ 2) :=
    lt_of_lt_of_le (by norm_num : 0 < (3 : ℝ) / 4) h_ge
  simpa [Twin.twinFactor] using this

/-- Positivity of the finite truncated singular series
    provided every entry of `S` is ≥ 3. -/
lemma truncSingularSeries_pos_of_all_ge_three
  {S : Finset ℕ} (hS : ∀ p ∈ S, 3 ≤ p) :
  0 < truncSingularSeries S := by
  classical
  have hpos : ∀ p ∈ S, 0 < twinFactor p := by
    intro p hp; exact twinFactor_pos_of_three_le (hS p hp)
  simpa [truncSingularSeries] using Finset.prod_pos hpos

/-- Nonnegativity of the truncated singular series from strict positivity
    (e.g. when every element of `S` is ≥ 3). -/
lemma truncSingularSeries_nonneg_of_ge_three
    {S : Finset ℕ} (hS : ∀ p ∈ S, 3 ≤ p) :
    0 ≤ truncSingularSeries S :=
  le_of_lt (truncSingularSeries_pos_of_all_ge_three (S := S) hS)

-- Compatibility alias under the name you used:
namespace SingularSeries
  lemma truncSingularSeries_nonneg
      {S : Finset ℕ} (hS : ∀ p ∈ S, 3 ≤ p) :
      0 ≤ Twin.truncSingularSeries S :=
    Twin.truncSingularSeries_nonneg_of_ge_three (S := S) hS
end SingularSeries

end Twin
