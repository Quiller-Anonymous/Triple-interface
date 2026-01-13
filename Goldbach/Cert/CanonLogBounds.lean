import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Goldbach.BankParams

/-!
Canonical log bounds used in the “turnkey / calibration” layer.

These are purely elementary inequalities about `log X0` (with `X0 = 10^6`), proved from:
- the explicit inequality `2^19 ≤ X0`, and
- the explicit decimal bound `Real.log_two_gt_d9`.

They are kept in a separate module so other certificate work can reuse them without duplicating
proofs.
-/

namespace Goldbach.Cert.CanonLogBounds

open Goldbach.BankParams

noncomputable section

lemma ten_le_log_X0 : (10 : ℝ) ≤ Real.log (X0 : ℝ) := by
  have hpow : (2 : ℕ) ^ 19 ≤ X0 := by
    -- `2^19 = 524288 ≤ 10^6 = X0`.
    decide
  have hpow' : ((2 : ℝ) ^ 19) ≤ (X0 : ℝ) := by exact_mod_cast hpow
  have hlog_pow_le : Real.log ((2 : ℝ) ^ 19) ≤ Real.log (X0 : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ) ^ 19) hpow'
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog_pow_gt : (10 : ℝ) < Real.log ((2 : ℝ) ^ 19) := by
    -- `log(2^19) = 19*log 2 > 19*0.693... > 10`.
    have hmul1 : (19 : ℝ) * (0.6931471803 : ℝ) < (19 : ℝ) * Real.log 2 := by
      have : (0 : ℝ) < (19 : ℝ) := by norm_num
      exact mul_lt_mul_of_pos_left hlog2 this
    have hmul0 : (10 : ℝ) < (19 : ℝ) * (0.6931471803 : ℝ) := by
      norm_num
    have hmul2 : (10 : ℝ) < (19 : ℝ) * Real.log 2 := lt_trans hmul0 hmul1
    simpa [Real.log_pow] using hmul2
  exact le_trans hlog_pow_gt.le hlog_pow_le

lemma ten_le_log_of_X0_le {X : ℕ} (hX : X0 ≤ X) : (10 : ℝ) ≤ Real.log (X : ℝ) := by
  have hX0pos : (0 : ℝ) < (X0 : ℝ) := by
    norm_num [Goldbach.BankParams.X0, X0]
  have hX0leX : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog_le : Real.log (X0 : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hX0pos hX0leX
  exact le_trans ten_le_log_X0 hlog_le

end

end Goldbach.Cert.CanonLogBounds

