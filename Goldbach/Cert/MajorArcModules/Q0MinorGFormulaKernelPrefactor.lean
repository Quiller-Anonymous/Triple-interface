import Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteABookkeeping

/-!
Local deterministic prefactor lemmas for the geometric Route A kernel budget.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private lemma geometricWindowParityMassConst_sum_eq_square :
    geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst
      = (((2 * H + 1 : ℕ) : ℝ) ^ 2) := by
  norm_num [geometricWindowParityMassEvenConst, geometricWindowParityMassOddConst, H]

private lemma norm_uniformWindowNormalization_eq_inv_mul
    {X : ℕ} (hX : X0 ≤ X) :
    ‖uniformWindowNormalization X‖
      = (((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℝ)⁻¹ := by
  have hlog_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX
  have hlog_pos : 0 < Real.log (X : ℝ) := by
    linarith
  unfold uniformWindowNormalization
  change ‖((Real.log (X : ℝ) : ℂ) * ((((2 * H + 1 : ℕ) : ℝ) : ℂ)) )⁻¹‖
      = (((Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ)) : ℝ)⁻¹
  have hnorm_mul :
      ‖((Real.log (X : ℝ) : ℂ) * ((((2 * H + 1 : ℕ) : ℝ) : ℂ)) )‖
        =
      (Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ) := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt hlog_pos), abs_of_nonneg (by positivity)]
  rw [norm_inv, hnorm_mul]

private lemma norm_uniformWindowNormalization_le_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    ‖uniformWindowNormalization X‖
      ≤ (((13 : ℝ) * ((2 * H + 1 : ℕ) : ℝ)) : ℝ)⁻¹ := by
  have hlog_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX
  have hmul :
      (13 : ℝ) * ((2 * H + 1 : ℕ) : ℝ)
        ≤ (Real.log (X : ℝ)) * ((2 * H + 1 : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonneg_right hlog_ge13 (by positivity)
  rw [norm_uniformWindowNormalization_eq_inv_mul hX]
  simpa [one_div] using
    (one_div_le_one_div_of_le (by positivity) hmul)

theorem uniformWindowParityPrefactor_le_one
    {X : ℕ} (hX : X0 ≤ X) :
    ‖uniformWindowNormalization X‖ ^ 4
      * (geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst)
      ≤ 1 := by
  have hU :=
    norm_uniformWindowNormalization_le_explicit (X := X) hX
  have hpow :
      ‖uniformWindowNormalization X‖ ^ 4
        ≤ ((((13 : ℝ) * ((2 * H + 1 : ℕ) : ℝ)) : ℝ)⁻¹) ^ 4 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hU 4
  have hmass_nonneg : 0 ≤ geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst := by
    norm_num [geometricWindowParityMassEvenConst, geometricWindowParityMassOddConst, H]
  calc
    ‖uniformWindowNormalization X‖ ^ 4
        * (geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst)
      ≤
    ((((13 : ℝ) * ((2 * H + 1 : ℕ) : ℝ)) : ℝ)⁻¹) ^ 4
        * (geometricWindowParityMassEvenConst + geometricWindowParityMassOddConst) := by
          exact mul_le_mul_of_nonneg_right hpow hmass_nonneg
    _ ≤ 1 := by
      norm_num [geometricWindowParityMassConst_sum_eq_square, H]

end

end Q0MinorGFormulaRouteA
