import Goldbach.Cert.MajorArcModules.Q0MajorTailConstModeBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
import Goldbach.Cert.MajorArcStep17MajorMinorSplit

/-!
Constant-mode (`t = 0`) bookkeeping for the ε₂-large TT*/Toeplitz route.

The Toeplitz expansion uses the α-Fourier coefficients
`majorArcWeightFourier X Δ t = ∫_{0..1} 1_{MA_{Q0}(X,Δ)}(α) * e(tα) dα`.

The `t = 0` mode is special: it is just the (real) mass of the major-arc set.  We isolate a
deterministic bound for this mode that can be used as a separate term in any TT*/dispersion proof.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma intervalIntegrable_majorArcWeightC (X : ℕ) (Δ : ℝ) :
    IntervalIntegrable (fun α : ℝ => majorArcWeightC X Δ α) volume (0 : ℝ) (1 : ℝ) := by
  have hs : MeasurableSet (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ) :=
    Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
  -- Indicator of a constant is interval-integrable on a compact interval.
  refine
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      (s := Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ) hs ?_
  simpa [majorArcWeightC] using
    (intervalIntegrable_const : IntervalIntegrable (fun _α : ℝ => (1 : ℂ)) volume (0 : ℝ) (1 : ℝ))

private lemma norm_majorArcWeightC_eq_majorArcWeight (X : ℕ) (Δ : ℝ) (α : ℝ) :
    ‖majorArcWeightC X Δ α‖ = majorArcWeight X Δ α := by
  by_cases hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ
  · simp [majorArcWeightC, majorArcWeight, hα]
  · simp [majorArcWeightC, majorArcWeight, hα]

lemma norm_majorArcWeightFourier_zero_le_constMode (X : ℕ) (Δ : ℝ) :
    ‖majorArcWeightFourier X Δ 0‖ ≤ majorArcConstMode X Δ := by
  -- Rewrite the `t=0` coefficient as an integral of the indicator weight.
  have h0 :
      majorArcWeightFourier X Δ 0
        =
      ∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightC X Δ α := by
    -- `fourier 0 = 1`.
    simp [majorArcWeightFourier, fourier_zero, mul_assoc]
  -- Apply `‖∫ f‖ ≤ ∫ ‖f‖` and identify the integral of `‖W‖` with the real mass.
  have hnorm :
      ‖∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightC X Δ α‖
        ≤
      ∫ α in (0 : ℝ)..(1 : ℝ), ‖majorArcWeightC X Δ α‖ := by
    have hab01 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
    simpa using
      (intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun α : ℝ => majorArcWeightC X Δ α) hab01)
  have hrew :
      (∫ α in (0 : ℝ)..(1 : ℝ), ‖majorArcWeightC X Δ α‖)
        =
      majorArcConstMode X Δ := by
    -- Pointwise `‖majorArcWeightC‖ = majorArcWeight` and unfold `majorArcConstMode`.
    unfold majorArcConstMode
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro α
    simpa [norm_majorArcWeightC_eq_majorArcWeight (X := X) (Δ := Δ) (α := α)]
  -- Combine.
  simpa [h0, hrew] using hnorm

lemma norm_majorArcWeightFourier_zero_le
    {X : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hX : 0 < X) :
    ‖majorArcWeightFourier X Δ 0‖ ≤ (2 * Δ * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)) / (X : ℝ) := by
  refine le_trans (norm_majorArcWeightFourier_zero_le_constMode (X := X) (Δ := Δ)) ?_
  exact majorArcConstMode_le (X := X) (Δ := Δ) hΔ hX

lemma norm_majorArcWeightFourier_zero_le_two_div_X_mul_sum_totient_div
    {X : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hX : 0 < X) :
    ‖majorArcWeightFourier X Δ 0‖
      ≤
    ((2 * Δ) / (X : ℝ))
      * (∑ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0),
          (Nat.totient q : ℝ) / (q : ℝ)) := by
  refine le_trans (norm_majorArcWeightFourier_zero_le_constMode (X := X) (Δ := Δ)) ?_
  exact majorArcConstMode_le_two_div_X_mul_sum_totient_div (X := X) (Δ := Δ) hΔ hX

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
