import Goldbach.BankPieces.Cert.RawScaleFrozenKernelLower
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval

namespace Goldbach.BankPieces.Cert.RawScaleFrozenScalarLower

open scoped BigOperators

open Complex MeasureTheory
open Goldbach
open Goldbach.Windows
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.BankPieces.Cert.RawScaleFrozenKernelLower
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_kernelPoly_real :
    Continuous fun β : ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
  dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
    Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
  refine continuous_finset_sum _ ?_
  intro k hk
  exact continuous_const.mul (((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC)

private lemma continuous_gExp_real (n : ℕ) : Continuous fun β : ℝ => gExp β n := by
  unfold gExp Goldbach.Cert.MajorArcExponential.e
  have hmul : Continuous fun β : ℝ => ((β : ℂ) * (n : ℂ)) := continuous_ofReal.mul continuous_const
  have hscale : Continuous fun β : ℝ => ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hmul
  have hexpArg :
      Continuous fun β : ℝ => (Complex.I : ℂ) * ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hscale
  simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.continuous_exp.comp hexpArg

private lemma continuous_frozenExpSumC (N : ℕ) :
    Continuous fun β : ℝ => frozenExpSumC N β := by
  classical
  unfold frozenExpSumC
  refine continuous_finset_sum _ ?_
  intro n hn
  exact continuous_gExp_real n

private lemma intervalIntegrable_scalarIntegrand (N : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * ‖frozenExpSumC N β‖ ^ 2)
      volume aβ bβ := by
  have hcont :
      Continuous
        (fun β : ℝ =>
          2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
            * ‖frozenExpSumC N β‖ ^ 2) := by
    let hK : Continuous fun β : ℝ =>
        Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)) :=
      Complex.continuous_re.comp continuous_kernelPoly_real
    let hS : Continuous fun β : ℝ => ‖frozenExpSumC N β‖ ^ 2 :=
      (continuous_frozenExpSumC N).norm.pow 2
    have hmul : Continuous fun β : ℝ =>
        (2 : ℝ) * (Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * ‖frozenExpSumC N β‖ ^ 2) := continuous_const.mul (hK.mul hS)
    simpa [mul_assoc] using hmul
  exact hcont.intervalIntegrable _ _

private lemma intervalIntegrable_normSq_frozenExpSumC (N : ℕ) :
    IntervalIntegrable (fun β : ℝ => ‖frozenExpSumC N β‖ ^ 2) volume aβ bβ := by
  exact ((continuous_frozenExpSumC N).norm.pow 2).intervalIntegrable _ _

private lemma scalar_lower_pointwise
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    ∀ β : ℝ,
      (tinyBetaSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)) β
        - (2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2)
      ≤
      betaSmallSet.indicator
        (fun β : ℝ =>
          2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
            * ‖frozenExpSumC N β‖ ^ 2) β := by
  have htail0 : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
    have htail_val : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
      norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
    nlinarith [htail_val]
  have hsubsetTiny : tinyBetaSet X ⊆ betaSmallSet := by
    intro β hβ
    have hβ' : -(tinyBetaRadius X) ≤ β ∧ β ≤ tinyBetaRadius X := by
      simpa [tinyBetaSet, Set.mem_Icc] using hβ
    have habs : |β| ≤ tinyBetaRadius X := (abs_le).2 ⟨by simpa using hβ'.1, hβ'.2⟩
    have hrad : tinyBetaRadius X ≤ betaSmallRadius := tinyBetaRadius_le_betaSmallRadius X
    exact by
      have : |β| ≤ betaSmallRadius := le_trans habs hrad
      simpa [betaSmallSet, Set.mem_Icc] using (abs_le.mp this)
  intro β
  by_cases hβsmall : β ∈ betaSmallSet
  · by_cases hβtiny : β ∈ tinyBetaSet X
    · have htiny :
          ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
            ≤
          2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
            * ‖frozenExpSumC N β‖ ^ 2 :=
        quarter_sq_div_two_le_scalarIntegrand_of_mem_tinyBetaSet hX hN hβtiny
      have htail_nonneg : 0 ≤ 2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2 := by
        nlinarith [htail0, sq_nonneg ‖frozenExpSumC N β‖]
      simp [Set.indicator_of_mem, hβsmall, hβtiny]
      linarith
    · have htail :
          -(2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2)
            ≤
          2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
            * ‖frozenExpSumC N β‖ ^ 2 :=
        scalarIntegrand_ge_neg_two_mul_C_tail_closed_mul_normSq
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hβsmall, hβtiny]
      exact htail
  · have hβnotiny : β ∉ tinyBetaSet X := by
      intro hβtiny
      exact hβsmall (hsubsetTiny hβtiny)
    have htail_nonneg : 0 ≤ 2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2 := by
      nlinarith [htail0, sq_nonneg ‖frozenExpSumC N β‖]
    simp [Set.indicator_of_notMem, hβsmall, hβnotiny]
    linarith

/-- Explicit scalar lower bound from tiny-interval positivity minus the global outer-band tail. -/
theorem re_two_mul_frozenBetaScalarC_lower_bound_explicit
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
      - 2 * Goldbach.BG_Identity.C_tail_closed * (N - 5 : ℝ)
      ≤
    Complex.re ((2 : ℂ) * frozenBetaScalarC N) := by
  have hN5 : 5 ≤ N := by
    have hX5 : 5 ≤ X := le_trans (by decide : 5 ≤ BankParams.X0) hX
    exact le_trans hX5 (Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN)
  have hab : aβ ≤ bβ := hle
  have hUpperInt :
      IntervalIntegrable
        (betaSmallSet.indicator
          (fun β : ℝ =>
            2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
              * ‖frozenExpSumC N β‖ ^ 2))
        volume aβ bβ := by
    exact intervalIntegrable_indicator_of_intervalIntegrable measurableSet_betaSmallSet
      (intervalIntegrable_scalarIntegrand N)
  have hTinyConstInt :
      IntervalIntegrable
        ((tinyBetaSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)))
        volume aβ bβ := by
    have hmeasTiny : MeasurableSet (tinyBetaSet X) := by
      simp [tinyBetaSet]
    have hconst :
        IntervalIntegrable (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8 : ℝ)) volume aβ bβ := by
      simpa using
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8 : ℝ)) volume aβ bβ)
    exact intervalIntegrable_indicator_of_intervalIntegrable
      hmeasTiny hconst
  have hNormSqInt : IntervalIntegrable (fun β : ℝ => ‖frozenExpSumC N β‖ ^ 2) volume aβ bβ :=
    intervalIntegrable_normSq_frozenExpSumC N
  have hTailInt' :
      IntervalIntegrable
        (fun β : ℝ => 2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2)
        volume aβ bβ := by
    exact (Continuous.intervalIntegrable
      (continuous_const.mul ((continuous_frozenExpSumC N).norm.pow 2)) _ _)
  have hLowerInt :
      IntervalIntegrable
        (fun β : ℝ =>
          (tinyBetaSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)) β
            - (2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2))
        volume aβ bβ := hTinyConstInt.sub hTailInt'
  have hmono :=
    intervalIntegral.integral_mono_on (μ := volume) (a := aβ) (b := bβ)
      hab hLowerInt hUpperInt (fun β _ => scalar_lower_pointwise hX hN β)
  rw [re_two_mul_frozenBetaScalarC_eq]
  have hsplit :
      (∫ β in aβ..bβ,
          (tinyBetaSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)) β
            - (2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2))
        =
      (∫ β in aβ..bβ,
          (tinyBetaSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)) β)
        -
      ∫ β in aβ..bβ, (2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2) := by
    exact intervalIntegral.integral_sub hTinyConstInt hTailInt'
  have hTinyEval :
      (∫ β in aβ..bβ,
          (tinyBetaSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)) β)
        =
      (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8) := by
    simpa using
      integral_indicator_tinyBetaSet_const_eq_volume_mul_const X ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
  have hTailEval :
      (∫ β in aβ..bβ, (2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2))
        =
      2 * Goldbach.BG_Identity.C_tail_closed * (N - 5 : ℝ) := by
    rw [intervalIntegral.integral_const_mul]
    simp [integral_normSq_frozenExpSumC_aβ_bβ_eq_N_sub_5 (N := N) hN5]
  calc
    (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
        - 2 * Goldbach.BG_Identity.C_tail_closed * (N - 5 : ℝ)
      =
    (∫ β in aβ..bβ,
        (tinyBetaSet X).indicator (fun _ : ℝ => ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)) β
          - (2 * Goldbach.BG_Identity.C_tail_closed * ‖frozenExpSumC N β‖ ^ 2)) := by
        rw [hsplit, hTinyEval, hTailEval]
    _ ≤
      ∫ β in aβ..bβ,
        betaSmallSet.indicator
          (fun β : ℝ =>
            2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
              * ‖frozenExpSumC N β‖ ^ 2) β := hmono

end

end Goldbach.BankPieces.Cert.RawScaleFrozenScalarLower
