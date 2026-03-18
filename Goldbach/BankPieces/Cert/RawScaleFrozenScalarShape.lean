import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
import Goldbach.Cert.MajorArcModules.Q0MajorSmallOuterIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma star_e (x : ℝ) : star (e x) = e (-x) := by
  unfold Goldbach.Cert.MajorArcExponential.e
  let z : ℂ := (Complex.I : ℂ) * (2 * Real.pi * x : ℂ)
  have hconjexp : star (Complex.exp z) = Complex.exp (star z) := by
    simpa [Complex.star_def] using (Complex.exp_conj (x := z)).symm
  have harg : star z = (Complex.I : ℂ) * (2 * Real.pi * (-x) : ℂ) := by
    simp [z, mul_assoc, mul_left_comm, mul_comm]
  rw [hconjexp, harg]
  simp

private lemma gExp_neg_eq_star (β : ℝ) (n : ℕ) :
    gExp (-β) n = star (gExp β n) := by
  unfold gExp
  simpa [neg_mul] using (star_e (β * (n : ℝ))).symm

/-- The centered exponential sum appearing in the frozen β-scalar. -/
noncomputable def frozenExpSumC (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp β n

private lemma frozenExpSumC_neg_eq_star (N : ℕ) (β : ℝ) :
    frozenExpSumC N (-β) = star (frozenExpSumC N β) := by
  calc
    frozenExpSumC N (-β)
      = ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), star (gExp β n) := by
          unfold frozenExpSumC
          refine Finset.sum_congr rfl ?_
          intro n hn
          simp [gExp_neg_eq_star]
    _ = star (frozenExpSumC N β) := by
          unfold frozenExpSumC
          symm
          simpa using
            (star_sum (s := Finset.Ico 4 ((N - 2) + 1)) (f := fun n : ℕ => gExp β n))

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_kernelPoly_real :
    Continuous fun β : ℝ => Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
  classical
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

private lemma continuous_smallBetaCenteredArchShell_zero (N : ℕ) :
    Continuous fun β : ℝ => smallBetaCenteredArchShell N 0 β := by
  have hK :
      Continuous fun β : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) :=
    continuous_kernelPoly_real
  have hS :
      Continuous fun β : ℝ => frozenExpSumC N β :=
    continuous_frozenExpSumC N
  have hSm :
      Continuous fun β : ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (-β) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    simpa using (continuous_gExp_real n).comp continuous_neg
  unfold smallBetaCenteredArchShell
  have hfour :
      Continuous fun _β : ℝ => (fourier (T := (1 : ℝ)) (-(N : ℤ)) ((0 : ℝ) : UC) : ℂ) :=
    continuous_const
  have hprod :
      Continuous fun β : ℝ =>
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (0 + β) n)
          *
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (0 - β) n) := by
    simpa using hS.mul hSm
  simpa [smallBetaCenteredArchShell] using hK.mul (hfour.mul hprod)

theorem smallBetaCenteredArchShell_zero_eq_kernel_mul_conj (N : ℕ) (β : ℝ) :
    smallBetaCenteredArchShell N 0 β =
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
        (frozenExpSumC N β * star (frozenExpSumC N β)) := by
  unfold smallBetaCenteredArchShell
  have hplus :
      (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (0 + β) n) = frozenExpSumC N β := by
    simp [frozenExpSumC]
  have hminus :
      (∑ n ∈ Finset.Ico 4 ((N - 2) + 1), gExp (0 - β) n) = frozenExpSumC N (-β) := by
    simp [frozenExpSumC]
  rw [hplus, hminus]
  rw [frozenExpSumC_neg_eq_star]
  simp [fourier_zero, mul_assoc, mul_left_comm, mul_comm]

theorem re_two_mul_smallBetaCenteredArchShell_zero_eq (N : ℕ) (β : ℝ) :
    Complex.re ((2 : ℂ) * smallBetaCenteredArchShell N 0 β)
      =
    2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * ‖frozenExpSumC N β‖ ^ 2 := by
  rw [smallBetaCenteredArchShell_zero_eq_kernel_mul_conj]
  have hsq :
      frozenExpSumC N β * star (frozenExpSumC N β)
        = ((‖frozenExpSumC N β‖ : ℂ) ^ 2) := by
    simpa using (RCLike.mul_conj (frozenExpSumC N β))
  rw [hsq]
  have hsqre :
      Complex.re (((‖frozenExpSumC N β‖ : ℂ) : ℂ) ^ 2)
        = ‖frozenExpSumC N β‖ ^ 2 := by
    simp [pow_two]
  have hsqim :
      Complex.im (((‖frozenExpSumC N β‖ : ℂ) : ℂ) ^ 2)
        = 0 := by
    simp [pow_two]
  norm_num [Complex.mul_re, hsqre, hsqim, mul_assoc, mul_left_comm, mul_comm]

private lemma intervalIntegrable_smallBetaCenteredArchShell_zero (N : ℕ) :
    IntervalIntegrable (fun β : ℝ => smallBetaCenteredArchShell N 0 β) volume
      Goldbach.Cert.MajorArcModules.BetaInterval.aβ
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
  (continuous_smallBetaCenteredArchShell_zero N).intervalIntegrable _ _

private lemma intervalIntegrable_betaSmall_indicator_smallBetaCenteredArchShell_zero (N : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β)
      volume
      Goldbach.Cert.MajorArcModules.BetaInterval.aβ
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      (intervalIntegrable_smallBetaCenteredArchShell_zero N)

theorem re_two_mul_frozenBetaScalarC_eq
    (N : ℕ) :
    Complex.re ((2 : ℂ) * frozenBetaScalarC N)
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          2 * Complex.re (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
            * ‖frozenExpSumC N β‖ ^ 2) β := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β)
        volume
        Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
    convert (intervalIntegrable_betaSmall_indicator_smallBetaCenteredArchShell_zero N).const_mul
      (2 : ℂ) using 1
    funext β
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [hβ, two_mul, mul_assoc]
    · simp [hβ]
  have hEq :
      (2 : ℂ) * frozenBetaScalarC N
        =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β := by
    unfold frozenBetaScalarC
    calc
      (2 : ℂ) *
          ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
              (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β
        =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        (2 : ℂ) *
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β := by
              exact (intervalIntegral.integral_const_mul
                (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
                (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
                (r := (2 : ℂ))
                (f := fun β : ℝ =>
                  Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
                    (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β)).symm
      _ =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β := by
            refine intervalIntegral.integral_congr_ae ?_
            exact Filter.Eventually.of_forall <| fun β _ => by
              by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
              · simp [hβ, mul_assoc]
              · simp [hβ]
  rw [hEq]
  have hab :
      Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        ≤ Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    Goldbach.Cert.MajorArcModules.BetaInterval.hle
  rw [intervalIntegral.integral_of_le hab]
  have hIntegrable :
      Integrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β)
        (volume.restrict
          (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)) := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le
        (μ := volume) (f := fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β) hab).1 hInt
  have hre :=
    (integral_re (μ := volume.restrict
      (Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ))
      (f := fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β) hIntegrable).symm
  have hre' :
      (∫ β in Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β ∂volume).re
        =
      ∫ β in Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          RCLike.re
            (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
              (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β) ∂volume := by
    simpa using hre
  rw [hre']
  rw [← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun β _ => by
    by_cases hβ :
        β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simpa [hβ] using re_two_mul_smallBetaCenteredArchShell_zero_eq N β
    · simp [hβ]

end

end Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
