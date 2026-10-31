import Goldbach.Cert.MajorArcModules.RouteABalancedQ0CircleSplit
import Goldbach.Cert.MajorArcModules.ArcSetBounds

/-!
# Pointwise Q0 major-arc approximation for balanced Route A

This module connects the exact circle integrand from `RouteABalancedQ0CircleSplit` to the
real-frequency BMOR approximation. It keeps the Fourier phase visible, so the later sum over
reduced residues has the standard Ramanujan phase.

The result is still pointwise. Integrating it over each arc and summing the resulting bounds is the
next analytic step.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedQ0MajorArcApprox

open scoped BigOperators ArithmeticFunction.Moebius

open Complex AddCircle MeasureTheory

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep13RealToCircle
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORBridge
open Goldbach.Cert.MajorArcModules.RouteABalancedQ0CircleSplit

noncomputable section

/-- Geometric exponential sum occurring in the balanced BMOR main term. -/
noncomputable def balancedGeometricExpSum (L N : ℕ) (beta : ℝ) : ℂ :=
  ∑ n ∈ balancedCandidateSupport L N, gExp beta n

/-- Trivial cardinality bound for the balanced geometric sum. -/
theorem norm_balancedGeometricExpSum_le_card (L N : ℕ) (beta : ℝ) :
    ‖balancedGeometricExpSum L N beta‖
      ≤ ((balancedCandidateSupport L N).card : ℝ) := by
  unfold balancedGeometricExpSum
  calc
    ‖∑ n ∈ balancedCandidateSupport L N, gExp beta n‖
        ≤ ∑ n ∈ balancedCandidateSupport L N, ‖gExp beta n‖ := norm_sum_le _ _
    _ = ∑ _n ∈ balancedCandidateSupport L N, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact norm_gExp beta n
    _ = ((balancedCandidateSupport L N).card : ℝ) := by simp

theorem card_balancedCandidateSupport (L N : ℕ) :
    (balancedCandidateSupport L N).card = N - L + 1 - L := by
  simp [balancedCandidateSupport, Nat.card_Icc]

/-- BMOR main approximation to the balanced von Mangoldt exponential sum near `a/q`. -/
noncomputable def balancedBMORMain (L N q : ℕ) (beta : ℝ) : ℂ :=
  ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (μ q : ℂ)
    * balancedGeometricExpSum L N beta

/-- The BMOR main term is no larger than the length of the balanced support. -/
theorem norm_balancedBMORMain_le_card
    {q : ℕ} (hq : 1 ≤ q) (L N : ℕ) (beta : ℝ) :
    ‖balancedBMORMain L N q beta‖
      ≤ ((balancedCandidateSupport L N).card : ℝ) := by
  have hqPos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hphiNat : 0 < Nat.totient q := Nat.totient_pos.mpr hqPos
  have hphiReal : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast hphiNat
  have hphiRealPos : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast hphiNat
  have hrecip : ‖(((1 / (Nat.totient q : ℝ) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · exact (div_le_one hphiRealPos).2 hphiReal
    · exact one_div_nonneg.mpr hphiRealPos.le
  have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := q)
  have hmuReal : |((μ q : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hmuInt
  have hmu : ‖(μ q : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_intCast] using hmuReal
  have hgeo := norm_balancedGeometricExpSum_le_card L N beta
  unfold balancedBMORMain
  rw [norm_mul, norm_mul]
  calc
    ‖(((1 / (Nat.totient q : ℝ) : ℝ) : ℂ))‖ * ‖(μ q : ℂ)‖
          * ‖balancedGeometricExpSum L N beta‖
        ≤ 1 * 1 * ((balancedCandidateSupport L N).card : ℝ) := by
          gcongr
    _ = ((balancedCandidateSupport L N).card : ℝ) := by ring

/-- Explicit error supplied by the published BMOR progression estimate. -/
noncomputable def balancedBMORError (L N q : ℕ) (beta : ℝ) : ℝ :=
  (q : ℝ) *
      ((Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ * ((N - L : ℕ) : ℝ)
            / Real.log ((L - 1 : ℕ) : ℝ))
        * (2 * (2 + (((N - L) - (L - 1) : ℕ) : ℝ)
            * (4 * Real.pi * |beta|))))
    +
    (((q + 1) * (Nat.log 2 (N - L) + 1) : ℕ) : ℝ) * Real.log (q : ℝ)

/-- Fourier phase which extracts the exact-center coefficient at `N`. -/
noncomputable def balancedCirclePhase (N : ℕ) (alpha : ℝ) : ℂ :=
  e (((-(N : ℤ) : ℝ) * alpha))

/-- Phase-corrected quadratic BMOR model for the actual circle integrand. -/
noncomputable def balancedMajorArcModel
    (L N q : ℕ) (beta alpha : ℝ) : ℂ :=
  balancedBMORMain L N q beta ^ 2 * balancedCirclePhase N alpha

/-- Exact real-frequency normal form of the balanced circle integrand. -/
theorem balancedVonMangoldtIntervalIntegrand_eq_real
    {L N : ℕ} (hL : 2 ≤ L) (alpha : ℝ) :
    finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N alpha
      = balancedVonMangoldtRealExpSum L N alpha ^ 2
          * balancedCirclePhase N alpha := by
  unfold finiteWeightIntervalIntegrand finiteWeightCircleIntegrand balancedCirclePhase
  change
    balancedVonMangoldtCircleExpSum L N (alpha : UC) ^ 2
        * fourier (T := (1 : ℝ)) (-(N : ℤ)) (alpha : UC)
      = balancedVonMangoldtRealExpSum L N alpha ^ 2
          * e (((-(N : ℤ) : ℝ) * alpha))
  rw [balancedVonMangoldtCircleExpSum_coe_eq_real hL alpha]
  rw [fourier_coe_eq_e]
  push_cast
  rfl

/-- Named-form restatement of the checked linear BMOR approximation. -/
theorem norm_balancedVonMangoldtRealExpSum_sub_balancedBMORMain_le
    {q a L N : ℕ}
    (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {beta : ℝ} (hbeta : |2 * Real.pi * beta| ≤ 1) :
    ‖balancedVonMangoldtRealExpSum L N (beta + (a : ℝ) / (q : ℝ))
        - balancedBMORMain L N q beta‖
      ≤ balancedBMORError L N q beta := by
  simpa [balancedBMORMain, balancedBMORError, balancedGeometricExpSum] using
    (norm_balancedVonMangoldtRealExpSum_sub_muMainTerm_le_of_BMOR
      (q := q) (a := a) (L := L) (N := N)
      hLU hL hXmin hq ha hqQ0 (beta := beta) hbeta)

/-- Named-form restatement of the checked quadratic BMOR approximation. -/
theorem norm_balancedVonMangoldtRealExpSum_sq_sub_balancedBMORMain_sq_le
    {q a L N : ℕ}
    (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {beta : ℝ} (hbeta : |2 * Real.pi * beta| ≤ 1) :
    ‖balancedVonMangoldtRealExpSum L N (beta + (a : ℝ) / (q : ℝ)) ^ 2
        - balancedBMORMain L N q beta ^ 2‖
      ≤ balancedBMORError L N q beta
          * (2 * ‖balancedBMORMain L N q beta‖ + balancedBMORError L N q beta) := by
  simpa [balancedBMORMain, balancedBMORError, balancedGeometricExpSum] using
    (norm_balancedVonMangoldtRealExpSum_sq_sub_muMainTerm_sq_le_of_BMOR
      (q := q) (a := a) (L := L) (N := N)
      hLU hL hXmin hq ha hqQ0 (beta := beta) hbeta)

/--
The quadratic BMOR estimate controls the actual phase-corrected circle integrand at
`alpha = beta + a/q`. The unit Fourier phase introduces no additional loss.
-/
theorem norm_balancedIntervalIntegrand_sub_majorArcModel_le
    {q a L N : ℕ}
    (hLtwo : 2 ≤ L)
    (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    {beta alpha : ℝ} (halpha : alpha = beta + (a : ℝ) / (q : ℝ))
    (hbeta : |2 * Real.pi * beta| ≤ 1) :
    ‖finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N alpha
        - balancedMajorArcModel L N q beta alpha‖
      ≤ balancedBMORError L N q beta
          * (2 * ‖balancedBMORMain L N q beta‖ + balancedBMORError L N q beta) := by
  have hsq :=
    norm_balancedVonMangoldtRealExpSum_sq_sub_balancedBMORMain_sq_le
      (q := q) (a := a) (L := L) (N := N)
      hLU hL hXmin hq ha hqQ0 (beta := beta) hbeta
  rw [balancedVonMangoldtIntervalIntegrand_eq_real hLtwo alpha]
  unfold balancedMajorArcModel
  rw [halpha]
  calc
    ‖balancedVonMangoldtRealExpSum L N (beta + (a : ℝ) / (q : ℝ)) ^ 2
          * balancedCirclePhase N (beta + (a : ℝ) / (q : ℝ))
        - balancedBMORMain L N q beta ^ 2
          * balancedCirclePhase N (beta + (a : ℝ) / (q : ℝ))‖
        = ‖(balancedVonMangoldtRealExpSum L N (beta + (a : ℝ) / (q : ℝ)) ^ 2
              - balancedBMORMain L N q beta ^ 2)
            * balancedCirclePhase N (beta + (a : ℝ) / (q : ℝ))‖ := by
              congr 1
              ring
    _ = ‖balancedVonMangoldtRealExpSum L N (beta + (a : ℝ) / (q : ℝ)) ^ 2
            - balancedBMORMain L N q beta ^ 2‖ := by
          rw [norm_mul]
          simp [balancedCirclePhase, norm_e]
    _ ≤ balancedBMORError L N q beta
          * (2 * ‖balancedBMORMain L N q beta‖ + balancedBMORError L N q beta) := hsq

/-- Integral of the phase-corrected BMOR model over one rational arc. -/
noncomputable def balancedMajorArcModelIntegral
    (L N q a : ℕ) (Delta : ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    (arcSetTextbook N q a Delta).indicator
      (fun alpha =>
        balancedMajorArcModel L N q
          (alpha - (a : ℝ) / (q : ℝ)) alpha) alpha

lemma continuous_balancedMajorArcModel_local
    (L N q a : ℕ) :
    Continuous fun alpha : ℝ =>
      balancedMajorArcModel L N q
        (alpha - (a : ℝ) / (q : ℝ)) alpha := by
  unfold balancedMajorArcModel balancedBMORMain balancedGeometricExpSum
    balancedCirclePhase gExp e
  fun_prop

lemma intervalIntegrable_balancedMajorArcModel_local
    (L N q a : ℕ) :
    IntervalIntegrable
      (fun alpha : ℝ =>
        balancedMajorArcModel L N q
          (alpha - (a : ℝ) / (q : ℝ)) alpha)
      MeasureTheory.volume (0 : ℝ) (1 : ℝ) :=
  (continuous_balancedMajorArcModel_local L N q a).intervalIntegrable _ _

/--
Turn any pointwise cap on the actual-minus-model error into an explicit one-arc integral bound.
This is the reusable measure-theory step needed before summing the BMOR errors over `(q,a)`.
-/
theorem norm_balancedVonMangoldtArcIntegral_sub_model_le
    {L N q a : ℕ} {Delta C : ℝ}
    (hDelta : 0 ≤ Delta) (hq : 1 ≤ q) (hN : 0 < N) (hC : 0 ≤ C)
    (hpoint :
      ∀ alpha, alpha ∈ arcSetTextbook N q a Delta →
        ‖finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N alpha
            - balancedMajorArcModel L N q
                (alpha - (a : ℝ) / (q : ℝ)) alpha‖ ≤ C) :
    ‖balancedVonMangoldtArcIntegral L N q a Delta
        - balancedMajorArcModelIntegral L N q a Delta‖
      ≤ C * (2 * (Delta / ((q : ℝ) * (N : ℝ)))) := by
  let s : Set ℝ := arcSetTextbook N q a Delta
  let f : ℝ → ℂ :=
    finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N
  let m : ℝ → ℂ := fun alpha =>
    balancedMajorArcModel L N q (alpha - (a : ℝ) / (q : ℝ)) alpha
  have hs : MeasurableSet s := by
    simpa [s] using measurableSet_arcSetTextbook N q a Delta
  have hf : IntervalIntegrable f volume (0 : ℝ) (1 : ℝ) := by
    simpa [f] using
      (intervalIntegrable_finiteWeightIntervalIntegrand
        (balancedVonMangoldtWeight L N) N)
  have hm : IntervalIntegrable m volume (0 : ℝ) (1 : ℝ) := by
    simpa [m] using intervalIntegrable_balancedMajorArcModel_local L N q a
  have hfi : IntervalIntegrable (s.indicator f) volume (0 : ℝ) (1 : ℝ) :=
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      hs hf
  have hmi : IntervalIntegrable (s.indicator m) volume (0 : ℝ) (1 : ℝ) :=
    Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegrable_indicator_of_intervalIntegrable
      hs hm
  have hind : s.indicator f - s.indicator m = s.indicator (f - m) := by
    funext alpha
    by_cases halpha : alpha ∈ s <;> simp [halpha]
  have hint :
      balancedVonMangoldtArcIntegral L N q a Delta
          - balancedMajorArcModelIntegral L N q a Delta
        = ∫ alpha in (0 : ℝ)..(1 : ℝ), s.indicator (f - m) alpha := by
    calc
      balancedVonMangoldtArcIntegral L N q a Delta
            - balancedMajorArcModelIntegral L N q a Delta
          = (∫ alpha in (0 : ℝ)..(1 : ℝ), s.indicator f alpha)
              - ∫ alpha in (0 : ℝ)..(1 : ℝ), s.indicator m alpha := by
                rfl
      _ = ∫ alpha in (0 : ℝ)..(1 : ℝ),
            (s.indicator f - s.indicator m) alpha := by
              symm
              exact intervalIntegral.integral_sub hfi hmi
      _ = ∫ alpha in (0 : ℝ)..(1 : ℝ), s.indicator (f - m) alpha := by
            rw [hind]
  rw [hint]
  apply Goldbach.Cert.MajorArcModules.ArcSetBounds.norm_intervalIntegral_indicator_arcSetTextbook_le
    hDelta hq hN hC
  intro alpha halpha
  exact hpoint alpha halpha

end

end Goldbach.Cert.MajorArcModules.RouteABalancedQ0MajorArcApprox
