import Goldbach.Cert.MajorArcModules.RouteABalancedQ0MajorArcApprox
import Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle

/-!
# Integrated finite-cutoff BMOR approximation

This module transports the checked pointwise BMOR approximation to the seam-safe fundamental
interval and sums the resulting error over a finite denominator cutoff. It does not bound the
post-major remainder.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffMajorApprox

open scoped BigOperators

open Complex MeasureTheory

open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedQ0MajorArcApprox
open Goldbach.Cert.MajorArcModules.RouteABalancedQ0SeamSafeSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle

noncomputable section

/-- Integral of the phase-corrected BMOR model on one seam-safe rational arc. -/
noncomputable def balancedShiftedMajorArcModelIntegral
    (L N q a : ℕ) (Delta : ℝ) : ℂ :=
  ∫ alpha in balancedQ0FundamentalStart N Delta..
      (balancedQ0FundamentalStart N Delta + 1),
    (arcSetTextbook N q a Delta).indicator
      (fun alpha =>
        balancedMajorArcModel L N q
          (alpha - (a : ℝ) / (q : ℝ)) alpha) alpha

/-- Explicit pointwise quadratic BMOR cap at the outer edge of a textbook arc. -/
noncomputable def balancedBMORPointErrorCap
    (L N q : ℕ) (Delta : ℝ) : ℝ :=
  let radius := Delta / ((q : ℝ) * (N : ℝ))
  let E := balancedBMORError L N q radius
  E * (2 * ((balancedCandidateSupport L N).card : ℝ) + E)

lemma balancedBMORError_nonneg_of_log_pos
    {L N q : ℕ} {beta : ℝ}
    (hlog : 0 < Real.log ((L - 1 : ℕ) : ℝ)) :
    0 ≤ balancedBMORError L N q beta := by
  have hCpsi := Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ_nonneg
  have hNL : 0 ≤ (((N - L : ℕ) : ℝ)) := by positivity
  have hwidth : 0 ≤ ((((N - L) - (L - 1) : ℕ) : ℝ)) := by positivity
  have hfourPi : 0 ≤ (4 : ℝ) * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hlogq : 0 ≤ Real.log (q : ℝ) := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq0))
  unfold balancedBMORError
  positivity

lemma balancedBMORError_le_radius
    {L N q : ℕ} {Delta beta : ℝ}
    (hlog : 0 < Real.log ((L - 1 : ℕ) : ℝ))
    (hDelta : 0 ≤ Delta) (hq : 1 ≤ q) (hN : 0 < N)
    (hbeta : |beta| ≤ Delta / ((q : ℝ) * (N : ℝ))) :
    balancedBMORError L N q beta
      ≤ balancedBMORError L N q (Delta / ((q : ℝ) * (N : ℝ))) := by
  have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hradius : 0 ≤ Delta / ((q : ℝ) * (N : ℝ)) :=
    div_nonneg hDelta (mul_pos hqReal hNReal).le
  have hA :
      0 ≤ Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ * ((N - L : ℕ) : ℝ)
          / Real.log ((L - 1 : ℕ) : ℝ) := by
    exact div_nonneg
      (mul_nonneg Goldbach.Cert.ExplicitPNTinAP_BMOR.Cψ_nonneg (by positivity)) hlog.le
  have hwidth : 0 ≤ ((((N - L) - (L - 1) : ℕ) : ℝ)) := by positivity
  have hfourPi : 0 ≤ (4 : ℝ) * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  unfold balancedBMORError
  rw [abs_of_nonneg hradius]
  gcongr

lemma balancedBMORPointError_le_cap
    {L N q : ℕ} {Delta beta : ℝ}
    (hlog : 0 < Real.log ((L - 1 : ℕ) : ℝ))
    (hDelta : 0 ≤ Delta) (hq : 1 ≤ q) (hN : 0 < N)
    (hbeta : |beta| ≤ Delta / ((q : ℝ) * (N : ℝ))) :
    balancedBMORError L N q beta
          * (2 * ‖balancedBMORMain L N q beta‖ + balancedBMORError L N q beta)
      ≤ balancedBMORPointErrorCap L N q Delta := by
  let radius : ℝ := Delta / ((q : ℝ) * (N : ℝ))
  let E : ℝ := balancedBMORError L N q radius
  have hEbeta : 0 ≤ balancedBMORError L N q beta :=
    balancedBMORError_nonneg_of_log_pos hlog
  have hE : 0 ≤ E := by
    exact balancedBMORError_nonneg_of_log_pos hlog
  have hErr : balancedBMORError L N q beta ≤ E := by
    simpa [radius, E] using
      balancedBMORError_le_radius hlog hDelta hq hN hbeta
  have hMain := norm_balancedBMORMain_le_card hq L N beta
  have hSecond :
      2 * ‖balancedBMORMain L N q beta‖ + balancedBMORError L N q beta
        ≤ 2 * ((balancedCandidateSupport L N).card : ℝ) + E := by
    linarith
  have hSecondNonneg :
      0 ≤ 2 * ‖balancedBMORMain L N q beta‖ + balancedBMORError L N q beta := by
    positivity
  have hmul := mul_le_mul hErr hSecond hSecondNonneg hE
  simpa [balancedBMORPointErrorCap, radius, E] using hmul

lemma balancedBMORPointErrorCap_nonneg
    {L N q : ℕ} {Delta : ℝ}
    (hlog : 0 < Real.log ((L - 1 : ℕ) : ℝ)) :
    0 ≤ balancedBMORPointErrorCap L N q Delta := by
  have hE :
      0 ≤ balancedBMORError L N q (Delta / ((q : ℝ) * (N : ℝ))) :=
    balancedBMORError_nonneg_of_log_pos hlog
  unfold balancedBMORPointErrorCap
  positivity

lemma log_L_sub_one_pos_of_BMOR
    {L : ℕ}
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1) :
    0 < Real.log ((L - 1 : ℕ) : ℝ) := by
  have htwo : 2 ≤ L - 1 := by
    exact le_trans (by norm_num [Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin]) hXmin
  apply Real.log_pos
  exact_mod_cast htwo

/-- Closed-form integrated BMOR error through a finite denominator cutoff. -/
noncomputable def balancedBMORIntegratedMajorError
    (L N Q : ℕ) (Delta : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q,
    (Nat.totient q : ℝ) * balancedBMORPointErrorCap L N q Delta
      * (2 * (Delta / ((q : ℝ) * (N : ℝ))))

lemma intervalIntegrable_balancedMajorArcModel_local_at
    (L N q a : ℕ) (u v : ℝ) :
    IntervalIntegrable
      (fun alpha : ℝ =>
        balancedMajorArcModel L N q
          (alpha - (a : ℝ) / (q : ℝ)) alpha)
      volume u v :=
  (continuous_balancedMajorArcModel_local L N q a).intervalIntegrable _ _

/--
An arbitrary pointwise error cap on one rational arc integrates with exactly the arc-length loss.
Unlike the earlier `[0,1]` lemma, this theorem uses the seam-safe fundamental interval.
-/
theorem norm_balancedVonMangoldtShiftedArcIntegral_sub_model_le
    {L N q a : ℕ} {Delta C : ℝ}
    (hDelta : 0 ≤ Delta) (hq : 1 ≤ q) (hN : 0 < N) (hC : 0 ≤ C)
    (hpoint :
      ∀ alpha, alpha ∈ arcSetTextbook N q a Delta →
        ‖finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N alpha
            - balancedMajorArcModel L N q
                (alpha - (a : ℝ) / (q : ℝ)) alpha‖ ≤ C) :
    ‖balancedVonMangoldtShiftedArcIntegral L N q a Delta
        - balancedShiftedMajorArcModelIntegral L N q a Delta‖
      ≤ C * (2 * (Delta / ((q : ℝ) * (N : ℝ)))) := by
  let s : Set ℝ := arcSetTextbook N q a Delta
  let f : ℝ → ℂ :=
    finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N
  let m : ℝ → ℂ := fun alpha =>
    balancedMajorArcModel L N q (alpha - (a : ℝ) / (q : ℝ)) alpha
  let u : ℝ := balancedQ0FundamentalStart N Delta
  let v : ℝ := balancedQ0FundamentalStart N Delta + 1
  have hs : MeasurableSet s := by
    simpa [s] using measurableSet_arcSetTextbook N q a Delta
  have hf : IntervalIntegrable f volume u v := by
    simpa [f] using
      (continuous_finiteWeightIntervalIntegrand
        (balancedVonMangoldtWeight L N) N).intervalIntegrable u v
  have hm : IntervalIntegrable m volume u v := by
    simpa [m] using intervalIntegrable_balancedMajorArcModel_local_at L N q a u v
  have hfi : IntervalIntegrable (s.indicator f) volume u v :=
    ⟨hf.1.indicator hs, hf.2.indicator hs⟩
  have hmi : IntervalIntegrable (s.indicator m) volume u v :=
    ⟨hm.1.indicator hs, hm.2.indicator hs⟩
  have hind : s.indicator f - s.indicator m = s.indicator (f - m) := by
    funext alpha
    by_cases halpha : alpha ∈ s <;> simp [halpha]
  have hint :
      balancedVonMangoldtShiftedArcIntegral L N q a Delta
          - balancedShiftedMajorArcModelIntegral L N q a Delta
        = ∫ alpha in u..v, s.indicator (f - m) alpha := by
    calc
      balancedVonMangoldtShiftedArcIntegral L N q a Delta
            - balancedShiftedMajorArcModelIntegral L N q a Delta
          = (∫ alpha in u..v, s.indicator f alpha)
              - ∫ alpha in u..v, s.indicator m alpha := by
                rfl
      _ = ∫ alpha in u..v, (s.indicator f - s.indicator m) alpha := by
            symm
            exact intervalIntegral.integral_sub hfi hmi
      _ = ∫ alpha in u..v, s.indicator (f - m) alpha := by rw [hind]
  rw [hint]
  apply Goldbach.Cert.MajorArcModules.ArcSetBounds.norm_intervalIntegral_indicator_arcSetTextbook_le_at
    (u := u) (v := v) (by simp [u, v]) hDelta hq hN hC
  intro alpha halpha
  exact hpoint alpha halpha

/-- The checked BMOR theorem supplies the pointwise hypothesis in the preceding integral bound. -/
theorem norm_balancedVonMangoldtShiftedArcIntegral_sub_model_le_of_BMOR
    {L N q a : ℕ} {Delta C : ℝ}
    (hLtwo : 2 ≤ L) (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    (hDelta : 0 ≤ Delta) (hN : 0 < N) (hC : 0 ≤ C)
    (hAngular :
      2 * Real.pi * (Delta / ((q : ℝ) * (N : ℝ))) ≤ 1)
    (hCap :
      ∀ beta : ℝ, |beta| ≤ Delta / ((q : ℝ) * (N : ℝ)) →
        balancedBMORError L N q beta
              * (2 * ‖balancedBMORMain L N q beta‖
                + balancedBMORError L N q beta)
          ≤ C) :
    ‖balancedVonMangoldtShiftedArcIntegral L N q a Delta
        - balancedShiftedMajorArcModelIntegral L N q a Delta‖
      ≤ C * (2 * (Delta / ((q : ℝ) * (N : ℝ)))) := by
  apply norm_balancedVonMangoldtShiftedArcIntegral_sub_model_le
    hDelta hq hN hC
  intro alpha halpha
  have hbeta :
      |alpha - (a : ℝ) / (q : ℝ)| ≤ Delta / ((q : ℝ) * (N : ℝ)) := by
    simpa [arcSetTextbook] using halpha
  have htwoPi : 0 ≤ (2 : ℝ) * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hbetaAngular :
      |2 * Real.pi * (alpha - (a : ℝ) / (q : ℝ))| ≤ 1 := by
    calc
      |2 * Real.pi * (alpha - (a : ℝ) / (q : ℝ))|
          = (2 * Real.pi) * |alpha - (a : ℝ) / (q : ℝ)| := by
              rw [abs_mul, abs_of_nonneg htwoPi]
      _ ≤ (2 * Real.pi) * (Delta / ((q : ℝ) * (N : ℝ))) :=
            mul_le_mul_of_nonneg_left hbeta htwoPi
      _ ≤ 1 := hAngular
  exact
    (norm_balancedIntervalIntegrand_sub_majorArcModel_le
      (q := q) (a := a) (L := L) (N := N)
      hLtwo hLU hL hXmin hq ha hqQ0
      (beta := alpha - (a : ℝ) / (q : ℝ)) (alpha := alpha)
      (by ring) hbetaAngular).trans
      (hCap (alpha - (a : ℝ) / (q : ℝ)) hbeta)

/-- Finite sum of the seam-safe BMOR model integrals through denominator `Q`. -/
noncomputable def balancedMajorArcModelUpToIntegral
    (L N Q : ℕ) (Delta : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
    balancedShiftedMajorArcModelIntegral L N q a Delta

/-- Sum one-arc error bounds into a finite-cutoff major-integral error bound. -/
theorem norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le
    {L N Q : ℕ} {Delta : ℝ} {arcError : ℕ → ℝ}
    (hArc :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q, ∀ a ∈ Rcop q,
        ‖balancedVonMangoldtShiftedArcIntegral L N q a Delta
            - balancedShiftedMajorArcModelIntegral L N q a Delta‖
          ≤ arcError q) :
    ‖balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
        - balancedMajorArcModelUpToIntegral L N Q Delta‖
      ≤ ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ _a ∈ Rcop q, arcError q := by
  classical
  have hrewrite :
      balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
          - balancedMajorArcModelUpToIntegral L N Q Delta
        = ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
            (balancedVonMangoldtShiftedArcIntegral L N q a Delta
              - balancedShiftedMajorArcModelIntegral L N q a Delta) := by
    simp only [balancedVonMangoldtMajorArcUpToIntegral,
      balancedMajorArcModelUpToIntegral, Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    ‖∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
        (balancedVonMangoldtShiftedArcIntegral L N q a Delta
          - balancedShiftedMajorArcModelIntegral L N q a Delta)‖
        ≤ ∑ q ∈ Finset.Icc (1 : ℕ) Q,
            ‖∑ a ∈ Rcop q,
              (balancedVonMangoldtShiftedArcIntegral L N q a Delta
                - balancedShiftedMajorArcModelIntegral L N q a Delta)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
          ‖balancedVonMangoldtShiftedArcIntegral L N q a Delta
            - balancedShiftedMajorArcModelIntegral L N q a Delta‖ := by
          refine Finset.sum_le_sum ?_
          intro q hq
          exact norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ _a ∈ Rcop q, arcError q := by
          refine Finset.sum_le_sum ?_
          intro q hq
          exact Finset.sum_le_sum (fun a ha => hArc q hq a ha)

/--
Integrated BMOR error through a finite denominator cutoff. The caller supplies an explicit
pointwise cap for each denominator; this theorem performs all arc integration and finite summation.
-/
theorem norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_of_BMOR
    {L N Q : ℕ} {Delta : ℝ} {pointError : ℕ → ℝ}
    (hLtwo : 2 ≤ L) (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hQ0 : Q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    (hDelta : 0 ≤ Delta) (hN : 0 < N)
    (hPointErrorNonneg :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q, 0 ≤ pointError q)
    (hAngular :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q,
        2 * Real.pi * (Delta / ((q : ℝ) * (N : ℝ))) ≤ 1)
    (hCap :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q, ∀ beta : ℝ,
        |beta| ≤ Delta / ((q : ℝ) * (N : ℝ)) →
          balancedBMORError L N q beta
                * (2 * ‖balancedBMORMain L N q beta‖
                  + balancedBMORError L N q beta)
            ≤ pointError q) :
    ‖balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
        - balancedMajorArcModelUpToIntegral L N Q Delta‖
      ≤ ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ _a ∈ Rcop q,
          pointError q * (2 * (Delta / ((q : ℝ) * (N : ℝ)))) := by
  apply norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le
  intro q hqMem a haMem
  have hqBounds : 1 ≤ q ∧ q ≤ Q := Finset.mem_Icc.mp hqMem
  have hq : 1 ≤ q := hqBounds.1
  have hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := hqBounds.2.trans hQ0
  have ha : Nat.Coprime a q := by
    change a ∈ (Finset.range q).filter (fun r => Nat.Coprime r q) at haMem
    exact (Finset.mem_filter.mp haMem).2
  exact norm_balancedVonMangoldtShiftedArcIntegral_sub_model_le_of_BMOR
    hLtwo hLU hL hXmin hq ha hqQ0 hDelta hN
    (hPointErrorNonneg q hqMem) (hAngular q hqMem) (hCap q hqMem)

/--
The finite-cutoff major integral differs from its BMOR model by the explicit integrated error
function above. No per-arc cap remains as an input.
-/
theorem norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_explicit
    {L N Q : ℕ} {Delta : ℝ}
    (hLtwo : 2 ≤ L) (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hQ0 : Q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    (hDelta : 0 ≤ Delta) (hN : 0 < N)
    (hAngular :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q,
        2 * Real.pi * (Delta / ((q : ℝ) * (N : ℝ))) ≤ 1) :
    ‖balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
        - balancedMajorArcModelUpToIntegral L N Q Delta‖
      ≤ balancedBMORIntegratedMajorError L N Q Delta := by
  have hlog := log_L_sub_one_pos_of_BMOR hXmin
  have h := norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_of_BMOR
    hLtwo hLU hL hXmin hQ0 hDelta hN
    (pointError := fun q => balancedBMORPointErrorCap L N q Delta)
    (fun q hq => balancedBMORPointErrorCap_nonneg hlog)
    hAngular
    (fun q hq beta hbeta =>
      balancedBMORPointError_le_cap hlog hDelta (Finset.mem_Icc.mp hq).1 hN hbeta)
  calc
    ‖balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
        - balancedMajorArcModelUpToIntegral L N Q Delta‖
        ≤ ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ _a ∈ Rcop q,
            balancedBMORPointErrorCap L N q Delta
              * (2 * (Delta / ((q : ℝ) * (N : ℝ)))) := h
    _ = balancedBMORIntegratedMajorError L N Q Delta := by
          unfold balancedBMORIntegratedMajorError
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_const, card_Rcop_eq_totient]
          simp only [nsmul_eq_mul]
          push_cast
          ring

/-- A single base-scale inequality discharges every denominator-specific angular hypothesis. -/
theorem norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_explicit_of_base_angular
    {L N Q : ℕ} {Delta : ℝ}
    (hLtwo : 2 ≤ L) (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hQ0 : Q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    (hDelta : 0 ≤ Delta) (hN : 0 < N)
    (hAngularBase : 2 * Real.pi * Delta ≤ (N : ℝ)) :
    ‖balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
        - balancedMajorArcModelUpToIntegral L N Q Delta‖
      ≤ balancedBMORIntegratedMajorError L N Q Delta := by
  apply norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_explicit
    hLtwo hLU hL hXmin hQ0 hDelta hN
  intro q hqMem
  have hq : 1 ≤ q := (Finset.mem_Icc.mp hqMem).1
  have hqReal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (q : ℝ) * (N : ℝ) :=
    mul_pos (lt_of_lt_of_le zero_lt_one hqReal) hNReal
  have hNle : (N : ℝ) ≤ (q : ℝ) * (N : ℝ) := by nlinarith
  calc
    2 * Real.pi * (Delta / ((q : ℝ) * (N : ℝ)))
        = (2 * Real.pi * Delta) / ((q : ℝ) * (N : ℝ)) := by ring
    _ ≤ 1 := (div_le_one hden).2 (hAngularBase.trans hNle)

/-- At the canonical arc width `Delta = 1`, `N >= 8` is already enough for the angular condition. -/
theorem norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_explicit_one
    {L N Q : ℕ}
    (hLtwo : 2 ≤ L) (hLU : L ≤ N - L) (hL : 0 < L)
    (hXmin : Goldbach.Cert.ExplicitPNTinAP_BMOR.Xmin ≤ L - 1)
    (hQ0 : Q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    (hN : 8 ≤ N) :
    ‖balancedVonMangoldtMajorArcUpToIntegral L N Q 1
        - balancedMajorArcModelUpToIntegral L N Q 1‖
      ≤ balancedBMORIntegratedMajorError L N Q 1 := by
  apply norm_balancedMajorArcUpToIntegral_sub_modelUpTo_le_explicit_of_base_angular
    hLtwo hLU hL hXmin hQ0 (by norm_num) (by omega)
  have hpi : 2 * Real.pi < 8 := by nlinarith [Real.pi_lt_four]
  have hNReal : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  norm_num
  exact hpi.le.trans hNReal

end

end Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffMajorApprox
