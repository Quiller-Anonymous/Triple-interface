import Goldbach.Cert.MajorArcModules.RouteABalancedQ0CircleSplit

/-!
# Seam-safe finite-Q0 split for balanced Route A

The real representative interval `[0,1]` cuts the principal arc centered at `0`: its left half is
represented near `1` on the circle. For the direct balanced circle method that would leave a major
peak inside the nominal minor arcs.

This module uses the translated fundamental interval

`[-Delta / N, 1 - Delta / N]`.

It still has length one, so the exact Fourier coefficient is unchanged, while the full principal
arc is represented contiguously. The module proves the exact split and the finite `(q,a)`
extraction on that interval. No analytic estimate is introduced.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedQ0SeamSafeSplit

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- Left endpoint of the seam-safe length-one representative interval. -/
noncomputable def balancedQ0FundamentalStart (N : ℕ) (Delta : ℝ) : ℝ :=
  -Delta / (N : ℝ)

/-- Balanced major contribution on the seam-safe fundamental interval. -/
noncomputable def balancedVonMangoldtMajorArcQ0ShiftedIntegral
    (L N : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightSetIntegralAt (balancedVonMangoldtWeight L N) N
    (balancedQ0FundamentalStart N Delta) (majorArcSetQ0 N Delta)

/-- Balanced minor contribution on the seam-safe fundamental interval. -/
noncomputable def balancedVonMangoldtMinorArcQ0ShiftedIntegral
    (L N : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightSetComplementIntegralAt (balancedVonMangoldtWeight L N) N
    (balancedQ0FundamentalStart N Delta) (majorArcSetQ0 N Delta)

/-- Exact complex split on the seam-safe finite-`Q0` decomposition. -/
theorem balancedVonMangoldtPairConvolution_cast_eq_majorQ0Shifted_add_minorQ0Shifted
    (L N : ℕ) (Delta : ℝ) :
    (balancedVonMangoldtPairConvolution L N : ℂ)
      = balancedVonMangoldtMajorArcQ0ShiftedIntegral L N Delta
        + balancedVonMangoldtMinorArcQ0ShiftedIntegral L N Delta := by
  simpa [balancedVonMangoldtPairConvolution,
    balancedVonMangoldtMajorArcQ0ShiftedIntegral,
    balancedVonMangoldtMinorArcQ0ShiftedIntegral] using
    (finiteWeightPairConvolution_cast_eq_set_add_compl_at
      (balancedVonMangoldtWeight L N) N (balancedQ0FundamentalStart N Delta)
      (majorArcSetQ0 N Delta) (majorArcSetQ0_measurableSet N Delta))

/-- Real form of the exact seam-safe split. -/
theorem balancedVonMangoldtPairConvolution_eq_majorQ0Shifted_re_add_minorQ0Shifted_re
    (L N : ℕ) (Delta : ℝ) :
    balancedVonMangoldtPairConvolution L N
      = (balancedVonMangoldtMajorArcQ0ShiftedIntegral L N Delta).re
        + (balancedVonMangoldtMinorArcQ0ShiftedIntegral L N Delta).re := by
  have h := congrArg Complex.re
    (balancedVonMangoldtPairConvolution_cast_eq_majorQ0Shifted_add_minorQ0Shifted
      L N Delta)
  simpa using h

/-- Extract the finite `Q0` union on any real interval. -/
theorem intervalIntegral_majorArcSetQ0_indicator_eq_sum_at
    (X : ℕ) (Delta : ℝ) (hsep : SepQ0 X Delta) (f : ℝ → ℂ)
    (u v : ℝ) (hf : IntervalIntegrable f volume u v) :
    (∫ x in u..v, (majorArcSetQ0 X Delta).indicator f x)
      = ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          ∫ x in u..v, (arcSetTextbook X q a Delta).indicator f x := by
  classical
  have hfun :
      (fun x : ℝ => (majorArcSetQ0 X Delta).indicator f x)
        = fun x : ℝ =>
            ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
              (arcSetTextbook X q a Delta).indicator f x := by
    funext x
    simpa using indicator_majorArcSetQ0_eq_sum X Delta hsep f x
  have hqInt :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        IntervalIntegrable
          (fun x : ℝ => ∑ a ∈ Rcop q,
            (arcSetTextbook X q a Delta).indicator f x)
          volume u v := by
    intro q hq
    have haInt :
        ∀ a ∈ Rcop q,
          IntervalIntegrable
            (fun x : ℝ => (arcSetTextbook X q a Delta).indicator f x)
            volume u v := by
      intro a ha
      have hs := measurableSet_arcSetTextbook X q a Delta
      exact ⟨hf.1.indicator hs, hf.2.indicator hs⟩
    have hsum :
        IntervalIntegrable
          (∑ a ∈ Rcop q,
            fun x : ℝ => (arcSetTextbook X q a Delta).indicator f x)
          volume u v :=
      IntervalIntegrable.sum (μ := volume) (a := u) (b := v)
        (s := Rcop q)
        (f := fun a x => (arcSetTextbook X q a Delta).indicator f x) haInt
    have hsumFun :
        (∑ a ∈ Rcop q,
            fun x : ℝ => (arcSetTextbook X q a Delta).indicator f x)
          = fun x : ℝ => ∑ a ∈ Rcop q,
              (arcSetTextbook X q a Delta).indicator f x := by
      funext x
      simp
    rw [hsumFun] at hsum
    exact hsum
  calc
    (∫ x in u..v, (majorArcSetQ0 X Delta).indicator f x)
        = ∫ x in u..v,
            (∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
              (arcSetTextbook X q a Delta).indicator f x) := by
                rw [hfun]
    _ = ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∫ x in u..v, ∑ a ∈ Rcop q,
            (arcSetTextbook X q a Delta).indicator f x := by
              simpa using
                (intervalIntegral.integral_finset_sum
                  (a := u) (b := v) (μ := volume)
                  (s := Finset.Icc (1 : ℕ) Q0)
                  (f := fun q x => ∑ a ∈ Rcop q,
                    (arcSetTextbook X q a Delta).indicator f x) hqInt)
    _ = ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          ∫ x in u..v, (arcSetTextbook X q a Delta).indicator f x := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            have haInt :
                ∀ a ∈ Rcop q,
                  IntervalIntegrable
                    (fun x : ℝ => (arcSetTextbook X q a Delta).indicator f x)
                    volume u v := by
              intro a ha
              have hs := measurableSet_arcSetTextbook X q a Delta
              exact ⟨hf.1.indicator hs, hf.2.indicator hs⟩
            simpa using
              (intervalIntegral.integral_finset_sum
                (a := u) (b := v) (μ := volume) (s := Rcop q)
                (f := fun a x => (arcSetTextbook X q a Delta).indicator f x) haInt)

/-- One exact rational-arc contribution on the seam-safe fundamental interval. -/
noncomputable def balancedVonMangoldtShiftedArcIntegral
    (L N q a : ℕ) (Delta : ℝ) : ℂ :=
  ∫ alpha in balancedQ0FundamentalStart N Delta..
      (balancedQ0FundamentalStart N Delta + 1),
    (arcSetTextbook N q a Delta).indicator
      (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha

/-- Extract the seam-safe balanced major integral into individual rational arcs. -/
theorem balancedVonMangoldtMajorArcQ0ShiftedIntegral_eq_sum
    (L N : ℕ) (Delta : ℝ) (hsep : SepQ0 N Delta) :
    balancedVonMangoldtMajorArcQ0ShiftedIntegral L N Delta
      = ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          balancedVonMangoldtShiftedArcIntegral L N q a Delta := by
  have hInt :
      IntervalIntegrable
        (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N)
        volume (balancedQ0FundamentalStart N Delta)
          (balancedQ0FundamentalStart N Delta + 1) :=
    (continuous_finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N).intervalIntegrable
      _ _
  simpa [balancedVonMangoldtMajorArcQ0ShiftedIntegral,
    finiteWeightSetIntegralAt, balancedVonMangoldtShiftedArcIntegral] using
    (intervalIntegral_majorArcSetQ0_indicator_eq_sum_at
      N Delta hsep
      (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N)
      (balancedQ0FundamentalStart N Delta)
      (balancedQ0FundamentalStart N Delta + 1) hInt)

/-- Honest analytic interface on the seam-safe finite-`Q0` decomposition. -/
structure BalancedQ0ShiftedVonMangoldtAnalyticCertificate
    (L Xmin : ℕ) (Delta : ℝ)
    (main majorError minorError : ℕ → ℝ) : Prop where
  two_le_threshold : 2 ≤ Xmin
  major_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(balancedVonMangoldtMajorArcQ0ShiftedIntegral L N Delta).re - main N|
        ≤ majorError N
  minor_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖balancedVonMangoldtMinorArcQ0ShiftedIntegral L N Delta‖ ≤ minorError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + minorError N
          + (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2
        < main N

/-- The seam-safe finite-`Q0` analytic certificate gives a genuine Goldbach representation. -/
theorem goldbachRep_of_balancedQ0ShiftedAnalyticCertificate
    {L Xmin : ℕ} {Delta : ℝ}
    {main majorError minorError : ℕ → ℝ}
    (hcert : BalancedQ0ShiftedVonMangoldtAnalyticCertificate L Xmin Delta
      main majorError minorError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N := by
  have hmajorAbs := hcert.major_approx hN hEven
  have hmajorLower :
      main N - majorError N
        ≤ (balancedVonMangoldtMajorArcQ0ShiftedIntegral L N Delta).re := by
    have h := (abs_le.mp hmajorAbs).1
    linarith
  have hminorAbs :
      |(balancedVonMangoldtMinorArcQ0ShiftedIntegral L N Delta).re| ≤ minorError N :=
    (Complex.abs_re_le_norm _).trans (hcert.minor_bound hN hEven)
  have hminorLower :
      -minorError N ≤ (balancedVonMangoldtMinorArcQ0ShiftedIntegral L N Delta).re :=
    (abs_le.mp hminorAbs).1
  have hPower := balancedPrimePowerContamination_le_five_halves_sqrt_log_sq
    (L := L) (hcert.two_le_threshold.trans hN)
  have hBudget := hcert.strict_budget hN hEven
  have hDecomp := balancedVonMangoldtPairConvolution_eq_prime_add_contamination L N
  have hCircle :=
    balancedVonMangoldtPairConvolution_eq_majorQ0Shifted_re_add_minorQ0Shifted_re
      L N Delta
  apply goldbachRep_of_balancedPrimePairConvolution_pos
  rw [hDecomp] at hCircle
  linarith

/-- A finite base plus the seam-safe balanced certificate closes Goldbach. -/
theorem goldbach_of_finiteBase_and_balancedQ0ShiftedAnalyticCertificate
    {L Xmin : ℕ} {Delta : ℝ}
    {main majorError minorError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BalancedQ0ShiftedVonMangoldtAnalyticCertificate L Xmin Delta
      main majorError minorError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_balancedQ0ShiftedAnalyticCertificate hcert (by omega) hEven

end

end Goldbach.Cert.MajorArcModules.RouteABalancedQ0SeamSafeSplit
