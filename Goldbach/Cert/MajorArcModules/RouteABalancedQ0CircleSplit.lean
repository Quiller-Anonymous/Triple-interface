import Goldbach.Cert.MajorArcModules.RouteABalancedBMORBridge
import Goldbach.Cert.MajorArcStep24IntegralExtraction

/-!
# Finite-Q0 circle split for balanced Route A

This module replaces the obsolete banked-kernel integration layer by applying the generic exact
circle identity directly to the balanced von Mangoldt weight. The major arcs are the finite union
with denominators `q ≤ Q0`, exactly the range on which the existing explicit BMOR estimate is
available.

Everything here is exact measure-theory bookkeeping:

* the balanced convolution is the sum of its `Q0` major and minor contributions;
* under the standard separation condition, the major contribution is a finite sum over the
  individual reduced rational arcs.

No major-arc approximation or minor-arc estimate is assumed or proved in this module.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedQ0CircleSplit

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- Balanced von Mangoldt contribution on the finite `q ≤ Q0` major-arc union. -/
noncomputable def balancedVonMangoldtMajorArcQ0Integral
    (L N : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightSetIntegral (balancedVonMangoldtWeight L N) N (majorArcSetQ0 N Delta)

/-- Balanced von Mangoldt contribution on the complement of the finite `Q0` major arcs. -/
noncomputable def balancedVonMangoldtMinorArcQ0Integral
    (L N : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightSetComplementIntegral
    (balancedVonMangoldtWeight L N) N (majorArcSetQ0 N Delta)

/-- Exact complex major/minor split on the finite `Q0` arc decomposition. -/
theorem balancedVonMangoldtPairConvolution_cast_eq_majorQ0_add_minorQ0
    (L N : ℕ) (Delta : ℝ) :
    (balancedVonMangoldtPairConvolution L N : ℂ)
      = balancedVonMangoldtMajorArcQ0Integral L N Delta
        + balancedVonMangoldtMinorArcQ0Integral L N Delta := by
  simpa [balancedVonMangoldtPairConvolution,
    balancedVonMangoldtMajorArcQ0Integral, balancedVonMangoldtMinorArcQ0Integral] using
    (finiteWeightPairConvolution_cast_eq_set_add_compl
      (balancedVonMangoldtWeight L N) N (majorArcSetQ0 N Delta)
      (majorArcSetQ0_measurableSet N Delta))

/-- Real form of the exact finite-`Q0` major/minor split. -/
theorem balancedVonMangoldtPairConvolution_eq_majorQ0_re_add_minorQ0_re
    (L N : ℕ) (Delta : ℝ) :
    balancedVonMangoldtPairConvolution L N
      = (balancedVonMangoldtMajorArcQ0Integral L N Delta).re
        + (balancedVonMangoldtMinorArcQ0Integral L N Delta).re := by
  have h := congrArg Complex.re
    (balancedVonMangoldtPairConvolution_cast_eq_majorQ0_add_minorQ0 L N Delta)
  simpa using h

/-- The exact contribution of one reduced rational arc to the balanced circle integral. -/
noncomputable def balancedVonMangoldtArcIntegral
    (L N q a : ℕ) (Delta : ℝ) : ℂ :=
  ∫ alpha in (0 : ℝ)..(1 : ℝ),
    (arcSetTextbook N q a Delta).indicator
      (finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N) alpha

/--
Extract the finite `Q0` major contribution into its individual `(q,a)` arcs. The separation
hypothesis is purely geometric and is already discharged by `sepQ0_one_of_two_mul_Q0_lt` when
`Delta = 1` and `N > 60000`.
-/
theorem balancedVonMangoldtMajorArcQ0Integral_eq_sum
    (L N : ℕ) (Delta : ℝ) (hsep : SepQ0 N Delta) :
    balancedVonMangoldtMajorArcQ0Integral L N Delta
      = ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          balancedVonMangoldtArcIntegral L N q a Delta := by
  simpa [balancedVonMangoldtMajorArcQ0Integral, finiteWeightSetIntegral,
    balancedVonMangoldtArcIntegral] using
    (intervalIntegral_majorArcSetQ0_indicator_eq_sum
      (X := N) (Δ := Delta) (hsep := hsep)
      (f := finiteWeightIntervalIntegrand (balancedVonMangoldtWeight L N) N)
      (intervalIntegrable_finiteWeightIntervalIntegrand
        (balancedVonMangoldtWeight L N) N))

/-- The canonical `Delta = 1` extraction above the elementary separation threshold. -/
theorem balancedVonMangoldtMajorArcQ0Integral_one_eq_sum
    (L N : ℕ) (hN : 2 * Goldbach.AO_OffDiag.TailBlock.Q0 < N) :
    balancedVonMangoldtMajorArcQ0Integral L N (1 : ℝ)
      = ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q,
          balancedVonMangoldtArcIntegral L N q a (1 : ℝ) :=
  balancedVonMangoldtMajorArcQ0Integral_eq_sum L N (1 : ℝ)
    (sepQ0_one_of_two_mul_Q0_lt hN)

/--
Honest analytic interface for the finite-`Q0` balanced route. Its two estimate fields are the
remaining mathematical work; the circle decomposition and prime-power allowance are already
proved.
-/
structure BalancedQ0VonMangoldtAnalyticCertificate
    (L Xmin : ℕ) (Delta : ℝ)
    (main majorError minorError : ℕ → ℝ) : Prop where
  two_le_threshold : 2 ≤ Xmin
  major_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(balancedVonMangoldtMajorArcQ0Integral L N Delta).re - main N|
        ≤ majorError N
  minor_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖balancedVonMangoldtMinorArcQ0Integral L N Delta‖ ≤ minorError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + minorError N
          + (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2
        < main N

/-- A finite-`Q0` balanced analytic certificate gives a genuine Goldbach representation. -/
theorem goldbachRep_of_balancedQ0AnalyticCertificate
    {L Xmin : ℕ} {Delta : ℝ}
    {main majorError minorError : ℕ → ℝ}
    (hcert : BalancedQ0VonMangoldtAnalyticCertificate L Xmin Delta
      main majorError minorError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N := by
  have hmajorAbs := hcert.major_approx hN hEven
  have hmajorLower :
      main N - majorError N
        ≤ (balancedVonMangoldtMajorArcQ0Integral L N Delta).re := by
    have h := (abs_le.mp hmajorAbs).1
    linarith
  have hminorAbs :
      |(balancedVonMangoldtMinorArcQ0Integral L N Delta).re| ≤ minorError N :=
    (Complex.abs_re_le_norm _).trans (hcert.minor_bound hN hEven)
  have hminorLower :
      -minorError N ≤ (balancedVonMangoldtMinorArcQ0Integral L N Delta).re :=
    (abs_le.mp hminorAbs).1
  have hPower := balancedPrimePowerContamination_le_five_halves_sqrt_log_sq
    (L := L) (hcert.two_le_threshold.trans hN)
  have hBudget := hcert.strict_budget hN hEven
  have hDecomp := balancedVonMangoldtPairConvolution_eq_prime_add_contamination L N
  have hCircle :=
    balancedVonMangoldtPairConvolution_eq_majorQ0_re_add_minorQ0_re L N Delta
  apply goldbachRep_of_balancedPrimePairConvolution_pos
  rw [hDecomp] at hCircle
  linarith

/-- A finite base plus the finite-`Q0` balanced certificate closes Goldbach. -/
theorem goldbach_of_finiteBase_and_balancedQ0AnalyticCertificate
    {L Xmin : ℕ} {Delta : ℝ}
    {main majorError minorError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BalancedQ0VonMangoldtAnalyticCertificate L Xmin Delta
      main majorError minorError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_balancedQ0AnalyticCertificate hcert (by omega) hEven

end

end Goldbach.Cert.MajorArcModules.RouteABalancedQ0CircleSplit
