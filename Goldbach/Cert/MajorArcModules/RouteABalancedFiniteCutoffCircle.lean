import Goldbach.Cert.MajorArcModules.RouteABalancedQ0SeamSafeSplit

/-!
# Finite-cutoff balanced circle program

The published BMOR error used by Route A grows with the denominator `q`, so applying it to every
`q ≤ Q0 = 30000` is far too expensive. This module exposes an exact split at an arbitrary finite
cutoff `Q`: the major contribution is the sum of the extracted rational-arc integrals for `q ≤ Q`,
and the complementary remainder is defined exactly by subtraction from the convolution.

No claim that the remainder is small is made here. The point is to make the analytically meaningful
cutoff an explicit parameter rather than silently paying the full `Q0` error.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle

open scoped BigOperators

open Complex

open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedQ0SeamSafeSplit

noncomputable section

/-- Sum of the exact seam-safe rational-arc integrals with denominator at most `Q`. -/
noncomputable def balancedVonMangoldtMajorArcUpToIntegral
    (L N Q : ℕ) (Delta : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q, ∑ a ∈ Rcop q,
    balancedVonMangoldtShiftedArcIntegral L N q a Delta

/-- Exact remainder after removing the finite-cutoff major contribution. -/
noncomputable def balancedVonMangoldtAfterMajorUpToRemainder
    (L N Q : ℕ) (Delta : ℝ) : ℂ :=
  (balancedVonMangoldtPairConvolution L N : ℂ)
    - balancedVonMangoldtMajorArcUpToIntegral L N Q Delta

/-- Exact complex decomposition at every finite denominator cutoff. -/
theorem balancedVonMangoldtPairConvolution_cast_eq_majorUpTo_add_remainder
    (L N Q : ℕ) (Delta : ℝ) :
    (balancedVonMangoldtPairConvolution L N : ℂ)
      = balancedVonMangoldtMajorArcUpToIntegral L N Q Delta
        + balancedVonMangoldtAfterMajorUpToRemainder L N Q Delta := by
  unfold balancedVonMangoldtAfterMajorUpToRemainder
  ring

/-- Real form of the exact finite-cutoff decomposition. -/
theorem balancedVonMangoldtPairConvolution_eq_majorUpTo_re_add_remainder_re
    (L N Q : ℕ) (Delta : ℝ) :
    balancedVonMangoldtPairConvolution L N
      = (balancedVonMangoldtMajorArcUpToIntegral L N Q Delta).re
        + (balancedVonMangoldtAfterMajorUpToRemainder L N Q Delta).re := by
  have h := congrArg Complex.re
    (balancedVonMangoldtPairConvolution_cast_eq_majorUpTo_add_remainder
      L N Q Delta)
  simpa using h

/-- Honest analytic interface at a chosen finite denominator cutoff. -/
structure BalancedFiniteCutoffAnalyticCertificate
    (L Xmin Q : ℕ) (Delta : ℝ)
    (main majorError remainderError : ℕ → ℝ) : Prop where
  two_le_threshold : 2 ≤ Xmin
  major_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(balancedVonMangoldtMajorArcUpToIntegral L N Q Delta).re - main N|
        ≤ majorError N
  remainder_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖balancedVonMangoldtAfterMajorUpToRemainder L N Q Delta‖ ≤ remainderError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + remainderError N
          + (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2
        < main N

/-- A finite-cutoff analytic certificate gives a genuine Goldbach representation. -/
theorem goldbachRep_of_balancedFiniteCutoffAnalyticCertificate
    {L Xmin Q : ℕ} {Delta : ℝ}
    {main majorError remainderError : ℕ → ℝ}
    (hcert : BalancedFiniteCutoffAnalyticCertificate L Xmin Q Delta
      main majorError remainderError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N := by
  have hmajorAbs := hcert.major_approx hN hEven
  have hmajorLower :
      main N - majorError N
        ≤ (balancedVonMangoldtMajorArcUpToIntegral L N Q Delta).re := by
    have h := (abs_le.mp hmajorAbs).1
    linarith
  have hremAbs :
      |(balancedVonMangoldtAfterMajorUpToRemainder L N Q Delta).re|
        ≤ remainderError N :=
    (Complex.abs_re_le_norm _).trans (hcert.remainder_bound hN hEven)
  have hremLower :
      -remainderError N
        ≤ (balancedVonMangoldtAfterMajorUpToRemainder L N Q Delta).re :=
    (abs_le.mp hremAbs).1
  have hPower := balancedPrimePowerContamination_le_five_halves_sqrt_log_sq
    (L := L) (hcert.two_le_threshold.trans hN)
  have hBudget := hcert.strict_budget hN hEven
  have hDecomp := balancedVonMangoldtPairConvolution_eq_prime_add_contamination L N
  have hCircle :=
    balancedVonMangoldtPairConvolution_eq_majorUpTo_re_add_remainder_re
      L N Q Delta
  apply goldbachRep_of_balancedPrimePairConvolution_pos
  rw [hDecomp] at hCircle
  linarith

/-- A finite base plus a finite-cutoff analytic certificate closes Goldbach. -/
theorem goldbach_of_finiteBase_and_balancedFiniteCutoffAnalyticCertificate
    {L Xmin Q : ℕ} {Delta : ℝ}
    {main majorError remainderError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BalancedFiniteCutoffAnalyticCertificate L Xmin Q Delta
      main majorError remainderError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_balancedFiniteCutoffAnalyticCertificate hcert (by omega) hEven

end

end Goldbach.Cert.MajorArcModules.RouteABalancedFiniteCutoffCircle
