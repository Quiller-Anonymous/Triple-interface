import Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerCount
import Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtCircleProgram

/-!
# Reduced analytic closure interface for corrected Route A

The higher-prime-power obligation is now discharged by a uniform theorem.  This module inserts that
bound into the production von Mangoldt circle program.  What remains is exactly the conventional
analytic pair:

* approximate the broad von Mangoldt major arcs by the Hardy--Littlewood main term;
* bound the broad von Mangoldt minor arcs;

with their combined error fitting inside the main term after reserving the explicit prime-power
allowance.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtClosure

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerCount
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
open Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtCircleProgram

noncomputable section

/-- Uniform allowance for removing higher prime powers after the von Mangoldt analysis. -/
noncomputable def broadPrimePowerError (N : ℕ) : ℝ :=
  (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2

theorem broadPrimePowerContamination_le_error
    {N : ℕ} (hTwo : 2 ≤ N) :
    broadPrimePowerContamination N ≤ broadPrimePowerError N := by
  simpa [broadPrimePowerError] using
    (broadPrimePowerContamination_le_five_halves_sqrt_log_sq hTwo)

/--
Final analytic certificate after the sparse prime-power argument has been internalized.

Unlike the obsolete fixed-bank route, this interface has no support-coverage assumption and no
window-mean positivity assumption.
-/
structure BroadVonMangoldtAnalyticCertificate
    (C : Goldbach.Singular.C2Const)
    (Xmin B : ℕ) (Delta : ℝ)
    (majorError minorError : ℕ → ℝ) : Prop where
  two_le_threshold : 2 ≤ Xmin
  major_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(broadVonMangoldtMajorArcIntegral N B Delta).re
          - broadVonMangoldtRawMain C N| ≤ majorError N
  minor_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖broadVonMangoldtMinorArcIntegral N B Delta‖ ≤ minorError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + minorError N + broadPrimePowerError N
        < broadVonMangoldtRawMain C N

theorem circleCertificate_of_analyticCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hcert : BroadVonMangoldtAnalyticCertificate C Xmin B Delta
      majorError minorError) :
    BroadVonMangoldtCircleCertificate C Xmin B Delta
      majorError minorError broadPrimePowerError where
  major_approx := hcert.major_approx
  minor_bound := hcert.minor_bound
  primePower_bound := by
    intro N hN hEven
    exact broadPrimePowerContamination_le_error
      (hcert.two_le_threshold.trans hN)
  strict_budget := hcert.strict_budget

theorem goldbachRep_of_analyticCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hcert : BroadVonMangoldtAnalyticCertificate C Xmin B Delta
      majorError minorError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N :=
  goldbachRep_of_vonMangoldtCircleCertificate
    (circleCertificate_of_analyticCertificate hcert) hN hEven

/-- The finite base and the two remaining broad analytic estimates imply Goldbach. -/
theorem goldbach_of_finiteBase_and_analyticCertificate
    {C : Goldbach.Singular.C2Const}
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BroadVonMangoldtAnalyticCertificate C Xmin B Delta
      majorError minorError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N :=
  goldbach_of_finiteBase_and_vonMangoldtCircleCertificate hBase
    (circleCertificate_of_analyticCertificate hcert)

end

end Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtClosure
