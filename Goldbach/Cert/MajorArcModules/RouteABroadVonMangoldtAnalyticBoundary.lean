import Goldbach.Cert.MajorArcModules.C2RamanujanEulerProduct
import Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtClosure

/-!
# Canonical analytic boundary for corrected Route A

This module fixes the singular-series constant to the canonical Euler-product realization and
separates the two genuinely open estimates from the parts already proved in Lean.

The checked arithmetic available at this boundary is:

* the canonical constant satisfies `C₂ > 33 / 50`;
* the raw Hardy--Littlewood main term is at least `(33 / 25) * N` on even inputs;
* higher-prime-power contamination is bounded by `broadPrimePowerError`.

Consequently a major-arc estimate and a minor-arc estimate close corrected Route A exactly when
their combined error is smaller than `canonicalBroadAnalyticReserve`. No fixed prime bank,
positive window mean, generated `X0` certificate, or abstract SSU interface occurs here.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtAnalyticBoundary

open Goldbach.BankPieces.Cert.TrueSingularSeries
open Goldbach.Cert.MajorArcModules.C2RamanujanEulerProduct
open Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtCircleProgram
open Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtClosure

noncomputable section

/-- The genuine Euler-product constant used by the canonical Ramanujan singular series. -/
noncomputable abbrev canonicalBroadC2 : Goldbach.Singular.C2Const :=
  ramanujanSeriesOnWindow.C

/-- Canonical raw Hardy--Littlewood main term for the complete von Mangoldt convolution. -/
noncomputable def canonicalBroadVonMangoldtRawMain (N : ℕ) : ℝ :=
  broadVonMangoldtRawMain canonicalBroadC2 N

/-- Error room left after reserving the proved higher-prime-power allowance. -/
noncomputable def canonicalBroadAnalyticReserve (N : ℕ) : ℝ :=
  canonicalBroadVonMangoldtRawMain N - broadPrimePowerError N

theorem canonicalBroadC2_gt_33_50 :
    (33 : ℝ) / 50 < canonicalBroadC2.C2 := by
  simpa [canonicalBroadC2] using ramanujanSeriesOnWindow_C2_gt_33_50

/-- A checked linear floor for the canonical raw main term on even inputs. -/
theorem canonicalBroadVonMangoldtRawMain_lower
    {N : ℕ} (hEven : Even N) :
    (33 / 25 : ℝ) * N ≤ canonicalBroadVonMangoldtRawMain N := by
  have hC2 : (33 / 25 : ℝ) ≤ 2 * canonicalBroadC2.C2 := by
    linarith [canonicalBroadC2_gt_33_50]
  have hSigma :
      (2 : ℝ) * canonicalBroadC2.C2
        ≤ Goldbach.Singular.sigma canonicalBroadC2 N :=
    Goldbach.Singular.sigma_floor_even hEven
  have hN : (0 : ℝ) ≤ N := by positivity
  calc
    (33 / 25 : ℝ) * N
        ≤ (2 * canonicalBroadC2.C2) * N :=
          mul_le_mul_of_nonneg_right hC2 hN
    _ ≤ Goldbach.Singular.sigma canonicalBroadC2 N * N :=
          mul_le_mul_of_nonneg_right hSigma hN
    _ = canonicalBroadVonMangoldtRawMain N := rfl

/-- The explicit linear lower envelope also lower-bounds the remaining analytic reserve. -/
theorem canonicalBroadAnalyticReserve_lower
    {N : ℕ} (hEven : Even N) :
    (33 / 25 : ℝ) * N - broadPrimePowerError N
      ≤ canonicalBroadAnalyticReserve N := by
  unfold canonicalBroadAnalyticReserve
  linarith [canonicalBroadVonMangoldtRawMain_lower hEven]

/-- The open broad major-arc estimate, isolated from every other Route A obligation. -/
structure CanonicalBroadMajorArcEstimate
    (Xmin B : ℕ) (Delta : ℝ) (majorError : ℕ → ℝ) : Prop where
  bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(broadVonMangoldtMajorArcIntegral N B Delta).re
          - canonicalBroadVonMangoldtRawMain N| ≤ majorError N

/-- The open broad minor-arc estimate, isolated from every other Route A obligation. -/
structure CanonicalBroadMinorArcEstimate
    (Xmin B : ℕ) (Delta : ℝ) (minorError : ℕ → ℝ) : Prop where
  bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖broadVonMangoldtMinorArcIntegral N B Delta‖ ≤ minorError N

/-- The numerical compatibility condition for the two analytic estimates. -/
structure CanonicalBroadErrorBudget
    (Xmin : ℕ) (majorError minorError : ℕ → ℝ) : Prop where
  fits :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + minorError N < canonicalBroadAnalyticReserve N

/-- Assemble the two honest analytic estimates into the production Route A certificate. -/
theorem analyticCertificate_of_major_minor
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hTwo : 2 ≤ Xmin)
    (hMajor : CanonicalBroadMajorArcEstimate Xmin B Delta majorError)
    (hMinor : CanonicalBroadMinorArcEstimate Xmin B Delta minorError)
    (hBudget : CanonicalBroadErrorBudget Xmin majorError minorError) :
    BroadVonMangoldtAnalyticCertificate canonicalBroadC2 Xmin B Delta
      majorError minorError where
  two_le_threshold := hTwo
  major_approx := hMajor.bound
  minor_bound := hMinor.bound
  strict_budget := by
    intro N hN hEven
    have h := hBudget.fits hN hEven
    unfold canonicalBroadAnalyticReserve canonicalBroadVonMangoldtRawMain at h
    linarith

/-- Final corrected Route A wrapper at the canonical singular-series constant. -/
theorem goldbach_of_finiteBase_and_major_minor
    {Xmin B : ℕ} {Delta : ℝ} {majorError minorError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hTwo : 2 ≤ Xmin)
    (hMajor : CanonicalBroadMajorArcEstimate Xmin B Delta majorError)
    (hMinor : CanonicalBroadMinorArcEstimate Xmin B Delta minorError)
    (hBudget : CanonicalBroadErrorBudget Xmin majorError minorError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N :=
  goldbach_of_finiteBase_and_analyticCertificate hBase
    (analyticCertificate_of_major_minor hTwo hMajor hMinor hBudget)

end

end Goldbach.Cert.MajorArcModules.RouteABroadVonMangoldtAnalyticBoundary
