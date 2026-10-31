import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle

/-!
# Exact circle identity for the complete prime convolution

The corrected Route A must split the circle-method frequency variable, not project the output
sequence of Goldbach correlations.  This module instantiates the generic finite-weight circle
identity with the prime-only logarithmic weight on every candidate in `[2, N - 2]`.

No arithmetic bank weight, offset band, or short-shift kernel occurs in this identity.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeCircle

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcStep7FourierOrthogonality

noncomputable section

/-- Complete prime exponential sum for the exact target integer `N`. -/
noncomputable def broadPrimeExponentialSum (N : ℕ) (alpha : UC) : ℂ :=
  finiteWeightExponentialSum Goldbach.BG_Bank.Λ N alpha

/-- Integrand whose zero Fourier coefficient extracts pairs summing to `N`. -/
noncomputable def broadPrimeCircleIntegrand (N : ℕ) (alpha : UC) : ℂ :=
  finiteWeightCircleIntegrand Goldbach.BG_Bank.Λ N alpha

/-- Exact circle integral for the complete prime-pair convolution. -/
noncomputable def broadPrimeCircleIntegral (N : ℕ) : ℂ :=
  finiteWeightCircleIntegral Goldbach.BG_Bank.Λ N

/--
The complete prime convolution is exactly the relevant Fourier coefficient of the unrestricted
prime exponential sum.
-/
theorem broadPrimeCircleIntegral_eq_convolution (N : ℕ) :
    broadPrimeCircleIntegral N = (broadPrimePairConvolution N : ℂ) := by
  simpa [broadPrimeCircleIntegral, broadPrimePairConvolution,
    finiteWeightPairConvolution] using
    (finiteWeightCircleIntegral_eq_convolution Goldbach.BG_Bank.Λ N)

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeCircle
