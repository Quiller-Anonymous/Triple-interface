import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0BoundaryInactive

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Boundary certificate plumbing for the `X0` Route A endpoint.

The public boundary certificate definitions are intentionally stated in terms of the
same rational shadows used by the analytic development. Some of those rational
definitions were marked `noncomputable` because they sit next to real-valued
objects, even though the fixed `X0` certificate computation is finite. This file
adds computable finite shadows and bridge lemmas, so generated certificate facts
can target executable definitions without changing the public theorem surface.
-/

def BoundaryActiveSupportFinite : Finset ℕ :=
  (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0).filter
    (fun q => Squarefree q ∧ q ≤ (H + 1) / 2)

theorem BoundaryActiveSupportExplicit_eq_finite :
    BoundaryActiveSupportExplicit = BoundaryActiveSupportFinite := by
  ext q
  simp [BoundaryActiveSupportExplicit, BoundaryActiveSupportFinite,
    mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff,
    and_assoc, and_left_comm, and_comm]

def centeredRamanujanGcdClassPairBoundaryRemainderRatFinite
    (X q q' g h : ℕ) : ℚ :=
  let P := centeredRamanujanPairBlockPeriod q q'
  let m := (H + 1) / P
  let r := (H + 1) % P
  ∑ k ∈ Finset.range r, centeredEvenRamanujanGcdClassPairOffsetRat X q q' g h (m * P + k)

theorem centeredRamanujanGcdClassPairBoundaryRemainderRat_eq_finite
    (X q q' g h : ℕ) :
    centeredRamanujanGcdClassPairBoundaryRemainderRat X q q' g h =
      centeredRamanujanGcdClassPairBoundaryRemainderRatFinite X q q' g h := by
  rfl

def surrogateCenteredRamanujanPairPeriodicBoundaryTermRatFinite
    (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * centeredRamanujanGcdClassPairBoundaryRemainderRatFinite X q q' g h

theorem surrogateCenteredRamanujanPairPeriodicBoundaryTermRat_eq_finite
    (X q q' : ℕ) :
    surrogateCenteredRamanujanPairPeriodicBoundaryTermRat X q q' =
      surrogateCenteredRamanujanPairPeriodicBoundaryTermRatFinite X q q' := by
  unfold surrogateCenteredRamanujanPairPeriodicBoundaryTermRat
    surrogateCenteredRamanujanPairPeriodicBoundaryTermRatFinite
  refine Finset.sum_congr rfl ?_
  intro g hg
  refine Finset.sum_congr rfl ?_
  intro h hh
  rw [centeredRamanujanGcdClassPairBoundaryRemainderRat_eq_finite]

def surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0RatFinite
    (X : ℕ) : ℚ :=
  ∑ q ∈ BoundaryActiveSupportFinite,
    ∑ q' ∈ BoundaryActiveSupportFinite,
      if q = q' then 0
      else
        surrogateNormalizedSigmaTruncSummandCoeffRat q
          * surrogateNormalizedSigmaTruncSummandCoeffRat q'
          * surrogateCenteredRamanujanPairPeriodicBoundaryTermRatFinite X q q'

theorem surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat_eq_finite
    (X : ℕ) :
    surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat X =
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0RatFinite X := by
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat,
    surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0RatFinite,
    BoundaryActiveSupportExplicit_eq_finite]
  rfl

def BoundaryActiveSignedFiniteRatCertificateAtX0 : Prop :=
  surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0RatFinite X0 =
    surrogateBoundaryX0ActiveSignedExactCert

theorem centeredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0_of_finite
    (hcert : BoundaryActiveSignedFiniteRatCertificateAtX0) :
    CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0 := by
  unfold BoundaryActiveSignedFiniteRatCertificateAtX0 at hcert
  unfold CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat_eq_finite]
  exact hcert

theorem centeredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0_of_full_and_active
    (hfull :
      surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0Rat X0 =
        surrogateBoundaryX0FullExactCert)
    (hactive :
      CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0) :
    CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0 := by
  unfold CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0
  unfold surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat
  unfold CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0 at hactive
  rw [hfull, hactive]
  unfold surrogateBoundaryX0FullExactCert
  ring

theorem surrogateBoundary_X0_eq_fullExactCert_of_active_and_inactive_finite
    (hactive : BoundaryActiveSignedFiniteRatCertificateAtX0)
    (hinactive : CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0) :
    surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryPairSumUpToQ0Rat X0 =
      surrogateBoundaryX0FullExactCert := by
  unfold BoundaryActiveSignedFiniteRatCertificateAtX0 at hactive
  unfold CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0 at hinactive
  unfold surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryInactiveCorrectionRat at hinactive
  rw [surrogateCenteredNormalizedSigmaTruncPeriodicBoundaryActiveSignedPairSumUpToQ0Rat_eq_finite,
    hactive] at hinactive
  unfold surrogateBoundaryX0FullExactCert
  linarith

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
