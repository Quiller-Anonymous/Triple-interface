import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
Sparse periodic-main certificate with the support fixed to the generated
nonzero-record set, and the zero records discharged through the reduced
dyadic-exception certificate surface.

This is the theorem-facing Route A shape: generated nonzero values plus the
four reduced dyadic zero obligations imply the standard sparse certificate.
-/
structure PeriodicMainNonzeroReducedSparseCertificateAtX0
    (value : ℕ × ℕ → ℚ) : Prop where
  value_on_nonzero_records :
    ∀ p ∈ PeriodicMainNonzeroRecordPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = value p
  nonzero_records_sum :
    (∑ p ∈ PeriodicMainNonzeroRecordPairs, value p) =
      surrogatePeriodicMainX0RatCert
  dyadic_zero :
    PeriodicMainDyadicExceptionReducedZeroCertificateAtX0

theorem PeriodicMainNonzeroRecordPairs_subset_fullBlockExplicit :
    PeriodicMainNonzeroRecordPairs ⊆
      PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact PeriodicMainNonzeroRecordPairs_subset_fullBlockSquarefreeExplicit hp

theorem periodicMainCert_true_of_nonzeroReducedSparseCertificate
    (value : ℕ × ℕ → ℚ)
    (cert : PeriodicMainNonzeroReducedSparseCertificateAtX0 value) :
    surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat X0 =
      surrogatePeriodicMainX0RatCert := by
  exact surrogateCenteredNormalizedSigmaTruncPeriodicMainPairSumUpToQ0Rat_eq_sparse_cert
    PeriodicMainNonzeroRecordPairs
    value
    PeriodicMainNonzeroRecordPairs_subset_fullBlockExplicit
    (PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicExceptionReduced
      cert.dyadic_zero)
    cert.value_on_nonzero_records
    cert.nonzero_records_sum

theorem centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_nonzeroReducedSparse
    (value : ℕ × ℕ → ℚ)
    (cert : PeriodicMainNonzeroReducedSparseCertificateAtX0 value) :
    CenteredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0 := by
  exact centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_of_eq_cert
    (periodicMainCert_true_of_nonzeroReducedSparseCertificate value cert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
