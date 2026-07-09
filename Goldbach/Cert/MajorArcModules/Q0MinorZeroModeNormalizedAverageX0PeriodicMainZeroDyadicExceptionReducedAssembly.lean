import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionCertificate
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualPayload

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
The coprime-core residual zero records are now discharged by the generated
payload. This is the remaining dyadic-exception surface: the only zero-record
obligations left for the periodic-main sparse certificate are non-coprime.
-/
structure PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0 : Prop where
  nonCoprime_rowThreeSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_residual_rightThreeSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_core_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainDyadicExceptionReducedZeroCertificateAtX0_of_nonCoprimeReduced
    (cert : PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionReducedZeroCertificateAtX0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact PeriodicMainZeroDyadicExceptionCoprimeCoreResidual_value_on_records_payload
  · exact cert.nonCoprime_rowThreeSix_value_on_records
  · exact cert.nonCoprime_residual_rightThreeSix_value_on_records
  · exact cert.nonCoprime_core_residual_value_on_records

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_nonCoprimeReduced
    (cert : PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicExceptionReduced
    (PeriodicMainDyadicExceptionReducedZeroCertificateAtX0_of_nonCoprimeReduced cert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
