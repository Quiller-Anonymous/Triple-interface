import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRightThreeSix
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRowThreeSixCertificate
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroRightColumns

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_swap_mem_rowThreeSix :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
      (p.2, p.1) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_value_on_records_transport :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [surrogatePeriodicMainActiveOrderedPairSummandRat_swap_public X0 p]
  exact
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSix_value_on_records_of_parity
      PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0_of_remaining
      (p.2, p.1)
      (PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_swap_mem_rowThreeSix p hp)

theorem PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0_of_transport :
    PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp _hleftThree
    exact PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_value_on_records_transport
      p (Finset.mem_filter.mp hp).1
  · intro p hp _hleftNotThree
    exact PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_value_on_records_transport
      p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp _hleftThree
    exact PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_value_on_records_transport
      p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp _hleftThree
    exact PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_value_on_records_transport
      p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
