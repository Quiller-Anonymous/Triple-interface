import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualQ42Transport
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroCoprimeCoreResidualChunk032

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_42_134_eq_zero_by_halving :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (42, 134) = 0 := by
  have hred :
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (21, 67) = 0 :=
    PeriodicMainRecordsZeroCoprimeCoreResidualChunk032_value_on_records
      (21, 67) (by decide)
  simpa using
    surrogatePeriodicMainActiveOrderedPairSummandRat_X0_two_mul_two_mul_eq_zero_of_reduced_active_zero
      (a := 21) (b := 67)
      (by decide) (by decide)
      (by norm_num) (by norm_num)
      (by norm_num)
      (by native_decide) (by native_decide)
      (by native_decide)
      hred

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_42_142_eq_zero_by_halving :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (42, 142) = 0 := by
  have hred :
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (21, 71) = 0 :=
    PeriodicMainRecordsZeroCoprimeCoreResidualChunk032_value_on_records
      (21, 71) (by decide)
  simpa using
    surrogatePeriodicMainActiveOrderedPairSummandRat_X0_two_mul_two_mul_eq_zero_of_reduced_active_zero
      (a := 21) (b := 71)
      (by decide) (by decide)
      (by norm_num) (by norm_num)
      (by norm_num)
      (by native_decide) (by native_decide)
      (by native_decide)
      hred

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_42_146_eq_zero_by_halving :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (42, 146) = 0 := by
  have hred :
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (21, 73) = 0 :=
    PeriodicMainRecordsZeroCoprimeCoreResidualChunk032_value_on_records
      (21, 73) (by decide)
  simpa using
    surrogatePeriodicMainActiveOrderedPairSummandRat_X0_two_mul_two_mul_eq_zero_of_reduced_active_zero
      (a := 21) (b := 73)
      (by decide) (by decide)
      (by norm_num) (by norm_num)
      (by norm_num)
      (by native_decide) (by native_decide)
      (by native_decide)
      hred

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
