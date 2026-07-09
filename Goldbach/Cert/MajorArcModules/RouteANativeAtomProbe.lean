import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeANativeAtomProbe_coeff :
    ramanujanGcdClassCoeffRat 15 1 = (1 : ℚ) / 1 := by
  native_decide

theorem routeANativeAtomProbe_avg :
    ramanujanGcdClassWindowAverageRat X0 15 1 = (2666 : ℚ) / 5001 := by
  native_decide

theorem routeANativeAtomProbe_block :
    rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 15 21 15 1 = (56 : ℚ) := by
  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
  all_goals native_decide

theorem routeANativeAtomProbe_pair :
    rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 15 21 1 1 = (48 : ℚ) := by
  rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_eq_periodic_of_compatible]
  · rw [rawEvenRamanujanGcdClassPairBlockPeriodicCountRat_eq_odd_totient_main_add_remainder]
    all_goals native_decide
  · norm_num [ramanujanGcdClassJointCompatibility]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
