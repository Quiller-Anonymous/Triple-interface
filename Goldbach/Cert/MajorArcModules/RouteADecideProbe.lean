import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem routeADecideProbe_divLeft :
    Nat.divisors 15 = ([1, 3, 5, 15] : List ℕ).toFinset := by
  decide

theorem routeADecideProbe_coeff :
    ramanujanGcdClassCoeffRat 15 3 = (-2 : ℚ) / 1 := by
  decide

theorem routeADecideProbe_avg :
    ramanujanGcdClassWindowAverageRat X0 15 3 = (1334 : ℚ) / 5001 := by
  decide

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
