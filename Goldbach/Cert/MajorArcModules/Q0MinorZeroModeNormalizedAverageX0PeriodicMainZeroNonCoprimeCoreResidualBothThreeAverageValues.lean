import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeAverageCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Exact one-variable average values needed by the coprime-core `bothThree`
certificate.

The structural coprime-core argument only needs to know that every coprime-core
record has at least one odd core in `bothThreeCoprimeCoreAverageZeroCores`, and
that these listed cores have zero `3 * core` window average.
-/

theorem bothThreeCoprimeCoreAverageZeroCoreValue_7 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 7 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_17 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 17 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_37 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 37 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_43 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 43 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_67 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 67 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_79 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 79 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_83 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 83 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_89 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 89 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_103 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 103 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_113 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 113 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_119 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 119 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_127 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 127 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_139 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 139 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_151 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 151 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_211 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 211 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_241 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 241 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_271 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 271 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_277 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 277 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_281 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 281 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_283 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 283 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageZeroCoreValue_331 :
    bothThreeCoprimeCoreAverageZeroCoreValueGood 331 := by
  unfold bothThreeCoprimeCoreAverageZeroCoreValueGood
  native_decide

theorem bothThreeCoprimeCoreAverageValueCert_true :
    BothThreeCoprimeCoreAverageValueCertificateAtX0 where
  value_on_zero_cores := by
    intro a ha
    have ha' :
        a = 7 ∨ a = 17 ∨ a = 37 ∨ a = 43 ∨ a = 67 ∨ a = 79 ∨
          a = 83 ∨ a = 89 ∨ a = 103 ∨ a = 113 ∨ a = 119 ∨
          a = 127 ∨ a = 139 ∨ a = 151 ∨ a = 211 ∨ a = 241 ∨
          a = 271 ∨ a = 277 ∨ a = 281 ∨ a = 283 ∨ a = 331 := by
      simpa [bothThreeCoprimeCoreAverageZeroCores] using ha
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_7
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_17
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_37
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_43
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_67
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_79
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_83
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_89
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_103
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_113
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_119
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_127
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_139
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_151
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_211
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_241
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_271
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_277
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_281
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_283
    · exact bothThreeCoprimeCoreAverageZeroCoreValue_331

theorem bothThreeBaseFullBlockZeroAtX0_of_coprimeCore_mem_certified
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    bothThreeBaseFullBlockZeroAtX0 p :=
  bothThreeBaseFullBlockZeroAtX0_of_coprimeCore_mem_of_averageValueCert
    bothThreeCoprimeCoreAverageValueCert_true hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
