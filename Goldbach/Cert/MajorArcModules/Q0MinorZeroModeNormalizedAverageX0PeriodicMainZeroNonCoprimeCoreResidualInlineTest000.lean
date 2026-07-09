import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualInlineTest000Row_1
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualInlineTest000Row_7

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Split generated periodic-main zero-record proof for selected JSON index 0. -/

theorem periodicMainPair_7_21_X1000000_divLeft : Nat.divisors 7 = ([1, 7] : List ℕ).toFinset := by
  native_decide

def periodicMainPair_7_21_X1000000_rowValue : ℕ → ℚ
| 1 => (0 : ℚ) / 1
| 7 => (0 : ℚ) / 1
| _ => 0

theorem periodicMainPair_7_21_X1000000_centeredTerm :
    centeredRamanujanPairPeriodicMainTermRat X0 7 21 = (0 : ℚ) / 1 := by
  unfold centeredRamanujanPairPeriodicMainTermRat
  have hsum :
      (∑ g ∈ Nat.divisors 7, ∑ h ∈ Nat.divisors 21,
        ramanujanGcdClassCoeffRat 7 g * ramanujanGcdClassCoeffRat 21 h
          * ((((H + 1) / centeredRamanujanPairBlockPeriod 7 21) : ℕ)
              • (rawEvenRamanujanGcdClassPairBlockResolvedCountRat X0 7 21 g h
                  - ramanujanGcdClassWindowAverageRat X0 21 h
                      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 7 g
                  - ramanujanGcdClassWindowAverageRat X0 7 g
                      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X0 7 21 21 h
                  + ramanujanGcdClassWindowAverageRat X0 7 g
                      * ramanujanGcdClassWindowAverageRat X0 21 h
                      * evenRamanujanBlockCountRat 7 21))
      ) = (∑ g ∈ Nat.divisors 7, periodicMainPair_7_21_X1000000_rowValue g) := by
    apply Finset.sum_congr rfl
    intro g hg
    rw [periodicMainPair_7_21_X1000000_divLeft] at hg
    simp at hg
    rcases hg with rfl | rfl
    · simpa [periodicMainPair_7_21_X1000000_rowValue] using periodicMainPair_7_21_X1000000_row_1
    · simpa [periodicMainPair_7_21_X1000000_rowValue] using periodicMainPair_7_21_X1000000_row_7
  rw [hsum, periodicMainPair_7_21_X1000000_divLeft]
  norm_num [periodicMainPair_7_21_X1000000_rowValue]

theorem periodicMainPair_7_21_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (Prod.mk 7 21) = (0 : ℚ) / 1 := by
  have hneq : 7 ≠ 21 := by
    norm_num
  have hCoeffLeft : surrogateNormalizedSigmaTruncSummandCoeffRat 7 = (5 : ℚ) / 36 := by
    native_decide
  have hCoeffRight : surrogateNormalizedSigmaTruncSummandCoeffRat 21 = (5 : ℚ) / 144 := by
    native_decide
  have hvalue : ((5 : ℚ) / 36) * ((5 : ℚ) / 144) * ((0 : ℚ) / 1) = (0 : ℚ) / 1 := by
    norm_num
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_of_pairValue
    hneq hCoeffLeft hCoeffRight
    periodicMainPair_7_21_X1000000_centeredTerm
    hvalue

def PeriodicMainRecordsTiny000Pairs : Finset (ℕ × ℕ) :=
  [(7, 21)].toFinset

theorem PeriodicMainRecordsTiny000_value_on_records :
    ∀ p ∈ PeriodicMainRecordsTiny000Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  simp [PeriodicMainRecordsTiny000Pairs] at hp
  rcases hp with h
  · subst p
    simpa using periodicMainPair_7_21_X1000000_orderedSummand

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
