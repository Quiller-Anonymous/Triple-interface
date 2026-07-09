import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRowThreeSix

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
The non-coprime residual right-column `3`/`6` surface.

This is the transpose-shaped companion to the non-coprime row `3`/`6` surface.
The right-`3` records all have a common factor `3` on the left; the right-`6`
records split by the actual common factor `2`, `3`, or `6`.
-/
def PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreePairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs.filter
    (fun p => p.2 = 3)

def PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs.filter
    (fun p => p.2 = 6)

def PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwoPairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs.filter
    (fun p => Nat.gcd p.1 p.2 = 2)

def PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThreePairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs.filter
    (fun p => Nat.gcd p.1 p.2 = 3)

def PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSixPairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs.filter
    (fun p => Nat.gcd p.1 p.2 = 6)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs_eq_rightThree_union_rightSix :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreePairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨_hpResidual, hpRight⟩
    rcases hpRight with hpThree | hpSix
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hpThree⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hpSix⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpThree | hpSix
    · exact (Finset.mem_filter.mp hpThree).1
    · exact (Finset.mem_filter.mp hpSix).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreePairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreePairs.card = 761 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs.card = 762 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwoPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwoPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThreePairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThreePairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSixPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSixPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs_eq_commonTwo_union_commonThree_union_commonSix :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs =
      (PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwoPairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThreePairs) ∪
          PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSixPairs := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThree_left_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreePairs,
      3 ∣ p.1 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpRightThreeSix, hpRightThree⟩
  rcases Finset.mem_filter.mp hpRightThreeSix with ⟨hpResidual, _hpRight⟩
  rcases Finset.mem_filter.mp hpResidual with ⟨hpNonCop, _hpNotLeftThreeSix⟩
  rcases Finset.mem_filter.mp hpNonCop with ⟨_hpDyadic, hdata⟩
  rcases hdata with ⟨_hnotUnitTwo, hnotCop⟩
  have hnotCop3 : ¬ Nat.Coprime p.1 3 := by
    simpa [hpRightThree] using hnotCop
  have hgcd_ne_one : Nat.gcd p.1 3 ≠ 1 := by
    intro hgcd
    exact hnotCop3 (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
  have hdvd : Nat.gcd p.1 3 ∣ 3 := Nat.gcd_dvd_right p.1 3
  have hgcd_pos : 0 < Nat.gcd p.1 3 := Nat.gcd_pos_of_pos_right p.1 (by norm_num)
  have hgcd_le : Nat.gcd p.1 3 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  have hgcd_ne_two : Nat.gcd p.1 3 ≠ 2 := by
    intro htwo
    have : 2 ∣ 3 := by simpa [htwo] using hdvd
    norm_num at this
  have hgcd_eq_three : Nat.gcd p.1 3 = 3 := by
    omega
  simpa [hgcd_eq_three] using Nat.gcd_dvd_left p.1 3

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwo_left_not_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwoPairs,
      ¬ 3 ∣ p.1 := by
  intro p hp hthreeLeft
  rcases Finset.mem_filter.mp hp with ⟨hpRightSix, hgcdTwo⟩
  rcases Finset.mem_filter.mp hpRightSix with ⟨_hpRightThreeSix, hpRightSixEq⟩
  have hthreeRight : 3 ∣ p.2 := by
    rw [hpRightSixEq]
    norm_num
  have hthreeGcd : 3 ∣ Nat.gcd p.1 p.2 := Nat.dvd_gcd hthreeLeft hthreeRight
  have : 3 ∣ 2 := by simpa [hgcdTwo] using hthreeGcd
  norm_num at this

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThree_left_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThreePairs,
      3 ∣ p.1 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_hpRightSix, hgcdThree⟩
  have hthreeLeft : 3 ∣ Nat.gcd p.1 p.2 := by
    rw [hgcdThree]
  exact dvd_trans hthreeLeft (Nat.gcd_dvd_left p.1 p.2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSix_left_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSixPairs,
      3 ∣ p.1 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_hpRightSix, hgcdSix⟩
  have hsixLeft : 6 ∣ p.1 := by
    simpa [hgcdSix] using Nat.gcd_dvd_left p.1 p.2
  exact dvd_trans (by norm_num : 3 ∣ 6) hsixLeft

structure PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0 :
    Prop where
  rightThree_commonThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreePairs,
      3 ∣ p.1 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rightSix_commonTwo_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwoPairs,
      ¬ 3 ∣ p.1 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rightSix_commonThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThreePairs,
      3 ∣ p.1 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rightSix_commonSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSixPairs,
      3 ∣ p.1 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSix_value_on_records_of_commonFactor
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixPairs_eq_commonTwo_union_commonThree_union_commonSix] at hp
  rcases Finset.mem_union.mp hp with hpLeft | hpSix
  · rcases Finset.mem_union.mp hpLeft with hpTwo | hpThree
    · exact cert.rightSix_commonTwo_value_on_records p hpTwo
        (PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonTwo_left_not_dvd_three
          p hpTwo)
    · exact cert.rightSix_commonThree_value_on_records p hpThree
        (PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonThree_left_dvd_three
          p hpThree)
  · exact cert.rightSix_commonSix_value_on_records p hpSix
      (PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSixCommonSix_left_dvd_three p hpSix)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_value_on_records_of_commonFactor
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs_eq_rightThree_union_rightSix] at hp
  rcases Finset.mem_union.mp hp with hpThree | hpSix
  · exact cert.rightThree_commonThree_value_on_records p hpThree
      (PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThree_left_dvd_three p hpThree)
  · exact PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightSix_value_on_records_of_commonFactor
      cert p hpSix

theorem PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixCommonFactor_rightThreeSixCommonFactor
    (rowCert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0)
    (rightCert :
      PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0)
    (coreResidual :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0) :
    PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0 := by
  exact PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixCommonFactor
    rowCert
    (PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSix_value_on_records_of_commonFactor
      rightCert)
    coreResidual

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
