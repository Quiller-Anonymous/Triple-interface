import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionReducedAssembly

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
The non-coprime row-three/six zero surface split by right parity.

This is the next certificate boundary for Route A.  The primitive exact record
route is too slow here, while the existing coprime structural row theorems do
not apply.  Keeping the four parity buckets explicit lets us discharge each by
the appropriate non-coprime row theorem or by a generated payload if a theorem
is not available.
-/
structure PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0 : Prop where
  rowThree_rightOdd_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rowThree_rightEven_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rowSix_rightOdd_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rowSix_rightEven_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

def PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwoPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs.filter
    (fun p => Nat.gcd p.1 p.2 = 2)

def PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs.filter
    (fun p => Nat.gcd p.1 p.2 = 6)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOdd_right_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs,
      3 ∣ p.2 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpRowThree, _hpOdd⟩
  rcases Finset.mem_filter.mp hpRowThree with ⟨hpNonCop, hpLeftThree⟩
  rcases Finset.mem_filter.mp hpNonCop with ⟨_hpDyadic, hdata⟩
  rcases hdata with ⟨_hnotUnitTwo, hnotCop⟩
  have hnotCop3 : ¬ Nat.Coprime 3 p.2 := by
    simpa [hpLeftThree] using hnotCop
  have hgcd_ne_one : Nat.gcd 3 p.2 ≠ 1 := by
    intro hgcd
    exact hnotCop3 (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
  have hdvd : Nat.gcd 3 p.2 ∣ 3 := Nat.gcd_dvd_left 3 p.2
  have hgcd_pos : 0 < Nat.gcd 3 p.2 := Nat.gcd_pos_of_pos_left p.2 (by norm_num)
  have hgcd_le : Nat.gcd 3 p.2 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  have hgcd_ne_two : Nat.gcd 3 p.2 ≠ 2 := by
    intro htwo
    have : 2 ∣ 3 := by simpa [htwo] using hdvd
    norm_num at this
  have hgcd_eq_three : Nat.gcd 3 p.2 = 3 := by
    omega
  simpa [hgcd_eq_three] using Nat.gcd_dvd_right 3 p.2

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEven_right_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs,
      3 ∣ p.2 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpRowThree, _hpEven⟩
  rcases Finset.mem_filter.mp hpRowThree with ⟨hpNonCop, hpLeftThree⟩
  rcases Finset.mem_filter.mp hpNonCop with ⟨_hpDyadic, hdata⟩
  rcases hdata with ⟨_hnotUnitTwo, hnotCop⟩
  have hnotCop3 : ¬ Nat.Coprime 3 p.2 := by
    simpa [hpLeftThree] using hnotCop
  have hgcd_ne_one : Nat.gcd 3 p.2 ≠ 1 := by
    intro hgcd
    exact hnotCop3 (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
  have hdvd : Nat.gcd 3 p.2 ∣ 3 := Nat.gcd_dvd_left 3 p.2
  have hgcd_pos : 0 < Nat.gcd 3 p.2 := Nat.gcd_pos_of_pos_left p.2 (by norm_num)
  have hgcd_le : Nat.gcd 3 p.2 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  have hgcd_ne_two : Nat.gcd 3 p.2 ≠ 2 := by
    intro htwo
    have : 2 ∣ 3 := by simpa [htwo] using hdvd
    norm_num at this
  have hgcd_eq_three : Nat.gcd 3 p.2 = 3 := by
    omega
  simpa [hgcd_eq_three] using Nat.gcd_dvd_right 3 p.2

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOdd_right_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs,
      3 ∣ p.2 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpRowSix, hpOdd⟩
  rcases Finset.mem_filter.mp hpRowSix with ⟨hpNonCop, hpLeftSix⟩
  rcases Finset.mem_filter.mp hpNonCop with ⟨_hpDyadic, hdata⟩
  rcases hdata with ⟨_hnotUnitTwo, hnotCop⟩
  have hnotCop6 : ¬ Nat.Coprime 6 p.2 := by
    simpa [hpLeftSix] using hnotCop
  have hgcd_ne_one : Nat.gcd 6 p.2 ≠ 1 := by
    intro hgcd
    exact hnotCop6 (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
  have hnotEvenRight : ¬ Goldbach.Windows.IsEven p.2 := by
    intro hEven
    exact (Nat.not_even_iff_odd.mpr hpOdd) (Goldbach.Windows.even_of_isEven hEven)
  have hdvd : Nat.gcd 6 p.2 ∣ 6 := Nat.gcd_dvd_left 6 p.2
  have hgcd_pos : 0 < Nat.gcd 6 p.2 := Nat.gcd_pos_of_pos_left p.2 (by norm_num)
  have hgcd_le : Nat.gcd 6 p.2 ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hgcd_ne_two : Nat.gcd 6 p.2 ≠ 2 := by
    intro htwo
    have htwoRight : 2 ∣ p.2 := by
      simpa [htwo] using Nat.gcd_dvd_right 6 p.2
    have hEvenRight : Even p.2 := (even_iff_two_dvd).2 htwoRight
    exact hnotEvenRight (Goldbach.Windows.isEven_of_even hEvenRight)
  have hgcd_ne_four : Nat.gcd 6 p.2 ≠ 4 := by
    intro hfour
    have : 4 ∣ 6 := by simpa [hfour] using hdvd
    norm_num at this
  have hgcd_ne_five : Nat.gcd 6 p.2 ≠ 5 := by
    intro hfive
    have : 5 ∣ 6 := by simpa [hfive] using hdvd
    norm_num at this
  have hgcd_ne_six : Nat.gcd 6 p.2 ≠ 6 := by
    intro hsix
    have htwoRight : 2 ∣ p.2 := by
      have hsixRight : 6 ∣ p.2 := by
        simpa [hsix] using Nat.gcd_dvd_right 6 p.2
      exact dvd_trans (by norm_num : 2 ∣ 6) hsixRight
    have hEvenRight : Even p.2 := (even_iff_two_dvd).2 htwoRight
    exact hnotEvenRight (Goldbach.Windows.isEven_of_even hEvenRight)
  have hgcd_eq_three : Nat.gcd 6 p.2 = 3 := by
    omega
  have hthree_dvd_gcd : 3 ∣ Nat.gcd 6 p.2 := by
    rw [hgcd_eq_three]
  exact dvd_trans hthree_dvd_gcd (Nat.gcd_dvd_right 6 p.2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs_eq_commonTwo_union_commonSix :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwoPairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwoPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwoPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwo_right_not_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwoPairs,
      ¬ 3 ∣ p.2 := by
  intro p hp hthreeRight
  rcases Finset.mem_filter.mp hp with ⟨hpEven, hgcdTwo⟩
  rcases Finset.mem_filter.mp hpEven with ⟨hpRowSix, _hpRightEven⟩
  rcases Finset.mem_filter.mp hpRowSix with ⟨_hpNonCop, hpLeftSix⟩
  have hthreeLeft : 3 ∣ p.1 := by
    rw [hpLeftSix]
    norm_num
  have hthreeGcd : 3 ∣ Nat.gcd p.1 p.2 := Nat.dvd_gcd hthreeLeft hthreeRight
  have : 3 ∣ 2 := by simpa [hgcdTwo] using hthreeGcd
  norm_num at this

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_right_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      3 ∣ p.2 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨_hpEven, hgcdSix⟩
  have hsixRight : 6 ∣ p.2 := by
    simpa [hgcdSix] using Nat.gcd_dvd_right p.1 p.2
  exact dvd_trans (by norm_num : 3 ∣ 6) hsixRight

structure PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0 : Prop where
  rowThree_rightOdd_commonThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs,
      3 ∣ p.2 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rowThree_rightEven_commonThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs,
      3 ∣ p.2 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rowSix_rightOdd_commonThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs,
      3 ∣ p.2 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rowSix_rightEven_commonTwo_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwoPairs,
      ¬ 3 ∣ p.2 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rowSix_rightEven_commonSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      3 ∣ p.2 →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0_of_commonFactor
    (cert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact cert.rowThree_rightOdd_commonThree_value_on_records p hp
      (PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOdd_right_dvd_three p hp)
  · intro p hp
    exact cert.rowThree_rightEven_commonThree_value_on_records p hp
      (PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEven_right_dvd_three p hp)
  · intro p hp
    exact cert.rowSix_rightOdd_commonThree_value_on_records p hp
      (PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOdd_right_dvd_three p hp)
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs_eq_commonTwo_union_commonSix] at hp
    rcases Finset.mem_union.mp hp with hpTwo | hpSix
    · exact cert.rowSix_rightEven_commonTwo_value_on_records p hpTwo
        (PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonTwo_right_not_dvd_three p hpTwo)
    · exact cert.rowSix_rightEven_commonSix_value_on_records p hpSix
        (PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_right_dvd_three p hpSix)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThree_value_on_records_of_parity
    (cert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs_eq_rightOdd_union_rightEven] at hp
  rcases Finset.mem_union.mp hp with hpOdd | hpEven
  · exact cert.rowThree_rightOdd_value_on_records p hpOdd
  · exact cert.rowThree_rightEven_value_on_records p hpEven

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSix_value_on_records_of_parity
    (cert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs_eq_rightOdd_union_rightEven] at hp
  rcases Finset.mem_union.mp hp with hpOdd | hpEven
  · exact cert.rowSix_rightOdd_value_on_records p hpOdd
  · exact cert.rowSix_rightEven_value_on_records p hpEven

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSix_value_on_records_of_parity
    (cert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs_eq_rowThree_union_rowSix] at hp
  rcases Finset.mem_union.mp hp with hpThree | hpSix
  · exact PeriodicMainZeroDyadicExceptionNonCoprimeRowThree_value_on_records_of_parity cert p hpThree
  · exact PeriodicMainZeroDyadicExceptionNonCoprimeRowSix_value_on_records_of_parity cert p hpSix

theorem PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixParity
    (rowCert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0)
    (residualRightThreeSix :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0)
    (coreResidual :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0) :
    PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0 := by
  refine ⟨?_, residualRightThreeSix, coreResidual⟩
  exact PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSix_value_on_records_of_parity rowCert

theorem PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixCommonFactor
    (rowCert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0)
    (residualRightThreeSix :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0)
    (coreResidual :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0) :
    PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0 := by
  exact PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixParity
    (PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0_of_commonFactor rowCert)
    residualRightThreeSix coreResidual

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_nonCoprimeRowThreeSixParity
    (rowCert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixParityZeroCertificateAtX0)
    (residualRightThreeSix :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0)
    (coreResidual :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_nonCoprimeReduced
    (PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixParity
      rowCert residualRightThreeSix coreResidual)

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_nonCoprimeRowThreeSixCommonFactor
    (rowCert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0)
    (residualRightThreeSix :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0)
    (coreResidual :
      ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_nonCoprimeReduced
    (PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixCommonFactor
      rowCert residualRightThreeSix coreResidual)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
