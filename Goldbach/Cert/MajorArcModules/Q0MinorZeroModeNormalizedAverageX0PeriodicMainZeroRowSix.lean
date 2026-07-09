import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroRowThreeRightEven

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private theorem X0_isEven_rowSix : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

theorem centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_six_left_odd_right_public
    {X b : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : b ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0)
    (hcop : Nat.Coprime 6 b) :
    centeredRamanujanPairPeriodicMainTerm X 6 b = 0 := by
  rcases mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mp hb with ⟨hbCoeff, hbOdd⟩
  have hbpos : 1 ≤ b :=
    (Finset.mem_Icc.mp (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hbCoeff).1).1
  have hcop3 : Nat.Coprime 3 b := by
    exact hcop.coprime_dvd_left ⟨2, by norm_num⟩
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  rw [centeredRamanujanPairPeriodicMainTerm_eq_oddOddSector_sub_oneBlockCorrection_of_two_mul_odd_left_of_coprime
    (X := X) (n := 3) (q' := b) (by norm_num : Odd 3) hbpos]
  · rw [centeredRamanujanPairPeriodicMainOddOddSector_eq_zero_of_isEven_eq_three_left_public
      hXEven hb hcop3]
    rw [centeredRamanujanPairPeriodicMainOddOddOneBlockCorrection_eq_zero_of_isEven_eq_three_left_public
      hXEven hb hcop3]
    ring
  · simpa using hcop

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_coprime_rowSix_rightOdd_public
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOddPairs) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  rcases Finset.mem_filter.mp hp with ⟨hpRowSix, hpRightOdd⟩
  rcases Finset.mem_filter.mp hpRowSix with ⟨hpCoprime, hpLeftSix⟩
  rcases Finset.mem_filter.mp hpCoprime with ⟨hpDyadic, hcopData⟩
  rcases hcopData with ⟨_hnotUnitTwo, hcop⟩
  have hpFullSq :
      p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit :=
    PeriodicMainZeroDyadicExceptionPairs_subset_fullBlockSquarefreeExplicit hpDyadic
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hpFullSq).1
  have hpRightSq : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).2
  have hpRightActive : p.2 ∈ PeriodicMainActiveSupportExplicit := by
    rw [PeriodicMainActiveSupportExplicit_eq_squarefreeExplicit]
    exact hpRightSq
  have hpRightCoeff : p.2 ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 := by
    exact (Finset.mem_filter.mp hpRightActive).1
  have hpRightOddSupp : p.2 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
    mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mpr
      ⟨hpRightCoeff, hpRightOdd⟩
  have hcop6 : Nat.Coprime 6 p.2 := by
    simpa [hpLeftSix] using hcop
  have hneq : p.1 ≠ p.2 := by
    intro hdiag
    have hpRightSix : p.2 = 6 := by
      rw [← hdiag, hpLeftSix]
    have hbadOdd : Odd 6 := by
      simpa [hpRightSix] using hpRightOdd
    norm_num at hbadOdd
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  rw [if_neg hneq]
  rw [hpLeftSix]
  rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_six_left_odd_right_public
    X0_isEven_rowSix hpRightOddSupp hcop6]
  ring

theorem PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOdd_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_coprime_rowSix_rightOdd_public hp

theorem PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEven_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  have hempty : PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs = ∅ :=
    Finset.card_eq_zero.mp PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs_card
  rw [hempty] at hp
  simp at hp

theorem PeriodicMainZeroDyadicExceptionCoprimeRowSix_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs_eq_rightOdd_union_rightEven] at hp
  rcases Finset.mem_union.mp hp with hpOdd | hpEven
  · exact PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOdd_value_on_records_public p hpOdd
  · exact PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEven_value_on_records_public p hpEven

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreeSix_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs_eq_rowThree_union_rowSix] at hp
  rcases Finset.mem_union.mp hp with hpThree | hpSix
  · exact PeriodicMainZeroDyadicExceptionCoprimeRowThree_value_on_records_public p hpThree
  · exact PeriodicMainZeroDyadicExceptionCoprimeRowSix_value_on_records_public p hpSix

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
