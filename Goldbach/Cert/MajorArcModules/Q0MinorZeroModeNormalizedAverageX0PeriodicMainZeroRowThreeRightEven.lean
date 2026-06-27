import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroRowThree

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private theorem X0_isEven_rightEven : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

private theorem divisor_pos_of_mem_divisors_of_pos_rightEven
    {n d : ℕ} (hd : d ∈ n.divisors) (hn : 1 ≤ n) :
    0 < d := by
  rcases Nat.mem_divisors.mp hd with ⟨hdvd, _hn0⟩
  exact Nat.pos_of_ne_zero (by
    intro hd0
    subst d
    rcases hdvd with ⟨k, hk⟩
    have : n = 0 := by simpa using hk
    exact (Nat.ne_of_gt hn) this)

private theorem ramanujanGcdClassDivisors_coprime_of_coprime_moduli_rightEven
    {q q' g h : ℕ} (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    Nat.Coprime g h := by
  have hgdvd : g ∣ q := (Nat.mem_divisors.mp hg).1
  have hhdvd : h ∣ q' := (Nat.mem_divisors.mp hh).1
  exact (hcop.coprime_dvd_left hgdvd).coprime_dvd_right hhdvd

private theorem ramanujanGcdClassJointCompatibility_of_coprime_moduli_divisors_rightEven
    {q q' g h : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hcop : Nat.Coprime q q')
    (hg : g ∈ q.divisors) (hh : h ∈ q'.divisors) :
    ramanujanGcdClassJointCompatibility q q' g h := by
  have hgpos : 0 < g := divisor_pos_of_mem_divisors_of_pos_rightEven hg hq
  have hhpos : 0 < h := divisor_pos_of_mem_divisors_of_pos_rightEven hh hq'
  have hgh : Nat.Coprime g h :=
    ramanujanGcdClassDivisors_coprime_of_coprime_moduli_rightEven hcop hg hh
  have hqg_dvd : q / g ∣ q := Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hg).1
  have hq'h_dvd : q' / h ∣ q' := Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hh).1
  have hlcm_div_g : Nat.lcm g h / g = h := by
    rw [hgh.lcm_eq_mul]
    simpa [Nat.mul_comm] using (Nat.mul_div_left h hgpos)
  have hlcm_div_h : Nat.lcm g h / h = g := by
    rw [hgh.lcm_eq_mul]
    simpa [Nat.mul_comm] using (Nat.mul_div_right g hhpos)
  unfold ramanujanGcdClassJointCompatibility
  constructor
  · rw [hlcm_div_g]
    exact ((hcop.coprime_dvd_left hqg_dvd).coprime_dvd_right (Nat.mem_divisors.mp hh).1)
  · rw [hlcm_div_h]
    exact (((hcop.coprime_dvd_right hq'h_dvd).coprime_dvd_left (Nat.mem_divisors.mp hg).1).symm)

theorem centeredRamanujanPairPeriodicMainOddOddOneBlockCorrection_eq_zero_of_isEven_eq_three_left_public
    {X b : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hb : b ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0)
    (hcop : Nat.Coprime 3 b) :
    centeredRamanujanPairPeriodicMainOddOddOneBlockCorrection X 3 b = 0 := by
  rcases mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mp hb with ⟨hbCoeff, hbOdd⟩
  have hbpos : 1 ≤ b :=
    (Finset.mem_Icc.mp (mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mp hbCoeff).1).1
  have hq : 1 ≤ 3 := by norm_num
  unfold centeredRamanujanPairPeriodicMainOddOddOneBlockCorrection
  refine Finset.sum_eq_zero ?_
  intro g hg
  refine Finset.sum_eq_zero ?_
  intro h hh
  have hgDiv : g ∈ (3 : ℕ).divisors := (Finset.mem_filter.mp hg).1
  have hhDiv : h ∈ b.divisors := (Finset.mem_filter.mp hh).1
  have hcompat : ramanujanGcdClassJointCompatibility 3 b g h := by
    exact ramanujanGcdClassJointCompatibility_of_coprime_moduli_divisors_rightEven
      hq hbpos hcop hgDiv hhDiv
  have hzero :
      rawEvenRamanujanGcdClassPairBlockPeriodicCount X 3 b g h
        - ramanujanGcdClassWindowAverage X b h
            * rawEvenRamanujanGcdClassBlockPeriodicCount X 3 b 3 g
        - ramanujanGcdClassWindowAverage X 3 g
            * rawEvenRamanujanGcdClassBlockPeriodicCount X 3 b b h
        + ramanujanGcdClassWindowAverage X 3 g * ramanujanGcdClassWindowAverage X b h
            * evenRamanujanBlockCount X 3 b = 0 := by
    have hfull :=
      centeredRamanujanGcdClassPairFullEvenBlockSum_eq_zero_of_isEven_eq_three_left_public
        hXEven hbpos hbOdd hcop hg hh
    rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_periodic_comparison
      hq hbpos hgDiv hhDiv hcompat] at hfull
    exact hfull
  unfold centeredRamanujanPairPeriodicMainOddOddRawPeriodicComparisonCore
  rw [hzero]
  simp

theorem centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_two_mul_right_public
    {X n : ℕ} (hXEven : Goldbach.Windows.IsEven X)
    (hn : n ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0)
    (hcop : Nat.Coprime 3 (2 * n)) :
    centeredRamanujanPairPeriodicMainTerm X 3 (2 * n) = 0 := by
  rcases mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mp hn with ⟨hnCoeff, hnOdd⟩
  have hcop3n : Nat.Coprime 3 n := by
    exact hcop.coprime_dvd_right ⟨2, by ring⟩
  rw [centeredRamanujanPairPeriodicMainTerm_eq_oddOddSector_sub_oneBlockCorrection_of_two_mul_odd_right_of_coprime
    (X := X) hnOdd (by norm_num : 1 ≤ 3) hcop]
  rw [centeredRamanujanPairPeriodicMainOddOddSector_eq_zero_of_isEven_eq_three_left_public
    hXEven hn hcop3n]
  rw [centeredRamanujanPairPeriodicMainOddOddOneBlockCorrection_eq_zero_of_isEven_eq_three_left_public
    hXEven hn hcop3n]
  ring

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_coprime_rowThree_rightEven_public
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEvenPairs) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  rcases Finset.mem_filter.mp hp with ⟨hpRowThree, hpRightEven⟩
  rcases Finset.mem_filter.mp hpRowThree with ⟨hpCoprime, hpLeftThree⟩
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
  have hpRightEvenNat : Even p.2 :=
    Nat.not_odd_iff_even.mp hpRightEven
  have hpRightIsEven : Goldbach.Windows.IsEven p.2 :=
    Goldbach.Windows.isEven_of_even hpRightEvenNat
  have hpRightEq : p.2 = 2 * (p.2 / 2) :=
    (Nat.two_mul_div_two_of_even hpRightEvenNat).symm
  have hpRightHalfOddSupp :
      p.2 / 2 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
    half_mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_of_mem_even_support
      (Finset.mem_filter.mpr ⟨hpRightCoeff, hpRightIsEven⟩)
  have hcop3Right : Nat.Coprime 3 p.2 := by
    simpa [hpLeftThree] using hcop
  have hcop3Half : Nat.Coprime 3 (2 * (p.2 / 2)) := by
    simpa [← hpRightEq] using hcop3Right
  have hneq : p.1 ≠ p.2 := by
    intro hdiag
    have hpRightThree : p.2 = 3 := by
      rw [← hdiag, hpLeftThree]
    have hbadEven : Even 3 := by
      simpa [hpRightThree] using hpRightEvenNat
    norm_num at hbadEven
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  rw [if_neg hneq]
  rw [hpLeftThree, hpRightEq]
  rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_two_mul_right_public
    X0_isEven_rightEven hpRightHalfOddSupp hcop3Half]
  ring

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEven_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_coprime_rowThree_rightEven_public hp

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThree_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs_eq_rightOdd_union_rightEven] at hp
  rcases Finset.mem_union.mp hp with hpOdd | hpEven
  · exact PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOdd_value_on_records_public p hpOdd
  · exact PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEven_value_on_records_public p hpEven

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
