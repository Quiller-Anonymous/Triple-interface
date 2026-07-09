import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowAssembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeRawCore
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroRowThreeRightEven
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRecords000

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private theorem X0_isEven_rowSliceSmall : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

private theorem ramanujanWindowAverage_X0_three_eq_zero_for_rowSlice002 :
    ramanujanWindowAverage X0 3 = 0 := by
  have hAvgRat : ramanujanWindowAverageByGcdRat X0 3 = 0 := by
    native_decide
  rw [ramanujanWindowAverage_eq_ratCast_ramanujanWindowAverageByGcdRat
    (X := X0) (q := 3) (by norm_num)]
  rw [hAvgRat]
  norm_num

theorem centeredRamanujanPairFullEvenBlockSum_X0_three_three_mul_eq_zero_of_odd_core
    {b : ℕ} (hbpos : 1 ≤ b) (hbOdd : Odd b) (hb3 : ¬ 3 ∣ b)
    (hbSq : Squarefree b) (hbne : b ≠ 1) :
    centeredRamanujanPairFullEvenBlockSum X0 3 (3 * b) = 0 := by
  have hP3 : Nat.Coprime (centeredRamanujanPairBlockPeriod 1 b) 3 :=
    centeredRamanujanPairBlockPeriod_coprime_three_of_not_dvd_three
      (q := 1) (q' := b) (by norm_num) hb3
  have hcore :
      rawEvenRamanujanPairBlockSum X0 1 b = 0 := by
    exact rawEvenRamanujanPairBlockSum_eq_zero_of_odd_squarefree_coprime_offDiagonal
      (X := X0) (q := 1) (q' := b)
      (by norm_num) hbpos (Nat.coprime_one_left b)
      (by decide : Odd 1) hbOdd (by native_decide : Squarefree 1) hbSq
      (by
        intro h
        exact hbne h.symm)
  have hpair :
      rawEvenRamanujanPairBlockSum X0 3 (3 * b) = 0 := by
    have h :=
      rawEvenRamanujanPairBlockSum_three_mul_both_eq_six_mul
        (X := X0) (q := 1) (q' := b) (by norm_num) hb3 hP3
    rw [h]
    rw [hcore]
    ring
  have hleft :
      rawEvenRamanujanBlockSum X0 3 (3 * b) 3 = 0 := by
    simpa using
      rawEvenRamanujanBlockSum_three_mul_both_eq_zero
        (X := X0) (q := 1) (q' := b) (q0 := 1)
        (by norm_num) hP3
        (by
          unfold centeredRamanujanPairBlockPeriod
          norm_num)
  have hright :
      rawEvenRamanujanBlockSum X0 3 (3 * b) (3 * b) = 0 := by
    simpa using
      rawEvenRamanujanBlockSum_three_mul_both_eq_zero
        (X := X0) (q := 1) (q' := b) (q0 := b)
        hb3 hP3
        (by
          unfold centeredRamanujanPairBlockPeriod
          exact dvd_mul_of_dvd_right (dvd_lcm_right 1 b) 2)
  rw [centeredRamanujanPairFullEvenBlockSum_eq_rawBlock_decomposition]
  rw [hpair, hleft, hright, ramanujanWindowAverage_X0_three_eq_zero_for_rowSlice002]
  ring

theorem centeredRamanujanPairPeriodicMainTerm_X0_three_three_mul_eq_zero_of_core_ne_one_two
    {b : ℕ} (hbpos : 1 ≤ b) (hb3 : ¬ 3 ∣ b)
    (hbSq : Squarefree b) (hbne_one : b ≠ 1) (hbne_two : b ≠ 2) :
    centeredRamanujanPairPeriodicMainTerm X0 3 (3 * b) = 0 := by
  by_cases hbOdd : Odd b
  · have hfull :
        centeredRamanujanPairFullEvenBlockSum X0 3 (3 * b) = 0 :=
      centeredRamanujanPairFullEvenBlockSum_X0_three_three_mul_eq_zero_of_odd_core
        hbpos hbOdd hb3 hbSq hbne_one
    rw [centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_bothThree_probe
      (X := X0) (q := 3) (q' := 3 * b)
      (by norm_num) (Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le Nat.zero_lt_one hbpos))]
    rw [hfull]
    simp
  · have hbEven : Even b := Nat.not_odd_iff_even.mp hbOdd
    let c := b / 2
    have hbEq : b = 2 * c := by
      simpa [c] using (Nat.two_mul_div_two_of_even hbEven).symm
    have hcpos : 1 ≤ c := by
      have hbpos' : 0 < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hbpos
      have hcpos0 : 0 < c := by
        rw [hbEq] at hbpos'
        omega
      omega
    have hcOdd : Odd c := by
      refine Nat.not_even_iff_odd.mp ?_
      intro hcEven
      rcases hcEven with ⟨t, ht⟩
      have h4dvd : 2 ^ 2 ∣ b := by
        refine ⟨t, ?_⟩
        rw [hbEq, ht]
        ring
      exact (Nat.squarefree_iff_prime_squarefree.mp hbSq) 2 Nat.prime_two (by
        simpa [pow_two] using h4dvd)
    have hcSq : Squarefree c := by
      have h2dvd : 2 ∣ b := by
        exact even_iff_two_dvd.mp hbEven
      exact Squarefree.squarefree_of_dvd (by
        simpa [c] using Nat.div_dvd_of_dvd h2dvd)
        hbSq
    have hc3 : ¬ 3 ∣ c := by
      intro h3c
      exact hb3 (dvd_trans h3c (by
        rw [hbEq]
        exact dvd_mul_left c 2))
    have hcne : c ≠ 1 := by
      intro hc1
      exact hbne_two (by
        rw [hbEq, hc1])
    have hfull :
        centeredRamanujanPairFullEvenBlockSum X0 3 (3 * c) = 0 :=
      centeredRamanujanPairFullEvenBlockSum_X0_three_three_mul_eq_zero_of_odd_core
        hcpos hcOdd hc3 hcSq hcne
    have hterm :
        centeredRamanujanPairPeriodicMainTerm X0 3 (2 * (3 * c)) = 0 :=
      centeredRamanujanPairPeriodicMainTerm_X0_two_mul_right_eq_zero_of_base_full_zero_for_bothThree_transport
        (q := 3) (q' := 3 * c)
        (by decide : Odd 3) ((by decide : Odd 3).mul hcOdd) hfull
    have hright : 3 * b = 2 * (3 * c) := by
      rw [hbEq]
      ring
    rw [hright]
    exact hterm

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice002_coprime
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 3 4)
    (hcop : Nat.Coprime p.1 p.2) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  have hpLeftThree : p.1 = 3 := by
    have hpLo : 3 ≤ p.1 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit at hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpHi : p.1 < 4 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit at hp
      exact (Finset.mem_filter.mp hp).2
    omega
  have hpFullSq : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
    unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
      PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit at hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hpFullSq).1
  have hpRightSq : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).2
  have hpRightActive : p.2 ∈ PeriodicMainActiveSupportExplicit := by
    rw [PeriodicMainActiveSupportExplicit_eq_squarefreeExplicit]
    exact hpRightSq
  have hpRightCoeff : p.2 ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
    (Finset.mem_filter.mp hpRightActive).1
  have hneq : p.1 ≠ p.2 :=
    (Finset.mem_filter.mp hpFullSq).2.1
  have hcop3Right : Nat.Coprime 3 p.2 := by
    simpa [hpLeftThree] using hcop
  by_cases hpRightOdd : Odd p.2
  · have hpRightOddSupp : p.2 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mpr
        ⟨hpRightCoeff, hpRightOdd⟩
    apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
    rw [if_neg hneq]
    rw [hpLeftThree]
    rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_public
      X0_isEven_rowSliceSmall hpRightOddSupp hcop3Right]
    ring
  · have hpRightEvenNat : Even p.2 :=
      Nat.not_odd_iff_even.mp hpRightOdd
    have hpRightIsEven : Goldbach.Windows.IsEven p.2 :=
      Goldbach.Windows.isEven_of_even hpRightEvenNat
    have hpRightEq : p.2 = 2 * (p.2 / 2) :=
      (Nat.two_mul_div_two_of_even hpRightEvenNat).symm
    have hpRightHalfOddSupp :
        p.2 / 2 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
      half_mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_of_mem_even_support
        (Finset.mem_filter.mpr ⟨hpRightCoeff, hpRightIsEven⟩)
    have hcop3Half : Nat.Coprime 3 (2 * (p.2 / 2)) := by
      simpa [← hpRightEq] using hcop3Right
    apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
    rw [if_neg hneq]
    rw [hpLeftThree, hpRightEq]
    rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_two_mul_right_public
      X0_isEven_rowSliceSmall hpRightHalfOddSupp hcop3Half]
    ring

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice002_nonCoprime_ne_three_six
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 3 4)
    (hncop : ¬ Nat.Coprime p.1 p.2)
    (hpne : p ≠ (3, 6)) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  have hpLeftThree : p.1 = 3 := by
    have hpLo : 3 ≤ p.1 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit at hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpHi : p.1 < 4 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit at hp
      exact (Finset.mem_filter.mp hp).2
    omega
  have hpFullSq : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
    unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
      PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit at hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hneq : p.1 ≠ p.2 :=
    (Finset.mem_filter.mp hpFullSq).2.1
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hpFullSq).1
  have hpRightSq : Squarefree p.2 := by
    have hpRight : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
      (Finset.mem_product.mp hpProd).2
    exact (Finset.mem_filter.mp hpRight).2
  have hpRightPos : 0 < p.2 := by
    have hpRight : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
      (Finset.mem_product.mp hpProd).2
    have hpIcc : p.2 ∈ Finset.Icc (1 : ℕ) ((H + 1) / 2) :=
      (Finset.mem_filter.mp hpRight).1
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpIcc).1
  have hrightDvdThree : 3 ∣ p.2 := by
    have hnotCop3 : ¬ Nat.Coprime 3 p.2 := by
      simpa [hpLeftThree] using hncop
    have hgcd_ne_one : Nat.gcd 3 p.2 ≠ 1 := by
      intro hgcd
      exact hnotCop3 (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
    have hdvd : Nat.gcd 3 p.2 ∣ 3 := Nat.gcd_dvd_left 3 p.2
    have hgcd_pos : 0 < Nat.gcd 3 p.2 := Nat.gcd_pos_of_pos_left p.2 (by norm_num)
    have hgcd_le : Nat.gcd 3 p.2 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hgcd_ne_two : Nat.gcd 3 p.2 ≠ 2 := by
      intro htwo
      have : 2 ∣ 3 := by
        rw [← htwo]
        exact hdvd
      norm_num at this
    have hgcd_eq_three : Nat.gcd 3 p.2 = 3 := by
      omega
    simpa [hgcd_eq_three] using Nat.gcd_dvd_right 3 p.2
  rcases hrightDvdThree with ⟨b, hb⟩
  have hbpos : 1 ≤ b := by
    have : 0 < b := by
      rw [hb] at hpRightPos
      omega
    omega
  have hbSq : Squarefree b := by
    exact Squarefree.squarefree_of_dvd (by
      refine ⟨3, ?_⟩
      simpa [Nat.mul_comm] using hb)
      hpRightSq
  have hb3 : ¬ 3 ∣ b := by
    intro h3b
    have h9dvd : 3 * 3 ∣ p.2 := by
      rcases h3b with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [hb, ht]
      ring
    exact (Nat.squarefree_iff_prime_squarefree.mp hpRightSq) 3 (by norm_num) h9dvd
  have hbneOne : b ≠ 1 := by
    intro hb1
    have hpRightThree : p.2 = 3 := by
      rw [hb, hb1]
    exact hneq (by
      rw [hpLeftThree, hpRightThree])
  have hbneTwo : b ≠ 2 := by
    intro hb2
    exact hpne (by
      ext <;> simp [hpLeftThree, hb, hb2])
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  rw [if_neg hneq]
  rw [hpLeftThree, hb]
  rw [centeredRamanujanPairPeriodicMainTerm_X0_three_three_mul_eq_zero_of_core_ne_one_two
    hbpos hb3 hbSq hbneOne hbneTwo]
  ring

theorem periodicMainRowSlice002_true :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 3 4,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainRowSliceTotal002 := by
  have hmem36 :
      (3, 6) ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 3 4 := by
    native_decide
  calc
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 3 4,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
        =
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (3, 6) := by
        exact Finset.sum_eq_single_of_mem (3, 6) hmem36 (by
          intro p hp hpne
          by_cases hcop : Nat.Coprime p.1 p.2
          · exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice002_coprime
              hp hcop
          · exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice002_nonCoprime_ne_three_six
              hp hcop hpne)
    _ = PeriodicMainRowSliceTotal002 := by
      rw [periodicMainPair_3_6_X1000000_orderedSummand]
      norm_num [PeriodicMainRowSliceTotal002]

theorem periodicMainRowSlice003_true :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 4 5,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainRowSliceTotal003 := by
  unfold PeriodicMainRowSliceTotal003
  trans 0
  · refine Finset.sum_eq_zero ?_
    intro p hp
    have hp1 : p.1 = 4 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit
        PeriodicMainActiveSupportSquarefreeExplicit at hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      omega
    have hpSquarefree : Squarefree p.1 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit
        PeriodicMainActiveSupportSquarefreeExplicit at hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      exact hp.1.1.1.1.2
    have hnot : ¬ Squarefree p.1 := by
      rw [hp1]
      native_decide
    exact False.elim (hnot hpSquarefree)
  · norm_num

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
