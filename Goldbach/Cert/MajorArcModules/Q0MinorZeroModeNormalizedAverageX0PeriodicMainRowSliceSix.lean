import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceSixStructural

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

theorem periodicMainPair_6_3_X1000000_orderedSummand :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (6, 3) = (62475 : ℚ) / 4 := by
  rw [surrogatePeriodicMainActiveOrderedPairSummandRat_swap_public X0 (6, 3)]
  simpa using periodicMainPair_3_6_X1000000_orderedSummand

private theorem X0_isEven_rowSlice005 : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

private theorem coprime_three_of_not_dvd
    {n : ℕ} (hn : ¬ 3 ∣ n) : Nat.Coprime 3 n := by
  exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mpr hn

private theorem odd_of_squarefree_half
    {n b : ℕ} (hnSq : Squarefree n) (hnEq : n = 2 * b) : Odd b := by
  refine Nat.not_even_iff_odd.mp ?_
  intro hbEven
  rcases hbEven with ⟨t, ht⟩
  have h4dvd : 2 ^ 2 ∣ n := by
    refine ⟨t, ?_⟩
    rw [hnEq, ht]
    ring
  exact (Nat.squarefree_iff_prime_squarefree.mp hnSq) 2 Nat.prime_two (by
    simpa [pow_two] using h4dvd)

private theorem squarefree_of_factor
    {a n : ℕ} (hdvd : a ∣ n) (hnSq : Squarefree n) : Squarefree a :=
  Squarefree.squarefree_of_dvd hdvd hnSq

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice005_coprime
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 6 7)
    (hcop : Nat.Coprime p.1 p.2) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  have hpLeftSix : p.1 = 6 := by
    have hpLo : 6 ≤ p.1 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit at hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpHi : p.1 < 7 := by
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
  have hpRightSqMem : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).2
  have hpRightActive : p.2 ∈ PeriodicMainActiveSupportExplicit := by
    rw [PeriodicMainActiveSupportExplicit_eq_squarefreeExplicit]
    exact hpRightSqMem
  have hpRightCoeff : p.2 ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
    (Finset.mem_filter.mp hpRightActive).1
  have hcop6 : Nat.Coprime 6 p.2 := by
    simpa [hpLeftSix] using hcop
  have hpRightOdd : Odd p.2 := by
    refine Nat.not_even_iff_odd.mp ?_
    intro hpEven
    have htwoRight : 2 ∣ p.2 := even_iff_two_dvd.mp hpEven
    have htwoGcd : 2 ∣ Nat.gcd 6 p.2 :=
      Nat.dvd_gcd (by norm_num) htwoRight
    have hgcd : Nat.gcd 6 p.2 = 1 := hcop6.gcd_eq_one
    norm_num [hgcd] at htwoGcd
  have hpRightOddSupp : p.2 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
    mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mpr
      ⟨hpRightCoeff, hpRightOdd⟩
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  rw [if_neg hneq]
  rw [hpLeftSix]
  rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_six_left_odd_right_public
    X0_isEven_rowSlice005 hpRightOddSupp hcop6]
  ring

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice005_nonCoprime_ne_six_three
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 6 7)
    (hncop : ¬ Nat.Coprime p.1 p.2)
    (hpne : p ≠ (6, 3)) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  have hpLeftSix : p.1 = 6 := by
    have hpLo : 6 ≤ p.1 := by
      unfold PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit
        PeriodicMainFullBlockOrderedPairSupportSquarefreeRowRemainderExplicit at hp
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpHi : p.1 < 7 := by
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
  have hpRightSqMem : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).2
  have hpRightSq : Squarefree p.2 :=
    (Finset.mem_filter.mp hpRightSqMem).2
  have hpRightPos : 0 < p.2 := by
    have hpIcc : p.2 ∈ Finset.Icc (1 : ℕ) ((H + 1) / 2) :=
      (Finset.mem_filter.mp hpRightSqMem).1
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpIcc).1
  by_cases hpRightEven : Even p.2
  · let b := p.2 / 2
    have hpRightEq : p.2 = 2 * b :=
      (Nat.two_mul_div_two_of_even hpRightEven).symm
    have hbpos : 1 ≤ b := by
      have hbpos0 : 0 < b := by
        rw [hpRightEq] at hpRightPos
        omega
      omega
    have hbOdd : Odd b := odd_of_squarefree_half hpRightSq hpRightEq
    have hbSq : Squarefree b := by
      have h2dvd : 2 ∣ p.2 := even_iff_two_dvd.mp hpRightEven
      exact squarefree_of_factor (by
        simpa [b] using Nat.div_dvd_of_dvd h2dvd)
        hpRightSq
    by_cases hthreeRight : 3 ∣ p.2
    · have hthreeB : 3 ∣ b := by
        have hthreeTwoB : 3 ∣ 2 * b := by
          simpa [← hpRightEq] using hthreeRight
        exact ((by norm_num : Nat.Coprime 3 2).dvd_mul_left).mp hthreeTwoB
      rcases hthreeB with ⟨c, hbEq⟩
      have hcpos : 1 ≤ c := by
        have : 0 < c := by
          rw [hbEq] at hbpos
          omega
        omega
      have hcOdd : Odd c := by
        refine Nat.not_even_iff_odd.mp ?_
        intro hcEven
        have htwoC : 2 ∣ c := even_iff_two_dvd.mp hcEven
        have htwoB : 2 ∣ b := by
          rw [hbEq]
          exact dvd_mul_of_dvd_right htwoC 3
        exact (Nat.not_even_iff_odd.mpr hbOdd) (even_iff_two_dvd.mpr htwoB)
      have hcSq : Squarefree c := by
        exact squarefree_of_factor (by
          refine ⟨6, ?_⟩
          rw [hpRightEq, hbEq]
          ring)
          hpRightSq
      have hc3 : ¬ 3 ∣ c := by
        intro h3c
        have h9dvd : 3 * 3 ∣ p.2 := by
          rcases h3c with ⟨t, ht⟩
          refine ⟨2 * t, ?_⟩
          rw [hpRightEq, hbEq, ht]
          ring
        exact (Nat.squarefree_iff_prime_squarefree.mp hpRightSq) 3 (by norm_num) h9dvd
      have hcne : c ≠ 1 := by
        intro hc1
        have hpRightSix : p.2 = 6 := by
          rw [hpRightEq, hbEq, hc1]
        exact hneq (by
          rw [hpLeftSix, hpRightSix])
      apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
      rw [if_neg hneq]
      rw [hpLeftSix]
      have hright : p.2 = 6 * c := by
        rw [hpRightEq, hbEq]
        ring
      rw [hright]
      rw [centeredRamanujanPairPeriodicMainTerm_X0_six_six_mul_eq_zero_of_odd_core_for_rowSlice005
        hcpos hcOdd hc3 hcSq hcne]
      ring
    · have hb3 : ¬ 3 ∣ b := by
        intro h3b
        exact hthreeRight (dvd_trans h3b (by
          rw [hpRightEq]
          exact dvd_mul_left b 2))
      have hcop3b : Nat.Coprime 3 b := coprime_three_of_not_dvd hb3
      apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
      rw [if_neg hneq]
      rw [hpLeftSix, hpRightEq]
      rw [centeredRamanujanPairPeriodicMainTerm_X0_six_two_mul_eq_zero_of_odd_coprime_for_rowSlice005
        hbpos hbOdd hcop3b]
      ring
  · have hpRightOdd : Odd p.2 := Nat.not_even_iff_odd.mp hpRightEven
    have hthreeRight : 3 ∣ p.2 := by
      have hnotCop6 : ¬ Nat.Coprime 6 p.2 := by
        simpa [hpLeftSix] using hncop
      have hgcd_ne_one : Nat.gcd 6 p.2 ≠ 1 := by
        intro hgcd
        exact hnotCop6 (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
      have hnotEvenRight : ¬ Goldbach.Windows.IsEven p.2 := by
        intro hEven
        exact (Nat.not_even_iff_odd.mpr hpRightOdd) (Goldbach.Windows.even_of_isEven hEven)
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
    rcases hthreeRight with ⟨b, hbEq⟩
    have hbpos : 1 ≤ b := by
      have : 0 < b := by
        rw [hbEq] at hpRightPos
        omega
      omega
    have hbOdd : Odd b := by
      refine Nat.not_even_iff_odd.mp ?_
      intro hbEven
      have htwoB : 2 ∣ b := even_iff_two_dvd.mp hbEven
      have htwoRight : 2 ∣ p.2 := by
        rw [hbEq]
        exact dvd_mul_of_dvd_right htwoB 3
      exact (Nat.not_even_iff_odd.mpr hpRightOdd) (even_iff_two_dvd.mpr htwoRight)
    have hbSq : Squarefree b := by
      exact squarefree_of_factor (by
        refine ⟨3, ?_⟩
        simpa [Nat.mul_comm] using hbEq)
        hpRightSq
    have hb3 : ¬ 3 ∣ b := by
      intro h3b
      have h9dvd : 3 * 3 ∣ p.2 := by
        rcases h3b with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [hbEq, ht]
        ring
      exact (Nat.squarefree_iff_prime_squarefree.mp hpRightSq) 3 (by norm_num) h9dvd
    have hbne : b ≠ 1 := by
      intro hb1
      exact hpne (by
        ext <;> simp [hpLeftSix, hbEq, hb1])
    apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
    rw [if_neg hneq]
    rw [hpLeftSix, hbEq]
    rw [centeredRamanujanPairPeriodicMainTerm_X0_six_three_mul_eq_zero_of_odd_core_for_rowSlice005
      hbpos hbOdd hb3 hbSq hbne]
    ring

theorem periodicMainRowSlice005_true :
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 6 7,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainRowSliceTotal005 := by
  have hmem63 :
      (6, 3) ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 6 7 := by
    native_decide
  calc
    (∑ p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeRowSliceExplicit 6 7,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
        =
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (6, 3) := by
        exact Finset.sum_eq_single_of_mem (6, 3) hmem63 (by
          intro p hp hpne
          by_cases hcop : Nat.Coprime p.1 p.2
          · exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice005_coprime
              hp hcop
          · exact surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_rowSlice005_nonCoprime_ne_six_three
              hp hcop hpne)
    _ = PeriodicMainRowSliceTotal005 := by
      rw [periodicMainPair_6_3_X1000000_orderedSummand]
      norm_num [PeriodicMainRowSliceTotal005]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
