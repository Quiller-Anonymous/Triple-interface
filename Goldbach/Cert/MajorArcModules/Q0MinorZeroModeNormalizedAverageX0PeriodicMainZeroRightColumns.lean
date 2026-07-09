import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroRowSix

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private theorem X0_isEven_rightColumns : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

theorem ramanujanGcdClassJointCompatibility_comm_public
    (q q' g h : ℕ) :
    ramanujanGcdClassJointCompatibility q q' g h ↔
      ramanujanGcdClassJointCompatibility q' q h g := by
  unfold ramanujanGcdClassJointCompatibility
  constructor
  · intro hc
    simpa [Nat.lcm_comm] using And.symm hc
  · intro hc
    simpa [Nat.lcm_comm] using And.symm hc

theorem rawEvenRamanujanGcdClassPairBlockResolvedCount_comm_public
    (X q q' g h : ℕ) :
    rawEvenRamanujanGcdClassPairBlockResolvedCount X q q' g h =
      rawEvenRamanujanGcdClassPairBlockResolvedCount X q' q h g := by
  unfold rawEvenRamanujanGcdClassPairBlockResolvedCount
  by_cases hcompat : ramanujanGcdClassJointCompatibility q q' g h
  · have hcompat' : ramanujanGcdClassJointCompatibility q' q h g :=
      (ramanujanGcdClassJointCompatibility_comm_public q q' g h).mp hcompat
    simp [hcompat, hcompat', rawEvenRamanujanGcdClassPairBlockPeriodicCount_comm]
  · have hcompat' : ¬ ramanujanGcdClassJointCompatibility q' q h g := by
      intro h'
      exact hcompat ((ramanujanGcdClassJointCompatibility_comm_public q q' g h).mpr h')
    simp [hcompat, hcompat']

theorem centeredRamanujanPairPeriodicMainTerm_comm_public
    (X q q' : ℕ) :
    centeredRamanujanPairPeriodicMainTerm X q q' =
      centeredRamanujanPairPeriodicMainTerm X q' q := by
  unfold centeredRamanujanPairPeriodicMainTerm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [centeredRamanujanPairBlockPeriod_comm]
  rw [rawEvenRamanujanGcdClassPairBlockResolvedCount_comm_public]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_comm X q q' q g]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCount_comm X q q' q' h]
  rw [evenRamanujanBlockCount_comm]
  ring

theorem centeredRamanujanPairPeriodicMainTermRat_comm_public
    (X q q' : ℕ) :
    centeredRamanujanPairPeriodicMainTermRat X q q' =
      centeredRamanujanPairPeriodicMainTermRat X q' q := by
  apply Rat.cast_injective (α := ℝ)
  rw [← centeredRamanujanPairPeriodicMainTerm_eq_ratCast]
  rw [← centeredRamanujanPairPeriodicMainTerm_eq_ratCast]
  exact centeredRamanujanPairPeriodicMainTerm_comm_public X q q'

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_swap_public
    (X : ℕ) (p : ℕ × ℕ) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X p =
      surrogatePeriodicMainActiveOrderedPairSummandRat X (p.2, p.1) := by
  rcases p with ⟨q, q'⟩
  by_cases hdiag : q = q'
  · simp [hdiag]
  · have hdiag' : q' ≠ q := by
      intro h
      exact hdiag h.symm
    calc
      surrogatePeriodicMainActiveOrderedPairSummandRat X (q, q')
          =
            surrogateNormalizedSigmaTruncSummandCoeffRat q
              * surrogateNormalizedSigmaTruncSummandCoeffRat q'
              * centeredRamanujanPairPeriodicMainTermRat X q q' := by
            simp [surrogatePeriodicMainActiveOrderedPairSummandRat, hdiag]
      _ =
            surrogateNormalizedSigmaTruncSummandCoeffRat q'
              * surrogateNormalizedSigmaTruncSummandCoeffRat q
              * centeredRamanujanPairPeriodicMainTermRat X q' q := by
            rw [centeredRamanujanPairPeriodicMainTermRat_comm_public]
            ring
      _ = surrogatePeriodicMainActiveOrderedPairSummandRat X (q', q) := by
            simp [surrogatePeriodicMainActiveOrderedPairSummandRat, hdiag']

def PeriodicMainZeroDyadicExceptionCoprimeResidualRightThreeSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimeResidualPairs.filter
    (fun p => p.2 = 3 ∨ p.2 = 6)

def PeriodicMainZeroDyadicExceptionCoprimeCoreResidualPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimeResidualPairs.filter
    (fun p => ¬ (p.2 = 3 ∨ p.2 = 6))

def PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs.filter
    (fun p => p.2 = 3 ∨ p.2 = 6)

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs.filter
    (fun p => ¬ (p.2 = 3 ∨ p.2 = 6))

theorem PeriodicMainZeroDyadicExceptionCoprimeResidualRightThreeSixPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeResidualRightThreeSixPairs.card = 1015 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeCoreResidualPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeCoreResidualPairs.card = 630 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs.card = 1523 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs.card = 2972 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeResidualPairs_eq_rightThreeSix_union_core :
    PeriodicMainZeroDyadicExceptionCoprimeResidualPairs =
      PeriodicMainZeroDyadicExceptionCoprimeResidualRightThreeSixPairs ∪
        PeriodicMainZeroDyadicExceptionCoprimeCoreResidualPairs := by
  ext p
  constructor
  · intro hp
    by_cases hright : p.2 = 3 ∨ p.2 = 6
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hright⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hright⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpRight | hpCore
    · exact (Finset.mem_filter.mp hpRight).1
    · exact (Finset.mem_filter.mp hpCore).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs_eq_rightThreeSix_union_core :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeResidualRightThreeSixPairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs := by
  ext p
  constructor
  · intro hp
    by_cases hright : p.2 = 3 ∨ p.2 = 6
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hright⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hright⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpRight | hpCore
    · exact (Finset.mem_filter.mp hpRight).1
    · exact (Finset.mem_filter.mp hpCore).1

theorem PeriodicMainZeroDyadicExceptionCoprimeResidualRightThreeSix_value_on_records_public :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeResidualRightThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpResidual, hpRight⟩
  rcases Finset.mem_filter.mp hpResidual with ⟨hpCop, _hpNotLeftThreeSix⟩
  rcases Finset.mem_filter.mp hpCop with ⟨hpDyadic, hcopData⟩
  rcases hcopData with ⟨_hnotUnitTwo, hcop⟩
  have hpFullSq :
      p ∈ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit :=
    PeriodicMainZeroDyadicExceptionPairs_subset_fullBlockSquarefreeExplicit hpDyadic
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hpFullSq).1
  have hpLeftSq : p.1 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).1
  have hpLeftActive : p.1 ∈ PeriodicMainActiveSupportExplicit := by
    rw [PeriodicMainActiveSupportExplicit_eq_squarefreeExplicit]
    exact hpLeftSq
  have hpLeftCoeff : p.1 ∈ normalizedSigmaTruncSummandCoeffSupportUpToQ0 :=
    (Finset.mem_filter.mp hpLeftActive).1
  have hneqSwap : p.2 ≠ p.1 := by
    intro hEq
    have hcopSelf : Nat.Coprime p.2 p.2 := by
      simpa [hEq] using hcop.symm
    rcases hpRight with hpRightThree | hpRightSix
    · norm_num [hpRightThree] at hcopSelf
    · norm_num [hpRightSix] at hcopSelf
  rw [surrogatePeriodicMainActiveOrderedPairSummandRat_swap_public X0 p]
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  rcases hpRight with hpRightThree | hpRightSix
  · have hcop3Left : Nat.Coprime 3 p.1 := by
      simpa [hpRightThree, Nat.coprime_comm] using hcop
    by_cases hpLeftOdd : Odd p.1
    · have hpLeftOddSupp : p.1 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
        mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mpr
          ⟨hpLeftCoeff, hpLeftOdd⟩
      rw [if_neg hneqSwap]
      rw [hpRightThree]
      rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_public
        X0_isEven_rightColumns hpLeftOddSupp hcop3Left]
      ring
    · have hpLeftEvenNat : Even p.1 := Nat.not_odd_iff_even.mp hpLeftOdd
      have hpLeftIsEven : Goldbach.Windows.IsEven p.1 :=
        Goldbach.Windows.isEven_of_even hpLeftEvenNat
      have hpLeftEq : p.1 = 2 * (p.1 / 2) :=
        (Nat.two_mul_div_two_of_even hpLeftEvenNat).symm
      have hpLeftHalfOddSupp :
          p.1 / 2 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
        half_mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_of_mem_even_support
          (Finset.mem_filter.mpr ⟨hpLeftCoeff, hpLeftIsEven⟩)
      have hcop3Half : Nat.Coprime 3 (2 * (p.1 / 2)) := by
        simpa [← hpLeftEq] using hcop3Left
      rw [if_neg hneqSwap]
      rw [hpRightThree, hpLeftEq]
      rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_three_left_two_mul_right_public
        X0_isEven_rightColumns hpLeftHalfOddSupp hcop3Half]
      ring
  · have hcop6Left : Nat.Coprime 6 p.1 := by
      simpa [hpRightSix, Nat.coprime_comm] using hcop
    have hpLeftOdd : Odd p.1 := by
      refine Nat.not_even_iff_odd.mp ?_
      intro hpLeftEven
      rcases hpLeftEven with ⟨k, hk⟩
      have htwo_dvd_left : 2 ∣ p.1 := by
        exact ⟨k, by simpa [two_mul] using hk⟩
      have htwo_dvd_gcd : 2 ∣ Nat.gcd 6 p.1 :=
        Nat.dvd_gcd (by norm_num) htwo_dvd_left
      have hgcd : Nat.gcd 6 p.1 = 1 := hcop6Left.gcd_eq_one
      norm_num [hgcd] at htwo_dvd_gcd
    have hpLeftOddSupp : p.1 ∈ normalizedSigmaTruncSummandOddCoeffSupportUpToQ0 :=
      mem_normalizedSigmaTruncSummandOddCoeffSupportUpToQ0_iff.mpr
        ⟨hpLeftCoeff, hpLeftOdd⟩
    rw [if_neg hneqSwap]
    rw [hpRightSix]
    rw [centeredRamanujanPairPeriodicMainTerm_eq_zero_of_isEven_eq_six_left_odd_right_public
      X0_isEven_rightColumns hpLeftOddSupp hcop6Left]
    ring

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
