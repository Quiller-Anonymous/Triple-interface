import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroClassified

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

def PeriodicMainZeroDyadicExceptionUnitTwoPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionPairs.filter
    (fun p => p.1 = 1 ∨ p.1 = 2 ∨ p.2 = 1 ∨ p.2 = 2)

def PeriodicMainZeroDyadicExceptionCoprimePairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionPairs.filter
    (fun p => ¬ (p.1 = 1 ∨ p.1 = 2 ∨ p.2 = 1 ∨ p.2 = 2) ∧ Nat.Coprime p.1 p.2)

def PeriodicMainZeroDyadicExceptionNonCoprimePairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionPairs.filter
    (fun p => ¬ (p.1 = 1 ∨ p.1 = 2 ∨ p.2 = 1 ∨ p.2 = 2) ∧ ¬ Nat.Coprime p.1 p.2)

def PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimePairs.filter
    (fun p => p.1 = 3 ∨ p.1 = 6)

def PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimePairs.filter
    (fun p => p.1 = 3)

def PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOddPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs.filter
    (fun p => Odd p.2)

def PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEvenPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs.filter
    (fun p => ¬ Odd p.2)

def PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimePairs.filter
    (fun p => p.1 = 6)

def PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOddPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs.filter
    (fun p => Odd p.2)

def PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs.filter
    (fun p => ¬ Odd p.2)

def PeriodicMainZeroDyadicExceptionCoprimeResidualPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionCoprimePairs.filter
    (fun p => ¬ (p.1 = 3 ∨ p.1 = 6))

def PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimePairs.filter
    (fun p => p.1 = 3 ∨ p.1 = 6)

def PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimePairs.filter
    (fun p => p.1 = 3)

def PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs.filter
    (fun p => Odd p.2)

def PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs.filter
    (fun p => ¬ Odd p.2)

def PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimePairs.filter
    (fun p => p.1 = 6)

def PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs.filter
    (fun p => Odd p.2)

def PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs.filter
    (fun p => ¬ Odd p.2)

def PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimePairs.filter
    (fun p => ¬ (p.1 = 3 ∨ p.1 = 6))

theorem PeriodicMainZeroDyadicExceptionUnitTwoPairs_card :
    PeriodicMainZeroDyadicExceptionUnitTwoPairs.card = 976 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimePairs_card :
    PeriodicMainZeroDyadicExceptionCoprimePairs.card = 2660 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimePairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimePairs.card = 6018 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs.card = 1015 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs.card = 761 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOddPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOddPairs.card = 507 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEvenPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEvenPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOddPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOddPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs.card = 0 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionCoprimeResidualPairs_card :
    PeriodicMainZeroDyadicExceptionCoprimeResidualPairs.card = 1645 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs.card = 1523 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs.card = 761 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs.card = 507 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs.card = 762 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs.card = 254 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs.card = 508 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs.card = 4495 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionPairs_eq_unitTwo_union_coprime_union_nonCoprime :
    PeriodicMainZeroDyadicExceptionPairs =
      (PeriodicMainZeroDyadicExceptionUnitTwoPairs ∪
        PeriodicMainZeroDyadicExceptionCoprimePairs) ∪
          PeriodicMainZeroDyadicExceptionNonCoprimePairs := by
  ext p
  constructor
  · intro hp
    by_cases hunit : p.1 = 1 ∨ p.1 = 2 ∨ p.2 = 1 ∨ p.2 = 2
    · exact Finset.mem_union.mpr (Or.inl <|
        Finset.mem_union.mpr (Or.inl <|
          Finset.mem_filter.mpr ⟨hp, hunit⟩))
    · by_cases hcop : Nat.Coprime p.1 p.2
      · exact Finset.mem_union.mpr (Or.inl <|
          Finset.mem_union.mpr (Or.inr <|
            Finset.mem_filter.mpr ⟨hp, ⟨hunit, hcop⟩⟩))
      · exact Finset.mem_union.mpr (Or.inr <|
          Finset.mem_filter.mpr ⟨hp, ⟨hunit, hcop⟩⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpLeft | hpNonCop
    · rcases Finset.mem_union.mp hpLeft with hpUnit | hpCop
      · exact (Finset.mem_filter.mp hpUnit).1
      · exact (Finset.mem_filter.mp hpCop).1
    · exact (Finset.mem_filter.mp hpNonCop).1

theorem PeriodicMainZeroDyadicExceptionCoprimePairs_eq_rowThreeSix_union_residual :
    PeriodicMainZeroDyadicExceptionCoprimePairs =
      PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs ∪
        PeriodicMainZeroDyadicExceptionCoprimeResidualPairs := by
  ext p
  constructor
  · intro hp
    by_cases hrow : p.1 = 3 ∨ p.1 = 6
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hrow⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hrow⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpRow | hpResidual
    · exact (Finset.mem_filter.mp hpRow).1
    · exact (Finset.mem_filter.mp hpResidual).1

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs_eq_rowThree_union_rowSix :
    PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs =
      PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs ∪
        PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpCop, hpRow⟩
    rcases hpRow with hpThree | hpSix
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hpCop, hpThree⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hpCop, hpSix⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpThree | hpSix
    · rcases Finset.mem_filter.mp hpThree with ⟨hpCop, hpThree'⟩
      exact Finset.mem_filter.mpr ⟨hpCop, Or.inl hpThree'⟩
    · rcases Finset.mem_filter.mp hpSix with ⟨hpCop, hpSix'⟩
      exact Finset.mem_filter.mpr ⟨hpCop, Or.inr hpSix'⟩

theorem PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs_eq_rightOdd_union_rightEven :
    PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs =
      PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOddPairs ∪
        PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEvenPairs := by
  ext p
  constructor
  · intro hp
    by_cases hodd : Odd p.2
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact (Finset.mem_filter.mp hpOdd).1
    · exact (Finset.mem_filter.mp hpEven).1

theorem PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs_eq_rightOdd_union_rightEven :
    PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs =
      PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOddPairs ∪
        PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs := by
  ext p
  constructor
  · intro hp
    by_cases hodd : Odd p.2
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact (Finset.mem_filter.mp hpOdd).1
    · exact (Finset.mem_filter.mp hpEven).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimePairs_eq_rowThreeSix_union_residual :
    PeriodicMainZeroDyadicExceptionNonCoprimePairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs := by
  ext p
  constructor
  · intro hp
    by_cases hrow : p.1 = 3 ∨ p.1 = 6
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hrow⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hrow⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpRow | hpResidual
    · exact (Finset.mem_filter.mp hpRow).1
    · exact (Finset.mem_filter.mp hpResidual).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs_eq_rowThree_union_rowSix :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpNonCop, hpRow⟩
    rcases hpRow with hpThree | hpSix
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hpNonCop, hpThree⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hpNonCop, hpSix⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpThree | hpSix
    · rcases Finset.mem_filter.mp hpThree with ⟨hpNonCop, hpThree'⟩
      exact Finset.mem_filter.mpr ⟨hpNonCop, Or.inl hpThree'⟩
    · rcases Finset.mem_filter.mp hpSix with ⟨hpNonCop, hpSix'⟩
      exact Finset.mem_filter.mpr ⟨hpNonCop, Or.inr hpSix'⟩

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs_eq_rightOdd_union_rightEven :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs := by
  ext p
  constructor
  · intro hp
    by_cases hodd : Odd p.2
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact (Finset.mem_filter.mp hpOdd).1
    · exact (Finset.mem_filter.mp hpEven).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs_eq_rightOdd_union_rightEven :
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs := by
  ext p
  constructor
  · intro hp
    by_cases hodd : Odd p.2
    · exact Finset.mem_union.mpr (Or.inl <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
    · exact Finset.mem_union.mpr (Or.inr <| Finset.mem_filter.mpr ⟨hp, hodd⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact (Finset.mem_filter.mp hpOdd).1
    · exact (Finset.mem_filter.mp hpEven).1

private theorem PeriodicMainFullBlockOrderedPairSupportExplicit_left_pos
    {p : ℕ × ℕ} (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit) :
    0 < p.1 := by
  rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit] at hp
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hp).1
  have hpLeft : p.1 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).1
  have hpIcc : p.1 ∈ Finset.Icc (1 : ℕ) ((H + 1) / 2) :=
    (Finset.mem_filter.mp hpLeft).1
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpIcc).1

private theorem PeriodicMainFullBlockOrderedPairSupportExplicit_right_pos
    {p : ℕ × ℕ} (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit) :
    0 < p.2 := by
  rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit] at hp
  have hpProd :
      p ∈ PeriodicMainActiveSupportSquarefreeExplicit ×ˢ
        PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_filter.mp hp).1
  have hpRight : p.2 ∈ PeriodicMainActiveSupportSquarefreeExplicit :=
    (Finset.mem_product.mp hpProd).2
  have hpIcc : p.2 ∈ Finset.Icc (1 : ℕ) ((H + 1) / 2) :=
    (Finset.mem_filter.mp hpRight).1
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpIcc).1

theorem PeriodicMainZeroDyadicExceptionUnitTwoPairs_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionUnitTwoPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpDyadic, hunit⟩
  have hpFull : p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit :=
    by
      rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
      exact PeriodicMainZeroDyadicExceptionPairs_subset_fullBlockSquarefreeExplicit hpDyadic
  rcases hunit with hp1 | hp2 | hp1r | hp2r
  · exact surrogatePeriodicMainActiveOrderedPairSummandRat_one_left_zero
      X0 p hp1 (PeriodicMainFullBlockOrderedPairSupportExplicit_right_pos hpFull)
  · exact surrogatePeriodicMainActiveOrderedPairSummandRat_two_left_zero
      X0 p hp2 (PeriodicMainFullBlockOrderedPairSupportExplicit_right_pos hpFull)
  · exact surrogatePeriodicMainActiveOrderedPairSummandRat_one_right_zero
      X0 p hp1r (PeriodicMainFullBlockOrderedPairSupportExplicit_left_pos hpFull)
  · exact surrogatePeriodicMainActiveOrderedPairSummandRat_two_right_zero
      X0 p hp2r (PeriodicMainFullBlockOrderedPairSupportExplicit_left_pos hpFull)

structure PeriodicMainDyadicExceptionSplitZeroCertificateAtX0 : Prop where
  coprime_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainDyadicExceptionZeroCertificateAtX0_of_split
    (cert : PeriodicMainDyadicExceptionSplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionZeroCertificateAtX0 := by
  refine ⟨?_⟩
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionPairs_eq_unitTwo_union_coprime_union_nonCoprime] at hp
  rcases Finset.mem_union.mp hp with hpLeft | hpNonCop
  · rcases Finset.mem_union.mp hpLeft with hpUnit | hpCop
    · exact PeriodicMainZeroDyadicExceptionUnitTwoPairs_value_on_records p hpUnit
    · exact cert.coprime_value_on_records p hpCop
  · exact cert.nonCoprime_value_on_records p hpNonCop

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicExceptionSplit
    (cert : PeriodicMainDyadicExceptionSplitZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicException
    (PeriodicMainDyadicExceptionZeroCertificateAtX0_of_split cert)

structure PeriodicMainDyadicExceptionRowSplitZeroCertificateAtX0 : Prop where
  coprime_rowThreeSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  coprime_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowThreeSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainDyadicExceptionSplitZeroCertificateAtX0_of_rowSplit
    (cert : PeriodicMainDyadicExceptionRowSplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionSplitZeroCertificateAtX0 := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionCoprimePairs_eq_rowThreeSix_union_residual] at hp
    rcases Finset.mem_union.mp hp with hpRow | hpResidual
    · exact cert.coprime_rowThreeSix_value_on_records p hpRow
    · exact cert.coprime_residual_value_on_records p hpResidual
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionNonCoprimePairs_eq_rowThreeSix_union_residual] at hp
    rcases Finset.mem_union.mp hp with hpRow | hpResidual
    · exact cert.nonCoprime_rowThreeSix_value_on_records p hpRow
    · exact cert.nonCoprime_residual_value_on_records p hpResidual

theorem PeriodicMainDyadicExceptionZeroCertificateAtX0_of_rowSplit
    (cert : PeriodicMainDyadicExceptionRowSplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionZeroCertificateAtX0 :=
  PeriodicMainDyadicExceptionZeroCertificateAtX0_of_split
    (PeriodicMainDyadicExceptionSplitZeroCertificateAtX0_of_rowSplit cert)

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicExceptionRowSplit
    (cert : PeriodicMainDyadicExceptionRowSplitZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicException
    (PeriodicMainDyadicExceptionZeroCertificateAtX0_of_rowSplit cert)

structure PeriodicMainDyadicExceptionFineSplitZeroCertificateAtX0 : Prop where
  coprime_rowThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  coprime_rowSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  coprime_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowSix_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainDyadicExceptionRowSplitZeroCertificateAtX0_of_fineSplit
    (cert : PeriodicMainDyadicExceptionFineSplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionRowSplitZeroCertificateAtX0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionCoprimeRowThreeSixPairs_eq_rowThree_union_rowSix] at hp
    rcases Finset.mem_union.mp hp with hpThree | hpSix
    · exact cert.coprime_rowThree_value_on_records p hpThree
    · exact cert.coprime_rowSix_value_on_records p hpSix
  · exact cert.coprime_residual_value_on_records
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeSixPairs_eq_rowThree_union_rowSix] at hp
    rcases Finset.mem_union.mp hp with hpThree | hpSix
    · exact cert.nonCoprime_rowThree_value_on_records p hpThree
    · exact cert.nonCoprime_rowSix_value_on_records p hpSix
  · exact cert.nonCoprime_residual_value_on_records

theorem PeriodicMainDyadicExceptionZeroCertificateAtX0_of_fineSplit
    (cert : PeriodicMainDyadicExceptionFineSplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionZeroCertificateAtX0 :=
  PeriodicMainDyadicExceptionZeroCertificateAtX0_of_rowSplit
    (PeriodicMainDyadicExceptionRowSplitZeroCertificateAtX0_of_fineSplit cert)

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicExceptionFineSplit
    (cert : PeriodicMainDyadicExceptionFineSplitZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicException
    (PeriodicMainDyadicExceptionZeroCertificateAtX0_of_fineSplit cert)

structure PeriodicMainDyadicExceptionParitySplitZeroCertificateAtX0 : Prop where
  coprime_rowThree_rightOdd_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  coprime_rowThree_rightEven_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowThreeRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  coprime_rowSix_rightOdd_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowSixRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  coprime_rowSix_rightEven_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeRowSixRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  coprime_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionCoprimeResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowThree_rightOdd_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowThree_rightEven_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowSix_rightOdd_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightOddPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_rowSix_rightEven_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprime_residual_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainDyadicExceptionFineSplitZeroCertificateAtX0_of_paritySplit
    (cert : PeriodicMainDyadicExceptionParitySplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionFineSplitZeroCertificateAtX0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionCoprimeRowThreePairs_eq_rightOdd_union_rightEven] at hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact cert.coprime_rowThree_rightOdd_value_on_records p hpOdd
    · exact cert.coprime_rowThree_rightEven_value_on_records p hpEven
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionCoprimeRowSixPairs_eq_rightOdd_union_rightEven] at hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact cert.coprime_rowSix_rightOdd_value_on_records p hpOdd
    · exact cert.coprime_rowSix_rightEven_value_on_records p hpEven
  · exact cert.coprime_residual_value_on_records
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionNonCoprimeRowThreePairs_eq_rightOdd_union_rightEven] at hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact cert.nonCoprime_rowThree_rightOdd_value_on_records p hpOdd
    · exact cert.nonCoprime_rowThree_rightEven_value_on_records p hpEven
  · intro p hp
    rw [PeriodicMainZeroDyadicExceptionNonCoprimeRowSixPairs_eq_rightOdd_union_rightEven] at hp
    rcases Finset.mem_union.mp hp with hpOdd | hpEven
    · exact cert.nonCoprime_rowSix_rightOdd_value_on_records p hpOdd
    · exact cert.nonCoprime_rowSix_rightEven_value_on_records p hpEven
  · exact cert.nonCoprime_residual_value_on_records

theorem PeriodicMainDyadicExceptionZeroCertificateAtX0_of_paritySplit
    (cert : PeriodicMainDyadicExceptionParitySplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionZeroCertificateAtX0 :=
  PeriodicMainDyadicExceptionZeroCertificateAtX0_of_fineSplit
    (PeriodicMainDyadicExceptionFineSplitZeroCertificateAtX0_of_paritySplit cert)

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicExceptionParitySplit
    (cert : PeriodicMainDyadicExceptionParitySplitZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_dyadicException
    (PeriodicMainDyadicExceptionZeroCertificateAtX0_of_paritySplit cert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
