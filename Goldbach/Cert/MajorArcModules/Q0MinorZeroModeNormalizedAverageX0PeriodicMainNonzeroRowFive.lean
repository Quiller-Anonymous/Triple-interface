import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroRowFiveBridge
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceFiveFinal

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
The q=5 row-slice payload contains 1013 row records. The canonical nonzero
surface contains 974 of them; the remaining 39 generated row records have
zero ordered summand. This module removes that zero correction and provides
the row-five intersection sum fact required by the nonzero bridge.
-/

def RowSliceFiveExtraNonzeroComplementPairs : Finset (ℕ × ℕ) :=
  [(5, 1), (5, 2), (5, 3), (5, 6), (5, 21), (5, 42), (5, 51), (5, 102),
    (5, 111), (5, 129), (5, 201), (5, 222), (5, 237), (5, 249), (5, 258),
    (5, 267), (5, 309), (5, 339), (5, 357), (5, 381), (5, 402), (5, 417),
    (5, 453), (5, 474), (5, 498), (5, 534), (5, 618), (5, 633), (5, 678),
    (5, 714), (5, 723), (5, 762), (5, 813), (5, 831), (5, 834), (5, 843),
    (5, 849), (5, 906), (5, 993)].toFinset

theorem RowSliceFiveExtraNonzeroComplementPairs_sum_zero :
    (∑ p ∈ RowSliceFiveExtraNonzeroComplementPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro p hp
  simp [RowSliceFiveExtraNonzeroComplementPairs] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl
  · simpa using RowSliceFivePayload.periodicMainPair_5_1_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_2_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_3_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_6_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_21_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_42_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_51_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_102_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_111_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_129_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_201_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_222_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_237_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_249_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_258_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_267_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_309_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_339_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_357_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_381_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_402_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_417_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_453_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_474_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_498_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_534_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_618_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_633_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_678_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_714_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_723_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_762_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_813_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_831_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_834_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_843_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_849_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_906_X1000000_orderedSummand
  · simpa using RowSliceFivePayload.periodicMainPair_5_993_X1000000_orderedSummand

theorem RowSliceFivePairs_eq_rowFive_union_extraNonzeroComplement :
    RowSliceFivePayload.RowSliceFivePairs =
      PeriodicMainNonzeroRecordPairsRowFive ∪
        RowSliceFiveExtraNonzeroComplementPairs := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsRowFive_disjoint_extraNonzeroComplement :
    Disjoint PeriodicMainNonzeroRecordPairsRowFive
      RowSliceFiveExtraNonzeroComplementPairs := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsRowFive_actual_sum :
    (∑ p ∈ PeriodicMainNonzeroRecordPairsRowFive,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
        RowSliceFivePayload.RowSliceFiveTotal := by
  have hfull := RowSliceFivePayload.rowSliceFive_actual_sum
  rw [RowSliceFivePairs_eq_rowFive_union_extraNonzeroComplement] at hfull
  rw [Finset.sum_union
    PeriodicMainNonzeroRecordPairsRowFive_disjoint_extraNonzeroComplement] at hfull
  rw [RowSliceFiveExtraNonzeroComplementPairs_sum_zero] at hfull
  simpa using hfull

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
