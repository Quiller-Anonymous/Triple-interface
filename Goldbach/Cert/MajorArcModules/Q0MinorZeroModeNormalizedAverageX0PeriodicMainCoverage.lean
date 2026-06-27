import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzero
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZero

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record coverage assembly facts. -/

def PeriodicMainAllRecordPairs : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairs ∪ PeriodicMainZeroRecordPairs

theorem PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs :
    Disjoint PeriodicMainNonzeroRecordPairs PeriodicMainZeroRecordPairs := by
  native_decide

theorem PeriodicMainAllRecordPairs_card :
    PeriodicMainAllRecordPairs.card = 49528 := by
  rw [PeriodicMainAllRecordPairs,
    Finset.card_union_of_disjoint
      PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs]
  norm_num [PeriodicMainNonzeroRecordPairs_card, PeriodicMainZeroRecordPairs_card]

theorem PeriodicMainFullBlockSquarefreeExplicit_card :
    PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit.card = 49528 := by
  native_decide

theorem PeriodicMainAllRecordPairs_subset_fullBlockSquarefreeExplicit :
    PeriodicMainAllRecordPairs ⊆
      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainAllRecordPairs] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairs_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairs_subset_fullBlockSquarefreeExplicit hp

theorem PeriodicMainAllRecordPairs_eq_fullBlockSquarefreeExplicit :
    PeriodicMainAllRecordPairs =
      PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  apply Finset.eq_of_subset_of_card_le
    PeriodicMainAllRecordPairs_subset_fullBlockSquarefreeExplicit
  rw [PeriodicMainAllRecordPairs_card, PeriodicMainFullBlockSquarefreeExplicit_card]

theorem PeriodicMainAllRecordPairs_eq_fullBlockExplicit :
    PeriodicMainAllRecordPairs =
      PeriodicMainFullBlockOrderedPairSupportExplicit := by
  rw [PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact PeriodicMainAllRecordPairs_eq_fullBlockSquarefreeExplicit

theorem PeriodicMainFullBlockExplicit_subset_allRecordPairs :
    PeriodicMainFullBlockOrderedPairSupportExplicit ⊆ PeriodicMainAllRecordPairs := by
  intro p hp
  rw [PeriodicMainAllRecordPairs_eq_fullBlockExplicit]
  exact hp

theorem PeriodicMainAllRecordPairs_subset_fullBlockExplicit :
    PeriodicMainAllRecordPairs ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  rw [PeriodicMainAllRecordPairs_eq_fullBlockExplicit] at hp
  exact hp

theorem PeriodicMainNonzeroRecordPairs_disjoint_zeroRecordPairs :
    Disjoint PeriodicMainNonzeroRecordPairs PeriodicMainZeroRecordPairs := by
  exact PeriodicMainNonzeroRecordPairs_disjoint_PeriodicMainZeroRecordPairs

theorem PeriodicMainFullBlockExplicit_not_nonzero_mem_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit)
    (hnot : p ∉ PeriodicMainNonzeroRecordPairs) :
    p ∈ PeriodicMainZeroRecordPairs := by
  have hpAll : p ∈ PeriodicMainAllRecordPairs := PeriodicMainFullBlockExplicit_subset_allRecordPairs hp
  unfold PeriodicMainAllRecordPairs at hpAll
  exact (Finset.mem_union.mp hpAll).resolve_left hnot

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
