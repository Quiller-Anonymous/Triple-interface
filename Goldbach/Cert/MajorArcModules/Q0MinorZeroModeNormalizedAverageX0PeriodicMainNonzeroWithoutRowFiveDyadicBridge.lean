import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroRowFiveSurface

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Dyadic split of the nonzero periodic-main complement after removing the q=5
row. The data report shows that the dyadic records `(q, 2q)` and `(2q, q)`
carry essentially all of this complement; this bridge makes that the next
certificate surface.
-/

def PeriodicMainNonzeroRecordPairsWithoutRowFiveDyadic : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsWithoutRowFive.filter
    (fun p => p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)

def PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsWithoutRowFive.filter
    (fun p => ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2))

theorem PeriodicMainNonzeroRecordPairsWithoutRowFive_eq_dyadic_union_nondyadic :
    PeriodicMainNonzeroRecordPairsWithoutRowFive =
      PeriodicMainNonzeroRecordPairsWithoutRowFiveDyadic ∪
        PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic := by
  ext p
  constructor
  · intro hp
    by_cases hd : p.2 = 2 * p.1 ∨ p.1 = 2 * p.2
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hp, hd⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hp, hd⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hpdy | hpnon
    · exact (Finset.mem_filter.mp hpdy).1
    · exact (Finset.mem_filter.mp hpnon).1

theorem PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic_mem_of_mem_nonzero
    {p : ℕ × ℕ}
    (hpNonzero : p ∈ PeriodicMainNonzeroRecordPairs)
    (hleft : p.1 ≠ 5)
    (hnotdyadic : ¬ (p.2 = 2 * p.1 ∨ p.1 = 2 * p.2)) :
    p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic := by
  unfold PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic
  exact Finset.mem_filter.mpr ⟨by
    unfold PeriodicMainNonzeroRecordPairsWithoutRowFive
    exact Finset.mem_sdiff.mpr ⟨hpNonzero, by
      intro hpRow
      exact hleft (PeriodicMainNonzeroRecordPairsRowFive_left_eq_five hpRow)⟩,
    hnotdyadic⟩

theorem PeriodicMainNonzeroRecordPairsWithoutRowFive_dyadic_disjoint_nondyadic :
    Disjoint PeriodicMainNonzeroRecordPairsWithoutRowFiveDyadic
      PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic := by
  rw [Finset.disjoint_left]
  intro p hpdy hpnon
  exact (Finset.mem_filter.mp hpnon).2 (Finset.mem_filter.mp hpdy).2

theorem PeriodicMainNonzeroRecordPairsWithoutRowFive_actual_sum_of_dyadic_and_nondyadic
    {dyadicTotal nondyadicTotal : ℚ}
    (hdyadic :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveDyadic,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
          dyadicTotal)
    (hnondyadic :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
          nondyadicTotal) :
    (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFive,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
        dyadicTotal + nondyadicTotal := by
  rw [PeriodicMainNonzeroRecordPairsWithoutRowFive_eq_dyadic_union_nondyadic]
  rw [Finset.sum_union
    PeriodicMainNonzeroRecordPairsWithoutRowFive_dyadic_disjoint_nondyadic]
  rw [hdyadic, hnondyadic]

theorem PeriodicMainNonzeroRecordPairsWithoutRowFive_plus_rowFive_eq_cert_of_dyadic_and_nondyadic
    {dyadicTotal nondyadicTotal rowFiveTotal certTotal : ℚ}
    (hdyadic :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveDyadic,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
          dyadicTotal)
    (hnondyadic :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFiveNonDyadic,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
          nondyadicTotal)
    (hTotals :
      dyadicTotal + nondyadicTotal + rowFiveTotal = certTotal) :
    (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFive,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) + rowFiveTotal =
        certTotal := by
  rw [PeriodicMainNonzeroRecordPairsWithoutRowFive_actual_sum_of_dyadic_and_nondyadic
    hdyadic hnondyadic]
  simpa [add_assoc] using hTotals

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
