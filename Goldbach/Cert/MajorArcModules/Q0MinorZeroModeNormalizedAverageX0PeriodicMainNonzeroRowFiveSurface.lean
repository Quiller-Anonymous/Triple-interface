import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverage

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Lightweight set surface for isolating the q=5 row on the canonical nonzero
periodic-main record set. This intentionally avoids importing the generated
q=5 value payload.
-/

def PeriodicMainNonzeroRecordPairsRowFive : Finset (ℕ × ℕ) :=
  (PeriodicMainNonzeroRecordPairsChunk000.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk001.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk002.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk003.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk004.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk005.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk006.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk007.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk008.filter (fun p => p.1 = 5)) ∪
    (PeriodicMainNonzeroRecordPairsChunk009.filter (fun p => p.1 = 5))

def PeriodicMainNonzeroRecordPairsWithoutRowFive : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairs \ PeriodicMainNonzeroRecordPairsRowFive

theorem PeriodicMainNonzeroRecordPairsChunk001_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk001 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk002_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk002 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk003_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk003 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk004_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk004 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk005_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk005 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk006_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk006 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk007_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk007 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk008_subset_rowFive :
    PeriodicMainNonzeroRecordPairsChunk008 ⊆ PeriodicMainNonzeroRecordPairsRowFive := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk000_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk000.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hp))))))))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk001_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk001.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk002_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk002.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk003_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk003.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk004_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk004.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp)))))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk005_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk005.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hp))))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk006_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk006.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inr hp)))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk007_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk007.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hp))

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk008_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk008.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inl (Or.inr hp)

theorem PeriodicMainNonzeroRecordPairsRowFive_of_mem_chunk009_filter
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsChunk009.filter (fun p : ℕ × ℕ => p.1 = 5)) :
    p ∈ PeriodicMainNonzeroRecordPairsRowFive := by
  simp only [PeriodicMainNonzeroRecordPairsRowFive, Finset.mem_union]
  exact Or.inr hp

theorem PeriodicMainNonzeroRecordPairsRowFive_left_eq_five
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainNonzeroRecordPairsRowFive) :
    p.1 = 5 := by
  unfold PeriodicMainNonzeroRecordPairsRowFive at hp
  rcases Finset.mem_union.mp hp with hp | h9
  · rcases Finset.mem_union.mp hp with hp | h8
    · rcases Finset.mem_union.mp hp with hp | h7
      · rcases Finset.mem_union.mp hp with hp | h6
        · rcases Finset.mem_union.mp hp with hp | h5
          · rcases Finset.mem_union.mp hp with hp | h4
            · rcases Finset.mem_union.mp hp with hp | h3
              · rcases Finset.mem_union.mp hp with hp | h2
                · rcases Finset.mem_union.mp hp with h0 | h1
                  · exact (Finset.mem_filter.mp h0).2
                  · exact (Finset.mem_filter.mp h1).2
                · exact (Finset.mem_filter.mp h2).2
              · exact (Finset.mem_filter.mp h3).2
            · exact (Finset.mem_filter.mp h4).2
          · exact (Finset.mem_filter.mp h5).2
        · exact (Finset.mem_filter.mp h6).2
      · exact (Finset.mem_filter.mp h7).2
    · exact (Finset.mem_filter.mp h8).2
  · exact (Finset.mem_filter.mp h9).2

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
