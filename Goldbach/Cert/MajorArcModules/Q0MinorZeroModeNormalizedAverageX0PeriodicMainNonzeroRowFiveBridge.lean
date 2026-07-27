import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainNonzeroRowFiveSurface

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Bridge from the completed q=5 row-slice payload to the nonzero sparse
periodic-main certificate surface.

This isolates the q=5 contribution on the canonical nonzero surface. The row
is represented by the local nonzero coverage chunks where q=5 occurs, rather
than by a global intersection against all nonzero records.
-/

theorem PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero :
    PeriodicMainNonzeroRecordPairsGroup000 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  simp [PeriodicMainNonzeroRecordPairs, PeriodicMainNonzeroRecordPairsUpTo012,
    PeriodicMainNonzeroRecordPairsUpTo011, PeriodicMainNonzeroRecordPairsUpTo010,
    PeriodicMainNonzeroRecordPairsUpTo009, PeriodicMainNonzeroRecordPairsUpTo008,
    PeriodicMainNonzeroRecordPairsUpTo007, PeriodicMainNonzeroRecordPairsUpTo006,
    PeriodicMainNonzeroRecordPairsUpTo005, PeriodicMainNonzeroRecordPairsUpTo004,
    PeriodicMainNonzeroRecordPairsUpTo003, PeriodicMainNonzeroRecordPairsUpTo002,
    PeriodicMainNonzeroRecordPairsUpTo001, PeriodicMainNonzeroRecordPairsUpTo000,
    hp]

theorem PeriodicMainNonzeroRecordPairsChunk000_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk000 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk001_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk001 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk002_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk002 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk003_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk003 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk004_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk004 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk005_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk005 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk006_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk006 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk007_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk007 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk008_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk008 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsChunk009_subset_nonzero :
    PeriodicMainNonzeroRecordPairsChunk009 ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  apply PeriodicMainNonzeroRecordPairsGroup000_subset_nonzero
  simp [PeriodicMainNonzeroRecordPairsGroup000,
    PeriodicMainNonzeroRecordPairsGroup000UpTo024,
    PeriodicMainNonzeroRecordPairsGroup000UpTo023,
    PeriodicMainNonzeroRecordPairsGroup000UpTo022,
    PeriodicMainNonzeroRecordPairsGroup000UpTo021,
    PeriodicMainNonzeroRecordPairsGroup000UpTo020,
    PeriodicMainNonzeroRecordPairsGroup000UpTo019,
    PeriodicMainNonzeroRecordPairsGroup000UpTo018,
    PeriodicMainNonzeroRecordPairsGroup000UpTo017,
    PeriodicMainNonzeroRecordPairsGroup000UpTo016,
    PeriodicMainNonzeroRecordPairsGroup000UpTo015,
    PeriodicMainNonzeroRecordPairsGroup000UpTo014,
    PeriodicMainNonzeroRecordPairsGroup000UpTo013,
    PeriodicMainNonzeroRecordPairsGroup000UpTo012,
    PeriodicMainNonzeroRecordPairsGroup000UpTo011,
    PeriodicMainNonzeroRecordPairsGroup000UpTo010,
    PeriodicMainNonzeroRecordPairsGroup000UpTo009,
    PeriodicMainNonzeroRecordPairsGroup000UpTo008,
    PeriodicMainNonzeroRecordPairsGroup000UpTo007,
    PeriodicMainNonzeroRecordPairsGroup000UpTo006,
    PeriodicMainNonzeroRecordPairsGroup000UpTo005,
    PeriodicMainNonzeroRecordPairsGroup000UpTo004,
    PeriodicMainNonzeroRecordPairsGroup000UpTo003,
    PeriodicMainNonzeroRecordPairsGroup000UpTo002,
    PeriodicMainNonzeroRecordPairsGroup000UpTo001,
    PeriodicMainNonzeroRecordPairsGroup000UpTo000, hp]

theorem PeriodicMainNonzeroRecordPairsRowFive_subset_nonzero :
    PeriodicMainNonzeroRecordPairsRowFive ⊆ PeriodicMainNonzeroRecordPairs := by
  intro p hp
  simp [PeriodicMainNonzeroRecordPairsRowFive] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · exact PeriodicMainNonzeroRecordPairsChunk000_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk001_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk002_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk003_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk004_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk005_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk006_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk007_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk008_subset_nonzero hp.1
  · exact PeriodicMainNonzeroRecordPairsChunk009_subset_nonzero hp.1

theorem PeriodicMainNonzeroRecordPairsRowFive_disjoint_withoutRowFive :
    Disjoint PeriodicMainNonzeroRecordPairsRowFive
      PeriodicMainNonzeroRecordPairsWithoutRowFive := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp_left hp_right
  exact (Finset.mem_sdiff.mp hp_right).2 hp_left

theorem PeriodicMainNonzeroRecordPairsRowFive_union_withoutRowFive_eq_nonzero :
    PeriodicMainNonzeroRecordPairsRowFive ∪
        PeriodicMainNonzeroRecordPairsWithoutRowFive =
      PeriodicMainNonzeroRecordPairs := by
  simpa [PeriodicMainNonzeroRecordPairsWithoutRowFive] using
    Finset.union_sdiff_of_subset PeriodicMainNonzeroRecordPairsRowFive_subset_nonzero

theorem PeriodicMainNonzeroRecordPairs_sum_eq_rowFive_add_withoutRowFive
    (f : ℕ × ℕ → ℚ) :
    (∑ p ∈ PeriodicMainNonzeroRecordPairs, f p) =
      (∑ p ∈ PeriodicMainNonzeroRecordPairsRowFive, f p)
        + (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFive, f p) := by
  rw [← PeriodicMainNonzeroRecordPairsRowFive_union_withoutRowFive_eq_nonzero]
  rw [Finset.sum_union
    PeriodicMainNonzeroRecordPairsRowFive_disjoint_withoutRowFive]

theorem PeriodicMainNonzeroRecordPairs_sum_eq_cert_of_rowFiveAndWithoutRowFiveSum
    {rowFiveTotal : ℚ}
    (hrow :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsRowFive,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) =
        rowFiveTotal)
    (hrest :
      (∑ p ∈ PeriodicMainNonzeroRecordPairsWithoutRowFive,
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
        + rowFiveTotal =
          surrogatePeriodicMainX0RatCert) :
    (∑ p ∈ PeriodicMainNonzeroRecordPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
        = surrogatePeriodicMainX0RatCert := by
  rw [PeriodicMainNonzeroRecordPairs_sum_eq_rowFive_add_withoutRowFive]
  rw [hrow]
  rw [add_comm]
  exact hrest

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
