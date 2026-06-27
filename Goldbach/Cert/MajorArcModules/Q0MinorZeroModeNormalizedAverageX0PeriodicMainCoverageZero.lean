import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroGroup007

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record light union assembly facts for PeriodicMainZeroRecordPairs. -/

def PeriodicMainZeroRecordPairsUpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup000

theorem PeriodicMainZeroRecordPairsUpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsUpTo000] using PeriodicMainZeroRecordPairsGroup000_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsUpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsUpTo000 ∪ PeriodicMainZeroRecordPairsGroup001

theorem PeriodicMainZeroRecordPairsUpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsUpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsUpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsGroup001_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsUpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsUpTo001 ∪ PeriodicMainZeroRecordPairsGroup002

theorem PeriodicMainZeroRecordPairsUpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsUpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsUpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsGroup002_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsUpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsUpTo002 ∪ PeriodicMainZeroRecordPairsGroup003

theorem PeriodicMainZeroRecordPairsUpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsUpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsUpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsGroup003_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsUpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsUpTo003 ∪ PeriodicMainZeroRecordPairsGroup004

theorem PeriodicMainZeroRecordPairsUpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsUpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsUpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsGroup004_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsUpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsUpTo004 ∪ PeriodicMainZeroRecordPairsGroup005

theorem PeriodicMainZeroRecordPairsUpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsUpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsUpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsGroup005_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsUpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsUpTo005 ∪ PeriodicMainZeroRecordPairsGroup006

theorem PeriodicMainZeroRecordPairsUpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsUpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsUpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsGroup006_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsUpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsUpTo006 ∪ PeriodicMainZeroRecordPairsGroup007

theorem PeriodicMainZeroRecordPairsUpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsUpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsUpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsUpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsGroup007_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairs : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsUpTo007

theorem PeriodicMainZeroRecordPairs_card :
    PeriodicMainZeroRecordPairs.card = 18870 := by
  native_decide

theorem PeriodicMainZeroRecordPairs_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairs ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairs] using PeriodicMainZeroRecordPairsUpTo007_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
