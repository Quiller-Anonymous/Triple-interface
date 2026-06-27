import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageNonzeroGroup012

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record light union assembly facts for PeriodicMainNonzeroRecordPairs. -/

def PeriodicMainNonzeroRecordPairsUpTo000 : Finset (ℕ × ℕ) := PeriodicMainNonzeroRecordPairsGroup000

theorem PeriodicMainNonzeroRecordPairsUpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainNonzeroRecordPairsUpTo000] using PeriodicMainNonzeroRecordPairsGroup000_subset_fullBlockSquarefreeExplicit

def PeriodicMainNonzeroRecordPairsUpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo000 ∪ PeriodicMainNonzeroRecordPairsGroup001

theorem PeriodicMainNonzeroRecordPairsUpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup001_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo001 ∪ PeriodicMainNonzeroRecordPairsGroup002

theorem PeriodicMainNonzeroRecordPairsUpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup002_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo002 ∪ PeriodicMainNonzeroRecordPairsGroup003

theorem PeriodicMainNonzeroRecordPairsUpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup003_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo003 ∪ PeriodicMainNonzeroRecordPairsGroup004

theorem PeriodicMainNonzeroRecordPairsUpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup004_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo004 ∪ PeriodicMainNonzeroRecordPairsGroup005

theorem PeriodicMainNonzeroRecordPairsUpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup005_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo005 ∪ PeriodicMainNonzeroRecordPairsGroup006

theorem PeriodicMainNonzeroRecordPairsUpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup006_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo006 ∪ PeriodicMainNonzeroRecordPairsGroup007

theorem PeriodicMainNonzeroRecordPairsUpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup007_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo007 ∪ PeriodicMainNonzeroRecordPairsGroup008

theorem PeriodicMainNonzeroRecordPairsUpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup008_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo008 ∪ PeriodicMainNonzeroRecordPairsGroup009

theorem PeriodicMainNonzeroRecordPairsUpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup009_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo009 ∪ PeriodicMainNonzeroRecordPairsGroup010

theorem PeriodicMainNonzeroRecordPairsUpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup010_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo010 ∪ PeriodicMainNonzeroRecordPairsGroup011

theorem PeriodicMainNonzeroRecordPairsUpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup011_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairsUpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainNonzeroRecordPairsUpTo011 ∪ PeriodicMainNonzeroRecordPairsGroup012

theorem PeriodicMainNonzeroRecordPairsUpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsUpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainNonzeroRecordPairsUpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonzeroRecordPairsUpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainNonzeroRecordPairsGroup012_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainNonzeroRecordPairs : Finset (ℕ × ℕ) := PeriodicMainNonzeroRecordPairsUpTo012

theorem PeriodicMainNonzeroRecordPairs_card :
    PeriodicMainNonzeroRecordPairs.card = 30658 := by
  native_decide

theorem PeriodicMainNonzeroRecordPairs_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairs ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainNonzeroRecordPairs] using PeriodicMainNonzeroRecordPairsUpTo012_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
