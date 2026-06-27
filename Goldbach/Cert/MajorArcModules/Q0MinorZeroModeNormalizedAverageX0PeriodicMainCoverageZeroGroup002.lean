import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk050
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk051
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk052
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk053
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk054
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk055
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk056
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk057
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk058
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk059
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk060
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk061
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk062
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk063
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk064
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk065
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk066
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk067
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk068
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk069
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk070
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk071
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk072
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk073
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk074

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup002. -/

def PeriodicMainZeroRecordPairsGroup002UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk050

theorem PeriodicMainZeroRecordPairsGroup002UpTo000_card :
    PeriodicMainZeroRecordPairsGroup002UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup002UpTo000] using PeriodicMainZeroRecordPairsChunk050_card

theorem PeriodicMainZeroRecordPairsGroup002UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup002UpTo000] using PeriodicMainZeroRecordPairsChunk050_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup002UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo000 ∪ PeriodicMainZeroRecordPairsChunk051

theorem PeriodicMainZeroRecordPairsGroup002UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk051 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo000 PeriodicMainZeroRecordPairsChunk051 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo001_card :
    PeriodicMainZeroRecordPairsGroup002UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk051]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo000_card, PeriodicMainZeroRecordPairsChunk051_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk051_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo001 ∪ PeriodicMainZeroRecordPairsChunk052

theorem PeriodicMainZeroRecordPairsGroup002UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk052 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo001 PeriodicMainZeroRecordPairsChunk052 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo002_card :
    PeriodicMainZeroRecordPairsGroup002UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk052]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo001_card, PeriodicMainZeroRecordPairsChunk052_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk052_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo002 ∪ PeriodicMainZeroRecordPairsChunk053

theorem PeriodicMainZeroRecordPairsGroup002UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk053 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo002 PeriodicMainZeroRecordPairsChunk053 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo003_card :
    PeriodicMainZeroRecordPairsGroup002UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk053]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo002_card, PeriodicMainZeroRecordPairsChunk053_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk053_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo003 ∪ PeriodicMainZeroRecordPairsChunk054

theorem PeriodicMainZeroRecordPairsGroup002UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk054 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo003 PeriodicMainZeroRecordPairsChunk054 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo004_card :
    PeriodicMainZeroRecordPairsGroup002UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk054]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo003_card, PeriodicMainZeroRecordPairsChunk054_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk054_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo004 ∪ PeriodicMainZeroRecordPairsChunk055

theorem PeriodicMainZeroRecordPairsGroup002UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk055 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo004 PeriodicMainZeroRecordPairsChunk055 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo005_card :
    PeriodicMainZeroRecordPairsGroup002UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk055]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo004_card, PeriodicMainZeroRecordPairsChunk055_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk055_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo005 ∪ PeriodicMainZeroRecordPairsChunk056

theorem PeriodicMainZeroRecordPairsGroup002UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk056 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo005 PeriodicMainZeroRecordPairsChunk056 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo006_card :
    PeriodicMainZeroRecordPairsGroup002UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk056]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo005_card, PeriodicMainZeroRecordPairsChunk056_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk056_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo006 ∪ PeriodicMainZeroRecordPairsChunk057

theorem PeriodicMainZeroRecordPairsGroup002UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk057 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo006 PeriodicMainZeroRecordPairsChunk057 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo007_card :
    PeriodicMainZeroRecordPairsGroup002UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk057]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo006_card, PeriodicMainZeroRecordPairsChunk057_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk057_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo007 ∪ PeriodicMainZeroRecordPairsChunk058

theorem PeriodicMainZeroRecordPairsGroup002UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk058 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo007 PeriodicMainZeroRecordPairsChunk058 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo008_card :
    PeriodicMainZeroRecordPairsGroup002UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk058]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo007_card, PeriodicMainZeroRecordPairsChunk058_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk058_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo008 ∪ PeriodicMainZeroRecordPairsChunk059

theorem PeriodicMainZeroRecordPairsGroup002UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk059 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo008 PeriodicMainZeroRecordPairsChunk059 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo009_card :
    PeriodicMainZeroRecordPairsGroup002UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk059]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo008_card, PeriodicMainZeroRecordPairsChunk059_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk059_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo009 ∪ PeriodicMainZeroRecordPairsChunk060

theorem PeriodicMainZeroRecordPairsGroup002UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk060 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo009 PeriodicMainZeroRecordPairsChunk060 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo010_card :
    PeriodicMainZeroRecordPairsGroup002UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk060]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo009_card, PeriodicMainZeroRecordPairsChunk060_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk060_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo010 ∪ PeriodicMainZeroRecordPairsChunk061

theorem PeriodicMainZeroRecordPairsGroup002UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk061 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo010 PeriodicMainZeroRecordPairsChunk061 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo011_card :
    PeriodicMainZeroRecordPairsGroup002UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk061]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo010_card, PeriodicMainZeroRecordPairsChunk061_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk061_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo011 ∪ PeriodicMainZeroRecordPairsChunk062

theorem PeriodicMainZeroRecordPairsGroup002UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk062 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo011 PeriodicMainZeroRecordPairsChunk062 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo012_card :
    PeriodicMainZeroRecordPairsGroup002UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk062]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo011_card, PeriodicMainZeroRecordPairsChunk062_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk062_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo012 ∪ PeriodicMainZeroRecordPairsChunk063

theorem PeriodicMainZeroRecordPairsGroup002UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk063 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo012 PeriodicMainZeroRecordPairsChunk063 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo013_card :
    PeriodicMainZeroRecordPairsGroup002UpTo013.card = 1400 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk063]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo012_card, PeriodicMainZeroRecordPairsChunk063_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk063_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo014 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo013 ∪ PeriodicMainZeroRecordPairsChunk064

theorem PeriodicMainZeroRecordPairsGroup002UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk064 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo013 PeriodicMainZeroRecordPairsChunk064 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo014_card :
    PeriodicMainZeroRecordPairsGroup002UpTo014.card = 1500 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo014, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk064]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo013_card, PeriodicMainZeroRecordPairsChunk064_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo014_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo014 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo013_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk064_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo015 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo014 ∪ PeriodicMainZeroRecordPairsChunk065

theorem PeriodicMainZeroRecordPairsGroup002UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk065 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo014 PeriodicMainZeroRecordPairsChunk065 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo015_card :
    PeriodicMainZeroRecordPairsGroup002UpTo015.card = 1600 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo015, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk065]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo014_card, PeriodicMainZeroRecordPairsChunk065_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo015_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo015 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo014_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk065_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo016 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo015 ∪ PeriodicMainZeroRecordPairsChunk066

theorem PeriodicMainZeroRecordPairsGroup002UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk066 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo015 PeriodicMainZeroRecordPairsChunk066 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo016_card :
    PeriodicMainZeroRecordPairsGroup002UpTo016.card = 1700 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo016, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk066]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo015_card, PeriodicMainZeroRecordPairsChunk066_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo016_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo016 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo015_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk066_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo017 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo016 ∪ PeriodicMainZeroRecordPairsChunk067

theorem PeriodicMainZeroRecordPairsGroup002UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk067 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo016 PeriodicMainZeroRecordPairsChunk067 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo017_card :
    PeriodicMainZeroRecordPairsGroup002UpTo017.card = 1800 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo017, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk067]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo016_card, PeriodicMainZeroRecordPairsChunk067_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo017_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo017 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo016_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk067_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo018 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo017 ∪ PeriodicMainZeroRecordPairsChunk068

theorem PeriodicMainZeroRecordPairsGroup002UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk068 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo017 PeriodicMainZeroRecordPairsChunk068 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo018_card :
    PeriodicMainZeroRecordPairsGroup002UpTo018.card = 1900 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo018, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk068]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo017_card, PeriodicMainZeroRecordPairsChunk068_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo018_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo018 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo017_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk068_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo019 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo018 ∪ PeriodicMainZeroRecordPairsChunk069

theorem PeriodicMainZeroRecordPairsGroup002UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk069 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo018 PeriodicMainZeroRecordPairsChunk069 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo019_card :
    PeriodicMainZeroRecordPairsGroup002UpTo019.card = 2000 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo019, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk069]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo018_card, PeriodicMainZeroRecordPairsChunk069_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo019_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo019 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo018_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk069_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo020 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo019 ∪ PeriodicMainZeroRecordPairsChunk070

theorem PeriodicMainZeroRecordPairsGroup002UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk070 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo019 PeriodicMainZeroRecordPairsChunk070 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo020_card :
    PeriodicMainZeroRecordPairsGroup002UpTo020.card = 2100 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo020, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk070]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo019_card, PeriodicMainZeroRecordPairsChunk070_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo020_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo020 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo020] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo019_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk070_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo021 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo020 ∪ PeriodicMainZeroRecordPairsChunk071

theorem PeriodicMainZeroRecordPairsGroup002UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk071 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo020 PeriodicMainZeroRecordPairsChunk071 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo021_card :
    PeriodicMainZeroRecordPairsGroup002UpTo021.card = 2200 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo021, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk071]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo020_card, PeriodicMainZeroRecordPairsChunk071_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo021_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo021 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo021] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo020_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk071_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo022 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo021 ∪ PeriodicMainZeroRecordPairsChunk072

theorem PeriodicMainZeroRecordPairsGroup002UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk072 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo021 PeriodicMainZeroRecordPairsChunk072 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo022_card :
    PeriodicMainZeroRecordPairsGroup002UpTo022.card = 2300 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo022, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk072]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo021_card, PeriodicMainZeroRecordPairsChunk072_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo022_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo022 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo022] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo021_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk072_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo023 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo022 ∪ PeriodicMainZeroRecordPairsChunk073

theorem PeriodicMainZeroRecordPairsGroup002UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk073 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo022 PeriodicMainZeroRecordPairsChunk073 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo023_card :
    PeriodicMainZeroRecordPairsGroup002UpTo023.card = 2400 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo023, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk073]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo022_card, PeriodicMainZeroRecordPairsChunk073_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo023_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo023 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo023] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo022_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk073_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002UpTo024 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup002UpTo023 ∪ PeriodicMainZeroRecordPairsChunk074

theorem PeriodicMainZeroRecordPairsGroup002UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk074 :
    Disjoint PeriodicMainZeroRecordPairsGroup002UpTo023 PeriodicMainZeroRecordPairsChunk074 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup002UpTo024_card :
    PeriodicMainZeroRecordPairsGroup002UpTo024.card = 2500 := by
  rw [PeriodicMainZeroRecordPairsGroup002UpTo024, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup002UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk074]
  norm_num [PeriodicMainZeroRecordPairsGroup002UpTo023_card, PeriodicMainZeroRecordPairsChunk074_card]

theorem PeriodicMainZeroRecordPairsGroup002UpTo024_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002UpTo024 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup002UpTo024] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup002UpTo023_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk074_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup002 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup002UpTo024

theorem PeriodicMainZeroRecordPairsGroup002_card :
    PeriodicMainZeroRecordPairsGroup002.card = 2500 := by
  simpa [PeriodicMainZeroRecordPairsGroup002] using PeriodicMainZeroRecordPairsGroup002UpTo024_card

theorem PeriodicMainZeroRecordPairsGroup002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup002] using PeriodicMainZeroRecordPairsGroup002UpTo024_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
