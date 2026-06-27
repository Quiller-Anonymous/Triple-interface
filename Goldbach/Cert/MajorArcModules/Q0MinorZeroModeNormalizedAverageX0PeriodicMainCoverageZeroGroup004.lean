import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk100
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk101
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk102
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk103
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk104
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk105
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk106
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk107
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk108
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk109
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk110
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk111
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk112
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk113
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk114
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk115
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk116
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk117
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk118
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk119
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk120
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk121
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk122
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk123
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk124

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup004. -/

def PeriodicMainZeroRecordPairsGroup004UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk100

theorem PeriodicMainZeroRecordPairsGroup004UpTo000_card :
    PeriodicMainZeroRecordPairsGroup004UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup004UpTo000] using PeriodicMainZeroRecordPairsChunk100_card

theorem PeriodicMainZeroRecordPairsGroup004UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup004UpTo000] using PeriodicMainZeroRecordPairsChunk100_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup004UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo000 ∪ PeriodicMainZeroRecordPairsChunk101

theorem PeriodicMainZeroRecordPairsGroup004UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk101 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo000 PeriodicMainZeroRecordPairsChunk101 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo001_card :
    PeriodicMainZeroRecordPairsGroup004UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk101]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo000_card, PeriodicMainZeroRecordPairsChunk101_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk101_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo001 ∪ PeriodicMainZeroRecordPairsChunk102

theorem PeriodicMainZeroRecordPairsGroup004UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk102 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo001 PeriodicMainZeroRecordPairsChunk102 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo002_card :
    PeriodicMainZeroRecordPairsGroup004UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk102]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo001_card, PeriodicMainZeroRecordPairsChunk102_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk102_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo002 ∪ PeriodicMainZeroRecordPairsChunk103

theorem PeriodicMainZeroRecordPairsGroup004UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk103 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo002 PeriodicMainZeroRecordPairsChunk103 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo003_card :
    PeriodicMainZeroRecordPairsGroup004UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk103]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo002_card, PeriodicMainZeroRecordPairsChunk103_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk103_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo003 ∪ PeriodicMainZeroRecordPairsChunk104

theorem PeriodicMainZeroRecordPairsGroup004UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk104 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo003 PeriodicMainZeroRecordPairsChunk104 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo004_card :
    PeriodicMainZeroRecordPairsGroup004UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk104]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo003_card, PeriodicMainZeroRecordPairsChunk104_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk104_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo004 ∪ PeriodicMainZeroRecordPairsChunk105

theorem PeriodicMainZeroRecordPairsGroup004UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk105 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo004 PeriodicMainZeroRecordPairsChunk105 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo005_card :
    PeriodicMainZeroRecordPairsGroup004UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk105]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo004_card, PeriodicMainZeroRecordPairsChunk105_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk105_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo005 ∪ PeriodicMainZeroRecordPairsChunk106

theorem PeriodicMainZeroRecordPairsGroup004UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk106 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo005 PeriodicMainZeroRecordPairsChunk106 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo006_card :
    PeriodicMainZeroRecordPairsGroup004UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk106]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo005_card, PeriodicMainZeroRecordPairsChunk106_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk106_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo006 ∪ PeriodicMainZeroRecordPairsChunk107

theorem PeriodicMainZeroRecordPairsGroup004UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk107 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo006 PeriodicMainZeroRecordPairsChunk107 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo007_card :
    PeriodicMainZeroRecordPairsGroup004UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk107]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo006_card, PeriodicMainZeroRecordPairsChunk107_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk107_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo007 ∪ PeriodicMainZeroRecordPairsChunk108

theorem PeriodicMainZeroRecordPairsGroup004UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk108 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo007 PeriodicMainZeroRecordPairsChunk108 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo008_card :
    PeriodicMainZeroRecordPairsGroup004UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk108]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo007_card, PeriodicMainZeroRecordPairsChunk108_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk108_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo008 ∪ PeriodicMainZeroRecordPairsChunk109

theorem PeriodicMainZeroRecordPairsGroup004UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk109 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo008 PeriodicMainZeroRecordPairsChunk109 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo009_card :
    PeriodicMainZeroRecordPairsGroup004UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk109]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo008_card, PeriodicMainZeroRecordPairsChunk109_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk109_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo009 ∪ PeriodicMainZeroRecordPairsChunk110

theorem PeriodicMainZeroRecordPairsGroup004UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk110 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo009 PeriodicMainZeroRecordPairsChunk110 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo010_card :
    PeriodicMainZeroRecordPairsGroup004UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk110]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo009_card, PeriodicMainZeroRecordPairsChunk110_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk110_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo010 ∪ PeriodicMainZeroRecordPairsChunk111

theorem PeriodicMainZeroRecordPairsGroup004UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk111 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo010 PeriodicMainZeroRecordPairsChunk111 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo011_card :
    PeriodicMainZeroRecordPairsGroup004UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk111]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo010_card, PeriodicMainZeroRecordPairsChunk111_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk111_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo011 ∪ PeriodicMainZeroRecordPairsChunk112

theorem PeriodicMainZeroRecordPairsGroup004UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk112 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo011 PeriodicMainZeroRecordPairsChunk112 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo012_card :
    PeriodicMainZeroRecordPairsGroup004UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk112]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo011_card, PeriodicMainZeroRecordPairsChunk112_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk112_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo012 ∪ PeriodicMainZeroRecordPairsChunk113

theorem PeriodicMainZeroRecordPairsGroup004UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk113 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo012 PeriodicMainZeroRecordPairsChunk113 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo013_card :
    PeriodicMainZeroRecordPairsGroup004UpTo013.card = 1400 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk113]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo012_card, PeriodicMainZeroRecordPairsChunk113_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk113_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo014 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo013 ∪ PeriodicMainZeroRecordPairsChunk114

theorem PeriodicMainZeroRecordPairsGroup004UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk114 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo013 PeriodicMainZeroRecordPairsChunk114 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo014_card :
    PeriodicMainZeroRecordPairsGroup004UpTo014.card = 1500 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo014, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk114]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo013_card, PeriodicMainZeroRecordPairsChunk114_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo014_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo014 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo013_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk114_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo015 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo014 ∪ PeriodicMainZeroRecordPairsChunk115

theorem PeriodicMainZeroRecordPairsGroup004UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk115 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo014 PeriodicMainZeroRecordPairsChunk115 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo015_card :
    PeriodicMainZeroRecordPairsGroup004UpTo015.card = 1600 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo015, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk115]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo014_card, PeriodicMainZeroRecordPairsChunk115_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo015_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo015 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo014_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk115_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo016 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo015 ∪ PeriodicMainZeroRecordPairsChunk116

theorem PeriodicMainZeroRecordPairsGroup004UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk116 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo015 PeriodicMainZeroRecordPairsChunk116 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo016_card :
    PeriodicMainZeroRecordPairsGroup004UpTo016.card = 1700 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo016, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk116]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo015_card, PeriodicMainZeroRecordPairsChunk116_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo016_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo016 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo015_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk116_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo017 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo016 ∪ PeriodicMainZeroRecordPairsChunk117

theorem PeriodicMainZeroRecordPairsGroup004UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk117 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo016 PeriodicMainZeroRecordPairsChunk117 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo017_card :
    PeriodicMainZeroRecordPairsGroup004UpTo017.card = 1800 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo017, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk117]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo016_card, PeriodicMainZeroRecordPairsChunk117_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo017_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo017 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo016_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk117_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo018 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo017 ∪ PeriodicMainZeroRecordPairsChunk118

theorem PeriodicMainZeroRecordPairsGroup004UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk118 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo017 PeriodicMainZeroRecordPairsChunk118 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo018_card :
    PeriodicMainZeroRecordPairsGroup004UpTo018.card = 1900 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo018, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk118]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo017_card, PeriodicMainZeroRecordPairsChunk118_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo018_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo018 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo017_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk118_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo019 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo018 ∪ PeriodicMainZeroRecordPairsChunk119

theorem PeriodicMainZeroRecordPairsGroup004UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk119 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo018 PeriodicMainZeroRecordPairsChunk119 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo019_card :
    PeriodicMainZeroRecordPairsGroup004UpTo019.card = 2000 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo019, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk119]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo018_card, PeriodicMainZeroRecordPairsChunk119_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo019_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo019 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo018_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk119_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo020 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo019 ∪ PeriodicMainZeroRecordPairsChunk120

theorem PeriodicMainZeroRecordPairsGroup004UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk120 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo019 PeriodicMainZeroRecordPairsChunk120 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo020_card :
    PeriodicMainZeroRecordPairsGroup004UpTo020.card = 2100 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo020, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk120]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo019_card, PeriodicMainZeroRecordPairsChunk120_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo020_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo020 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo020] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo019_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk120_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo021 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo020 ∪ PeriodicMainZeroRecordPairsChunk121

theorem PeriodicMainZeroRecordPairsGroup004UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk121 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo020 PeriodicMainZeroRecordPairsChunk121 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo021_card :
    PeriodicMainZeroRecordPairsGroup004UpTo021.card = 2200 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo021, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk121]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo020_card, PeriodicMainZeroRecordPairsChunk121_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo021_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo021 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo021] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo020_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk121_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo022 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo021 ∪ PeriodicMainZeroRecordPairsChunk122

theorem PeriodicMainZeroRecordPairsGroup004UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk122 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo021 PeriodicMainZeroRecordPairsChunk122 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo022_card :
    PeriodicMainZeroRecordPairsGroup004UpTo022.card = 2300 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo022, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk122]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo021_card, PeriodicMainZeroRecordPairsChunk122_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo022_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo022 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo022] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo021_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk122_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo023 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo022 ∪ PeriodicMainZeroRecordPairsChunk123

theorem PeriodicMainZeroRecordPairsGroup004UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk123 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo022 PeriodicMainZeroRecordPairsChunk123 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo023_card :
    PeriodicMainZeroRecordPairsGroup004UpTo023.card = 2400 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo023, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk123]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo022_card, PeriodicMainZeroRecordPairsChunk123_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo023_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo023 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo023] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo022_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk123_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004UpTo024 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup004UpTo023 ∪ PeriodicMainZeroRecordPairsChunk124

theorem PeriodicMainZeroRecordPairsGroup004UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk124 :
    Disjoint PeriodicMainZeroRecordPairsGroup004UpTo023 PeriodicMainZeroRecordPairsChunk124 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup004UpTo024_card :
    PeriodicMainZeroRecordPairsGroup004UpTo024.card = 2500 := by
  rw [PeriodicMainZeroRecordPairsGroup004UpTo024, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup004UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk124]
  norm_num [PeriodicMainZeroRecordPairsGroup004UpTo023_card, PeriodicMainZeroRecordPairsChunk124_card]

theorem PeriodicMainZeroRecordPairsGroup004UpTo024_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004UpTo024 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup004UpTo024] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup004UpTo023_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk124_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup004 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup004UpTo024

theorem PeriodicMainZeroRecordPairsGroup004_card :
    PeriodicMainZeroRecordPairsGroup004.card = 2500 := by
  simpa [PeriodicMainZeroRecordPairsGroup004] using PeriodicMainZeroRecordPairsGroup004UpTo024_card

theorem PeriodicMainZeroRecordPairsGroup004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup004] using PeriodicMainZeroRecordPairsGroup004UpTo024_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
