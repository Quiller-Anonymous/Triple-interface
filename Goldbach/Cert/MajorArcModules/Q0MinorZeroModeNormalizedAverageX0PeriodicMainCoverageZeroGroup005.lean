import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk125
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk126
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk127
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk128
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk129
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk130
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk131
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk132
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk133
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk134
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk135
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk136
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk137
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk138
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk139
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk140
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk141
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk142
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk143
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk144
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk145
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk146
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk147
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk148
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk149

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup005. -/

def PeriodicMainZeroRecordPairsGroup005UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk125

theorem PeriodicMainZeroRecordPairsGroup005UpTo000_card :
    PeriodicMainZeroRecordPairsGroup005UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup005UpTo000] using PeriodicMainZeroRecordPairsChunk125_card

theorem PeriodicMainZeroRecordPairsGroup005UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup005UpTo000] using PeriodicMainZeroRecordPairsChunk125_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup005UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo000 ∪ PeriodicMainZeroRecordPairsChunk126

theorem PeriodicMainZeroRecordPairsGroup005UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk126 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo000 PeriodicMainZeroRecordPairsChunk126 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo001_card :
    PeriodicMainZeroRecordPairsGroup005UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk126]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo000_card, PeriodicMainZeroRecordPairsChunk126_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk126_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo001 ∪ PeriodicMainZeroRecordPairsChunk127

theorem PeriodicMainZeroRecordPairsGroup005UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk127 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo001 PeriodicMainZeroRecordPairsChunk127 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo002_card :
    PeriodicMainZeroRecordPairsGroup005UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk127]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo001_card, PeriodicMainZeroRecordPairsChunk127_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk127_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo002 ∪ PeriodicMainZeroRecordPairsChunk128

theorem PeriodicMainZeroRecordPairsGroup005UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk128 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo002 PeriodicMainZeroRecordPairsChunk128 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo003_card :
    PeriodicMainZeroRecordPairsGroup005UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk128]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo002_card, PeriodicMainZeroRecordPairsChunk128_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk128_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo003 ∪ PeriodicMainZeroRecordPairsChunk129

theorem PeriodicMainZeroRecordPairsGroup005UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk129 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo003 PeriodicMainZeroRecordPairsChunk129 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo004_card :
    PeriodicMainZeroRecordPairsGroup005UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk129]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo003_card, PeriodicMainZeroRecordPairsChunk129_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk129_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo004 ∪ PeriodicMainZeroRecordPairsChunk130

theorem PeriodicMainZeroRecordPairsGroup005UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk130 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo004 PeriodicMainZeroRecordPairsChunk130 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo005_card :
    PeriodicMainZeroRecordPairsGroup005UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk130]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo004_card, PeriodicMainZeroRecordPairsChunk130_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk130_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo005 ∪ PeriodicMainZeroRecordPairsChunk131

theorem PeriodicMainZeroRecordPairsGroup005UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk131 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo005 PeriodicMainZeroRecordPairsChunk131 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo006_card :
    PeriodicMainZeroRecordPairsGroup005UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk131]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo005_card, PeriodicMainZeroRecordPairsChunk131_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk131_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo006 ∪ PeriodicMainZeroRecordPairsChunk132

theorem PeriodicMainZeroRecordPairsGroup005UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk132 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo006 PeriodicMainZeroRecordPairsChunk132 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo007_card :
    PeriodicMainZeroRecordPairsGroup005UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk132]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo006_card, PeriodicMainZeroRecordPairsChunk132_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk132_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo007 ∪ PeriodicMainZeroRecordPairsChunk133

theorem PeriodicMainZeroRecordPairsGroup005UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk133 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo007 PeriodicMainZeroRecordPairsChunk133 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo008_card :
    PeriodicMainZeroRecordPairsGroup005UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk133]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo007_card, PeriodicMainZeroRecordPairsChunk133_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk133_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo008 ∪ PeriodicMainZeroRecordPairsChunk134

theorem PeriodicMainZeroRecordPairsGroup005UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk134 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo008 PeriodicMainZeroRecordPairsChunk134 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo009_card :
    PeriodicMainZeroRecordPairsGroup005UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk134]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo008_card, PeriodicMainZeroRecordPairsChunk134_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk134_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo009 ∪ PeriodicMainZeroRecordPairsChunk135

theorem PeriodicMainZeroRecordPairsGroup005UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk135 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo009 PeriodicMainZeroRecordPairsChunk135 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo010_card :
    PeriodicMainZeroRecordPairsGroup005UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk135]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo009_card, PeriodicMainZeroRecordPairsChunk135_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk135_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo010 ∪ PeriodicMainZeroRecordPairsChunk136

theorem PeriodicMainZeroRecordPairsGroup005UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk136 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo010 PeriodicMainZeroRecordPairsChunk136 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo011_card :
    PeriodicMainZeroRecordPairsGroup005UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk136]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo010_card, PeriodicMainZeroRecordPairsChunk136_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk136_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo011 ∪ PeriodicMainZeroRecordPairsChunk137

theorem PeriodicMainZeroRecordPairsGroup005UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk137 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo011 PeriodicMainZeroRecordPairsChunk137 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo012_card :
    PeriodicMainZeroRecordPairsGroup005UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk137]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo011_card, PeriodicMainZeroRecordPairsChunk137_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk137_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo012 ∪ PeriodicMainZeroRecordPairsChunk138

theorem PeriodicMainZeroRecordPairsGroup005UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk138 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo012 PeriodicMainZeroRecordPairsChunk138 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo013_card :
    PeriodicMainZeroRecordPairsGroup005UpTo013.card = 1400 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk138]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo012_card, PeriodicMainZeroRecordPairsChunk138_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk138_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo014 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo013 ∪ PeriodicMainZeroRecordPairsChunk139

theorem PeriodicMainZeroRecordPairsGroup005UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk139 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo013 PeriodicMainZeroRecordPairsChunk139 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo014_card :
    PeriodicMainZeroRecordPairsGroup005UpTo014.card = 1500 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo014, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk139]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo013_card, PeriodicMainZeroRecordPairsChunk139_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo014_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo014 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo013_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk139_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo015 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo014 ∪ PeriodicMainZeroRecordPairsChunk140

theorem PeriodicMainZeroRecordPairsGroup005UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk140 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo014 PeriodicMainZeroRecordPairsChunk140 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo015_card :
    PeriodicMainZeroRecordPairsGroup005UpTo015.card = 1600 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo015, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk140]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo014_card, PeriodicMainZeroRecordPairsChunk140_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo015_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo015 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo014_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk140_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo016 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo015 ∪ PeriodicMainZeroRecordPairsChunk141

theorem PeriodicMainZeroRecordPairsGroup005UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk141 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo015 PeriodicMainZeroRecordPairsChunk141 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo016_card :
    PeriodicMainZeroRecordPairsGroup005UpTo016.card = 1700 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo016, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk141]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo015_card, PeriodicMainZeroRecordPairsChunk141_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo016_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo016 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo015_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk141_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo017 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo016 ∪ PeriodicMainZeroRecordPairsChunk142

theorem PeriodicMainZeroRecordPairsGroup005UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk142 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo016 PeriodicMainZeroRecordPairsChunk142 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo017_card :
    PeriodicMainZeroRecordPairsGroup005UpTo017.card = 1800 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo017, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk142]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo016_card, PeriodicMainZeroRecordPairsChunk142_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo017_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo017 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo016_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk142_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo018 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo017 ∪ PeriodicMainZeroRecordPairsChunk143

theorem PeriodicMainZeroRecordPairsGroup005UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk143 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo017 PeriodicMainZeroRecordPairsChunk143 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo018_card :
    PeriodicMainZeroRecordPairsGroup005UpTo018.card = 1900 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo018, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk143]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo017_card, PeriodicMainZeroRecordPairsChunk143_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo018_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo018 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo017_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk143_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo019 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo018 ∪ PeriodicMainZeroRecordPairsChunk144

theorem PeriodicMainZeroRecordPairsGroup005UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk144 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo018 PeriodicMainZeroRecordPairsChunk144 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo019_card :
    PeriodicMainZeroRecordPairsGroup005UpTo019.card = 2000 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo019, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk144]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo018_card, PeriodicMainZeroRecordPairsChunk144_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo019_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo019 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo018_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk144_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo020 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo019 ∪ PeriodicMainZeroRecordPairsChunk145

theorem PeriodicMainZeroRecordPairsGroup005UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk145 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo019 PeriodicMainZeroRecordPairsChunk145 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo020_card :
    PeriodicMainZeroRecordPairsGroup005UpTo020.card = 2100 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo020, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk145]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo019_card, PeriodicMainZeroRecordPairsChunk145_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo020_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo020 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo020] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo019_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk145_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo021 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo020 ∪ PeriodicMainZeroRecordPairsChunk146

theorem PeriodicMainZeroRecordPairsGroup005UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk146 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo020 PeriodicMainZeroRecordPairsChunk146 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo021_card :
    PeriodicMainZeroRecordPairsGroup005UpTo021.card = 2200 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo021, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk146]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo020_card, PeriodicMainZeroRecordPairsChunk146_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo021_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo021 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo021] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo020_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk146_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo022 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo021 ∪ PeriodicMainZeroRecordPairsChunk147

theorem PeriodicMainZeroRecordPairsGroup005UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk147 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo021 PeriodicMainZeroRecordPairsChunk147 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo022_card :
    PeriodicMainZeroRecordPairsGroup005UpTo022.card = 2300 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo022, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk147]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo021_card, PeriodicMainZeroRecordPairsChunk147_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo022_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo022 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo022] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo021_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk147_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo023 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo022 ∪ PeriodicMainZeroRecordPairsChunk148

theorem PeriodicMainZeroRecordPairsGroup005UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk148 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo022 PeriodicMainZeroRecordPairsChunk148 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo023_card :
    PeriodicMainZeroRecordPairsGroup005UpTo023.card = 2400 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo023, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk148]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo022_card, PeriodicMainZeroRecordPairsChunk148_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo023_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo023 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo023] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo022_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk148_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005UpTo024 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup005UpTo023 ∪ PeriodicMainZeroRecordPairsChunk149

theorem PeriodicMainZeroRecordPairsGroup005UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk149 :
    Disjoint PeriodicMainZeroRecordPairsGroup005UpTo023 PeriodicMainZeroRecordPairsChunk149 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup005UpTo024_card :
    PeriodicMainZeroRecordPairsGroup005UpTo024.card = 2500 := by
  rw [PeriodicMainZeroRecordPairsGroup005UpTo024, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup005UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk149]
  norm_num [PeriodicMainZeroRecordPairsGroup005UpTo023_card, PeriodicMainZeroRecordPairsChunk149_card]

theorem PeriodicMainZeroRecordPairsGroup005UpTo024_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005UpTo024 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup005UpTo024] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup005UpTo023_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk149_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup005 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup005UpTo024

theorem PeriodicMainZeroRecordPairsGroup005_card :
    PeriodicMainZeroRecordPairsGroup005.card = 2500 := by
  simpa [PeriodicMainZeroRecordPairsGroup005] using PeriodicMainZeroRecordPairsGroup005UpTo024_card

theorem PeriodicMainZeroRecordPairsGroup005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup005] using PeriodicMainZeroRecordPairsGroup005UpTo024_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
