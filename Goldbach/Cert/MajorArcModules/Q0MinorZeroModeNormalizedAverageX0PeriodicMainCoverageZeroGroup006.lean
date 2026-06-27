import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk150
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk151
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk152
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk153
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk154
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk155
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk156
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk157
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk158
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk159
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk160
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk161
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk162
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk163
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk164
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk165
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk166
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk167
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk168
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk169
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk170
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk171
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk172
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk173
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk174

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup006. -/

def PeriodicMainZeroRecordPairsGroup006UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk150

theorem PeriodicMainZeroRecordPairsGroup006UpTo000_card :
    PeriodicMainZeroRecordPairsGroup006UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup006UpTo000] using PeriodicMainZeroRecordPairsChunk150_card

theorem PeriodicMainZeroRecordPairsGroup006UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup006UpTo000] using PeriodicMainZeroRecordPairsChunk150_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup006UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo000 ∪ PeriodicMainZeroRecordPairsChunk151

theorem PeriodicMainZeroRecordPairsGroup006UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk151 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo000 PeriodicMainZeroRecordPairsChunk151 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo001_card :
    PeriodicMainZeroRecordPairsGroup006UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk151]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo000_card, PeriodicMainZeroRecordPairsChunk151_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk151_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo001 ∪ PeriodicMainZeroRecordPairsChunk152

theorem PeriodicMainZeroRecordPairsGroup006UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk152 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo001 PeriodicMainZeroRecordPairsChunk152 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo002_card :
    PeriodicMainZeroRecordPairsGroup006UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk152]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo001_card, PeriodicMainZeroRecordPairsChunk152_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk152_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo002 ∪ PeriodicMainZeroRecordPairsChunk153

theorem PeriodicMainZeroRecordPairsGroup006UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk153 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo002 PeriodicMainZeroRecordPairsChunk153 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo003_card :
    PeriodicMainZeroRecordPairsGroup006UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk153]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo002_card, PeriodicMainZeroRecordPairsChunk153_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk153_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo003 ∪ PeriodicMainZeroRecordPairsChunk154

theorem PeriodicMainZeroRecordPairsGroup006UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk154 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo003 PeriodicMainZeroRecordPairsChunk154 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo004_card :
    PeriodicMainZeroRecordPairsGroup006UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk154]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo003_card, PeriodicMainZeroRecordPairsChunk154_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk154_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo004 ∪ PeriodicMainZeroRecordPairsChunk155

theorem PeriodicMainZeroRecordPairsGroup006UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk155 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo004 PeriodicMainZeroRecordPairsChunk155 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo005_card :
    PeriodicMainZeroRecordPairsGroup006UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk155]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo004_card, PeriodicMainZeroRecordPairsChunk155_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk155_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo005 ∪ PeriodicMainZeroRecordPairsChunk156

theorem PeriodicMainZeroRecordPairsGroup006UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk156 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo005 PeriodicMainZeroRecordPairsChunk156 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo006_card :
    PeriodicMainZeroRecordPairsGroup006UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk156]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo005_card, PeriodicMainZeroRecordPairsChunk156_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk156_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo006 ∪ PeriodicMainZeroRecordPairsChunk157

theorem PeriodicMainZeroRecordPairsGroup006UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk157 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo006 PeriodicMainZeroRecordPairsChunk157 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo007_card :
    PeriodicMainZeroRecordPairsGroup006UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk157]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo006_card, PeriodicMainZeroRecordPairsChunk157_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk157_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo007 ∪ PeriodicMainZeroRecordPairsChunk158

theorem PeriodicMainZeroRecordPairsGroup006UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk158 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo007 PeriodicMainZeroRecordPairsChunk158 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo008_card :
    PeriodicMainZeroRecordPairsGroup006UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk158]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo007_card, PeriodicMainZeroRecordPairsChunk158_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk158_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo008 ∪ PeriodicMainZeroRecordPairsChunk159

theorem PeriodicMainZeroRecordPairsGroup006UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk159 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo008 PeriodicMainZeroRecordPairsChunk159 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo009_card :
    PeriodicMainZeroRecordPairsGroup006UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk159]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo008_card, PeriodicMainZeroRecordPairsChunk159_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk159_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo009 ∪ PeriodicMainZeroRecordPairsChunk160

theorem PeriodicMainZeroRecordPairsGroup006UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk160 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo009 PeriodicMainZeroRecordPairsChunk160 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo010_card :
    PeriodicMainZeroRecordPairsGroup006UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk160]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo009_card, PeriodicMainZeroRecordPairsChunk160_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk160_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo010 ∪ PeriodicMainZeroRecordPairsChunk161

theorem PeriodicMainZeroRecordPairsGroup006UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk161 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo010 PeriodicMainZeroRecordPairsChunk161 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo011_card :
    PeriodicMainZeroRecordPairsGroup006UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk161]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo010_card, PeriodicMainZeroRecordPairsChunk161_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk161_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo011 ∪ PeriodicMainZeroRecordPairsChunk162

theorem PeriodicMainZeroRecordPairsGroup006UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk162 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo011 PeriodicMainZeroRecordPairsChunk162 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo012_card :
    PeriodicMainZeroRecordPairsGroup006UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk162]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo011_card, PeriodicMainZeroRecordPairsChunk162_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk162_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo012 ∪ PeriodicMainZeroRecordPairsChunk163

theorem PeriodicMainZeroRecordPairsGroup006UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk163 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo012 PeriodicMainZeroRecordPairsChunk163 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo013_card :
    PeriodicMainZeroRecordPairsGroup006UpTo013.card = 1400 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk163]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo012_card, PeriodicMainZeroRecordPairsChunk163_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk163_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo014 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo013 ∪ PeriodicMainZeroRecordPairsChunk164

theorem PeriodicMainZeroRecordPairsGroup006UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk164 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo013 PeriodicMainZeroRecordPairsChunk164 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo014_card :
    PeriodicMainZeroRecordPairsGroup006UpTo014.card = 1500 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo014, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk164]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo013_card, PeriodicMainZeroRecordPairsChunk164_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo014_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo014 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo013_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk164_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo015 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo014 ∪ PeriodicMainZeroRecordPairsChunk165

theorem PeriodicMainZeroRecordPairsGroup006UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk165 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo014 PeriodicMainZeroRecordPairsChunk165 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo015_card :
    PeriodicMainZeroRecordPairsGroup006UpTo015.card = 1600 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo015, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk165]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo014_card, PeriodicMainZeroRecordPairsChunk165_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo015_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo015 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo014_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk165_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo016 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo015 ∪ PeriodicMainZeroRecordPairsChunk166

theorem PeriodicMainZeroRecordPairsGroup006UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk166 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo015 PeriodicMainZeroRecordPairsChunk166 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo016_card :
    PeriodicMainZeroRecordPairsGroup006UpTo016.card = 1700 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo016, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk166]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo015_card, PeriodicMainZeroRecordPairsChunk166_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo016_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo016 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo015_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk166_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo017 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo016 ∪ PeriodicMainZeroRecordPairsChunk167

theorem PeriodicMainZeroRecordPairsGroup006UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk167 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo016 PeriodicMainZeroRecordPairsChunk167 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo017_card :
    PeriodicMainZeroRecordPairsGroup006UpTo017.card = 1800 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo017, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk167]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo016_card, PeriodicMainZeroRecordPairsChunk167_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo017_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo017 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo016_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk167_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo018 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo017 ∪ PeriodicMainZeroRecordPairsChunk168

theorem PeriodicMainZeroRecordPairsGroup006UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk168 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo017 PeriodicMainZeroRecordPairsChunk168 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo018_card :
    PeriodicMainZeroRecordPairsGroup006UpTo018.card = 1900 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo018, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk168]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo017_card, PeriodicMainZeroRecordPairsChunk168_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo018_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo018 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo017_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk168_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo019 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo018 ∪ PeriodicMainZeroRecordPairsChunk169

theorem PeriodicMainZeroRecordPairsGroup006UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk169 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo018 PeriodicMainZeroRecordPairsChunk169 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo019_card :
    PeriodicMainZeroRecordPairsGroup006UpTo019.card = 2000 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo019, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk169]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo018_card, PeriodicMainZeroRecordPairsChunk169_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo019_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo019 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo018_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk169_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo020 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo019 ∪ PeriodicMainZeroRecordPairsChunk170

theorem PeriodicMainZeroRecordPairsGroup006UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk170 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo019 PeriodicMainZeroRecordPairsChunk170 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo020_card :
    PeriodicMainZeroRecordPairsGroup006UpTo020.card = 2100 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo020, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk170]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo019_card, PeriodicMainZeroRecordPairsChunk170_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo020_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo020 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo020] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo019_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk170_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo021 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo020 ∪ PeriodicMainZeroRecordPairsChunk171

theorem PeriodicMainZeroRecordPairsGroup006UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk171 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo020 PeriodicMainZeroRecordPairsChunk171 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo021_card :
    PeriodicMainZeroRecordPairsGroup006UpTo021.card = 2200 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo021, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk171]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo020_card, PeriodicMainZeroRecordPairsChunk171_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo021_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo021 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo021] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo020_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk171_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo022 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo021 ∪ PeriodicMainZeroRecordPairsChunk172

theorem PeriodicMainZeroRecordPairsGroup006UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk172 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo021 PeriodicMainZeroRecordPairsChunk172 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo022_card :
    PeriodicMainZeroRecordPairsGroup006UpTo022.card = 2300 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo022, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk172]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo021_card, PeriodicMainZeroRecordPairsChunk172_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo022_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo022 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo022] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo021_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk172_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo023 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo022 ∪ PeriodicMainZeroRecordPairsChunk173

theorem PeriodicMainZeroRecordPairsGroup006UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk173 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo022 PeriodicMainZeroRecordPairsChunk173 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo023_card :
    PeriodicMainZeroRecordPairsGroup006UpTo023.card = 2400 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo023, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk173]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo022_card, PeriodicMainZeroRecordPairsChunk173_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo023_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo023 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo023] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo022_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk173_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006UpTo024 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup006UpTo023 ∪ PeriodicMainZeroRecordPairsChunk174

theorem PeriodicMainZeroRecordPairsGroup006UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk174 :
    Disjoint PeriodicMainZeroRecordPairsGroup006UpTo023 PeriodicMainZeroRecordPairsChunk174 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup006UpTo024_card :
    PeriodicMainZeroRecordPairsGroup006UpTo024.card = 2500 := by
  rw [PeriodicMainZeroRecordPairsGroup006UpTo024, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup006UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk174]
  norm_num [PeriodicMainZeroRecordPairsGroup006UpTo023_card, PeriodicMainZeroRecordPairsChunk174_card]

theorem PeriodicMainZeroRecordPairsGroup006UpTo024_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006UpTo024 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup006UpTo024] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup006UpTo023_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk174_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup006 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup006UpTo024

theorem PeriodicMainZeroRecordPairsGroup006_card :
    PeriodicMainZeroRecordPairsGroup006.card = 2500 := by
  simpa [PeriodicMainZeroRecordPairsGroup006] using PeriodicMainZeroRecordPairsGroup006UpTo024_card

theorem PeriodicMainZeroRecordPairsGroup006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup006] using PeriodicMainZeroRecordPairsGroup006UpTo024_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
