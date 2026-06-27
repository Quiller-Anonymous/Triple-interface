import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk175
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk176
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk177
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk178
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk179
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk180
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk181
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk182
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk183
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk184
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk185
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk186
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk187
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk188

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup007. -/

def PeriodicMainZeroRecordPairsGroup007UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk175

theorem PeriodicMainZeroRecordPairsGroup007UpTo000_card :
    PeriodicMainZeroRecordPairsGroup007UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup007UpTo000] using PeriodicMainZeroRecordPairsChunk175_card

theorem PeriodicMainZeroRecordPairsGroup007UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup007UpTo000] using PeriodicMainZeroRecordPairsChunk175_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup007UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo000 ∪ PeriodicMainZeroRecordPairsChunk176

theorem PeriodicMainZeroRecordPairsGroup007UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk176 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo000 PeriodicMainZeroRecordPairsChunk176 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo001_card :
    PeriodicMainZeroRecordPairsGroup007UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk176]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo000_card, PeriodicMainZeroRecordPairsChunk176_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk176_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo001 ∪ PeriodicMainZeroRecordPairsChunk177

theorem PeriodicMainZeroRecordPairsGroup007UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk177 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo001 PeriodicMainZeroRecordPairsChunk177 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo002_card :
    PeriodicMainZeroRecordPairsGroup007UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk177]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo001_card, PeriodicMainZeroRecordPairsChunk177_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk177_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo002 ∪ PeriodicMainZeroRecordPairsChunk178

theorem PeriodicMainZeroRecordPairsGroup007UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk178 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo002 PeriodicMainZeroRecordPairsChunk178 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo003_card :
    PeriodicMainZeroRecordPairsGroup007UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk178]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo002_card, PeriodicMainZeroRecordPairsChunk178_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk178_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo003 ∪ PeriodicMainZeroRecordPairsChunk179

theorem PeriodicMainZeroRecordPairsGroup007UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk179 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo003 PeriodicMainZeroRecordPairsChunk179 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo004_card :
    PeriodicMainZeroRecordPairsGroup007UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk179]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo003_card, PeriodicMainZeroRecordPairsChunk179_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk179_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo004 ∪ PeriodicMainZeroRecordPairsChunk180

theorem PeriodicMainZeroRecordPairsGroup007UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk180 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo004 PeriodicMainZeroRecordPairsChunk180 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo005_card :
    PeriodicMainZeroRecordPairsGroup007UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk180]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo004_card, PeriodicMainZeroRecordPairsChunk180_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk180_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo005 ∪ PeriodicMainZeroRecordPairsChunk181

theorem PeriodicMainZeroRecordPairsGroup007UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk181 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo005 PeriodicMainZeroRecordPairsChunk181 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo006_card :
    PeriodicMainZeroRecordPairsGroup007UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk181]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo005_card, PeriodicMainZeroRecordPairsChunk181_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk181_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo006 ∪ PeriodicMainZeroRecordPairsChunk182

theorem PeriodicMainZeroRecordPairsGroup007UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk182 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo006 PeriodicMainZeroRecordPairsChunk182 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo007_card :
    PeriodicMainZeroRecordPairsGroup007UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk182]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo006_card, PeriodicMainZeroRecordPairsChunk182_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk182_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo007 ∪ PeriodicMainZeroRecordPairsChunk183

theorem PeriodicMainZeroRecordPairsGroup007UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk183 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo007 PeriodicMainZeroRecordPairsChunk183 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo008_card :
    PeriodicMainZeroRecordPairsGroup007UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk183]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo007_card, PeriodicMainZeroRecordPairsChunk183_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk183_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo008 ∪ PeriodicMainZeroRecordPairsChunk184

theorem PeriodicMainZeroRecordPairsGroup007UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk184 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo008 PeriodicMainZeroRecordPairsChunk184 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo009_card :
    PeriodicMainZeroRecordPairsGroup007UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk184]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo008_card, PeriodicMainZeroRecordPairsChunk184_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk184_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo009 ∪ PeriodicMainZeroRecordPairsChunk185

theorem PeriodicMainZeroRecordPairsGroup007UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk185 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo009 PeriodicMainZeroRecordPairsChunk185 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo010_card :
    PeriodicMainZeroRecordPairsGroup007UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk185]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo009_card, PeriodicMainZeroRecordPairsChunk185_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk185_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo010 ∪ PeriodicMainZeroRecordPairsChunk186

theorem PeriodicMainZeroRecordPairsGroup007UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk186 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo010 PeriodicMainZeroRecordPairsChunk186 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo011_card :
    PeriodicMainZeroRecordPairsGroup007UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk186]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo010_card, PeriodicMainZeroRecordPairsChunk186_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk186_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo011 ∪ PeriodicMainZeroRecordPairsChunk187

theorem PeriodicMainZeroRecordPairsGroup007UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk187 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo011 PeriodicMainZeroRecordPairsChunk187 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo012_card :
    PeriodicMainZeroRecordPairsGroup007UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk187]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo011_card, PeriodicMainZeroRecordPairsChunk187_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk187_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup007UpTo012 ∪ PeriodicMainZeroRecordPairsChunk188

theorem PeriodicMainZeroRecordPairsGroup007UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk188 :
    Disjoint PeriodicMainZeroRecordPairsGroup007UpTo012 PeriodicMainZeroRecordPairsChunk188 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup007UpTo013_card :
    PeriodicMainZeroRecordPairsGroup007UpTo013.card = 1370 := by
  rw [PeriodicMainZeroRecordPairsGroup007UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup007UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk188]
  norm_num [PeriodicMainZeroRecordPairsGroup007UpTo012_card, PeriodicMainZeroRecordPairsChunk188_card]

theorem PeriodicMainZeroRecordPairsGroup007UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup007UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup007UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk188_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup007 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup007UpTo013

theorem PeriodicMainZeroRecordPairsGroup007_card :
    PeriodicMainZeroRecordPairsGroup007.card = 1370 := by
  simpa [PeriodicMainZeroRecordPairsGroup007] using PeriodicMainZeroRecordPairsGroup007UpTo013_card

theorem PeriodicMainZeroRecordPairsGroup007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup007] using PeriodicMainZeroRecordPairsGroup007UpTo013_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
