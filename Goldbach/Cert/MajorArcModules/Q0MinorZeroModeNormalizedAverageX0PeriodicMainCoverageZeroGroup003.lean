import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk075
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk076
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk077
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk078
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk079
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk080
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk081
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk082
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk083
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk084
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk085
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk086
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk087
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk088
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk089
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk090
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk091
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk092
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk093
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk094
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk095
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk096
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk097
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk098
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk099

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup003. -/

def PeriodicMainZeroRecordPairsGroup003UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk075

theorem PeriodicMainZeroRecordPairsGroup003UpTo000_card :
    PeriodicMainZeroRecordPairsGroup003UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup003UpTo000] using PeriodicMainZeroRecordPairsChunk075_card

theorem PeriodicMainZeroRecordPairsGroup003UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup003UpTo000] using PeriodicMainZeroRecordPairsChunk075_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup003UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo000 ∪ PeriodicMainZeroRecordPairsChunk076

theorem PeriodicMainZeroRecordPairsGroup003UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk076 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo000 PeriodicMainZeroRecordPairsChunk076 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo001_card :
    PeriodicMainZeroRecordPairsGroup003UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk076]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo000_card, PeriodicMainZeroRecordPairsChunk076_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk076_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo001 ∪ PeriodicMainZeroRecordPairsChunk077

theorem PeriodicMainZeroRecordPairsGroup003UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk077 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo001 PeriodicMainZeroRecordPairsChunk077 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo002_card :
    PeriodicMainZeroRecordPairsGroup003UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk077]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo001_card, PeriodicMainZeroRecordPairsChunk077_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk077_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo002 ∪ PeriodicMainZeroRecordPairsChunk078

theorem PeriodicMainZeroRecordPairsGroup003UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk078 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo002 PeriodicMainZeroRecordPairsChunk078 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo003_card :
    PeriodicMainZeroRecordPairsGroup003UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk078]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo002_card, PeriodicMainZeroRecordPairsChunk078_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk078_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo003 ∪ PeriodicMainZeroRecordPairsChunk079

theorem PeriodicMainZeroRecordPairsGroup003UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk079 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo003 PeriodicMainZeroRecordPairsChunk079 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo004_card :
    PeriodicMainZeroRecordPairsGroup003UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk079]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo003_card, PeriodicMainZeroRecordPairsChunk079_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk079_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo004 ∪ PeriodicMainZeroRecordPairsChunk080

theorem PeriodicMainZeroRecordPairsGroup003UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk080 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo004 PeriodicMainZeroRecordPairsChunk080 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo005_card :
    PeriodicMainZeroRecordPairsGroup003UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk080]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo004_card, PeriodicMainZeroRecordPairsChunk080_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk080_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo005 ∪ PeriodicMainZeroRecordPairsChunk081

theorem PeriodicMainZeroRecordPairsGroup003UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk081 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo005 PeriodicMainZeroRecordPairsChunk081 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo006_card :
    PeriodicMainZeroRecordPairsGroup003UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk081]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo005_card, PeriodicMainZeroRecordPairsChunk081_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk081_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo006 ∪ PeriodicMainZeroRecordPairsChunk082

theorem PeriodicMainZeroRecordPairsGroup003UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk082 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo006 PeriodicMainZeroRecordPairsChunk082 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo007_card :
    PeriodicMainZeroRecordPairsGroup003UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk082]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo006_card, PeriodicMainZeroRecordPairsChunk082_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk082_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo007 ∪ PeriodicMainZeroRecordPairsChunk083

theorem PeriodicMainZeroRecordPairsGroup003UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk083 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo007 PeriodicMainZeroRecordPairsChunk083 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo008_card :
    PeriodicMainZeroRecordPairsGroup003UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk083]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo007_card, PeriodicMainZeroRecordPairsChunk083_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk083_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo008 ∪ PeriodicMainZeroRecordPairsChunk084

theorem PeriodicMainZeroRecordPairsGroup003UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk084 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo008 PeriodicMainZeroRecordPairsChunk084 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo009_card :
    PeriodicMainZeroRecordPairsGroup003UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk084]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo008_card, PeriodicMainZeroRecordPairsChunk084_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk084_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo009 ∪ PeriodicMainZeroRecordPairsChunk085

theorem PeriodicMainZeroRecordPairsGroup003UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk085 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo009 PeriodicMainZeroRecordPairsChunk085 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo010_card :
    PeriodicMainZeroRecordPairsGroup003UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk085]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo009_card, PeriodicMainZeroRecordPairsChunk085_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk085_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo010 ∪ PeriodicMainZeroRecordPairsChunk086

theorem PeriodicMainZeroRecordPairsGroup003UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk086 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo010 PeriodicMainZeroRecordPairsChunk086 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo011_card :
    PeriodicMainZeroRecordPairsGroup003UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk086]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo010_card, PeriodicMainZeroRecordPairsChunk086_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk086_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo011 ∪ PeriodicMainZeroRecordPairsChunk087

theorem PeriodicMainZeroRecordPairsGroup003UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk087 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo011 PeriodicMainZeroRecordPairsChunk087 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo012_card :
    PeriodicMainZeroRecordPairsGroup003UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk087]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo011_card, PeriodicMainZeroRecordPairsChunk087_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk087_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo012 ∪ PeriodicMainZeroRecordPairsChunk088

theorem PeriodicMainZeroRecordPairsGroup003UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk088 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo012 PeriodicMainZeroRecordPairsChunk088 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo013_card :
    PeriodicMainZeroRecordPairsGroup003UpTo013.card = 1400 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk088]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo012_card, PeriodicMainZeroRecordPairsChunk088_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk088_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo014 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo013 ∪ PeriodicMainZeroRecordPairsChunk089

theorem PeriodicMainZeroRecordPairsGroup003UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk089 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo013 PeriodicMainZeroRecordPairsChunk089 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo014_card :
    PeriodicMainZeroRecordPairsGroup003UpTo014.card = 1500 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo014, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk089]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo013_card, PeriodicMainZeroRecordPairsChunk089_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo014_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo014 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo013_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk089_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo015 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo014 ∪ PeriodicMainZeroRecordPairsChunk090

theorem PeriodicMainZeroRecordPairsGroup003UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk090 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo014 PeriodicMainZeroRecordPairsChunk090 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo015_card :
    PeriodicMainZeroRecordPairsGroup003UpTo015.card = 1600 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo015, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk090]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo014_card, PeriodicMainZeroRecordPairsChunk090_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo015_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo015 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo014_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk090_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo016 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo015 ∪ PeriodicMainZeroRecordPairsChunk091

theorem PeriodicMainZeroRecordPairsGroup003UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk091 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo015 PeriodicMainZeroRecordPairsChunk091 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo016_card :
    PeriodicMainZeroRecordPairsGroup003UpTo016.card = 1700 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo016, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk091]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo015_card, PeriodicMainZeroRecordPairsChunk091_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo016_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo016 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo015_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk091_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo017 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo016 ∪ PeriodicMainZeroRecordPairsChunk092

theorem PeriodicMainZeroRecordPairsGroup003UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk092 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo016 PeriodicMainZeroRecordPairsChunk092 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo017_card :
    PeriodicMainZeroRecordPairsGroup003UpTo017.card = 1800 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo017, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk092]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo016_card, PeriodicMainZeroRecordPairsChunk092_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo017_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo017 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo016_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk092_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo018 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo017 ∪ PeriodicMainZeroRecordPairsChunk093

theorem PeriodicMainZeroRecordPairsGroup003UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk093 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo017 PeriodicMainZeroRecordPairsChunk093 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo018_card :
    PeriodicMainZeroRecordPairsGroup003UpTo018.card = 1900 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo018, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk093]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo017_card, PeriodicMainZeroRecordPairsChunk093_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo018_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo018 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo017_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk093_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo019 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo018 ∪ PeriodicMainZeroRecordPairsChunk094

theorem PeriodicMainZeroRecordPairsGroup003UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk094 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo018 PeriodicMainZeroRecordPairsChunk094 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo019_card :
    PeriodicMainZeroRecordPairsGroup003UpTo019.card = 2000 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo019, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk094]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo018_card, PeriodicMainZeroRecordPairsChunk094_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo019_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo019 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo018_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk094_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo020 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo019 ∪ PeriodicMainZeroRecordPairsChunk095

theorem PeriodicMainZeroRecordPairsGroup003UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk095 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo019 PeriodicMainZeroRecordPairsChunk095 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo020_card :
    PeriodicMainZeroRecordPairsGroup003UpTo020.card = 2100 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo020, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk095]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo019_card, PeriodicMainZeroRecordPairsChunk095_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo020_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo020 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo020] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo019_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk095_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo021 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo020 ∪ PeriodicMainZeroRecordPairsChunk096

theorem PeriodicMainZeroRecordPairsGroup003UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk096 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo020 PeriodicMainZeroRecordPairsChunk096 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo021_card :
    PeriodicMainZeroRecordPairsGroup003UpTo021.card = 2200 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo021, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk096]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo020_card, PeriodicMainZeroRecordPairsChunk096_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo021_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo021 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo021] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo020_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk096_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo022 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo021 ∪ PeriodicMainZeroRecordPairsChunk097

theorem PeriodicMainZeroRecordPairsGroup003UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk097 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo021 PeriodicMainZeroRecordPairsChunk097 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo022_card :
    PeriodicMainZeroRecordPairsGroup003UpTo022.card = 2300 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo022, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk097]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo021_card, PeriodicMainZeroRecordPairsChunk097_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo022_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo022 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo022] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo021_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk097_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo023 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo022 ∪ PeriodicMainZeroRecordPairsChunk098

theorem PeriodicMainZeroRecordPairsGroup003UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk098 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo022 PeriodicMainZeroRecordPairsChunk098 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo023_card :
    PeriodicMainZeroRecordPairsGroup003UpTo023.card = 2400 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo023, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk098]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo022_card, PeriodicMainZeroRecordPairsChunk098_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo023_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo023 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo023] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo022_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk098_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003UpTo024 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup003UpTo023 ∪ PeriodicMainZeroRecordPairsChunk099

theorem PeriodicMainZeroRecordPairsGroup003UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk099 :
    Disjoint PeriodicMainZeroRecordPairsGroup003UpTo023 PeriodicMainZeroRecordPairsChunk099 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup003UpTo024_card :
    PeriodicMainZeroRecordPairsGroup003UpTo024.card = 2500 := by
  rw [PeriodicMainZeroRecordPairsGroup003UpTo024, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup003UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk099]
  norm_num [PeriodicMainZeroRecordPairsGroup003UpTo023_card, PeriodicMainZeroRecordPairsChunk099_card]

theorem PeriodicMainZeroRecordPairsGroup003UpTo024_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003UpTo024 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup003UpTo024] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup003UpTo023_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk099_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup003 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup003UpTo024

theorem PeriodicMainZeroRecordPairsGroup003_card :
    PeriodicMainZeroRecordPairsGroup003.card = 2500 := by
  simpa [PeriodicMainZeroRecordPairsGroup003] using PeriodicMainZeroRecordPairsGroup003UpTo024_card

theorem PeriodicMainZeroRecordPairsGroup003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup003] using PeriodicMainZeroRecordPairsGroup003UpTo024_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
