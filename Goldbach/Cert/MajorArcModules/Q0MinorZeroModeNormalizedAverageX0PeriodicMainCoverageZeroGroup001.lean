import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk025
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk026
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk027
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk028
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk029
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk030
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk031
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk032
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk033
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk034
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk035
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk036
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk037
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk038
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk039
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk040
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk041
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk042
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk043
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk044
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk045
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk046
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk047
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk048
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk049

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup001. -/

def PeriodicMainZeroRecordPairsGroup001UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk025

theorem PeriodicMainZeroRecordPairsGroup001UpTo000_card :
    PeriodicMainZeroRecordPairsGroup001UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup001UpTo000] using PeriodicMainZeroRecordPairsChunk025_card

theorem PeriodicMainZeroRecordPairsGroup001UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup001UpTo000] using PeriodicMainZeroRecordPairsChunk025_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup001UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo000 ∪ PeriodicMainZeroRecordPairsChunk026

theorem PeriodicMainZeroRecordPairsGroup001UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk026 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo000 PeriodicMainZeroRecordPairsChunk026 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo001_card :
    PeriodicMainZeroRecordPairsGroup001UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk026]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo000_card, PeriodicMainZeroRecordPairsChunk026_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk026_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo001 ∪ PeriodicMainZeroRecordPairsChunk027

theorem PeriodicMainZeroRecordPairsGroup001UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk027 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo001 PeriodicMainZeroRecordPairsChunk027 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo002_card :
    PeriodicMainZeroRecordPairsGroup001UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk027]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo001_card, PeriodicMainZeroRecordPairsChunk027_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk027_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo002 ∪ PeriodicMainZeroRecordPairsChunk028

theorem PeriodicMainZeroRecordPairsGroup001UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk028 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo002 PeriodicMainZeroRecordPairsChunk028 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo003_card :
    PeriodicMainZeroRecordPairsGroup001UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk028]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo002_card, PeriodicMainZeroRecordPairsChunk028_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk028_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo003 ∪ PeriodicMainZeroRecordPairsChunk029

theorem PeriodicMainZeroRecordPairsGroup001UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk029 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo003 PeriodicMainZeroRecordPairsChunk029 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo004_card :
    PeriodicMainZeroRecordPairsGroup001UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk029]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo003_card, PeriodicMainZeroRecordPairsChunk029_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk029_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo004 ∪ PeriodicMainZeroRecordPairsChunk030

theorem PeriodicMainZeroRecordPairsGroup001UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk030 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo004 PeriodicMainZeroRecordPairsChunk030 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo005_card :
    PeriodicMainZeroRecordPairsGroup001UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk030]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo004_card, PeriodicMainZeroRecordPairsChunk030_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk030_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo005 ∪ PeriodicMainZeroRecordPairsChunk031

theorem PeriodicMainZeroRecordPairsGroup001UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk031 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo005 PeriodicMainZeroRecordPairsChunk031 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo006_card :
    PeriodicMainZeroRecordPairsGroup001UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk031]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo005_card, PeriodicMainZeroRecordPairsChunk031_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk031_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo006 ∪ PeriodicMainZeroRecordPairsChunk032

theorem PeriodicMainZeroRecordPairsGroup001UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk032 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo006 PeriodicMainZeroRecordPairsChunk032 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo007_card :
    PeriodicMainZeroRecordPairsGroup001UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk032]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo006_card, PeriodicMainZeroRecordPairsChunk032_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk032_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo007 ∪ PeriodicMainZeroRecordPairsChunk033

theorem PeriodicMainZeroRecordPairsGroup001UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk033 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo007 PeriodicMainZeroRecordPairsChunk033 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo008_card :
    PeriodicMainZeroRecordPairsGroup001UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk033]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo007_card, PeriodicMainZeroRecordPairsChunk033_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk033_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo008 ∪ PeriodicMainZeroRecordPairsChunk034

theorem PeriodicMainZeroRecordPairsGroup001UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk034 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo008 PeriodicMainZeroRecordPairsChunk034 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo009_card :
    PeriodicMainZeroRecordPairsGroup001UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk034]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo008_card, PeriodicMainZeroRecordPairsChunk034_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk034_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo009 ∪ PeriodicMainZeroRecordPairsChunk035

theorem PeriodicMainZeroRecordPairsGroup001UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk035 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo009 PeriodicMainZeroRecordPairsChunk035 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo010_card :
    PeriodicMainZeroRecordPairsGroup001UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk035]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo009_card, PeriodicMainZeroRecordPairsChunk035_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk035_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo010 ∪ PeriodicMainZeroRecordPairsChunk036

theorem PeriodicMainZeroRecordPairsGroup001UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk036 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo010 PeriodicMainZeroRecordPairsChunk036 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo011_card :
    PeriodicMainZeroRecordPairsGroup001UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk036]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo010_card, PeriodicMainZeroRecordPairsChunk036_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk036_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo011 ∪ PeriodicMainZeroRecordPairsChunk037

theorem PeriodicMainZeroRecordPairsGroup001UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk037 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo011 PeriodicMainZeroRecordPairsChunk037 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo012_card :
    PeriodicMainZeroRecordPairsGroup001UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk037]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo011_card, PeriodicMainZeroRecordPairsChunk037_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk037_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo012 ∪ PeriodicMainZeroRecordPairsChunk038

theorem PeriodicMainZeroRecordPairsGroup001UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk038 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo012 PeriodicMainZeroRecordPairsChunk038 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo013_card :
    PeriodicMainZeroRecordPairsGroup001UpTo013.card = 1400 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk038]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo012_card, PeriodicMainZeroRecordPairsChunk038_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk038_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo014 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo013 ∪ PeriodicMainZeroRecordPairsChunk039

theorem PeriodicMainZeroRecordPairsGroup001UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk039 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo013 PeriodicMainZeroRecordPairsChunk039 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo014_card :
    PeriodicMainZeroRecordPairsGroup001UpTo014.card = 1500 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo014, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk039]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo013_card, PeriodicMainZeroRecordPairsChunk039_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo014_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo014 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo013_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk039_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo015 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo014 ∪ PeriodicMainZeroRecordPairsChunk040

theorem PeriodicMainZeroRecordPairsGroup001UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk040 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo014 PeriodicMainZeroRecordPairsChunk040 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo015_card :
    PeriodicMainZeroRecordPairsGroup001UpTo015.card = 1600 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo015, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk040]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo014_card, PeriodicMainZeroRecordPairsChunk040_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo015_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo015 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo014_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk040_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo016 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo015 ∪ PeriodicMainZeroRecordPairsChunk041

theorem PeriodicMainZeroRecordPairsGroup001UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk041 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo015 PeriodicMainZeroRecordPairsChunk041 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo016_card :
    PeriodicMainZeroRecordPairsGroup001UpTo016.card = 1700 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo016, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk041]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo015_card, PeriodicMainZeroRecordPairsChunk041_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo016_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo016 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo015_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk041_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo017 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo016 ∪ PeriodicMainZeroRecordPairsChunk042

theorem PeriodicMainZeroRecordPairsGroup001UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk042 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo016 PeriodicMainZeroRecordPairsChunk042 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo017_card :
    PeriodicMainZeroRecordPairsGroup001UpTo017.card = 1800 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo017, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk042]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo016_card, PeriodicMainZeroRecordPairsChunk042_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo017_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo017 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo016_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk042_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo018 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo017 ∪ PeriodicMainZeroRecordPairsChunk043

theorem PeriodicMainZeroRecordPairsGroup001UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk043 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo017 PeriodicMainZeroRecordPairsChunk043 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo018_card :
    PeriodicMainZeroRecordPairsGroup001UpTo018.card = 1900 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo018, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk043]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo017_card, PeriodicMainZeroRecordPairsChunk043_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo018_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo018 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo017_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk043_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo019 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo018 ∪ PeriodicMainZeroRecordPairsChunk044

theorem PeriodicMainZeroRecordPairsGroup001UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk044 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo018 PeriodicMainZeroRecordPairsChunk044 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo019_card :
    PeriodicMainZeroRecordPairsGroup001UpTo019.card = 2000 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo019, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk044]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo018_card, PeriodicMainZeroRecordPairsChunk044_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo019_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo019 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo018_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk044_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo020 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo019 ∪ PeriodicMainZeroRecordPairsChunk045

theorem PeriodicMainZeroRecordPairsGroup001UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk045 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo019 PeriodicMainZeroRecordPairsChunk045 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo020_card :
    PeriodicMainZeroRecordPairsGroup001UpTo020.card = 2100 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo020, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk045]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo019_card, PeriodicMainZeroRecordPairsChunk045_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo020_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo020 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo020] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo019_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk045_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo021 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo020 ∪ PeriodicMainZeroRecordPairsChunk046

theorem PeriodicMainZeroRecordPairsGroup001UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk046 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo020 PeriodicMainZeroRecordPairsChunk046 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo021_card :
    PeriodicMainZeroRecordPairsGroup001UpTo021.card = 2200 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo021, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk046]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo020_card, PeriodicMainZeroRecordPairsChunk046_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo021_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo021 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo021] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo020_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk046_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo022 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo021 ∪ PeriodicMainZeroRecordPairsChunk047

theorem PeriodicMainZeroRecordPairsGroup001UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk047 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo021 PeriodicMainZeroRecordPairsChunk047 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo022_card :
    PeriodicMainZeroRecordPairsGroup001UpTo022.card = 2300 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo022, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk047]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo021_card, PeriodicMainZeroRecordPairsChunk047_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo022_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo022 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo022] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo021_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk047_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo023 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo022 ∪ PeriodicMainZeroRecordPairsChunk048

theorem PeriodicMainZeroRecordPairsGroup001UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk048 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo022 PeriodicMainZeroRecordPairsChunk048 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo023_card :
    PeriodicMainZeroRecordPairsGroup001UpTo023.card = 2400 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo023, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk048]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo022_card, PeriodicMainZeroRecordPairsChunk048_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo023_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo023 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo023] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo022_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk048_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001UpTo024 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup001UpTo023 ∪ PeriodicMainZeroRecordPairsChunk049

theorem PeriodicMainZeroRecordPairsGroup001UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk049 :
    Disjoint PeriodicMainZeroRecordPairsGroup001UpTo023 PeriodicMainZeroRecordPairsChunk049 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup001UpTo024_card :
    PeriodicMainZeroRecordPairsGroup001UpTo024.card = 2500 := by
  rw [PeriodicMainZeroRecordPairsGroup001UpTo024, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup001UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk049]
  norm_num [PeriodicMainZeroRecordPairsGroup001UpTo023_card, PeriodicMainZeroRecordPairsChunk049_card]

theorem PeriodicMainZeroRecordPairsGroup001UpTo024_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001UpTo024 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup001UpTo024] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup001UpTo023_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk049_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup001 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup001UpTo024

theorem PeriodicMainZeroRecordPairsGroup001_card :
    PeriodicMainZeroRecordPairsGroup001.card = 2500 := by
  simpa [PeriodicMainZeroRecordPairsGroup001] using PeriodicMainZeroRecordPairsGroup001UpTo024_card

theorem PeriodicMainZeroRecordPairsGroup001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup001] using PeriodicMainZeroRecordPairsGroup001UpTo024_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
