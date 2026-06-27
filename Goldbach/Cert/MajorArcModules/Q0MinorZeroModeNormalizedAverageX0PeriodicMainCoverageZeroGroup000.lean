import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk009
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk011
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk012
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk013
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk014
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk016
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk017
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk018
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk019
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk020
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk021
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk022
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk023
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainCoverageZeroChunk024

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record union assembly facts for PeriodicMainZeroRecordPairsGroup000. -/

def PeriodicMainZeroRecordPairsGroup000UpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsChunk000

theorem PeriodicMainZeroRecordPairsGroup000UpTo000_card :
    PeriodicMainZeroRecordPairsGroup000UpTo000.card = 100 := by
  simpa [PeriodicMainZeroRecordPairsGroup000UpTo000] using PeriodicMainZeroRecordPairsChunk000_card

theorem PeriodicMainZeroRecordPairsGroup000UpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup000UpTo000] using PeriodicMainZeroRecordPairsChunk000_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroRecordPairsGroup000UpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo000 ∪ PeriodicMainZeroRecordPairsChunk001

theorem PeriodicMainZeroRecordPairsGroup000UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk001 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo000 PeriodicMainZeroRecordPairsChunk001 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo001_card :
    PeriodicMainZeroRecordPairsGroup000UpTo001.card = 200 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo001, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo000_disjoint_PeriodicMainZeroRecordPairsChunk001]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo000_card, PeriodicMainZeroRecordPairsChunk001_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk001_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo001 ∪ PeriodicMainZeroRecordPairsChunk002

theorem PeriodicMainZeroRecordPairsGroup000UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk002 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo001 PeriodicMainZeroRecordPairsChunk002 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo002_card :
    PeriodicMainZeroRecordPairsGroup000UpTo002.card = 300 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo002, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo001_disjoint_PeriodicMainZeroRecordPairsChunk002]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo001_card, PeriodicMainZeroRecordPairsChunk002_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk002_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo002 ∪ PeriodicMainZeroRecordPairsChunk003

theorem PeriodicMainZeroRecordPairsGroup000UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk003 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo002 PeriodicMainZeroRecordPairsChunk003 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo003_card :
    PeriodicMainZeroRecordPairsGroup000UpTo003.card = 400 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo003, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo002_disjoint_PeriodicMainZeroRecordPairsChunk003]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo002_card, PeriodicMainZeroRecordPairsChunk003_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk003_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo003 ∪ PeriodicMainZeroRecordPairsChunk004

theorem PeriodicMainZeroRecordPairsGroup000UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk004 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo003 PeriodicMainZeroRecordPairsChunk004 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo004_card :
    PeriodicMainZeroRecordPairsGroup000UpTo004.card = 500 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo004, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo003_disjoint_PeriodicMainZeroRecordPairsChunk004]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo003_card, PeriodicMainZeroRecordPairsChunk004_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo004_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo004 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo003_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk004_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo004 ∪ PeriodicMainZeroRecordPairsChunk005

theorem PeriodicMainZeroRecordPairsGroup000UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk005 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo004 PeriodicMainZeroRecordPairsChunk005 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo005_card :
    PeriodicMainZeroRecordPairsGroup000UpTo005.card = 600 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo005, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo004_disjoint_PeriodicMainZeroRecordPairsChunk005]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo004_card, PeriodicMainZeroRecordPairsChunk005_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo005_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo005 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo004_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk005_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo005 ∪ PeriodicMainZeroRecordPairsChunk006

theorem PeriodicMainZeroRecordPairsGroup000UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk006 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo005 PeriodicMainZeroRecordPairsChunk006 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo006_card :
    PeriodicMainZeroRecordPairsGroup000UpTo006.card = 700 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo006, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo005_disjoint_PeriodicMainZeroRecordPairsChunk006]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo005_card, PeriodicMainZeroRecordPairsChunk006_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo006_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo006 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo005_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk006_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo006 ∪ PeriodicMainZeroRecordPairsChunk007

theorem PeriodicMainZeroRecordPairsGroup000UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk007 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo006 PeriodicMainZeroRecordPairsChunk007 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo007_card :
    PeriodicMainZeroRecordPairsGroup000UpTo007.card = 800 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo007, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo006_disjoint_PeriodicMainZeroRecordPairsChunk007]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo006_card, PeriodicMainZeroRecordPairsChunk007_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo007_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo007 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo006_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk007_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo007 ∪ PeriodicMainZeroRecordPairsChunk008

theorem PeriodicMainZeroRecordPairsGroup000UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk008 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo007 PeriodicMainZeroRecordPairsChunk008 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo008_card :
    PeriodicMainZeroRecordPairsGroup000UpTo008.card = 900 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo008, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo007_disjoint_PeriodicMainZeroRecordPairsChunk008]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo007_card, PeriodicMainZeroRecordPairsChunk008_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo008_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo008 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo007_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk008_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo008 ∪ PeriodicMainZeroRecordPairsChunk009

theorem PeriodicMainZeroRecordPairsGroup000UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk009 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo008 PeriodicMainZeroRecordPairsChunk009 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo009_card :
    PeriodicMainZeroRecordPairsGroup000UpTo009.card = 1000 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo009, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo008_disjoint_PeriodicMainZeroRecordPairsChunk009]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo008_card, PeriodicMainZeroRecordPairsChunk009_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo009_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo009 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo008_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk009_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo010 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo009 ∪ PeriodicMainZeroRecordPairsChunk010

theorem PeriodicMainZeroRecordPairsGroup000UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk010 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo009 PeriodicMainZeroRecordPairsChunk010 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo010_card :
    PeriodicMainZeroRecordPairsGroup000UpTo010.card = 1100 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo010, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo009_disjoint_PeriodicMainZeroRecordPairsChunk010]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo009_card, PeriodicMainZeroRecordPairsChunk010_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo010_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo010 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo009_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk010_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo011 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo010 ∪ PeriodicMainZeroRecordPairsChunk011

theorem PeriodicMainZeroRecordPairsGroup000UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk011 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo010 PeriodicMainZeroRecordPairsChunk011 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo011_card :
    PeriodicMainZeroRecordPairsGroup000UpTo011.card = 1200 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo011, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo010_disjoint_PeriodicMainZeroRecordPairsChunk011]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo010_card, PeriodicMainZeroRecordPairsChunk011_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo011_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo011 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo010_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk011_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo012 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo011 ∪ PeriodicMainZeroRecordPairsChunk012

theorem PeriodicMainZeroRecordPairsGroup000UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk012 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo011 PeriodicMainZeroRecordPairsChunk012 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo012_card :
    PeriodicMainZeroRecordPairsGroup000UpTo012.card = 1300 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo012, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo011_disjoint_PeriodicMainZeroRecordPairsChunk012]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo011_card, PeriodicMainZeroRecordPairsChunk012_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo012_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo012 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo011_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk012_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo013 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo012 ∪ PeriodicMainZeroRecordPairsChunk013

theorem PeriodicMainZeroRecordPairsGroup000UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk013 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo012 PeriodicMainZeroRecordPairsChunk013 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo013_card :
    PeriodicMainZeroRecordPairsGroup000UpTo013.card = 1400 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo013, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo012_disjoint_PeriodicMainZeroRecordPairsChunk013]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo012_card, PeriodicMainZeroRecordPairsChunk013_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo013_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo013 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo012_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk013_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo014 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo013 ∪ PeriodicMainZeroRecordPairsChunk014

theorem PeriodicMainZeroRecordPairsGroup000UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk014 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo013 PeriodicMainZeroRecordPairsChunk014 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo014_card :
    PeriodicMainZeroRecordPairsGroup000UpTo014.card = 1500 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo014, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo013_disjoint_PeriodicMainZeroRecordPairsChunk014]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo013_card, PeriodicMainZeroRecordPairsChunk014_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo014_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo014 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo013_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk014_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo015 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo014 ∪ PeriodicMainZeroRecordPairsChunk015

theorem PeriodicMainZeroRecordPairsGroup000UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk015 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo014 PeriodicMainZeroRecordPairsChunk015 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo015_card :
    PeriodicMainZeroRecordPairsGroup000UpTo015.card = 1600 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo015, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo014_disjoint_PeriodicMainZeroRecordPairsChunk015]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo014_card, PeriodicMainZeroRecordPairsChunk015_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo015_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo015 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo014_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk015_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo016 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo015 ∪ PeriodicMainZeroRecordPairsChunk016

theorem PeriodicMainZeroRecordPairsGroup000UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk016 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo015 PeriodicMainZeroRecordPairsChunk016 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo016_card :
    PeriodicMainZeroRecordPairsGroup000UpTo016.card = 1700 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo016, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo015_disjoint_PeriodicMainZeroRecordPairsChunk016]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo015_card, PeriodicMainZeroRecordPairsChunk016_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo016_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo016 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo015_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk016_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo017 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo016 ∪ PeriodicMainZeroRecordPairsChunk017

theorem PeriodicMainZeroRecordPairsGroup000UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk017 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo016 PeriodicMainZeroRecordPairsChunk017 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo017_card :
    PeriodicMainZeroRecordPairsGroup000UpTo017.card = 1800 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo017, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo016_disjoint_PeriodicMainZeroRecordPairsChunk017]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo016_card, PeriodicMainZeroRecordPairsChunk017_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo017_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo017 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo016_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk017_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo018 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo017 ∪ PeriodicMainZeroRecordPairsChunk018

theorem PeriodicMainZeroRecordPairsGroup000UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk018 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo017 PeriodicMainZeroRecordPairsChunk018 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo018_card :
    PeriodicMainZeroRecordPairsGroup000UpTo018.card = 1900 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo018, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo017_disjoint_PeriodicMainZeroRecordPairsChunk018]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo017_card, PeriodicMainZeroRecordPairsChunk018_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo018_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo018 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo017_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk018_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo019 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo018 ∪ PeriodicMainZeroRecordPairsChunk019

theorem PeriodicMainZeroRecordPairsGroup000UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk019 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo018 PeriodicMainZeroRecordPairsChunk019 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo019_card :
    PeriodicMainZeroRecordPairsGroup000UpTo019.card = 2000 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo019, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo018_disjoint_PeriodicMainZeroRecordPairsChunk019]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo018_card, PeriodicMainZeroRecordPairsChunk019_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo019_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo019 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo018_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk019_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo020 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo019 ∪ PeriodicMainZeroRecordPairsChunk020

theorem PeriodicMainZeroRecordPairsGroup000UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk020 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo019 PeriodicMainZeroRecordPairsChunk020 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo020_card :
    PeriodicMainZeroRecordPairsGroup000UpTo020.card = 2100 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo020, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo019_disjoint_PeriodicMainZeroRecordPairsChunk020]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo019_card, PeriodicMainZeroRecordPairsChunk020_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo020_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo020 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo020] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo019_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk020_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo021 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo020 ∪ PeriodicMainZeroRecordPairsChunk021

theorem PeriodicMainZeroRecordPairsGroup000UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk021 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo020 PeriodicMainZeroRecordPairsChunk021 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo021_card :
    PeriodicMainZeroRecordPairsGroup000UpTo021.card = 2200 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo021, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo020_disjoint_PeriodicMainZeroRecordPairsChunk021]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo020_card, PeriodicMainZeroRecordPairsChunk021_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo021_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo021 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo021] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo020_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk021_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo022 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo021 ∪ PeriodicMainZeroRecordPairsChunk022

theorem PeriodicMainZeroRecordPairsGroup000UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk022 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo021 PeriodicMainZeroRecordPairsChunk022 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo022_card :
    PeriodicMainZeroRecordPairsGroup000UpTo022.card = 2300 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo022, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo021_disjoint_PeriodicMainZeroRecordPairsChunk022]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo021_card, PeriodicMainZeroRecordPairsChunk022_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo022_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo022 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo022] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo021_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk022_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo023 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo022 ∪ PeriodicMainZeroRecordPairsChunk023

theorem PeriodicMainZeroRecordPairsGroup000UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk023 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo022 PeriodicMainZeroRecordPairsChunk023 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo023_card :
    PeriodicMainZeroRecordPairsGroup000UpTo023.card = 2400 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo023, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo022_disjoint_PeriodicMainZeroRecordPairsChunk023]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo022_card, PeriodicMainZeroRecordPairsChunk023_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo023_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo023 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo023] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo022_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk023_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000UpTo024 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroRecordPairsGroup000UpTo023 ∪ PeriodicMainZeroRecordPairsChunk024

theorem PeriodicMainZeroRecordPairsGroup000UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk024 :
    Disjoint PeriodicMainZeroRecordPairsGroup000UpTo023 PeriodicMainZeroRecordPairsChunk024 := by
  native_decide

theorem PeriodicMainZeroRecordPairsGroup000UpTo024_card :
    PeriodicMainZeroRecordPairsGroup000UpTo024.card = 2500 := by
  rw [PeriodicMainZeroRecordPairsGroup000UpTo024, Finset.card_union_of_disjoint PeriodicMainZeroRecordPairsGroup000UpTo023_disjoint_PeriodicMainZeroRecordPairsChunk024]
  norm_num [PeriodicMainZeroRecordPairsGroup000UpTo023_card, PeriodicMainZeroRecordPairsChunk024_card]

theorem PeriodicMainZeroRecordPairsGroup000UpTo024_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000UpTo024 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroRecordPairsGroup000UpTo024] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroRecordPairsGroup000UpTo023_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroRecordPairsChunk024_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroRecordPairsGroup000 : Finset (ℕ × ℕ) := PeriodicMainZeroRecordPairsGroup000UpTo024

theorem PeriodicMainZeroRecordPairsGroup000_card :
    PeriodicMainZeroRecordPairsGroup000.card = 2500 := by
  simpa [PeriodicMainZeroRecordPairsGroup000] using PeriodicMainZeroRecordPairsGroup000UpTo024_card

theorem PeriodicMainZeroRecordPairsGroup000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsGroup000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroRecordPairsGroup000] using PeriodicMainZeroRecordPairsGroup000UpTo024_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
