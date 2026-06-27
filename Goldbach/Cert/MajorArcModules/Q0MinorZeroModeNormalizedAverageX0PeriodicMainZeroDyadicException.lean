import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroDyadicExceptionGroup003

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record light union assembly facts for PeriodicMainZeroDyadicExceptionPairs. -/

def PeriodicMainZeroDyadicExceptionPairsUpTo000 : Finset (ℕ × ℕ) := PeriodicMainZeroDyadicExceptionPairsGroup000

theorem PeriodicMainZeroDyadicExceptionPairsUpTo000_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroDyadicExceptionPairsUpTo000 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroDyadicExceptionPairsUpTo000] using PeriodicMainZeroDyadicExceptionPairsGroup000_subset_fullBlockSquarefreeExplicit

def PeriodicMainZeroDyadicExceptionPairsUpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionPairsUpTo000 ∪ PeriodicMainZeroDyadicExceptionPairsGroup001

theorem PeriodicMainZeroDyadicExceptionPairsUpTo001_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroDyadicExceptionPairsUpTo001 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionPairsUpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroDyadicExceptionPairsUpTo000_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroDyadicExceptionPairsGroup001_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroDyadicExceptionPairsUpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionPairsUpTo001 ∪ PeriodicMainZeroDyadicExceptionPairsGroup002

theorem PeriodicMainZeroDyadicExceptionPairsUpTo002_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroDyadicExceptionPairsUpTo002 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionPairsUpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroDyadicExceptionPairsUpTo001_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroDyadicExceptionPairsGroup002_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroDyadicExceptionPairsUpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionPairsUpTo002 ∪ PeriodicMainZeroDyadicExceptionPairsGroup003

theorem PeriodicMainZeroDyadicExceptionPairsUpTo003_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroDyadicExceptionPairsUpTo003 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionPairsUpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainZeroDyadicExceptionPairsUpTo002_subset_fullBlockSquarefreeExplicit hp
  · exact PeriodicMainZeroDyadicExceptionPairsGroup003_subset_fullBlockSquarefreeExplicit hp

def PeriodicMainZeroDyadicExceptionPairs : Finset (ℕ × ℕ) := PeriodicMainZeroDyadicExceptionPairsUpTo003

theorem PeriodicMainZeroDyadicExceptionPairs_card :
    PeriodicMainZeroDyadicExceptionPairs.card = 9654 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionPairs_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroDyadicExceptionPairs ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  simpa [PeriodicMainZeroDyadicExceptionPairs] using PeriodicMainZeroDyadicExceptionPairsUpTo003_subset_fullBlockSquarefreeExplicit

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
