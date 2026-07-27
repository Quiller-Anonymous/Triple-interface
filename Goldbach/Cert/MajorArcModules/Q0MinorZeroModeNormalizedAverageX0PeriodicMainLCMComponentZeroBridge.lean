import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMWrapperAbs0000_0005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMWrapperAbs0005_0010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMWrapperAbs0010_0015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMWrapperAbs0015_0020
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0000_0001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0001_0002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0002_0003Assembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0003_0005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0005_0006Assembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0006_0007Assembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0007_0010
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0010_0011Assembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0011_0015
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0015_0016
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0016_0017Assembly
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMComponentZeroAbs0017_0020

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Assumption-free bridge from the generated LCM component-zero proofs to the
existing LCM wrapper actual-sum theorems.
-/

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber000_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber000Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber000Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0000_0005Fiber000_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0000_0001Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber001_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber001Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber001Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0000_0005Fiber001_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0001_0002Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber002_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber002Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber002Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0000_0005Fiber002_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0002_0003Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber003_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber003Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber003Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0000_0005Fiber003_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0003_0005Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber004_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber004Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber004Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0000_0005Fiber004_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0003_0005Fiber001_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber005_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber005Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber005Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0005_0010Fiber000_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0005_0006Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber006_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber006Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber006Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0005_0010Fiber001_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0006_0007Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber007_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber007Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber007Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0005_0010Fiber002_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0007_0010Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber008_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber008Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber008Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0005_0010Fiber003_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0007_0010Fiber001_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber009_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber009Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber009Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0005_0010Fiber004_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0007_0010Fiber002_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber010_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber010Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber010Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0010_0015Fiber000_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0010_0011Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber011_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber011Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber011Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0010_0015Fiber001_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber012_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber012Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber012Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0010_0015Fiber002_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber001_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber013_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber013Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber013Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0010_0015Fiber003_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber002_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber014_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber014Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber014Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0010_0015Fiber004_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber003_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber015_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber015Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber015Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0015_0020Fiber000_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0015_0016Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber016_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber016Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber016Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0015_0020Fiber001_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0016_0017Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber017_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber017Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber017Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0015_0020Fiber002_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0017_0020Fiber000_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber018_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber018Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber018Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0015_0020Fiber003_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0017_0020Fiber001_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsFiber019_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber019Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMLCMAbs0000_0020Fiber019Total := by
  exact PeriodicMainNonDyadicLCMLCMWrapAbs0015_0020Fiber004_actual_sum
    PeriodicMainNonDyadicLCMLCMComponentZeroAbs0017_0020Fiber002_componentZeros

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo000_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo000) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0000_0001Fiber000_componentZeros p
    (by simpa [PeriodicMainNonDyadicLCMGroup000PairsUpTo000] using hp)

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo001_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo001) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo000_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0001_0002Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo002_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo002) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo001_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0002_0003Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo003_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo003) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo002_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0003_0005Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo004_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo004) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo003_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0003_0005Fiber001_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo005_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo005) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo004_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0005_0006Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo006_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo006) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo005_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0006_0007Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo007_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo007) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo006_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0007_0010Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo008_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo008) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo007_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0007_0010Fiber001_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo009_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo009) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo008_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0007_0010Fiber002_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo010_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo010) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo010] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo009_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0010_0011Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo011_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo011) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo011] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo010_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo012_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo012) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo012] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo011_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber001_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo013_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo013) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo013] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo012_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber002_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo014_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo014) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo014] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo013_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0011_0015Fiber003_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo015_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo015) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo015] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo014_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0015_0016Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo016_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo016) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo016] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo015_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0016_0017Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo017_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo017) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo017] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo016_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0017_0020Fiber000_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo018_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo018) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo018] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo017_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0017_0020Fiber001_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo019_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000PairsUpTo019) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  rw [PeriodicMainNonDyadicLCMGroup000PairsUpTo019] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo018_componentZeros p hp
  · exact PeriodicMainNonDyadicLCMLCMComponentZeroAbs0017_0020Fiber002_componentZeros p hp

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000_componentZeros
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMGroup000Pairs) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p := by
  exact PeriodicMainNonDyadicLCMComponentZeroAbsGroup000PairsUpTo019_componentZeros p
    (by simpa [PeriodicMainNonDyadicLCMGroup000Pairs] using hp)

theorem PeriodicMainNonDyadicLCMComponentZeroAbsGroup000_actual_sum :
    (∑ p ∈ PeriodicMainNonDyadicLCMGroup000Pairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p)
      = PeriodicMainNonDyadicLCMGroup000Total := by
  exact PeriodicMainNonDyadicLCMGroup000_actual_sum
    PeriodicMainNonDyadicLCMComponentZeroAbsGroup000_componentZeros

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
