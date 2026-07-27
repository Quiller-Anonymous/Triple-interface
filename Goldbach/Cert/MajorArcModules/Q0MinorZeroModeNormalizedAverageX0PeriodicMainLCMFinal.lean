import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainLCMSuperGroup009

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated final LCM assembly for the non-dyadic nonzero periodic-main block. -/

def PeriodicMainNonDyadicLCMPairsUpTo000 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMSuperGroup000Pairs

def PeriodicMainNonDyadicLCMTotalUpTo000 : ℚ :=
  PeriodicMainNonDyadicLCMSuperGroup000Total

def PeriodicMainNonDyadicLCMLCMsUpTo000 : Finset ℕ :=
  PeriodicMainNonDyadicLCMSuperGroup000LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo000_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo000) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo000 := by
  have h := PeriodicMainNonDyadicLCMSuperGroup000_lcm_mem p (by simpa [PeriodicMainNonDyadicLCMPairsUpTo000] using hp)
  simpa [PeriodicMainNonDyadicLCMLCMsUpTo000] using h

theorem PeriodicMainNonDyadicLCMPairsUpTo000_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo000, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo000, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo000 := by
  simpa [PeriodicMainNonDyadicLCMPairsUpTo000, PeriodicMainNonDyadicLCMTotalUpTo000] using
    PeriodicMainNonDyadicLCMSuperGroup000_actual_sum (by
      intro p hp
      exact hzero p (by simpa [PeriodicMainNonDyadicLCMPairsUpTo000] using hp))

def PeriodicMainNonDyadicLCMPairsUpTo001 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo000 ∪ PeriodicMainNonDyadicLCMSuperGroup001Pairs

def PeriodicMainNonDyadicLCMTotalUpTo001 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo000 + PeriodicMainNonDyadicLCMSuperGroup001Total

def PeriodicMainNonDyadicLCMLCMsUpTo001 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo000 ∪ PeriodicMainNonDyadicLCMSuperGroup001LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo000_disjoint_PeriodicMainNonDyadicLCMSuperGroup001Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo000 PeriodicMainNonDyadicLCMSuperGroup001Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo000_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup001_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo001_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo001) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo001 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo001] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo000_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup001_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo001_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo001, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo001, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo001 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo001, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo000_disjoint_PeriodicMainNonDyadicLCMSuperGroup001Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo000_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo001]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup001_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo001]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo002 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo001 ∪ PeriodicMainNonDyadicLCMSuperGroup002Pairs

def PeriodicMainNonDyadicLCMTotalUpTo002 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo001 + PeriodicMainNonDyadicLCMSuperGroup002Total

def PeriodicMainNonDyadicLCMLCMsUpTo002 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo001 ∪ PeriodicMainNonDyadicLCMSuperGroup002LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo001_disjoint_PeriodicMainNonDyadicLCMSuperGroup002Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo001 PeriodicMainNonDyadicLCMSuperGroup002Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo001_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup002_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo002_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo002) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo002 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo002] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo001_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup002_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo002_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo002, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo002, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo002 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo002, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo001_disjoint_PeriodicMainNonDyadicLCMSuperGroup002Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo001_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo002]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup002_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo002]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo003 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo002 ∪ PeriodicMainNonDyadicLCMSuperGroup003Pairs

def PeriodicMainNonDyadicLCMTotalUpTo003 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo002 + PeriodicMainNonDyadicLCMSuperGroup003Total

def PeriodicMainNonDyadicLCMLCMsUpTo003 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo002 ∪ PeriodicMainNonDyadicLCMSuperGroup003LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo002_disjoint_PeriodicMainNonDyadicLCMSuperGroup003Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo002 PeriodicMainNonDyadicLCMSuperGroup003Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo002_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup003_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo003_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo003) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo003 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo003] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo002_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup003_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo003_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo003, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo003, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo003 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo003, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo002_disjoint_PeriodicMainNonDyadicLCMSuperGroup003Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo002_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo003]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup003_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo003]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo004 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo003 ∪ PeriodicMainNonDyadicLCMSuperGroup004Pairs

def PeriodicMainNonDyadicLCMTotalUpTo004 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo003 + PeriodicMainNonDyadicLCMSuperGroup004Total

def PeriodicMainNonDyadicLCMLCMsUpTo004 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo003 ∪ PeriodicMainNonDyadicLCMSuperGroup004LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo003_disjoint_PeriodicMainNonDyadicLCMSuperGroup004Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo003 PeriodicMainNonDyadicLCMSuperGroup004Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo003_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup004_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo004_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo004) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo004 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo004] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo003_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup004_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo004_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo004, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo004, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo004 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo004, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo003_disjoint_PeriodicMainNonDyadicLCMSuperGroup004Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo003_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo004]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup004_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo004]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo005 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo004 ∪ PeriodicMainNonDyadicLCMSuperGroup005Pairs

def PeriodicMainNonDyadicLCMTotalUpTo005 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo004 + PeriodicMainNonDyadicLCMSuperGroup005Total

def PeriodicMainNonDyadicLCMLCMsUpTo005 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo004 ∪ PeriodicMainNonDyadicLCMSuperGroup005LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo004_disjoint_PeriodicMainNonDyadicLCMSuperGroup005Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo004 PeriodicMainNonDyadicLCMSuperGroup005Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo004_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup005_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo005_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo005) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo005 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo005] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo004_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup005_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo005_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo005, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo005, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo005 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo005, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo004_disjoint_PeriodicMainNonDyadicLCMSuperGroup005Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo004_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo005]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup005_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo005]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo006 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo005 ∪ PeriodicMainNonDyadicLCMSuperGroup006Pairs

def PeriodicMainNonDyadicLCMTotalUpTo006 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo005 + PeriodicMainNonDyadicLCMSuperGroup006Total

def PeriodicMainNonDyadicLCMLCMsUpTo006 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo005 ∪ PeriodicMainNonDyadicLCMSuperGroup006LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo005_disjoint_PeriodicMainNonDyadicLCMSuperGroup006Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo005 PeriodicMainNonDyadicLCMSuperGroup006Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo005_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup006_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo006_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo006) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo006 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo006] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo005_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup006_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo006_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo006, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo006, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo006 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo006, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo005_disjoint_PeriodicMainNonDyadicLCMSuperGroup006Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo005_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo006]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup006_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo006]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo007 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo006 ∪ PeriodicMainNonDyadicLCMSuperGroup007Pairs

def PeriodicMainNonDyadicLCMTotalUpTo007 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo006 + PeriodicMainNonDyadicLCMSuperGroup007Total

def PeriodicMainNonDyadicLCMLCMsUpTo007 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo006 ∪ PeriodicMainNonDyadicLCMSuperGroup007LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo006_disjoint_PeriodicMainNonDyadicLCMSuperGroup007Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo006 PeriodicMainNonDyadicLCMSuperGroup007Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo006_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup007_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo007_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo007) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo007 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo007] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo006_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup007_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo007_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo007, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo007, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo007 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo007, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo006_disjoint_PeriodicMainNonDyadicLCMSuperGroup007Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo006_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo007]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup007_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo007]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo008 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo007 ∪ PeriodicMainNonDyadicLCMSuperGroup008Pairs

def PeriodicMainNonDyadicLCMTotalUpTo008 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo007 + PeriodicMainNonDyadicLCMSuperGroup008Total

def PeriodicMainNonDyadicLCMLCMsUpTo008 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo007 ∪ PeriodicMainNonDyadicLCMSuperGroup008LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo007_disjoint_PeriodicMainNonDyadicLCMSuperGroup008Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo007 PeriodicMainNonDyadicLCMSuperGroup008Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo007_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup008_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo008_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo008) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo008 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo008] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo007_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup008_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo008_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo008, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo008, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo008 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo008, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo007_disjoint_PeriodicMainNonDyadicLCMSuperGroup008Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo007_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo008]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup008_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo008]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairsUpTo009 : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo008 ∪ PeriodicMainNonDyadicLCMSuperGroup009Pairs

def PeriodicMainNonDyadicLCMTotalUpTo009 : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo008 + PeriodicMainNonDyadicLCMSuperGroup009Total

def PeriodicMainNonDyadicLCMLCMsUpTo009 : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo008 ∪ PeriodicMainNonDyadicLCMSuperGroup009LCMs

theorem PeriodicMainNonDyadicLCMPairsUpTo008_disjoint_PeriodicMainNonDyadicLCMSuperGroup009Pairs :
    Disjoint PeriodicMainNonDyadicLCMPairsUpTo008 PeriodicMainNonDyadicLCMSuperGroup009Pairs := by
  exact Finset.pair_disjoint_of_lcm_mem
    PeriodicMainNonDyadicLCMPairsUpTo008_lcm_mem
    PeriodicMainNonDyadicLCMSuperGroup009_lcm_mem
    (by native_decide)

theorem PeriodicMainNonDyadicLCMPairsUpTo009_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairsUpTo009) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMsUpTo009 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo009] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union.mpr (Or.inl (PeriodicMainNonDyadicLCMPairsUpTo008_lcm_mem p hp))
  · exact Finset.mem_union.mpr (Or.inr (by
      have h := PeriodicMainNonDyadicLCMSuperGroup009_lcm_mem p hp
      simpa using h))

theorem PeriodicMainNonDyadicLCMPairsUpTo009_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairsUpTo009, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairsUpTo009, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotalUpTo009 := by
  rw [PeriodicMainNonDyadicLCMPairsUpTo009, Finset.sum_union PeriodicMainNonDyadicLCMPairsUpTo008_disjoint_PeriodicMainNonDyadicLCMSuperGroup009Pairs]
  rw [PeriodicMainNonDyadicLCMPairsUpTo008_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo009]
      exact Finset.mem_union.mpr (Or.inl hp)))]
  rw [PeriodicMainNonDyadicLCMSuperGroup009_actual_sum (by
    intro p hp
    exact hzero p (by
      rw [PeriodicMainNonDyadicLCMPairsUpTo009]
      exact Finset.mem_union.mpr (Or.inr hp)))]
  rfl

def PeriodicMainNonDyadicLCMPairs : Finset (ℕ × ℕ) :=
  PeriodicMainNonDyadicLCMPairsUpTo009

def PeriodicMainNonDyadicLCMTotal : ℚ :=
  PeriodicMainNonDyadicLCMTotalUpTo009

def PeriodicMainNonDyadicLCMLCMs : Finset ℕ :=
  PeriodicMainNonDyadicLCMLCMsUpTo009

theorem PeriodicMainNonDyadicLCM_lcm_mem
    (p : ℕ × ℕ) (hp : p ∈ PeriodicMainNonDyadicLCMPairs) :
    Nat.lcm p.1 p.2 ∈ PeriodicMainNonDyadicLCMLCMs := by
  have h := PeriodicMainNonDyadicLCMPairsUpTo009_lcm_mem p (by simpa [PeriodicMainNonDyadicLCMPairs] using hp)
  simpa [PeriodicMainNonDyadicLCMLCMs] using h

theorem PeriodicMainNonDyadicLCM_actual_sum
    (hzero : ∀ p ∈ PeriodicMainNonDyadicLCMPairs, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p) :
    (∑ p ∈ PeriodicMainNonDyadicLCMPairs, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = PeriodicMainNonDyadicLCMTotal := by
  simpa [PeriodicMainNonDyadicLCMPairs, PeriodicMainNonDyadicLCMTotal] using
    PeriodicMainNonDyadicLCMPairsUpTo009_actual_sum (by
      intro p hp
      exact hzero p (by simpa [PeriodicMainNonDyadicLCMPairs] using hp))

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
