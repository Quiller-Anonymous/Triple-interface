import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeStructural

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Split the `bothThree` residual by the gcd of the odd cores exposed in
`BothThreeStructural`.

The first structural probe showed that the clean `(3a, 3b)` coprime-core
orthogonality mechanism cannot cover every record.  This split isolates the
672 records where that mechanism is expected to apply from the 802 records that
need a common-core argument or a generated subcertificate.
-/

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs.filter
    (fun p => Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2))

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs.filter
    (fun p => ¬ Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2))

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs_eq_coprimeCore_union_nonCoprimeCore :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs =
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs := by
  ext p
  constructor
  · intro hp
    by_cases hcop : Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2)
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hp, hcop⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hp, hcop⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with hpCop | hpNon
    · exact (Finset.mem_filter.mp hpCop).1
    · exact (Finset.mem_filter.mp hpNon).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs,
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_mem_bothThree :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs,
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_odd_cores_coprime :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs,
      Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2) := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_odd_cores_not_coprime :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs,
      ¬ Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2) := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2

structure PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeCoreSplitZeroCertificateAtX0 :
    Prop where
  coprimeCore_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs,
      Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2) →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  nonCoprimeCore_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs,
      ¬ Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2) →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_of_coreSplit
    (cert : PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeCoreSplitZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs_eq_coprimeCore_union_nonCoprimeCore] at hp
  rcases Finset.mem_union.mp hp with hpCop | hpNon
  · exact cert.coprimeCore_value_on_records p hpCop
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_odd_cores_coprime
        p hpCop)
  · exact cert.nonCoprimeCore_value_on_records p hpNon
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_odd_cores_not_coprime
        p hpNon)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
