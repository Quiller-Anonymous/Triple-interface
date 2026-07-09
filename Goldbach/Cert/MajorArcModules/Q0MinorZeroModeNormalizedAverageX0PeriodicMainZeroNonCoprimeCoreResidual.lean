import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRightThreeSix

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
The final non-coprime dyadic core residual surface.

After removing row `3`/`6` and right-column `3`/`6`, every remaining
non-coprime dyadic zero record still carries a factor `3` on at least one side.
This split preserves that structure for the last zero certificate instead of
falling back to one raw 2972-record payload.
-/
def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs.filter
    (fun p => 3 ∣ p.1 ∧ ¬ 3 ∣ p.2)

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs.filter
    (fun p => ¬ 3 ∣ p.1 ∧ 3 ∣ p.2)

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs.filter
    (fun p => 3 ∣ p.1 ∧ 3 ∣ p.2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs_eq_leftOnlyThree_union_rightOnlyThree_union_bothThree :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs =
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs ∪
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs) ∪
          PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs.card = 749 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs.card = 749 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs_card :
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs.card = 1474 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_left_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      3 ∣ p.1 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_right_not_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      ¬ 3 ∣ p.2 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.2

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_left_not_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs,
      ¬ 3 ∣ p.1 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_right_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs,
      3 ∣ p.2 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.2

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      3 ∣ p.1 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_dvd_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      3 ∣ p.2 := by
  intro p hp
  exact (Finset.mem_filter.mp hp).2.2

structure PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0 :
    Prop where
  leftOnlyThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThreePairs,
      3 ∣ p.1 →
        ¬ 3 ∣ p.2 →
          surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  rightOnlyThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThreePairs,
      ¬ 3 ∣ p.1 →
        3 ∣ p.2 →
          surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  bothThree_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      3 ∣ p.1 →
        3 ∣ p.2 →
          surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidual_value_on_records_of_divisibility
    (cert : PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualPairs_eq_leftOnlyThree_union_rightOnlyThree_union_bothThree] at hp
  rcases Finset.mem_union.mp hp with hpLeft | hpBoth
  · rcases Finset.mem_union.mp hpLeft with hpLeftOnly | hpRightOnly
    · exact cert.leftOnlyThree_value_on_records p hpLeftOnly
        (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_left_dvd_three
          p hpLeftOnly)
        (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualLeftOnlyThree_right_not_dvd_three
          p hpLeftOnly)
    · exact cert.rightOnlyThree_value_on_records p hpRightOnly
        (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_left_not_dvd_three
          p hpRightOnly)
        (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualRightOnlyThree_right_dvd_three
          p hpRightOnly)
  · exact cert.bothThree_value_on_records p hpBoth
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_dvd_three p hpBoth)
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_dvd_three p hpBoth)

theorem PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_commonFactorSurfaces
    (rowCert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0)
    (rightCert :
      PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0)
    (coreCert : PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0 := by
  exact
    PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_rowThreeSixCommonFactor_rightThreeSixCommonFactor
      rowCert rightCert
      (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidual_value_on_records_of_divisibility
        coreCert)

theorem PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_commonFactorSurfaces
    (rowCert : PeriodicMainDyadicExceptionNonCoprimeRowThreeSixCommonFactorZeroCertificateAtX0)
    (rightCert :
      PeriodicMainDyadicExceptionNonCoprimeResidualRightThreeSixCommonFactorZeroCertificateAtX0)
    (coreCert : PeriodicMainDyadicExceptionNonCoprimeCoreResidualDivisibilityZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainFullBlockOrderedPairSupportExplicit,
      p ∉ PeriodicMainNonzeroRecordPairs →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  exact PeriodicMainFullBlockExplicit_zero_off_nonzeroRecordPairs_of_nonCoprimeReduced
    (PeriodicMainDyadicExceptionNonCoprimeReducedZeroCertificateAtX0_of_commonFactorSurfaces
      rowCert rightCert coreCert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
