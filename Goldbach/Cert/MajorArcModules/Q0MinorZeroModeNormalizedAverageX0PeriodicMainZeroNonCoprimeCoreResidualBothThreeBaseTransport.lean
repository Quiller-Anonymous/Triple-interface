import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeDyadicTransport

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Reduction of every `bothThree` dyadic shape to the odd-core base pair.

For a record `p`, write the odd cores as `a = bothThreeOddCore p.1` and
`b = bothThreeOddCore p.2`.  The structural module proves that each side is
either `3 * core` or `6 * core`.  The dyadic transport module strips the
optional factor `2`, so it remains only to prove the full-block zero for the
base pair `(3 * a, 3 * b)`.
-/

def bothThreeBaseFullBlockZeroAtX0 (p : ℕ × ℕ) : Prop :=
  centeredRamanujanPairFullEvenBlockSum X0
    (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2) = 0

theorem centeredRamanujanPairPeriodicMainTerm_X0_eq_zero_of_bothThree_baseFullBlockZero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (hbase : bothThreeBaseFullBlockZeroAtX0 p) :
    centeredRamanujanPairPeriodicMainTerm X0 p.1 p.2 = 0 := by
  let a := bothThreeOddCore p.1
  let b := bothThreeOddCore p.2
  have haOddCore : Odd a := by
    exact odd_of_not_isEven_for_bothThree_transport
      (by
        simpa [a] using
          PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_odd p hp)
  have hbOddCore : Odd b := by
    exact odd_of_not_isEven_for_bothThree_transport
      (by
        simpa [b] using
          PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_odd p hp)
  have h3aOdd : Odd (3 * a) := by
    exact (by decide : Odd 3).mul haOddCore
  have h3bOdd : Odd (3 * b) := by
    exact (by decide : Odd 3).mul hbOddCore
  have hbase' :
      centeredRamanujanPairFullEvenBlockSum X0 (3 * a) (3 * b) = 0 := by
    simpa [bothThreeBaseFullBlockZeroAtX0, a, b] using hbase
  have h33 :
      centeredRamanujanPairPeriodicMainTerm X0 (3 * a) (3 * b) = 0 := by
    rw [centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_bothThree_probe
      (X := X0) (q := 3 * a) (q' := 3 * b)
      (by exact Nat.mul_pos (by norm_num) haOddCore.pos)
      (by exact Nat.mul_pos (by norm_num) hbOddCore.pos)]
    rw [hbase']
    simp
  rcases
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_eq_three_or_six_mul_core
        p hp with hleft | hleft
  · rcases
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core
          p hp with hright | hright
    · rw [hleft, hright]
      simpa [a, b] using h33
    · rw [hleft, hright]
      rw [show 6 * bothThreeOddCore p.2 = 2 * (3 * b) by
        simp [b]
        ring]
      exact centeredRamanujanPairPeriodicMainTerm_X0_two_mul_right_eq_zero_of_base_full_zero_for_bothThree_transport
        h3aOdd h3bOdd hbase'
  · rcases
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core
          p hp with hright | hright
    · rw [hleft, hright]
      rw [show 6 * bothThreeOddCore p.1 = 2 * (3 * a) by
        simp [a]
        ring]
      exact centeredRamanujanPairPeriodicMainTerm_X0_two_mul_left_eq_zero_of_base_full_zero_for_bothThree_transport
        h3aOdd h3bOdd hbase'
    · rw [hleft, hright]
      rw [show 6 * bothThreeOddCore p.1 = 2 * (3 * a) by
        simp [a]
        ring]
      rw [show 6 * bothThreeOddCore p.2 = 2 * (3 * b) by
        simp [b]
        ring]
      exact centeredRamanujanPairPeriodicMainTerm_X0_two_mul_both_eq_zero_of_base_full_zero_for_bothThree_transport
        h3aOdd h3bOdd hbase'

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_eq_zero_of_bothThree_baseFullBlockZero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (hbase : bothThreeBaseFullBlockZeroAtX0 p) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  have hterm :=
    centeredRamanujanPairPeriodicMainTerm_X0_eq_zero_of_bothThree_baseFullBlockZero
      hp hbase
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · simp [hdiag, hterm]

structure PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeBaseFullBlockZeroCertificateAtX0 :
    Prop where
  baseFullBlockZero_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      bothThreeBaseFullBlockZeroAtX0 p

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_of_baseFullBlockZero
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeBaseFullBlockZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  exact surrogatePeriodicMainActiveOrderedPairSummandRat_X0_eq_zero_of_bothThree_baseFullBlockZero
    hp (cert.baseFullBlockZero_on_records p hp)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
