import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeBaseCenteredRaw

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Structural facts for the odd-core base pair in the `bothThree` residual.

The intended general proof is not a raw finite calculation.  For a record `p`,
write `a = bothThreeOddCore p.1` and `b = bothThreeOddCore p.2`.  The base pair
is `(3 * a, 3 * b)`, and the key reduction is the pointwise factorisation
`R(3a) = R(3) * R(a)` and `R(3b) = R(3) * R(b)`.
-/

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_pos
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs) :
    0 < bothThreeOddCore p.1 := by
  exact (odd_of_not_isEven_for_bothThree_transport
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_odd p hp)).pos

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_pos
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs) :
    0 < bothThreeOddCore p.2 := by
  exact (odd_of_not_isEven_for_bothThree_transport
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_odd p hp)).pos

theorem ramanujanR_bothThree_base_left_eq_three_mul_core
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (N : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * bothThreeOddCore p.1) N
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 N
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR (bothThreeOddCore p.1) N := by
  exact ramanujanR_three_mul_eq_three_mul_for_bothThree
    (r := bothThreeOddCore p.1) (N := N)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hp)

theorem ramanujanR_bothThree_base_right_eq_three_mul_core
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (N : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * bothThreeOddCore p.2) N
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 N
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR (bothThreeOddCore p.2) N := by
  exact ramanujanR_three_mul_eq_three_mul_for_bothThree
    (r := bothThreeOddCore p.2) (N := N)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hp)

theorem ramanujanR_bothThree_base_pair_product_factor
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs)
    (N : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * bothThreeOddCore p.1) N
      * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * bothThreeOddCore p.2) N
      =
    (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 N) ^ 2
      * (Goldbach.AO_OffDiag.TailBlock.ramanujanR (bothThreeOddCore p.1) N
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR (bothThreeOddCore p.2) N) := by
  rw [ramanujanR_bothThree_base_left_eq_three_mul_core hp N]
  rw [ramanujanR_bothThree_base_right_eq_three_mul_core hp N]
  ring

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_cores_coprime
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_odd_cores_coprime
    p hp

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_cores_coprime_three_product
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs) :
    Nat.Coprime 3 (bothThreeOddCore p.1 * bothThreeOddCore p.2) := by
  have h3prime : Nat.Prime 3 := by norm_num
  refine (h3prime.coprime_iff_not_dvd).2 ?_
  intro hdiv
  rcases (h3prime.dvd_mul.mp hdiv) with hleft | hright
  · exact PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hp hleft
  · exact PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hp hright

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
