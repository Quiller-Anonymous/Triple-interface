import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRowSixRightEvenCommonSixTransport

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/--
Even-window transport for pairs whose two moduli both carry exactly one
extra factor of `2`. This is the q=42 structural surface needed by the
non-coprime core residual: it replaces hard generated arithmetic by reducing
`(2*a, 2*b)` to `(a,b)` at the full-block level.
-/
theorem centeredEvenRamanujanPairOffset_X0_two_mul_two_mul_eq
    {a b k : ℕ} (haOdd : Odd a) (hbOdd : Odd b) :
    centeredEvenRamanujanPairOffset X0 (2 * a) (2 * b) k
      =
    centeredEvenRamanujanPairOffset X0 a b k := by
  unfold centeredEvenRamanujanPairOffset centeredRamanujanPairKernel
  by_cases hEven : Goldbach.Windows.IsEven (X0 + k)
  · rw [if_pos hEven, if_pos hEven]
    rw [centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_commonSix_transport
      (n := a) haOdd hEven]
    rw [centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_commonSix_transport
      (n := b) hbOdd hEven]
  · rw [if_neg hEven, if_neg hEven]

theorem centeredRamanujanPairBlockPeriod_two_mul_two_mul_eq_two_mul
    (a b : ℕ) :
    centeredRamanujanPairBlockPeriod (2 * a) (2 * b)
      =
    2 * centeredRamanujanPairBlockPeriod a b := by
  unfold centeredRamanujanPairBlockPeriod
  rw [Nat.lcm_mul_left]

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_two_mul_eq_two_mul
    {a b : ℕ} (haOdd : Odd a) (hbOdd : Odd b) :
    centeredRamanujanPairFullEvenBlockSum X0 (2 * a) (2 * b)
      =
    2 * centeredRamanujanPairFullEvenBlockSum X0 a b := by
  let P := centeredRamanujanPairBlockPeriod a b
  have hP2 :
      centeredRamanujanPairBlockPeriod (2 * a) (2 * b) = 2 * P := by
    simpa [P] using centeredRamanujanPairBlockPeriod_two_mul_two_mul_eq_two_mul a b
  unfold centeredRamanujanPairFullEvenBlockSum
  rw [hP2]
  have htwoP : 2 * P = P + P := by omega
  rw [htwoP, Finset.sum_range_add]
  have hfirst :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 (2 * a) (2 * b) k)
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 a b k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact centeredEvenRamanujanPairOffset_X0_two_mul_two_mul_eq haOdd hbOdd
  have hsecond :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 (2 * a) (2 * b) (P + k))
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 a b k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [centeredEvenRamanujanPairOffset_X0_two_mul_two_mul_eq haOdd hbOdd]
    simpa [P, Nat.add_comm] using
      centeredEvenRamanujanPairOffset_add_blockPeriod (X := X0) (q := a) (q' := b) (k := k)
  rw [hfirst, hsecond]
  ring

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_two_mul_eq_zero_of_reduced_zero
    {a b : ℕ} (haOdd : Odd a) (hbOdd : Odd b)
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 a b = 0) :
    centeredRamanujanPairFullEvenBlockSum X0 (2 * a) (2 * b) = 0 := by
  rw [centeredRamanujanPairFullEvenBlockSum_X0_two_mul_two_mul_eq_two_mul haOdd hbOdd]
  simp [hzero]

theorem centeredRamanujanPairPeriodicMainTermRat_X0_eq_zero_of_activeSummand_zero
    {a b : ℕ}
    (hneq : a ≠ b)
    (hcoeffA : surrogateNormalizedSigmaTruncSummandCoeffRat a ≠ 0)
    (hcoeffB : surrogateNormalizedSigmaTruncSummandCoeffRat b ≠ 0)
    (hzero : surrogatePeriodicMainActiveOrderedPairSummandRat X0 (a, b) = 0) :
    centeredRamanujanPairPeriodicMainTermRat X0 a b = 0 := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat at hzero
  rw [if_neg hneq] at hzero
  have hprod :
      surrogateNormalizedSigmaTruncSummandCoeffRat a
          * surrogateNormalizedSigmaTruncSummandCoeffRat b ≠ 0 :=
    mul_ne_zero hcoeffA hcoeffB
  rcases mul_eq_zero.mp hzero with hprodZero | htermZero
  · exact False.elim (hprod hprodZero)
  · exact htermZero

theorem centeredRamanujanPairPeriodicMainTerm_X0_eq_zero_of_activeSummand_zero
    {a b : ℕ}
    (hneq : a ≠ b)
    (hcoeffA : surrogateNormalizedSigmaTruncSummandCoeffRat a ≠ 0)
    (hcoeffB : surrogateNormalizedSigmaTruncSummandCoeffRat b ≠ 0)
    (hzero : surrogatePeriodicMainActiveOrderedPairSummandRat X0 (a, b) = 0) :
    centeredRamanujanPairPeriodicMainTerm X0 a b = 0 := by
  rw [centeredRamanujanPairPeriodicMainTerm_eq_ratCast]
  exact_mod_cast
    centeredRamanujanPairPeriodicMainTermRat_X0_eq_zero_of_activeSummand_zero
      hneq hcoeffA hcoeffB hzero

theorem centeredRamanujanPairFullEvenBlockSum_X0_eq_zero_of_activeSummand_zero
    {a b : ℕ}
    (haPos : 1 ≤ a) (hbPos : 1 ≤ b)
    (hneq : a ≠ b)
    (hcoeffA : surrogateNormalizedSigmaTruncSummandCoeffRat a ≠ 0)
    (hcoeffB : surrogateNormalizedSigmaTruncSummandCoeffRat b ≠ 0)
    (hblockScalar :
      0 < (H + 1) / centeredRamanujanPairBlockPeriod a b)
    (hzero : surrogatePeriodicMainActiveOrderedPairSummandRat X0 (a, b) = 0) :
    centeredRamanujanPairFullEvenBlockSum X0 a b = 0 := by
  have hterm :
      centeredRamanujanPairPeriodicMainTerm X0 a b = 0 :=
    centeredRamanujanPairPeriodicMainTerm_X0_eq_zero_of_activeSummand_zero
      hneq hcoeffA hcoeffB hzero
  have hbridge :=
    centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_commonSix_transport
      (X := X0) (q := a) (q' := b) haPos hbPos
  rw [hbridge] at hterm
  simp only [nsmul_eq_mul] at hterm
  have hscalar_ne :
      (((H + 1) / centeredRamanujanPairBlockPeriod a b : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hblockScalar
  rcases mul_eq_zero.mp hterm with hscalar | hblock
  · exact False.elim (hscalar_ne hscalar)
  · exact hblock

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_two_mul_two_mul_eq_zero_of_reduced_active_zero
    {a b : ℕ}
    (haOdd : Odd a) (hbOdd : Odd b)
    (haPos : 1 ≤ a) (hbPos : 1 ≤ b)
    (hneq : a ≠ b)
    (hcoeffA : surrogateNormalizedSigmaTruncSummandCoeffRat a ≠ 0)
    (hcoeffB : surrogateNormalizedSigmaTruncSummandCoeffRat b ≠ 0)
    (hblockScalar :
      0 < (H + 1) / centeredRamanujanPairBlockPeriod a b)
    (hzero : surrogatePeriodicMainActiveOrderedPairSummandRat X0 (a, b) = 0) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X0 (2 * a, 2 * b) = 0 := by
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  have hfullReduced :
      centeredRamanujanPairFullEvenBlockSum X0 a b = 0 :=
    centeredRamanujanPairFullEvenBlockSum_X0_eq_zero_of_activeSummand_zero
      haPos hbPos hneq hcoeffA hcoeffB hblockScalar hzero
  have hfullDoubled :
      centeredRamanujanPairFullEvenBlockSum X0 (2 * a) (2 * b) = 0 :=
    centeredRamanujanPairFullEvenBlockSum_X0_two_mul_two_mul_eq_zero_of_reduced_zero
      haOdd hbOdd hfullReduced
  have htermDoubled :
      centeredRamanujanPairPeriodicMainTerm X0 (2 * a) (2 * b) = 0 := by
    have hbridge :=
      centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_commonSix_transport
        (X := X0) (q := 2 * a) (q' := 2 * b) (by omega) (by omega)
    rw [hbridge, hfullDoubled]
    simp
  by_cases hdiag : (2 * a) = (2 * b)
  · simp [hdiag]
  · simp [hdiag, htermDoubled]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
