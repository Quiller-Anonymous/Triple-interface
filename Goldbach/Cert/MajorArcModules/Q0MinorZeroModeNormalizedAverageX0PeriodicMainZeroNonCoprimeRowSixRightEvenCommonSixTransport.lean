import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRowThreeSix
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeRowThreeRightOddFinal

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private theorem isEven_of_mem_EvenIn_for_commonSix_transport
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    Goldbach.Windows.IsEven N := by
  unfold EvenIn IccShift at hN
  exact (Finset.mem_filter.mp hN).2

theorem gcd_odd_two_mul_eq_for_commonSix_transport
    {n k : ℕ} (hnOdd : Odd n) :
    Nat.gcd n (2 * k) = Nat.gcd n k := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  have h := Nat.Coprime.gcd_mul_left_cancel (k := 2) (m := k) (n := n) hcop
  simpa [Nat.gcd_comm, Nat.mul_comm] using h

theorem totient_two_mul_eq_of_odd_for_commonSix_transport
    {n : ℕ} (hnOdd : Odd n) :
    Nat.totient (2 * n) = Nat.totient n := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  rw [Nat.totient_mul hcop]
  norm_num

theorem ramanujanR_two_mul_eq_of_isEven_of_odd_for_commonSix_transport
    {n N : ℕ} (hnOdd : Odd n) (hNEven : Goldbach.Windows.IsEven N) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
      = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N := by
  have hnpos : 0 < n := hnOdd.pos
  rcases (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hNEven) with ⟨k, hk⟩
  subst hk
  set d : ℕ := Nat.gcd n k
  have hgcdn : Nat.gcd n (2 * k) = d := by
    simpa [d] using gcd_odd_two_mul_eq_for_commonSix_transport (n := n) (k := k) hnOdd
  have hgcd2n : Nat.gcd (2 * n) (2 * k) = 2 * d := by
    simpa [d, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.gcd_mul_left 2 n k)
  have hdvd : d ∣ n := by
    simpa [d] using Nat.gcd_dvd_left n k
  have hdpos : 0 < d := by
    simpa [d] using Nat.gcd_pos_of_pos_left k hnpos
  have hdOdd : Odd d := by
    have hnotEven : ¬ Even d := by
      intro hdEven
      rcases hdvd with ⟨m, hm⟩
      rcases hdEven with ⟨c, hc⟩
      have hnEven : Even n := by
        refine ⟨c * m, ?_⟩
        rw [hm, hc]
        ring
      exact (Nat.not_even_iff_odd.mpr hnOdd) hnEven
    exact Nat.not_even_iff_odd.mp hnotEven
  have hquot : (2 * n) / (2 * d) = n / d := by
    apply Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2 * d)
    calc
      2 * n = 2 * ((n / d) * d) := by rw [Nat.div_mul_cancel hdvd]
      _ = (n / d) * (2 * d) := by ring
  have hphi : Nat.totient (2 * d) = Nat.totient d :=
    totient_two_mul_eq_of_odd_for_commonSix_transport hdOdd
  rw [ramanujanR_eq_moebius_mul_totient_gcd, ramanujanR_eq_moebius_mul_totient_gcd]
  rw [hgcd2n, hgcdn, hquot, hphi]

theorem ramanujanWindowAverage_two_mul_eq_of_odd_for_commonSix_transport
    {X n : ℕ} (hnOdd : Odd n) :
    ramanujanWindowAverage X (2 * n) = ramanujanWindowAverage X n := by
  unfold ramanujanWindowAverage
  refine congrArg ((((EvenIn X H).card : ℝ)⁻¹) * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact ramanujanR_two_mul_eq_of_isEven_of_odd_for_commonSix_transport hnOdd
    (isEven_of_mem_EvenIn_for_commonSix_transport hN)

theorem centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_commonSix_transport
    {n N : ℕ} (hnOdd : Odd n) (hNEven : Goldbach.Windows.IsEven N) :
    centeredRamanujanObservable X0 (2 * n) N
      = centeredRamanujanObservable X0 n N := by
  calc
    centeredRamanujanObservable X0 (2 * n) N
      = Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
          - ramanujanWindowAverage X0 n := by
            simp [centeredRamanujanObservable,
              ramanujanWindowAverage_two_mul_eq_of_odd_for_commonSix_transport hnOdd]
    _ = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N
          - ramanujanWindowAverage X0 n := by
            rw [ramanujanR_two_mul_eq_of_isEven_of_odd_for_commonSix_transport hnOdd
              hNEven]
    _ = centeredRamanujanObservable X0 n N := by
            rfl

theorem centeredRamanujanObservable_X0_two_mul_eq_of_odd_for_commonSix_transport
    {n N : ℕ} (hnOdd : Odd n) (hN : N ∈ EvenIn X0 H) :
    centeredRamanujanObservable X0 (2 * n) N
      = centeredRamanujanObservable X0 n N := by
  exact centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_commonSix_transport
    hnOdd (isEven_of_mem_EvenIn_for_commonSix_transport hN)

theorem centeredEvenRamanujanPairOffset_X0_six_two_mul_eq_three
    {n k : ℕ} (hnOdd : Odd n) :
    centeredEvenRamanujanPairOffset X0 6 (2 * n) k
      =
    centeredEvenRamanujanPairOffset X0 3 n k := by
  unfold centeredEvenRamanujanPairOffset centeredRamanujanPairKernel
  by_cases hEven : Goldbach.Windows.IsEven (X0 + k)
  · rw [if_pos hEven, if_pos hEven]
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    rw [centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_commonSix_transport
      (n := 3) (by decide) hEven]
    rw [centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_commonSix_transport
      (n := n) hnOdd hEven]
  · rw [if_neg hEven, if_neg hEven]

theorem centeredEvenRamanujanPairOffset_eq_sum_gcdClassOffsets_for_commonSix_transport
    {X q q' k : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredEvenRamanujanPairOffset X q q' k
      =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * centeredEvenRamanujanGcdClassPairOffset X q q' g h k := by
  unfold centeredEvenRamanujanPairOffset centeredRamanujanPairKernel
    centeredEvenRamanujanGcdClassPairOffset centeredRamanujanGcdClassPairKernel
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · simp [hEven]
    rw [centeredRamanujanObservable_eq_sum_centeredGcdClasses
      (X := X) (q := q) (N := X + k) hq]
    rw [centeredRamanujanObservable_eq_sum_centeredGcdClasses
      (X := X) (q := q') (N := X + k) hq']
    calc
      (∑ g ∈ q.divisors,
          ramanujanGcdClassCoeff q g * centeredRamanujanGcdClassObservable X q g (X + k))
        * (∑ h ∈ q'.divisors,
          ramanujanGcdClassCoeff q' h * centeredRamanujanGcdClassObservable X q' h (X + k))
          =
        ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
          (ramanujanGcdClassCoeff q g * centeredRamanujanGcdClassObservable X q g (X + k))
            * (ramanujanGcdClassCoeff q' h
                * centeredRamanujanGcdClassObservable X q' h (X + k)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro g _hg
            rw [Finset.mul_sum]
      _ =
        ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
          ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
            * (centeredRamanujanGcdClassObservable X q g (X + k)
                * centeredRamanujanGcdClassObservable X q' h (X + k)) := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            refine Finset.sum_congr rfl ?_
            intro h _hh
            ring
  · simp [hEven]

theorem centeredRamanujanPairBlockPeriod_six_two_mul_eq_two_mul_three
    (n : ℕ) :
    centeredRamanujanPairBlockPeriod 6 (2 * n)
      =
    2 * centeredRamanujanPairBlockPeriod 3 n := by
  unfold centeredRamanujanPairBlockPeriod
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  rw [Nat.lcm_mul_left]

theorem centeredRamanujanPairFullEvenBlockSum_X0_six_two_mul_eq_two_mul_three
    {n : ℕ} (hnOdd : Odd n) :
    centeredRamanujanPairFullEvenBlockSum X0 6 (2 * n)
      =
    2 * centeredRamanujanPairFullEvenBlockSum X0 3 n := by
  let P := centeredRamanujanPairBlockPeriod 3 n
  have hP6 :
      centeredRamanujanPairBlockPeriod 6 (2 * n) = 2 * P := by
    simpa [P] using centeredRamanujanPairBlockPeriod_six_two_mul_eq_two_mul_three n
  unfold centeredRamanujanPairFullEvenBlockSum
  rw [hP6]
  have htwoP : 2 * P = P + P := by omega
  rw [htwoP, Finset.sum_range_add]
  have hfirst :
      (∑ k ∈ Finset.range P, centeredEvenRamanujanPairOffset X0 6 (2 * n) k)
        =
      (∑ k ∈ Finset.range P, centeredEvenRamanujanPairOffset X0 3 n k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact centeredEvenRamanujanPairOffset_X0_six_two_mul_eq_three hnOdd
  have hsecond :
      (∑ k ∈ Finset.range P, centeredEvenRamanujanPairOffset X0 6 (2 * n) (P + k))
        =
      (∑ k ∈ Finset.range P, centeredEvenRamanujanPairOffset X0 3 n k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [centeredEvenRamanujanPairOffset_X0_six_two_mul_eq_three hnOdd]
    simpa [P, Nat.add_comm] using
      centeredEvenRamanujanPairOffset_add_blockPeriod (X := X0) (q := 3) (q' := n) (k := k)
  rw [hfirst, hsecond]
  ring

theorem centeredRamanujanPairFullEvenBlockSum_X0_six_two_mul_eq_zero_of_three_zero
    {n : ℕ} (hnOdd : Odd n)
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 3 n = 0) :
    centeredRamanujanPairFullEvenBlockSum X0 6 (2 * n) = 0 := by
  rw [centeredRamanujanPairFullEvenBlockSum_X0_six_two_mul_eq_two_mul_three hnOdd]
  simp [hzero]

theorem centeredRamanujanPairFullEvenBlockSum_eq_sum_gcdClassFullEvenBlockSums_for_commonSix_transport
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairFullEvenBlockSum X q q'
      =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * centeredRamanujanGcdClassPairFullEvenBlockSum X q q' g h := by
  unfold centeredRamanujanPairFullEvenBlockSum centeredRamanujanGcdClassPairFullEvenBlockSum
  calc
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
        centeredEvenRamanujanPairOffset X q q' k
      =
    ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
      ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
          * centeredEvenRamanujanGcdClassPairOffset X q q' g h k := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        exact centeredEvenRamanujanPairOffset_eq_sum_gcdClassOffsets_for_commonSix_transport
          hq hq'
    _ =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
        ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
          * centeredEvenRamanujanGcdClassPairOffset X q q' g h k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro g _hg
        rw [Finset.sum_comm]
    _ =
    ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
      ramanujanGcdClassCoeff q g * ramanujanGcdClassCoeff q' h
        * ∑ k ∈ Finset.range (centeredRamanujanPairBlockPeriod q q'),
          centeredEvenRamanujanGcdClassPairOffset X q q' g h k := by
        refine Finset.sum_congr rfl ?_
        intro g _hg
        refine Finset.sum_congr rfl ?_
        intro h _hh
        rw [Finset.mul_sum]

theorem centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_commonSix_transport
    {X q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    centeredRamanujanPairPeriodicMainTerm X q q'
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q') : ℕ)
      • centeredRamanujanPairFullEvenBlockSum X q q' := by
  rw [centeredRamanujanPairFullEvenBlockSum_eq_sum_gcdClassFullEvenBlockSums_for_commonSix_transport
    hq hq']
  unfold centeredRamanujanPairPeriodicMainTerm
  simp only [nsmul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro g hg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h hh
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_resolved_periodic_comparison
    hq hq' hg hh]
  ring

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_mem_rowThreeRightOdd :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      (3, p.2 / 2) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_left_eq_six :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      p.1 = 6 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_right_eq_two_mul_halved :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      p.2 = 2 * (p.2 / 2) := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_ne_three :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      3 ≠ p.2 / 2 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_pos :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      1 ≤ p.2 / 2 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_coeff_ne_zero :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      surrogateNormalizedSigmaTruncSummandCoeffRat (p.2 / 2) ≠ 0 := by
  native_decide

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_blockScalar_pos :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      0 < (H + 1) / centeredRamanujanPairBlockPeriod 3 (p.2 / 2) := by
  native_decide

theorem centeredRamanujanPairPeriodicMainTermRat_X0_three_halved_eq_zero_of_commonSix
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs) :
    centeredRamanujanPairPeriodicMainTermRat X0 3 (p.2 / 2) = 0 := by
  have hpHalf :
      (3, p.2 / 2) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_mem_rowThreeRightOdd
      p hp
  have hrow :
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 (3, p.2 / 2) = 0 :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOdd_value_on_records_generated
      (3, p.2 / 2) hpHalf
  have hneq : (3 : ℕ) ≠ p.2 / 2 :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_ne_three p hp
  have hcoeff3 : surrogateNormalizedSigmaTruncSummandCoeffRat 3 ≠ 0 := by
    native_decide
  have hcoeffRight :
      surrogateNormalizedSigmaTruncSummandCoeffRat (p.2 / 2) ≠ 0 :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_coeff_ne_zero p hp
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat at hrow
  rw [if_neg hneq] at hrow
  have hprod :
      surrogateNormalizedSigmaTruncSummandCoeffRat 3
          * surrogateNormalizedSigmaTruncSummandCoeffRat (p.2 / 2) ≠ 0 :=
    mul_ne_zero hcoeff3 hcoeffRight
  have hzero := mul_eq_zero.mp hrow
  rcases hzero with hprodZero | htermZero
  · exact False.elim (hprod hprodZero)
  · exact htermZero

theorem centeredRamanujanPairPeriodicMainTerm_X0_three_halved_eq_zero_of_commonSix
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs) :
    centeredRamanujanPairPeriodicMainTerm X0 3 (p.2 / 2) = 0 := by
  rw [centeredRamanujanPairPeriodicMainTerm_eq_ratCast]
  exact_mod_cast
    centeredRamanujanPairPeriodicMainTermRat_X0_three_halved_eq_zero_of_commonSix hp

theorem centeredRamanujanPairFullEvenBlockSum_X0_three_halved_eq_zero_of_commonSix
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs) :
    centeredRamanujanPairFullEvenBlockSum X0 3 (p.2 / 2) = 0 := by
  have hterm :=
    centeredRamanujanPairPeriodicMainTerm_X0_three_halved_eq_zero_of_commonSix hp
  have hbridge :=
    centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_commonSix_transport
      (X := X0) (q := 3) (q' := p.2 / 2) (by norm_num)
      (PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_pos p hp)
  rw [hbridge] at hterm
  simp only [nsmul_eq_mul] at hterm
  have hscalar_ne :
      (((H + 1) / centeredRamanujanPairBlockPeriod 3 (p.2 / 2) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_blockScalar_pos p hp)
  rcases mul_eq_zero.mp hterm with hscalar | hblock
  · exact False.elim (hscalar_ne hscalar)
  · exact hblock

theorem centeredRamanujanPairFullEvenBlockSum_X0_commonSix_eq_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs) :
    centeredRamanujanPairFullEvenBlockSum X0 p.1 p.2 = 0 := by
  have hleft :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_left_eq_six p hp
  have hright :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_right_eq_two_mul_halved p hp
  have hpHalf :
      (3, p.2 / 2) ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowThreeRightOddPairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_mem_rowThreeRightOdd
      p hp
  have hodd : Odd (p.2 / 2) := by
    exact (Finset.mem_filter.mp hpHalf).2
  have hthreeZero :=
    centeredRamanujanPairFullEvenBlockSum_X0_three_halved_eq_zero_of_commonSix hp
  rw [hleft, hright]
  exact centeredRamanujanPairFullEvenBlockSum_X0_six_two_mul_eq_zero_of_three_zero
    hodd hthreeZero

theorem centeredRamanujanPairPeriodicMainTerm_X0_commonSix_eq_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs) :
    centeredRamanujanPairPeriodicMainTerm X0 p.1 p.2 = 0 := by
  have hleft :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_left_eq_six p hp
  have hright :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_right_eq_two_mul_halved p hp
  have hhalfpos :=
    PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_halved_pos p hp
  have hp1 : 1 ≤ p.1 := by
    rw [hleft]
    norm_num
  have hp2 : 1 ≤ p.2 := by
    rw [hright]
    omega
  have hbridge :=
    centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_commonSix_transport
      (X := X0) (q := p.1) (q' := p.2) hp1 hp2
  rw [hbridge]
  rw [centeredRamanujanPairFullEvenBlockSum_X0_commonSix_eq_zero hp]
  simp

theorem PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSix_value_on_records_transport :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeRowSixRightEvenCommonSixPairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp
  apply surrogatePeriodicMainActiveOrderedPairSummandRat_eq_zero_of_real
  have hterm := centeredRamanujanPairPeriodicMainTerm_X0_commonSix_eq_zero hp
  by_cases hdiag : p.1 = p.2
  · simp [hdiag]
  · simp [hdiag, hterm]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
