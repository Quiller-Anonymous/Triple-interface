import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeShapeSplit

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Lightweight dyadic transport for `bothThree`.

On the even window, doubling an odd modulus does not change the Ramanujan
observable.  This is the transport layer needed to reduce the `36`, `63`, and
`66` dyadic-shape buckets to the same odd-core surface as the `33` bucket.
-/

private theorem isEven_of_mem_EvenIn_for_bothThree_transport
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    Goldbach.Windows.IsEven N := by
  unfold EvenIn IccShift at hN
  exact (Finset.mem_filter.mp hN).2

theorem odd_of_not_isEven_for_bothThree_transport
    {n : ℕ} (hnOdd : ¬ Goldbach.Windows.IsEven n) :
    Odd n := by
  refine Nat.not_even_iff_odd.mp ?_
  intro hnEven
  exact hnOdd (Goldbach.Windows.isEven_of_even hnEven)

theorem gcd_odd_two_mul_eq_for_bothThree_transport
    {n k : ℕ} (hnOdd : Odd n) :
    Nat.gcd n (2 * k) = Nat.gcd n k := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  have h := Nat.Coprime.gcd_mul_left_cancel (k := 2) (m := k) (n := n) hcop
  simpa [Nat.gcd_comm, Nat.mul_comm] using h

theorem totient_two_mul_eq_of_odd_for_bothThree_transport
    {n : ℕ} (hnOdd : Odd n) :
    Nat.totient (2 * n) = Nat.totient n := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  rw [Nat.totient_mul hcop]
  norm_num

theorem ramanujanR_two_mul_eq_of_isEven_of_odd_for_bothThree_transport
    {n N : ℕ} (hnOdd : Odd n) (hNEven : Goldbach.Windows.IsEven N) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
      = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N := by
  have hnpos : 0 < n := hnOdd.pos
  rcases (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hNEven) with ⟨k, hk⟩
  subst hk
  set d : ℕ := Nat.gcd n k
  have hgcdn : Nat.gcd n (2 * k) = d := by
    simpa [d] using gcd_odd_two_mul_eq_for_bothThree_transport (n := n) (k := k) hnOdd
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
    totient_two_mul_eq_of_odd_for_bothThree_transport hdOdd
  rw [ramanujanR_eq_moebius_mul_totient_gcd, ramanujanR_eq_moebius_mul_totient_gcd]
  rw [hgcd2n, hgcdn, hquot, hphi]

theorem ramanujanWindowAverage_two_mul_eq_of_odd_for_bothThree_transport
    {X n : ℕ} (hnOdd : Odd n) :
    ramanujanWindowAverage X (2 * n) = ramanujanWindowAverage X n := by
  unfold ramanujanWindowAverage
  refine congrArg ((((EvenIn X H).card : ℝ)⁻¹) * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact ramanujanR_two_mul_eq_of_isEven_of_odd_for_bothThree_transport hnOdd
    (isEven_of_mem_EvenIn_for_bothThree_transport hN)

theorem centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_bothThree_transport
    {n N : ℕ} (hnOdd : Odd n) (hNEven : Goldbach.Windows.IsEven N) :
    centeredRamanujanObservable X0 (2 * n) N
      = centeredRamanujanObservable X0 n N := by
  calc
    centeredRamanujanObservable X0 (2 * n) N
        = Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
            - ramanujanWindowAverage X0 n := by
              simp [centeredRamanujanObservable,
                ramanujanWindowAverage_two_mul_eq_of_odd_for_bothThree_transport hnOdd]
    _ = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N
            - ramanujanWindowAverage X0 n := by
              rw [ramanujanR_two_mul_eq_of_isEven_of_odd_for_bothThree_transport hnOdd
                hNEven]
    _ = centeredRamanujanObservable X0 n N := by
              rfl

theorem centeredEvenRamanujanPairOffset_X0_two_mul_left_eq_of_odd_for_bothThree_transport
    {q q' k : ℕ} (hqOdd : Odd q) :
    centeredEvenRamanujanPairOffset X0 (2 * q) q' k
      =
    centeredEvenRamanujanPairOffset X0 q q' k := by
  unfold centeredEvenRamanujanPairOffset centeredRamanujanPairKernel
  by_cases hEven : Goldbach.Windows.IsEven (X0 + k)
  · rw [if_pos hEven, if_pos hEven]
    rw [centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_bothThree_transport
      (n := q) hqOdd hEven]
  · rw [if_neg hEven, if_neg hEven]

theorem centeredEvenRamanujanPairOffset_X0_two_mul_right_eq_of_odd_for_bothThree_transport
    {q q' k : ℕ} (hq'Odd : Odd q') :
    centeredEvenRamanujanPairOffset X0 q (2 * q') k
      =
    centeredEvenRamanujanPairOffset X0 q q' k := by
  unfold centeredEvenRamanujanPairOffset centeredRamanujanPairKernel
  by_cases hEven : Goldbach.Windows.IsEven (X0 + k)
  · rw [if_pos hEven, if_pos hEven]
    rw [centeredRamanujanObservable_X0_two_mul_eq_of_odd_of_isEven_for_bothThree_transport
      (n := q') hq'Odd hEven]
  · rw [if_neg hEven, if_neg hEven]

theorem centeredEvenRamanujanPairOffset_X0_two_mul_both_eq_of_odd_for_bothThree_transport
    {q q' k : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q') :
    centeredEvenRamanujanPairOffset X0 (2 * q) (2 * q') k
      =
    centeredEvenRamanujanPairOffset X0 q q' k := by
  rw [centeredEvenRamanujanPairOffset_X0_two_mul_left_eq_of_odd_for_bothThree_transport
    (q := q) (q' := 2 * q') hqOdd]
  rw [centeredEvenRamanujanPairOffset_X0_two_mul_right_eq_of_odd_for_bothThree_transport
    (q := q) (q' := q') hq'Odd]

theorem centeredRamanujanPairBlockPeriod_two_mul_right_eq_two_mul_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q') :
    centeredRamanujanPairBlockPeriod q (2 * q')
      =
    2 * centeredRamanujanPairBlockPeriod q q' := by
  rw [show centeredRamanujanPairBlockPeriod q (2 * q')
        = centeredRamanujanPairBlockPeriod (2 * q') q by
        unfold centeredRamanujanPairBlockPeriod
        rw [Nat.lcm_comm]]
  rw [centeredRamanujanPairBlockPeriod_two_mul_left_of_odd hq'Odd hqOdd]
  rw [show centeredRamanujanPairBlockPeriod q' q
        = centeredRamanujanPairBlockPeriod q q' by
        unfold centeredRamanujanPairBlockPeriod
        rw [Nat.lcm_comm]]

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_left_eq_two_mul_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q') :
    centeredRamanujanPairFullEvenBlockSum X0 (2 * q) q'
      =
    2 * centeredRamanujanPairFullEvenBlockSum X0 q q' := by
  let P := centeredRamanujanPairBlockPeriod q q'
  have hP2 :
      centeredRamanujanPairBlockPeriod (2 * q) q' = 2 * P := by
    simpa [P] using centeredRamanujanPairBlockPeriod_two_mul_left_of_odd
      (n := q) (q' := q') hqOdd hq'Odd
  unfold centeredRamanujanPairFullEvenBlockSum
  rw [hP2]
  have htwoP : 2 * P = P + P := by omega
  rw [htwoP, Finset.sum_range_add]
  have hfirst :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 (2 * q) q' k)
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q q' k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact centeredEvenRamanujanPairOffset_X0_two_mul_left_eq_of_odd_for_bothThree_transport
      hqOdd
  have hsecond :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 (2 * q) q' (P + k))
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q q' k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [centeredEvenRamanujanPairOffset_X0_two_mul_left_eq_of_odd_for_bothThree_transport
      hqOdd]
    simpa [P, Nat.add_comm] using
      centeredEvenRamanujanPairOffset_add_blockPeriod (X := X0) (q := q) (q' := q') (k := k)
  rw [hfirst, hsecond]
  ring

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_right_eq_two_mul_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q') :
    centeredRamanujanPairFullEvenBlockSum X0 q (2 * q')
      =
    2 * centeredRamanujanPairFullEvenBlockSum X0 q q' := by
  let P := centeredRamanujanPairBlockPeriod q q'
  have hP2 :
      centeredRamanujanPairBlockPeriod q (2 * q') = 2 * P := by
    simpa [P] using
      centeredRamanujanPairBlockPeriod_two_mul_right_eq_two_mul_for_bothThree_transport
        hqOdd hq'Odd
  unfold centeredRamanujanPairFullEvenBlockSum
  rw [hP2]
  have htwoP : 2 * P = P + P := by omega
  rw [htwoP, Finset.sum_range_add]
  have hfirst :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q (2 * q') k)
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q q' k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact centeredEvenRamanujanPairOffset_X0_two_mul_right_eq_of_odd_for_bothThree_transport
      hq'Odd
  have hsecond :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q (2 * q') (P + k))
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q q' k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [centeredEvenRamanujanPairOffset_X0_two_mul_right_eq_of_odd_for_bothThree_transport
      hq'Odd]
    simpa [P, Nat.add_comm] using
      centeredEvenRamanujanPairOffset_add_blockPeriod (X := X0) (q := q) (q' := q') (k := k)
  rw [hfirst, hsecond]
  ring

theorem centeredRamanujanPairBlockPeriod_two_mul_both_eq_two_mul_for_bothThree_transport
    (q q' : ℕ) :
    centeredRamanujanPairBlockPeriod (2 * q) (2 * q')
      =
    2 * centeredRamanujanPairBlockPeriod q q' := by
  unfold centeredRamanujanPairBlockPeriod
  rw [Nat.lcm_mul_left]

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_both_eq_two_mul_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q') :
    centeredRamanujanPairFullEvenBlockSum X0 (2 * q) (2 * q')
      =
    2 * centeredRamanujanPairFullEvenBlockSum X0 q q' := by
  let P := centeredRamanujanPairBlockPeriod q q'
  have hP2 :
      centeredRamanujanPairBlockPeriod (2 * q) (2 * q') = 2 * P := by
    simpa [P] using
      centeredRamanujanPairBlockPeriod_two_mul_both_eq_two_mul_for_bothThree_transport q q'
  unfold centeredRamanujanPairFullEvenBlockSum
  rw [hP2]
  have htwoP : 2 * P = P + P := by omega
  rw [htwoP, Finset.sum_range_add]
  have hfirst :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 (2 * q) (2 * q') k)
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q q' k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    exact centeredEvenRamanujanPairOffset_X0_two_mul_both_eq_of_odd_for_bothThree_transport
      hqOdd hq'Odd
  have hsecond :
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 (2 * q) (2 * q') (P + k))
        =
      (∑ k ∈ Finset.range P,
          centeredEvenRamanujanPairOffset X0 q q' k) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [centeredEvenRamanujanPairOffset_X0_two_mul_both_eq_of_odd_for_bothThree_transport
      hqOdd hq'Odd]
    simpa [P, Nat.add_comm] using
      centeredEvenRamanujanPairOffset_add_blockPeriod (X := X0) (q := q) (q' := q') (k := k)
  rw [hfirst, hsecond]
  ring

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_left_eq_zero_of_base_zero_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q')
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 q q' = 0) :
    centeredRamanujanPairFullEvenBlockSum X0 (2 * q) q' = 0 := by
  rw [centeredRamanujanPairFullEvenBlockSum_X0_two_mul_left_eq_two_mul_for_bothThree_transport
    hqOdd hq'Odd]
  simp [hzero]

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_right_eq_zero_of_base_zero_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q')
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 q q' = 0) :
    centeredRamanujanPairFullEvenBlockSum X0 q (2 * q') = 0 := by
  rw [centeredRamanujanPairFullEvenBlockSum_X0_two_mul_right_eq_two_mul_for_bothThree_transport
    hqOdd hq'Odd]
  simp [hzero]

theorem centeredRamanujanPairFullEvenBlockSum_X0_two_mul_both_eq_zero_of_base_zero_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q')
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 q q' = 0) :
    centeredRamanujanPairFullEvenBlockSum X0 (2 * q) (2 * q') = 0 := by
  rw [centeredRamanujanPairFullEvenBlockSum_X0_two_mul_both_eq_two_mul_for_bothThree_transport
    hqOdd hq'Odd]
  simp [hzero]

theorem centeredRamanujanPairPeriodicMainTerm_X0_two_mul_left_eq_zero_of_base_full_zero_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q')
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 q q' = 0) :
    centeredRamanujanPairPeriodicMainTerm X0 (2 * q) q' = 0 := by
  rw [centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_bothThree_probe
    (X := X0) (q := 2 * q) (q' := q')
    (by exact Nat.mul_pos (by norm_num) hqOdd.pos)
    (by exact hq'Odd.pos)]
  rw [centeredRamanujanPairFullEvenBlockSum_X0_two_mul_left_eq_zero_of_base_zero_for_bothThree_transport
    hqOdd hq'Odd hzero]
  simp

theorem centeredRamanujanPairPeriodicMainTerm_X0_two_mul_right_eq_zero_of_base_full_zero_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q')
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 q q' = 0) :
    centeredRamanujanPairPeriodicMainTerm X0 q (2 * q') = 0 := by
  rw [centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_bothThree_probe
    (X := X0) (q := q) (q' := 2 * q')
    (by exact hqOdd.pos)
    (by exact Nat.mul_pos (by norm_num) hq'Odd.pos)]
  rw [centeredRamanujanPairFullEvenBlockSum_X0_two_mul_right_eq_zero_of_base_zero_for_bothThree_transport
    hqOdd hq'Odd hzero]
  simp

theorem centeredRamanujanPairPeriodicMainTerm_X0_two_mul_both_eq_zero_of_base_full_zero_for_bothThree_transport
    {q q' : ℕ} (hqOdd : Odd q) (hq'Odd : Odd q')
    (hzero : centeredRamanujanPairFullEvenBlockSum X0 q q' = 0) :
    centeredRamanujanPairPeriodicMainTerm X0 (2 * q) (2 * q') = 0 := by
  rw [centeredRamanujanPairPeriodicMainTerm_eq_blockScalar_fullEvenBlockSum_for_bothThree_probe
    (X := X0) (q := 2 * q) (q' := 2 * q')
    (by exact Nat.mul_pos (by norm_num) hqOdd.pos)
    (by exact Nat.mul_pos (by norm_num) hq'Odd.pos)]
  rw [centeredRamanujanPairFullEvenBlockSum_X0_two_mul_both_eq_zero_of_base_zero_for_bothThree_transport
    hqOdd hq'Odd hzero]
  simp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
