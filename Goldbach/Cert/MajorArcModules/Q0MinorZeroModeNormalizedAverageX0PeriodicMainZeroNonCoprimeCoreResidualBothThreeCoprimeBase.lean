import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeBaseStructural

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
First structural lemmas for the coprime-core part of the `bothThree` residual.

The base pair is `(3 * a, 3 * b)`, where the cores are odd and coprime to `3`.
These lemmas record the period/count bookkeeping needed before proving the
common-three orthogonality statement.
-/

theorem centeredRamanujanPairBlockPeriod_three_mul_both_eq_three_mul
    (q q' : ℕ) :
    centeredRamanujanPairBlockPeriod (3 * q) (3 * q')
      =
    3 * centeredRamanujanPairBlockPeriod q q' := by
  unfold centeredRamanujanPairBlockPeriod
  rw [Nat.lcm_mul_left]
  ring

theorem evenRamanujanBlockCount_three_mul_both_eq_three_mul
    (X q q' : ℕ) :
    evenRamanujanBlockCount X (3 * q) (3 * q')
      =
    3 * evenRamanujanBlockCount X q q' := by
  rw [evenRamanujanBlockCount_eq_lcm, evenRamanujanBlockCount_eq_lcm]
  rw [Nat.lcm_mul_left]
  norm_num

theorem centeredRamanujanPairBlockPeriod_coprime_three_of_not_dvd_three
    {q q' : ℕ} (hq3 : ¬ 3 ∣ q) (hq'3 : ¬ 3 ∣ q') :
    Nat.Coprime (centeredRamanujanPairBlockPeriod q q') 3 := by
  have hprime3 : Nat.Prime 3 := by norm_num
  have h3q : Nat.Coprime 3 q := (hprime3.coprime_iff_not_dvd).2 hq3
  have h3q' : Nat.Coprime 3 q' := (hprime3.coprime_iff_not_dvd).2 hq'3
  have h3qq' : Nat.Coprime 3 (q * q') :=
    (Nat.coprime_mul_iff_right).2 ⟨h3q, h3q'⟩
  have hlcm_dvd : Nat.lcm q q' ∣ q * q' :=
    Nat.lcm_dvd (dvd_mul_right q q') (dvd_mul_left q' q)
  have h3lcm : Nat.Coprime 3 (Nat.lcm q q') :=
    h3qq'.of_dvd_right hlcm_dvd
  have h32 : Nat.Coprime 3 2 := by norm_num
  have h3period : Nat.Coprime 3 (2 * Nat.lcm q q') :=
    (Nat.coprime_mul_iff_right).2 ⟨h32, h3lcm⟩
  simpa [centeredRamanujanPairBlockPeriod, Nat.coprime_comm] using h3period.symm

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseBlockPeriod
    {p : ℕ × ℕ}
    (_hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    centeredRamanujanPairBlockPeriod
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
      =
    3 * centeredRamanujanPairBlockPeriod
        (bothThreeOddCore p.1) (bothThreeOddCore p.2) := by
  exact centeredRamanujanPairBlockPeriod_three_mul_both_eq_three_mul
    (bothThreeOddCore p.1) (bothThreeOddCore p.2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseEvenBlockCount
    {p : ℕ × ℕ}
    (_hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    evenRamanujanBlockCount X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
      =
    3 * evenRamanujanBlockCount X0
        (bothThreeOddCore p.1) (bothThreeOddCore p.2) := by
  exact evenRamanujanBlockCount_three_mul_both_eq_three_mul
    X0 (bothThreeOddCore p.1) (bothThreeOddCore p.2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_coreBlockPeriod_coprime_three
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    Nat.Coprime
      (centeredRamanujanPairBlockPeriod (bothThreeOddCore p.1) (bothThreeOddCore p.2))
      3 := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  exact centeredRamanujanPairBlockPeriod_coprime_three_of_not_dvd_three
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hpBoth)

theorem ramanujanR_three_sq_eq_ite_dvd
    (N : ℕ) :
    (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 N) ^ 2
      =
    if 3 ∣ N then (4 : ℝ) else 1 := by
  by_cases hN : 3 ∣ N
  · rw [if_pos hN]
    rw [ramanujanR_prime_eq_sub_one_of_dvd_for_bothThree
      (p := 3) (N := N) (by norm_num) hN]
    norm_num
  · rw [if_neg hN]
    rw [ramanujanR_prime_eq_neg_one_of_not_dvd_for_bothThree
      (p := 3) (N := N) (by norm_num) hN]
    norm_num

theorem rawEvenRamanujanPairBlockSummand_three_mul_factor
    {X q q' k : ℕ} (hq3 : ¬ 3 ∣ q) (hq'3 : ¬ 3 ∣ q') :
    (if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + k)
    else 0)
      =
    (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)) ^ 2
      * (if Goldbach.Windows.IsEven (X + k) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
        else 0) := by
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos hEven, if_pos hEven]
    rw [ramanujanR_three_mul_eq_three_mul_for_bothThree
      (r := q) (N := X + k) hq3]
    rw [ramanujanR_three_mul_eq_three_mul_for_bothThree
      (r := q') (N := X + k) hq'3]
    ring
  · rw [if_neg hEven, if_neg hEven]
    ring

theorem rawEvenRamanujanBlockSummand_three_mul_factor
    {X q0 k : ℕ} (hq03 : ¬ 3 ∣ q0) :
    (if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + k)
    else 0)
      =
    Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)
      * (if Goldbach.Windows.IsEven (X + k) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + k)
        else 0) := by
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos hEven, if_pos hEven]
    rw [ramanujanR_three_mul_eq_three_mul_for_bothThree
      (r := q0) (N := X + k) hq03]
  · rw [if_neg hEven, if_neg hEven]
    ring

theorem rawEvenRamanujanPairBlockSummand_add_coreBlockPeriod
    (X q q' k : ℕ) :
    (if Goldbach.Windows.IsEven (X + (k + centeredRamanujanPairBlockPeriod q q')) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q
          (X + (k + centeredRamanujanPairBlockPeriod q q'))
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q'
          (X + (k + centeredRamanujanPairBlockPeriod q q'))
    else 0)
      =
    (if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
    else 0) := by
  let L := Nat.lcm q q'
  have hpar :
      Goldbach.Windows.IsEven (X + (k + centeredRamanujanPairBlockPeriod q q'))
        ↔
      Goldbach.Windows.IsEven (X + k) := by
    dsimp [Goldbach.Windows.IsEven, centeredRamanujanPairBlockPeriod]
    omega
  have hshift :
      X + (k + centeredRamanujanPairBlockPeriod q q')
        =
      (X + k) + centeredRamanujanPairBlockPeriod q q' := by
    omega
  have hqper :
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q
          (X + (k + centeredRamanujanPairBlockPeriod q q'))
        =
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k) := by
    rw [hshift]
    exact ramanujanR_add_period_of_dvd
      (q := q) (P := centeredRamanujanPairBlockPeriod q q') (N := X + k)
      (by
        unfold centeredRamanujanPairBlockPeriod
        exact dvd_mul_of_dvd_right (dvd_lcm_left q q') 2)
  have hq'per :
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q'
          (X + (k + centeredRamanujanPairBlockPeriod q q'))
        =
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k) := by
    rw [hshift]
    exact ramanujanR_add_period_of_dvd
      (q := q') (P := centeredRamanujanPairBlockPeriod q q') (N := X + k)
      (by
        unfold centeredRamanujanPairBlockPeriod
        exact dvd_mul_of_dvd_right (dvd_lcm_right q q') 2)
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos ((hpar).2 hEven), if_pos hEven, hqper, hq'per]
  · have hEvenShift :
        ¬ Goldbach.Windows.IsEven
          (X + (k + centeredRamanujanPairBlockPeriod q q')) := by
      intro h
      exact hEven ((hpar).1 h)
    rw [if_neg hEvenShift, if_neg hEven]

theorem ramanujanR_three_sq_cycle_sum_of_coprime_step
    {N P : ℕ} (hP : Nat.Coprime P 3) :
    (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 N) ^ 2
      + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (N + P)) ^ 2
      + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (N + 2 * P)) ^ 2
      =
    (6 : ℝ) := by
  have hPnot : ¬ 3 ∣ P := by
    intro hdiv
    have h3cop : Nat.Coprime 3 P := hP.symm
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) (dvd_refl 3) hdiv h3cop
  have hPmod : P % 3 = 1 ∨ P % 3 = 2 := by
    have hlt : P % 3 < 3 := Nat.mod_lt P (by norm_num)
    have hnot0 : P % 3 ≠ 0 := by
      intro h0
      exact hPnot (Nat.dvd_iff_mod_eq_zero.mpr h0)
    omega
  have hNmod : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by
    have hlt : N % 3 < 3 := Nat.mod_lt N (by norm_num)
    omega
  rw [ramanujanR_three_sq_eq_ite_dvd,
    ramanujanR_three_sq_eq_ite_dvd,
    ramanujanR_three_sq_eq_ite_dvd]
  rcases hPmod with hP1 | hP2
  · rcases hNmod with hN0 | hN12
    · have h0 : 3 ∣ N := Nat.dvd_iff_mod_eq_zero.mpr hN0
      have h1 : ¬ 3 ∣ N + P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      have h2 : ¬ 3 ∣ N + 2 * P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      norm_num [h0, h1, h2]
    · rcases hN12 with hN1 | hN2
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : ¬ 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : ¬ 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]
  · rcases hNmod with hN0 | hN12
    · have h0 : 3 ∣ N := Nat.dvd_iff_mod_eq_zero.mpr hN0
      have h1 : ¬ 3 ∣ N + P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      have h2 : ¬ 3 ∣ N + 2 * P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      norm_num [h0, h1, h2]
    · rcases hN12 with hN1 | hN2
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : ¬ 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : ¬ 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]

theorem rawEvenRamanujanPairBlockSummand_three_shift_sum_eq_six_mul
    {X q q' k : ℕ}
    (hq3 : ¬ 3 ∣ q) (hq'3 : ¬ 3 ∣ q')
    (hP3 : Nat.Coprime (centeredRamanujanPairBlockPeriod q q') 3) :
    let P := centeredRamanujanPairBlockPeriod q q'
    (if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + k)
    else 0)
      +
    (if Goldbach.Windows.IsEven (X + (k + P)) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + (k + P))
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + (k + P))
    else 0)
      +
    (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + (k + 2 * P))
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + (k + 2 * P))
    else 0)
      =
    6 * (if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
    else 0) := by
  intro P
  let G : ℝ :=
    if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
    else 0
  have hG1 :
      (if Goldbach.Windows.IsEven (X + (k + P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + (k + P))
          * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + (k + P))
      else 0) = G := by
    simpa [G, P] using
      rawEvenRamanujanPairBlockSummand_add_coreBlockPeriod X q q' k
  have hG2 :
      (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + (k + 2 * P))
          * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + (k + 2 * P))
      else 0) = G := by
    have hstep1 :=
      rawEvenRamanujanPairBlockSummand_add_coreBlockPeriod X q q' (k + P)
    have hstep1' :
        (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + (k + 2 * P))
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + (k + 2 * P))
        else 0)
          =
        (if Goldbach.Windows.IsEven (X + ((k + P) + P)) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + ((k + P) + P))
            * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + ((k + P) + P))
        else 0) := by
      have hk2 : k + 2 * P = (k + P) + P := by omega
      simp [hk2]
    rw [hstep1']
    rw [hstep1]
    exact hG1
  have hF0 :
      (if Goldbach.Windows.IsEven (X + k) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + k)
          * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + k)
      else 0)
        =
      (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)) ^ 2 * G := by
    simpa [G] using
      rawEvenRamanujanPairBlockSummand_three_mul_factor
        (X := X) (q := q) (q' := q') (k := k) hq3 hq'3
  have hF1 :
      (if Goldbach.Windows.IsEven (X + (k + P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + (k + P))
          * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + (k + P))
      else 0)
        =
      (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P))) ^ 2 * G := by
    rw [rawEvenRamanujanPairBlockSummand_three_mul_factor
      (X := X) (q := q) (q' := q') (k := k + P) hq3 hq'3]
    rw [hG1]
  have hF2 :
      (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + (k + 2 * P))
          * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + (k + 2 * P))
      else 0)
        =
      (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P))) ^ 2 * G := by
    have hfactor :=
      rawEvenRamanujanPairBlockSummand_three_mul_factor
        (X := X) (q := q) (q' := q') (k := k + 2 * P) hq3 hq'3
    simpa [hG2] using hfactor
  have hcycle :
      (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)) ^ 2
        + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P))) ^ 2
        + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P))) ^ 2
        =
      (6 : ℝ) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ramanujanR_three_sq_cycle_sum_of_coprime_step
        (N := X + k) (P := P) hP3
  rw [hF0, hF1, hF2]
  calc
    (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)) ^ 2 * G
        + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P))) ^ 2 * G
        + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P))) ^ 2 * G
        =
      ((Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)) ^ 2
        + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P))) ^ 2
        + (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P))) ^ 2) * G := by
          ring
    _ = 6 * G := by rw [hcycle]

theorem rawEvenRamanujanPairBlockSum_three_mul_both_eq_six_mul
    {X q q' : ℕ}
    (hq3 : ¬ 3 ∣ q) (hq'3 : ¬ 3 ∣ q')
    (hP3 : Nat.Coprime (centeredRamanujanPairBlockPeriod q q') 3) :
    rawEvenRamanujanPairBlockSum X (3 * q) (3 * q')
      =
    6 * rawEvenRamanujanPairBlockSum X q q' := by
  let P := centeredRamanujanPairBlockPeriod q q'
  let F : ℕ → ℝ := fun k =>
    if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q) (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q') (X + k)
    else 0
  let G : ℕ → ℝ := fun k =>
    if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q (X + k)
        * Goldbach.AO_OffDiag.TailBlock.ramanujanR q' (X + k)
    else 0
  have hperiod :
      centeredRamanujanPairBlockPeriod (3 * q) (3 * q') = 3 * P := by
    simpa [P] using centeredRamanujanPairBlockPeriod_three_mul_both_eq_three_mul q q'
  have hsplit :
      Finset.sum (Finset.range (3 * P)) F
        =
      Finset.sum (Finset.range P)
        (fun k => F k + F (k + P) + F (k + 2 * P)) := by
    have hsplit1 :
        Finset.sum (Finset.range (3 * P)) F
          =
        Finset.sum (Finset.range P) F
          + Finset.sum (Finset.range (2 * P)) (fun k => F (P + k)) := by
      rw [show 3 * P = P + 2 * P by omega]
      rw [Finset.sum_range_add]
    have hsplit2 :
        Finset.sum (Finset.range (2 * P)) (fun k => F (P + k))
          =
        Finset.sum (Finset.range P) (fun k => F (P + k))
          + Finset.sum (Finset.range P) (fun k => F (P + (P + k))) := by
      rw [show 2 * P = P + P by omega]
      rw [Finset.sum_range_add]
    rw [hsplit1, hsplit2]
    have htail :
        Finset.sum (Finset.range P) (fun k => F (P + (P + k)))
          =
        Finset.sum (Finset.range P) (fun k => F (k + 2 * P)) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      have hk : P + (P + k) = k + 2 * P := by omega
      rw [hk]
    rw [htail]
    rw [show
        Finset.sum (Finset.range P) F
          + (Finset.sum (Finset.range P) (fun k => F (P + k))
            + Finset.sum (Finset.range P) (fun k => F (k + 2 * P)))
        =
        (Finset.sum (Finset.range P) F
          + Finset.sum (Finset.range P) (fun k => F (P + k)))
          + Finset.sum (Finset.range P) (fun k => F (k + 2 * P)) by ring]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    have hkP : P + k = k + P := by omega
    rw [hkP]
  have hpoint :
      ∀ k ∈ Finset.range P,
        F k + F (k + P) + F (k + 2 * P) = 6 * G k := by
    intro k _hk
    simpa [F, G, P] using
      rawEvenRamanujanPairBlockSummand_three_shift_sum_eq_six_mul
        (X := X) (q := q) (q' := q') (k := k) hq3 hq'3 hP3
  calc
    rawEvenRamanujanPairBlockSum X (3 * q) (3 * q')
        =
      Finset.sum (Finset.range (3 * P)) F := by
        unfold rawEvenRamanujanPairBlockSum
        rw [hperiod]
    _ =
      Finset.sum (Finset.range P)
        (fun k => F k + F (k + P) + F (k + 2 * P)) := hsplit
    _ =
      Finset.sum (Finset.range P) (fun k => 6 * G k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        exact hpoint k hk
    _ =
      6 * Finset.sum (Finset.range P) G := by
        rw [Finset.mul_sum]
    _ =
      6 * rawEvenRamanujanPairBlockSum X q q' := by
        unfold rawEvenRamanujanPairBlockSum
        simp [G, P]

theorem ramanujanR_three_eq_ite_dvd
    (N : ℕ) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 N
      =
    if 3 ∣ N then (2 : ℝ) else -1 := by
  by_cases hN : 3 ∣ N
  · rw [if_pos hN]
    rw [ramanujanR_prime_eq_sub_one_of_dvd_for_bothThree
      (p := 3) (N := N) (by norm_num) hN]
    norm_num
  · rw [if_neg hN]
    rw [ramanujanR_prime_eq_neg_one_of_not_dvd_for_bothThree
      (p := 3) (N := N) (by norm_num) hN]

theorem ramanujanR_three_cycle_sum_of_coprime_step
    {N P : ℕ} (hP : Nat.Coprime P 3) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 N
      + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (N + P)
      + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (N + 2 * P)
      =
    (0 : ℝ) := by
  have hPnot : ¬ 3 ∣ P := by
    intro hdiv
    have h3cop : Nat.Coprime 3 P := hP.symm
    exact Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) (dvd_refl 3) hdiv h3cop
  have hPmod : P % 3 = 1 ∨ P % 3 = 2 := by
    have hlt : P % 3 < 3 := Nat.mod_lt P (by norm_num)
    have hnot0 : P % 3 ≠ 0 := by
      intro h0
      exact hPnot (Nat.dvd_iff_mod_eq_zero.mpr h0)
    omega
  have hNmod : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by
    have hlt : N % 3 < 3 := Nat.mod_lt N (by norm_num)
    omega
  rw [ramanujanR_three_eq_ite_dvd,
    ramanujanR_three_eq_ite_dvd,
    ramanujanR_three_eq_ite_dvd]
  rcases hPmod with hP1 | hP2
  · rcases hNmod with hN0 | hN12
    · have h0 : 3 ∣ N := Nat.dvd_iff_mod_eq_zero.mpr hN0
      have h1 : ¬ 3 ∣ N + P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      have h2 : ¬ 3 ∣ N + 2 * P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      norm_num [h0, h1, h2]
    · rcases hN12 with hN1 | hN2
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : ¬ 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : ¬ 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]
  · rcases hNmod with hN0 | hN12
    · have h0 : 3 ∣ N := Nat.dvd_iff_mod_eq_zero.mpr hN0
      have h1 : ¬ 3 ∣ N + P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      have h2 : ¬ 3 ∣ N + 2 * P := by
        rw [Nat.dvd_iff_mod_eq_zero]
        omega
      norm_num [h0, h1, h2]
    · rcases hN12 with hN1 | hN2
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : ¬ 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]
      · have h0 : ¬ 3 ∣ N := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h1 : ¬ 3 ∣ N + P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have h2 : 3 ∣ N + 2 * P := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        norm_num [h0, h1, h2]

theorem rawEvenRamanujanBlockSummand_add_coreBlockPeriod
    {q0 : ℕ} (X q q' k : ℕ)
    (hdiv : q0 ∣ centeredRamanujanPairBlockPeriod q q') :
    (if Goldbach.Windows.IsEven (X + (k + centeredRamanujanPairBlockPeriod q q')) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q0
          (X + (k + centeredRamanujanPairBlockPeriod q q'))
    else 0)
      =
    (if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + k)
    else 0) := by
  have hpar :
      Goldbach.Windows.IsEven (X + (k + centeredRamanujanPairBlockPeriod q q'))
        ↔
      Goldbach.Windows.IsEven (X + k) := by
    dsimp [Goldbach.Windows.IsEven, centeredRamanujanPairBlockPeriod]
    omega
  have hshift :
      X + (k + centeredRamanujanPairBlockPeriod q q')
        =
      (X + k) + centeredRamanujanPairBlockPeriod q q' := by
    omega
  have hq0per :
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q0
          (X + (k + centeredRamanujanPairBlockPeriod q q'))
        =
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + k) := by
    rw [hshift]
    exact ramanujanR_add_period_of_dvd
      (q := q0) (P := centeredRamanujanPairBlockPeriod q q') (N := X + k)
      hdiv
  by_cases hEven : Goldbach.Windows.IsEven (X + k)
  · rw [if_pos ((hpar).2 hEven), if_pos hEven, hq0per]
  · have hEvenShift :
        ¬ Goldbach.Windows.IsEven
          (X + (k + centeredRamanujanPairBlockPeriod q q')) := by
      intro h
      exact hEven ((hpar).1 h)
    rw [if_neg hEvenShift, if_neg hEven]

theorem rawEvenRamanujanBlockSummand_three_shift_sum_eq_zero
    {X q q' q0 k : ℕ}
    (hq03 : ¬ 3 ∣ q0)
    (hP3 : Nat.Coprime (centeredRamanujanPairBlockPeriod q q') 3)
    (hdiv : q0 ∣ centeredRamanujanPairBlockPeriod q q') :
    let P := centeredRamanujanPairBlockPeriod q q'
    (if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + k)
    else 0)
      +
    (if Goldbach.Windows.IsEven (X + (k + P)) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + (k + P))
    else 0)
      +
    (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + (k + 2 * P))
    else 0)
      =
    (0 : ℝ) := by
  intro P
  let G : ℝ :=
    if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + k)
    else 0
  have hG1 :
      (if Goldbach.Windows.IsEven (X + (k + P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + (k + P))
      else 0) = G := by
    simpa [G, P] using
      rawEvenRamanujanBlockSummand_add_coreBlockPeriod
        (q0 := q0) X q q' k hdiv
  have hG2 :
      (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + (k + 2 * P))
      else 0) = G := by
    have hstep1 :=
      rawEvenRamanujanBlockSummand_add_coreBlockPeriod
        (q0 := q0) X q q' (k + P) hdiv
    have hstep1' :
        (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + (k + 2 * P))
        else 0)
          =
        (if Goldbach.Windows.IsEven (X + ((k + P) + P)) then
          Goldbach.AO_OffDiag.TailBlock.ramanujanR q0 (X + ((k + P) + P))
        else 0) := by
      have hk2 : k + 2 * P = (k + P) + P := by omega
      simp [hk2]
    rw [hstep1']
    rw [hstep1]
    exact hG1
  have hF0 :
      (if Goldbach.Windows.IsEven (X + k) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + k)
      else 0)
        =
      Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k) * G := by
    simpa [G] using
      rawEvenRamanujanBlockSummand_three_mul_factor
        (X := X) (q0 := q0) (k := k) hq03
  have hF1 :
      (if Goldbach.Windows.IsEven (X + (k + P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + (k + P))
      else 0)
        =
      Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P)) * G := by
    rw [rawEvenRamanujanBlockSummand_three_mul_factor
      (X := X) (q0 := q0) (k := k + P) hq03]
    rw [hG1]
  have hF2 :
      (if Goldbach.Windows.IsEven (X + (k + 2 * P)) then
        Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + (k + 2 * P))
      else 0)
        =
      Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P)) * G := by
    have hfactor :=
      rawEvenRamanujanBlockSummand_three_mul_factor
        (X := X) (q0 := q0) (k := k + 2 * P) hq03
    simpa [hG2] using hfactor
  have hcycle :
      Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)
        + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P))
        + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P))
        =
      (0 : ℝ) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ramanujanR_three_cycle_sum_of_coprime_step
        (N := X + k) (P := P) hP3
  rw [hF0, hF1, hF2]
  calc
    Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k) * G
        + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P)) * G
        + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P)) * G
        =
      (Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + k)
        + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + P))
        + Goldbach.AO_OffDiag.TailBlock.ramanujanR 3 (X + (k + 2 * P))) * G := by
          ring
    _ = 0 := by rw [hcycle]; ring

theorem rawEvenRamanujanBlockSum_three_mul_both_eq_zero
    {X q q' q0 : ℕ}
    (hq03 : ¬ 3 ∣ q0)
    (hP3 : Nat.Coprime (centeredRamanujanPairBlockPeriod q q') 3)
    (hdiv : q0 ∣ centeredRamanujanPairBlockPeriod q q') :
    rawEvenRamanujanBlockSum X (3 * q) (3 * q') (3 * q0)
      =
    (0 : ℝ) := by
  let P := centeredRamanujanPairBlockPeriod q q'
  let F : ℕ → ℝ := fun k =>
    if Goldbach.Windows.IsEven (X + k) then
      Goldbach.AO_OffDiag.TailBlock.ramanujanR (3 * q0) (X + k)
    else 0
  have hperiod :
      centeredRamanujanPairBlockPeriod (3 * q) (3 * q') = 3 * P := by
    simpa [P] using centeredRamanujanPairBlockPeriod_three_mul_both_eq_three_mul q q'
  have hsplit :
      Finset.sum (Finset.range (3 * P)) F
        =
      Finset.sum (Finset.range P)
        (fun k => F k + F (k + P) + F (k + 2 * P)) := by
    have hsplit1 :
        Finset.sum (Finset.range (3 * P)) F
          =
        Finset.sum (Finset.range P) F
          + Finset.sum (Finset.range (2 * P)) (fun k => F (P + k)) := by
      rw [show 3 * P = P + 2 * P by omega]
      rw [Finset.sum_range_add]
    have hsplit2 :
        Finset.sum (Finset.range (2 * P)) (fun k => F (P + k))
          =
        Finset.sum (Finset.range P) (fun k => F (P + k))
          + Finset.sum (Finset.range P) (fun k => F (P + (P + k))) := by
      rw [show 2 * P = P + P by omega]
      rw [Finset.sum_range_add]
    rw [hsplit1, hsplit2]
    have htail :
        Finset.sum (Finset.range P) (fun k => F (P + (P + k)))
          =
        Finset.sum (Finset.range P) (fun k => F (k + 2 * P)) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      have hk : P + (P + k) = k + 2 * P := by omega
      rw [hk]
    rw [htail]
    rw [show
        Finset.sum (Finset.range P) F
          + (Finset.sum (Finset.range P) (fun k => F (P + k))
            + Finset.sum (Finset.range P) (fun k => F (k + 2 * P)))
        =
        (Finset.sum (Finset.range P) F
          + Finset.sum (Finset.range P) (fun k => F (P + k)))
          + Finset.sum (Finset.range P) (fun k => F (k + 2 * P)) by ring]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    have hkP : P + k = k + P := by omega
    rw [hkP]
  have hpoint :
      ∀ k ∈ Finset.range P,
        F k + F (k + P) + F (k + 2 * P) = 0 := by
    intro k _hk
    simpa [F, P] using
      rawEvenRamanujanBlockSummand_three_shift_sum_eq_zero
        (X := X) (q := q) (q' := q') (q0 := q0) (k := k)
        hq03 hP3 hdiv
  calc
    rawEvenRamanujanBlockSum X (3 * q) (3 * q') (3 * q0)
        =
      Finset.sum (Finset.range (3 * P)) F := by
        unfold rawEvenRamanujanBlockSum
        rw [hperiod]
    _ =
      Finset.sum (Finset.range P)
        (fun k => F k + F (k + P) + F (k + 2 * P)) := hsplit
    _ = 0 := by
      exact Finset.sum_eq_zero hpoint

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_basePairRawBlockSum
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    rawEvenRamanujanPairBlockSum X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
      =
    6 * rawEvenRamanujanPairBlockSum X0
        (bothThreeOddCore p.1) (bothThreeOddCore p.2) := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  exact rawEvenRamanujanPairBlockSum_three_mul_both_eq_six_mul
    (X := X0) (q := bothThreeOddCore p.1) (q' := bothThreeOddCore p.2)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_coreBlockPeriod_coprime_three
      hp)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_basePairRawBlockSum_eq_zero_of_core
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hcore :
      rawEvenRamanujanPairBlockSum X0
        (bothThreeOddCore p.1) (bothThreeOddCore p.2) = 0) :
    rawEvenRamanujanPairBlockSum X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
      =
    0 := by
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_basePairRawBlockSum
    hp]
  rw [hcore]
  ring

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseLeftRawBlockSum_eq_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    rawEvenRamanujanBlockSum X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
        (3 * bothThreeOddCore p.1)
      =
    0 := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  exact rawEvenRamanujanBlockSum_three_mul_both_eq_zero
    (X := X0) (q := bothThreeOddCore p.1) (q' := bothThreeOddCore p.2)
    (q0 := bothThreeOddCore p.1)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_coreBlockPeriod_coprime_three
      hp)
    (by
      unfold centeredRamanujanPairBlockPeriod
      exact dvd_mul_of_dvd_right
        (dvd_lcm_left (bothThreeOddCore p.1) (bothThreeOddCore p.2)) 2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseRightRawBlockSum_eq_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs) :
    rawEvenRamanujanBlockSum X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
        (3 * bothThreeOddCore p.2)
      =
    0 := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  exact rawEvenRamanujanBlockSum_three_mul_both_eq_zero
    (X := X0) (q := bothThreeOddCore p.1) (q' := bothThreeOddCore p.2)
    (q0 := bothThreeOddCore p.2)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_coreBlockPeriod_coprime_three
      hp)
    (by
      unfold centeredRamanujanPairBlockPeriod
      exact dvd_mul_of_dvd_right
        (dvd_lcm_right (bothThreeOddCore p.1) (bothThreeOddCore p.2)) 2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseFullBlockZero_of_corePairRawBlockSum_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs)
    (hcore :
      rawEvenRamanujanPairBlockSum X0
        (bothThreeOddCore p.1) (bothThreeOddCore p.2) = 0)
    (havg :
      ramanujanWindowAverage X0 (3 * bothThreeOddCore p.1) = 0
        ∨ ramanujanWindowAverage X0 (3 * bothThreeOddCore p.2) = 0) :
    bothThreeBaseFullBlockZeroAtX0 p := by
  unfold bothThreeBaseFullBlockZeroAtX0
  rw [centeredRamanujanPairFullEvenBlockSum_eq_rawBlock_decomposition]
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_basePairRawBlockSum_eq_zero_of_core
    hp hcore]
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseLeftRawBlockSum_eq_zero
    hp]
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coprimeCore_baseRightRawBlockSum_eq_zero
    hp]
  rcases havg with havgLeft | havgRight
  · rw [havgLeft]
    ring
  · rw [havgRight]
    ring

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
