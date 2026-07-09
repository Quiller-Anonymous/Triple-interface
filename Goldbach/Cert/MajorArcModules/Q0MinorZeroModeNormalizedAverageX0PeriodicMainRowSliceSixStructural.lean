import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainRowSliceSmall
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeDyadicTransport

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

private theorem X0_isEven_rowSlice005_structural : Goldbach.Windows.IsEven X0 := by
  norm_num [X0, Goldbach.Windows.IsEven]

private theorem not_isEven_of_odd_nat {n : ℕ} (hn : Odd n) :
    ¬ Goldbach.Windows.IsEven n := by
  intro hEven
  exact (Nat.not_even_iff_odd.mpr hn) (Goldbach.Windows.even_of_isEven hEven)

private theorem not_isEven_of_dvd_odd {d n : ℕ} (hdvd : d ∣ n) (hn : Odd n) :
    ¬ Goldbach.Windows.IsEven d := by
  intro hdEven
  have htwoDvdD : 2 ∣ d :=
    even_iff_two_dvd.mp (Goldbach.Windows.even_of_isEven hdEven)
  have htwoDvdN : 2 ∣ n := dvd_trans htwoDvdD hdvd
  exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr htwoDvdN)

private theorem not_isEven_of_mem_three_divisors
    {g : ℕ} (hg : g ∈ (3 : ℕ).divisors) :
    ¬ Goldbach.Windows.IsEven g := by
  have hgdvd : g ∣ 3 := (Nat.mem_divisors.mp hg).1
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgdvd (by norm_num)
  have hgle : g ≤ 3 := Nat.le_of_dvd (by norm_num) hgdvd
  interval_cases g
  · norm_num [Goldbach.Windows.IsEven]
  · norm_num at hgdvd
  · norm_num [Goldbach.Windows.IsEven]

theorem centeredRamanujanPairFullEvenBlockSum_X0_three_odd_coprime_eq_zero_for_rowSlice005
    {b : ℕ} (hbpos : 1 ≤ b) (hbOdd : Odd b) (hcop : Nat.Coprime 3 b) :
    centeredRamanujanPairFullEvenBlockSum X0 3 b = 0 := by
  rw [centeredRamanujanPairFullEvenBlockSum_eq_sum_gcdClassFullEvenBlockSums_for_bothThree_probe
    (X := X0) (q := 3) (q' := b) (by norm_num) hbpos]
  refine Finset.sum_eq_zero ?_
  intro g hg
  refine Finset.sum_eq_zero ?_
  intro h hh
  have hgOdd : ¬ Goldbach.Windows.IsEven g := not_isEven_of_mem_three_divisors hg
  have hhDvd : h ∣ b := (Nat.mem_divisors.mp hh).1
  have hhOdd : ¬ Goldbach.Windows.IsEven h := not_isEven_of_dvd_odd hhDvd hbOdd
  rw [centeredRamanujanGcdClassPairFullEvenBlockSum_eq_zero_of_isEven_eq_three_left_public
    X0_isEven_rowSlice005_structural hbpos hbOdd hcop
      (Finset.mem_filter.mpr ⟨hg, hgOdd⟩)
      (Finset.mem_filter.mpr ⟨hh, hhOdd⟩)]
  simp

theorem centeredRamanujanPairPeriodicMainTerm_X0_six_two_mul_eq_zero_of_odd_coprime_for_rowSlice005
    {b : ℕ} (hbpos : 1 ≤ b) (hbOdd : Odd b) (hcop : Nat.Coprime 3 b) :
    centeredRamanujanPairPeriodicMainTerm X0 6 (2 * b) = 0 := by
  have hfull :
      centeredRamanujanPairFullEvenBlockSum X0 3 b = 0 :=
    centeredRamanujanPairFullEvenBlockSum_X0_three_odd_coprime_eq_zero_for_rowSlice005
      hbpos hbOdd hcop
  have h :=
    centeredRamanujanPairPeriodicMainTerm_X0_two_mul_both_eq_zero_of_base_full_zero_for_bothThree_transport
      (q := 3) (q' := b) (by decide : Odd 3) hbOdd hfull
  simpa [show 2 * 3 = 6 by norm_num, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem centeredRamanujanPairPeriodicMainTerm_X0_six_three_mul_eq_zero_of_odd_core_for_rowSlice005
    {b : ℕ} (hbpos : 1 ≤ b) (hbOdd : Odd b) (hb3 : ¬ 3 ∣ b)
    (hbSq : Squarefree b) (hbne : b ≠ 1) :
    centeredRamanujanPairPeriodicMainTerm X0 6 (3 * b) = 0 := by
  have hfull :
      centeredRamanujanPairFullEvenBlockSum X0 3 (3 * b) = 0 :=
    centeredRamanujanPairFullEvenBlockSum_X0_three_three_mul_eq_zero_of_odd_core
      hbpos hbOdd hb3 hbSq hbne
  have h :=
    centeredRamanujanPairPeriodicMainTerm_X0_two_mul_left_eq_zero_of_base_full_zero_for_bothThree_transport
      (q := 3) (q' := 3 * b) (by decide : Odd 3) ((by decide : Odd 3).mul hbOdd) hfull
  simpa [show 2 * 3 = 6 by norm_num, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem centeredRamanujanPairPeriodicMainTerm_X0_six_six_mul_eq_zero_of_odd_core_for_rowSlice005
    {b : ℕ} (hbpos : 1 ≤ b) (hbOdd : Odd b) (hb3 : ¬ 3 ∣ b)
    (hbSq : Squarefree b) (hbne : b ≠ 1) :
    centeredRamanujanPairPeriodicMainTerm X0 6 (6 * b) = 0 := by
  have hfull :
      centeredRamanujanPairFullEvenBlockSum X0 3 (3 * b) = 0 :=
    centeredRamanujanPairFullEvenBlockSum_X0_three_three_mul_eq_zero_of_odd_core
      hbpos hbOdd hb3 hbSq hbne
  have h :=
    centeredRamanujanPairPeriodicMainTerm_X0_two_mul_both_eq_zero_of_base_full_zero_for_bothThree_transport
      (q := 3) (q' := 3 * b) (by decide : Odd 3) ((by decide : Odd 3).mul hbOdd) hfull
  simpa [show 2 * 3 = 6 by norm_num, show 2 * (3 * b) = 6 * b by ring,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
