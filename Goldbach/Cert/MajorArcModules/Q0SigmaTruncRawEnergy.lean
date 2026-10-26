import Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorDensity
import Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorPositivity
import Goldbach.Cert.MajorArcModules.IndicatorSquareCoefficientMass
import Goldbach.Cert.MajorArcModules.DivisorIndicatorSquareEnergy

/-! Uniform raw energy of the finite even Ramanujan observable. -/

namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncRawEnergy

open scoped BigOperators
open Goldbach.AO_OffDiag.TailBlock
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncEvenDivisor
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorDensity
open Goldbach.Cert.MajorArcModules.IndicatorSquareCoefficientMass
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorPositivity
open Goldbach.Cert.MajorArcModules.DivisorIndicatorSquareEnergy

noncomputable section

def nonconstantDivisors : Finset ℕ := Finset.Icc 2 cutoff

def B (d : ℕ) : ℝ := (divisorCoefficientRat d : ℝ)

theorem fullDivisors_eq_insert :
    Finset.Icc 1 cutoff = insert 1 nonconstantDivisors := by
  ext d
  simp only [nonconstantDivisors, Finset.mem_Icc, Finset.mem_insert]
  dsimp [cutoff]
  omega

theorem one_not_mem_nonconstantDivisors : 1 ∉ nonconstantDivisors := by
  simp [nonconstantDivisors]

theorem B_nonneg (d : ℕ) (hd : d ∈ nonconstantDivisors) : 0 ≤ B d := by
  apply divisorCoefficientRat_cast_nonneg
  obtain ⟨hdlo, hdhi⟩ := Finset.mem_Icc.mp hd
  exact Finset.mem_Icc.mpr ⟨by omega, hdhi⟩

/-- Separate the constant divisor before combining each diagonal with its linear term. -/
theorem density_split_one (s : Finset ℕ) (b : ℕ → ℝ) (h1 : 1 ∉ s) :
    (2 - b 1) ^ 2 +
      (∑ i ∈ s, (b i ^ 2 - 2 * (2 - b 1) * b i) / (i : ℝ)) +
      (∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else b i * b j / (Nat.lcm i j : ℝ)) =
        (∑ i ∈ insert 1 s, ∑ j ∈ insert 1 s, b i * b j / (Nat.lcm i j : ℝ))
          - 4 * (∑ i ∈ insert 1 s, b i / (i : ℝ)) + 4 := by
  have hpair :
      (∑ i ∈ s, ∑ j ∈ s, b i * b j / (Nat.lcm i j : ℝ)) =
        (∑ i ∈ s, b i ^ 2 / (i : ℝ)) +
        ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else b i * b j / (Nat.lcm i j : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ∑ j ∈ s,
          ((if i = j then b i ^ 2 / (i : ℝ) else 0) +
            (if i = j then 0 else b i * b j / (Nat.lcm i j : ℝ))) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j
        · subst j
          simp [pow_two]
        · simp [hij]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [hi]
  have hfullpair :
      (∑ i ∈ insert 1 s, ∑ j ∈ insert 1 s, b i * b j / (Nat.lcm i j : ℝ)) =
        b 1 ^ 2 + 2 * b 1 * (∑ i ∈ s, b i / (i : ℝ)) +
          ∑ i ∈ s, ∑ j ∈ s, b i * b j / (Nat.lcm i j : ℝ) := by
    simp only [Finset.sum_insert h1, Nat.lcm_one_left, Nat.lcm_one_right,
      Nat.cast_one, div_one, Finset.sum_add_distrib]
    have hleft : (∑ i ∈ s, b 1 * b i / (i : ℝ)) =
        b 1 * ∑ i ∈ s, b i / (i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hright : (∑ i ∈ s, b i * b 1 / (i : ℝ)) =
        b 1 * ∑ i ∈ s, b i / (i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hleft, hright]
    ring
  have hlinear :
      (∑ i ∈ s, (b i ^ 2 - 2 * (2 - b 1) * b i) / (i : ℝ)) =
        (∑ i ∈ s, b i ^ 2 / (i : ℝ)) -
          2 * (2 - b 1) * ∑ i ∈ s, b i / (i : ℝ) := by
    simp only [sub_div, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfullpair, hpair, Finset.sum_insert h1]
  simp only [Nat.cast_one, div_one]
  rw [hlinear]
  ring

theorem nonconstant_density_eq_variance :
    (2 - B 1) ^ 2 +
      (∑ i ∈ nonconstantDivisors, (B i ^ 2 - 2 * (2 - B 1) * B i) / (i : ℝ)) +
      (∑ i ∈ nonconstantDivisors, ∑ j ∈ nonconstantDivisors,
        if i = j then 0 else B i * B j / (Nat.lcm i j : ℝ)) =
      (varianceRat : ℝ) := by
  rw [density_split_one _ _ one_not_mem_nonconstantDivisors, ← fullDivisors_eq_insert]
  exact centered_divisor_density

theorem nonconstant_coefficient_sum :
    (∑ i ∈ nonconstantDivisors, B i) = (valueAtZeroRat : ℝ) - B 1 := by
  have h := divisorCoefficient_sum
  rw [fullDivisors_eq_insert, Finset.sum_insert one_not_mem_nonconstantDivisors] at h
  change B 1 + (∑ i ∈ nonconstantDivisors, B i) = (valueAtZeroRat : ℝ) at h
  linarith

theorem raw_minus_two_eq_nonconstant (n : ℕ) :
    sigma_trunc_Q0 (2 * n) - 2 =
      (∑ i ∈ nonconstantDivisors, if i ∣ n then B i else 0) - (2 - B 1) := by
  rw [sigma_trunc_Q0_even_eq_divisorCoefficientRat, fullDivisors_eq_insert,
    Finset.sum_insert one_not_mem_nonconstantDivisors]
  simp only [one_dvd, if_true]
  dsimp [B]
  ring

theorem nonconstant_coefficientMass_le
    (hB : ∀ i ∈ nonconstantDivisors, 0 ≤ B i) :
    coefficientMass nonconstantDivisors B (2 - B 1) ≤ (twoTermL1BoundRat : ℝ) := by
  have hB1 : B 1 < (1321 : ℝ) / 1000 := by
    dsimp [B]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      ((Rat.cast_lt (K := ℝ)).2 divisorCoefficientRat_one_bounds.2)
  have h3 : B 3 ≤ 2 * (2 - B 1) := by
    dsimp [B]
    exact_mod_cast three_five_le_twice_mean_gap.1
  have h5 : B 5 ≤ 2 * (2 - B 1) := by
    dsimp [B]
    exact_mod_cast three_five_le_twice_mean_gap.2
  have hmass := coefficientMass_le_with_two_cancellations
    nonconstantDivisors B (2 - B 1) 3 5 (by linarith) hB
      (by norm_num [nonconstantDivisors, cutoff])
      (by norm_num [nonconstantDivisors, cutoff]) (by decide) h3 h5
  rw [nonconstant_coefficient_sum] at hmass
  have hcast : (twoTermL1BoundRat : ℝ) =
      (2 + (valueAtZeroRat : ℝ) - 2 * B 1) ^ 2 - 2 * (B 3 ^ 2 + B 5 ^ 2) := by
    simp [twoTermL1BoundRat, B]
  calc
    _ ≤ ((2 - B 1) + ((valueAtZeroRat : ℝ) - B 1)) ^ 2 -
        2 * (B 3 ^ 2 + B 5 ^ 2) := hmass
    _ = _ := by rw [hcast]; ring

theorem nonconstant_coefficientMass_le_twoTermL1BoundRat :
    coefficientMass nonconstantDivisors B (2 - B 1) ≤ (twoTermL1BoundRat : ℝ) :=
  nonconstant_coefficientMass_le B_nonneg

/-- A uniform raw bound for every interval of consecutive half-arguments. -/
theorem raw_reference_energy_Ioc_le (A m : ℕ) :
    (∑ n ∈ Finset.Ioc A (A + m), (sigma_trunc_Q0 (2 * n) - 2) ^ 2) ≤
      (m : ℝ) * (varianceRat : ℝ) + (twoTermL1BoundRat : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.Ioc A (A + m),
        ((∑ i ∈ nonconstantDivisors, if i ∣ n then B i else 0) - (2 - B 1)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [raw_minus_two_eq_nonconstant]
    _ ≤ (m : ℝ) *
        ((2 - B 1) ^ 2 +
          (∑ i ∈ nonconstantDivisors, (B i ^ 2 - 2 * (2 - B 1) * B i) / (i : ℝ)) +
          (∑ i ∈ nonconstantDivisors, ∑ j ∈ nonconstantDivisors,
            if i = j then 0 else B i * B j / (Nat.lcm i j : ℝ))) +
          coefficientMass nonconstantDivisors B (2 - B 1) :=
      divisor_indicator_square_Ioc_le_density_add_coefficientMass A m
        nonconstantDivisors B (2 - B 1)
          (by intro i hi; have := (Finset.mem_Icc.mp hi).1; omega) B_nonneg
    _ ≤ _ := by
      rw [nonconstant_density_eq_variance]
      exact add_le_add_left nonconstant_coefficientMass_le_twoTermL1BoundRat _

theorem raw_reference_energy_Ioc_le_5001 (A m : ℕ) (hm : m ≤ 5001) :
    (∑ n ∈ Finset.Ioc A (A + m), (sigma_trunc_Q0 (2 * n) - 2) ^ 2) ≤
      5001 * (varianceRat : ℝ) + (twoTermL1BoundRat : ℝ) := by
  have hv : (0 : ℝ) ≤ (varianceRat : ℝ) := by exact_mod_cast varianceRat_nonneg
  exact (raw_reference_energy_Ioc_le A m).trans
    (add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hv) _)

end
end Goldbach.Cert.MajorArcModules.Q0SigmaTruncRawEnergy
