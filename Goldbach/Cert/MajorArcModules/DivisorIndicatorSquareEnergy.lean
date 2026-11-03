import Goldbach.Cert.MajorArcModules.DivisorWindowDiscrepancy
import Goldbach.Cert.MajorArcModules.IndicatorSquareCoefficientMass

/-!
# Uniform window energy for a finite divisor-indicator square

Combine diagonal and linear terms before taking absolute values. Multiple ordered pairs may have
the same lcm; the proof keeps their indices separate and applies the unit count discrepancy to each.
-/

namespace Goldbach.Cert.MajorArcModules.DivisorIndicatorSquareEnergy

open scoped BigOperators
open Goldbach.Cert.DivisorWindowDiscrepancy
open Goldbach.Cert.MajorArcModules.IndicatorSquareCoefficientMass

theorem sum_single_divisor_Ioc_le_density_add_abs
    (A m d : ℕ) (c : ℝ) (hd : 0 < d) :
    (∑ n ∈ Finset.Ioc A (A + m), if d ∣ n then c else 0)
      ≤ (m : ℝ) * (c / (d : ℝ)) + |c| := by
  have hcount := abs_divisorCount_Ioc_sub_density_le_one A m d hd
  have hprod :
      c * ((divisorCount (Finset.Ioc A (A + m)) d : ℝ) - (m : ℝ) / d) ≤ |c| := by
    calc
      _ ≤ |c * ((divisorCount (Finset.Ioc A (A + m)) d : ℝ) - (m : ℝ) / d)| :=
        le_abs_self _
      _ = |c| * |(divisorCount (Finset.Ioc A (A + m)) d : ℝ) - (m : ℝ) / d| :=
        abs_mul _ _
      _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left hcount (abs_nonneg _)
      _ = |c| := mul_one _
  have hsum :
      (∑ n ∈ Finset.Ioc A (A + m), if d ∣ n then c else 0)
        = c * (divisorCount (Finset.Ioc A (A + m)) d : ℝ) := by
    rw [← Finset.sum_filter]
    simp [divisorCount, nsmul_eq_mul, mul_comm]
  rw [hsum]
  calc
    c * (divisorCount (Finset.Ioc A (A + m)) d : ℝ)
        = (m : ℝ) * (c / (d : ℝ))
          + c * ((divisorCount (Finset.Ioc A (A + m)) d : ℝ) - (m : ℝ) / d) := by ring
    _ ≤ (m : ℝ) * (c / (d : ℝ)) + |c| := add_le_add_left hprod _

/-- Indexed divisor sums need no injectivity assumption on their divisor map. -/
theorem sum_indexed_divisors_Ioc_le_density_add_l1
    {ι : Type*} (A m : ℕ) (s : Finset ι) (d : ι → ℕ) (C : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) :
    (∑ n ∈ Finset.Ioc A (A + m), ∑ i ∈ s, if d i ∣ n then C i else 0)
      ≤ (m : ℝ) * (∑ i ∈ s, C i / (d i : ℝ)) + ∑ i ∈ s, |C i| := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i ∈ s, ((m : ℝ) * (C i / (d i : ℝ)) + |C i|) :=
      Finset.sum_le_sum fun i hi => sum_single_divisor_Ioc_le_density_add_abs A m (d i) (C i) (hd i hi)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Exact expansion of a finite divisor-indicator square at one integer. -/
theorem divisor_indicator_square_expansion
    (s : Finset ℕ) (B : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    ((∑ i ∈ s, if i ∣ n then B i else 0) - a) ^ 2
      = a ^ 2 + (∑ i ∈ s, if i ∣ n then B i ^ 2 - 2 * a * B i else 0)
          + ∑ p ∈ s ×ˢ s,
              if Nat.lcm p.1 p.2 ∣ n then (if p.1 = p.2 then 0 else B p.1 * B p.2) else 0 := by
  have hsq := indicator_square_expansion s B (fun i => if i ∣ n then (1 : ℝ) else 0) a
    (by intro i hi; by_cases h : i ∣ n <;> simp [h])
  simp only [mul_ite, mul_one, mul_zero] at hsq
  rw [hsq]
  congr 1
  unfold offDiagonalMass
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases hij : i = j
  · simp [hij]
  · by_cases hin : i ∣ n <;> by_cases hjn : j ∣ n <;>
      simp [hij, hin, hjn, Nat.lcm_dvd_iff]

/-- Uniform raw energy from the exact density and the expanded coefficient mass. -/
theorem divisor_indicator_square_Ioc_le_density_add_coefficientMass
    (A m : ℕ) (s : Finset ℕ) (B : ℕ → ℝ) (a : ℝ)
    (hd : ∀ i ∈ s, 0 < i) (hB : ∀ i ∈ s, 0 ≤ B i) :
    (∑ n ∈ Finset.Ioc A (A + m), ((∑ i ∈ s, if i ∣ n then B i else 0) - a) ^ 2)
      ≤ (m : ℝ) *
          (a ^ 2 + (∑ i ∈ s, (B i ^ 2 - 2 * a * B i) / (i : ℝ))
            + ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else B i * B j / (Nat.lcm i j : ℝ))
        + coefficientMass s B a := by
  let C : ℕ → ℝ := fun i => B i ^ 2 - 2 * a * B i
  let D : ℕ × ℕ → ℝ := fun p => if p.1 = p.2 then 0 else B p.1 * B p.2
  have hDpos : ∀ p ∈ s ×ˢ s, 0 ≤ D p := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hi, hj⟩
    dsimp [D]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hB p.1 hi) (hB p.2 hj)
  have hdiag := sum_indexed_divisors_Ioc_le_density_add_l1 A m s id C hd
  have hpair := sum_indexed_divisors_Ioc_le_density_add_l1 A m (s ×ˢ s)
    (fun p => Nat.lcm p.1 p.2) D
    (by
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨hi, hj⟩
      exact Nat.lcm_pos (hd p.1 hi) (hd p.2 hj))
  have hpairDensity :
      (∑ p ∈ s ×ˢ s, D p / (Nat.lcm p.1 p.2 : ℝ))
        = ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else B i * B j / (Nat.lcm i j : ℝ) := by
    rw [Finset.sum_product]
    simp only [D, ite_div, zero_div]
  have hpairMass : (∑ p ∈ s ×ˢ s, |D p|) = offDiagonalMass s B := by
    calc
      _ = ∑ p ∈ s ×ˢ s, D p :=
        Finset.sum_congr rfl fun p hp => abs_of_nonneg (hDpos p hp)
      _ = offDiagonalMass s B := by rw [Finset.sum_product]; rfl
  rw [hpairDensity, hpairMass] at hpair
  have hexpand :
      (∑ n ∈ Finset.Ioc A (A + m), ((∑ i ∈ s, if i ∣ n then B i else 0) - a) ^ 2)
        = (m : ℝ) * a ^ 2
          + (∑ n ∈ Finset.Ioc A (A + m), ∑ i ∈ s, if i ∣ n then C i else 0)
          + ∑ n ∈ Finset.Ioc A (A + m), ∑ p ∈ s ×ˢ s,
              if Nat.lcm p.1 p.2 ∣ n then D p else 0 := by
    calc
      _ = ∑ n ∈ Finset.Ioc A (A + m),
            (a ^ 2 + (∑ i ∈ s, if i ∣ n then C i else 0)
              + ∑ p ∈ s ×ˢ s, if Nat.lcm p.1 p.2 ∣ n then D p else 0) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              exact divisor_indicator_square_expansion s B a n
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp
  rw [hexpand]
  dsimp [id, C] at hdiag
  unfold coefficientMass
  nlinarith [sq_nonneg a]

end Goldbach.Cert.MajorArcModules.DivisorIndicatorSquareEnergy
