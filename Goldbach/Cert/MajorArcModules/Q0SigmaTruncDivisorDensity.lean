import Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds
import Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorMoments
import Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion
import Goldbach.Cert.MajorArcModules.Q0SigmaTruncMomentScalars

/-! Exact full-period densities of the even-domain divisor coefficients. -/

namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorDensity

open scoped BigOperators ArithmeticFunction.Moebius
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds
open Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorMoments
open Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion
open Goldbach.Cert.DivisorWindowDiscrepancy

noncomputable section

def divisorAtom (q d : ℕ) : ℝ := if d ∣ q then (d : ℝ) * (μ (q / d) : ℝ) else 0

theorem divisorCoefficientRat_cast_eq_sum_atom (d : ℕ) :
    (divisorCoefficientRat d : ℝ) =
      ∑ q ∈ Finset.Icc 1 cutoff, (oddWeightRat q : ℝ) * divisorAtom q d := by
  rw [divisorCoefficientRat_cast]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h : d ∣ q <;> simp [divisorAtom, h] <;> ring

theorem divisorAtom_mean_density
    (q : ℕ) (hq : q ∈ Finset.Icc 1 cutoff) :
    (∑ d ∈ Finset.Icc 1 cutoff, divisorAtom q d / d) = if q = 1 then 1 else 0 := by
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hqQ := (Finset.mem_Icc.mp hq).2
  rw [← ramanujan_divisor_mean_density q hqpos,
    divisors_eq_filter_Icc hqpos hqQ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ q <;> simp [divisorAtom, h]

theorem divisorAtom_sum
    (q : ℕ) (hq : q ∈ Finset.Icc 1 cutoff) :
    (∑ d ∈ Finset.Icc 1 cutoff, divisorAtom q d) = (Nat.totient q : ℝ) := by
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  rw [totient_eq_sum_divisors_moebius q hqpos,
    divisors_eq_filter_Icc hqpos (Finset.mem_Icc.mp hq).2, Finset.sum_filter]
  rfl

theorem divisorCoefficient_sum_eq_weighted_totient :
    (∑ d ∈ Finset.Icc 1 cutoff, (divisorCoefficientRat d : ℝ)) =
      ∑ q ∈ Finset.Icc 1 cutoff, (oddWeightRat q : ℝ) * (Nat.totient q : ℝ) := by
  simp_rw [divisorCoefficientRat_cast_eq_sum_atom]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum, divisorAtom_sum q hq]

theorem divisorAtom_pair_density
    (q r : ℕ) (hq : q ∈ Finset.Icc 1 cutoff) (hr : r ∈ Finset.Icc 1 cutoff) :
    (∑ d ∈ Finset.Icc 1 cutoff, ∑ e ∈ Finset.Icc 1 cutoff,
      divisorAtom q d * divisorAtom r e / (Nat.lcm d e : ℝ)) =
      if q = r then (Nat.totient q : ℝ) else 0 := by
  have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  rw [← ramanujan_divisor_pair_density q r hqpos hrpos,
    divisors_eq_filter_Icc hqpos (Finset.mem_Icc.mp hq).2,
    divisors_eq_filter_Icc hrpos (Finset.mem_Icc.mp hr).2]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdq : d ∣ q
  · simp only [divisorAtom, if_pos hdq]
    apply Finset.sum_congr rfl
    intro e he
    by_cases her : e ∣ r <;> simp [her]
  · simp [divisorAtom, hdq]

theorem oddWeightRat_one : (oddWeightRat 1 : ℝ) = 2 := by
  norm_num [oddWeightRat, evenMultiplicity, cutoff, totientFast]

/-- The grouped finite truncation has full-even-period raw mean exactly two. -/
theorem divisorCoefficient_mean_density :
    (∑ d ∈ Finset.Icc 1 cutoff, (divisorCoefficientRat d : ℝ) / d) = 2 := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 cutoff, ∑ q ∈ Finset.Icc 1 cutoff,
        (oddWeightRat q : ℝ) * (divisorAtom q d / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [divisorCoefficientRat_cast_eq_sum_atom, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ q ∈ Finset.Icc 1 cutoff,
        (oddWeightRat q : ℝ) * (∑ d ∈ Finset.Icc 1 cutoff, divisorAtom q d / d) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
    _ = ∑ q ∈ Finset.Icc 1 cutoff,
        (oddWeightRat q : ℝ) * (if q = 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [divisorAtom_mean_density q hq]
    _ = 2 := by
      have h1 : 1 ∈ Finset.Icc 1 cutoff := by norm_num [cutoff]
      rw [Finset.sum_eq_single_of_mem 1 h1]
      · simp [oddWeightRat_one]
      · intro q hq hq1
        simp [hq1]

/-- Reorder the four finite indices used when expanding a quadratic divisor density. -/
private theorem sum_four_reorder (D R : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ d ∈ D, ∑ e ∈ D, ∑ q ∈ R, ∑ r ∈ R, f d e q r) =
      ∑ q ∈ R, ∑ r ∈ R, ∑ d ∈ D, ∑ e ∈ D, f d e q r := by
  calc
    _ = ∑ d ∈ D, ∑ q ∈ R, ∑ e ∈ D, ∑ r ∈ R, f d e q r := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = ∑ q ∈ R, ∑ d ∈ D, ∑ e ∈ D, ∑ r ∈ R, f d e q r := Finset.sum_comm
    _ = ∑ q ∈ R, ∑ d ∈ D, ∑ r ∈ R, ∑ e ∈ D, f d e q r := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm

/-- The quadratic divisor density is diagonal in the Ramanujan modulus. -/
theorem divisorCoefficient_pair_density :
    (∑ d ∈ Finset.Icc 1 cutoff, ∑ e ∈ Finset.Icc 1 cutoff,
      (divisorCoefficientRat d : ℝ) * (divisorCoefficientRat e : ℝ) /
        (Nat.lcm d e : ℝ)) =
      ∑ q ∈ Finset.Icc 1 cutoff, (oddWeightRat q : ℝ) ^ 2 * (Nat.totient q : ℝ) := by
  calc
    _ = ∑ d ∈ Finset.Icc 1 cutoff, ∑ e ∈ Finset.Icc 1 cutoff,
        ∑ q ∈ Finset.Icc 1 cutoff, ∑ r ∈ Finset.Icc 1 cutoff,
          ((oddWeightRat q : ℝ) * (oddWeightRat r : ℝ)) *
            (divisorAtom q d * divisorAtom r e / (Nat.lcm d e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [divisorCoefficientRat_cast_eq_sum_atom d, divisorCoefficientRat_cast_eq_sum_atom e,
        Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ q ∈ Finset.Icc 1 cutoff, ∑ r ∈ Finset.Icc 1 cutoff,
        ∑ d ∈ Finset.Icc 1 cutoff, ∑ e ∈ Finset.Icc 1 cutoff,
          ((oddWeightRat q : ℝ) * (oddWeightRat r : ℝ)) *
            (divisorAtom q d * divisorAtom r e / (Nat.lcm d e : ℝ)) :=
      sum_four_reorder _ _ _
    _ = ∑ q ∈ Finset.Icc 1 cutoff, ∑ r ∈ Finset.Icc 1 cutoff,
        ((oddWeightRat q : ℝ) * (oddWeightRat r : ℝ)) *
          (∑ d ∈ Finset.Icc 1 cutoff, ∑ e ∈ Finset.Icc 1 cutoff,
            divisorAtom q d * divisorAtom r e / (Nat.lcm d e : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mul_sum]
    _ = _ := weighted_orthogonal_kernel_sum _ _ _ _
      (fun q hq r hr => divisorAtom_pair_density q r hq hr)

/-- The sum of all divisor coefficients is the common-period spike value. -/
theorem divisorCoefficient_sum :
    (∑ d ∈ Finset.Icc 1 cutoff, (divisorCoefficientRat d : ℝ)) = (valueAtZeroRat : ℝ) := by
  rw [divisorCoefficient_sum_eq_weighted_totient,
    Q0SigmaTruncMomentScalars.sum_oddWeightRat_mul_totient_cast]

/-- Exact full-even-period raw second moment. -/
theorem divisorCoefficient_pair_density_eq_four_add_variance :
    (∑ d ∈ Finset.Icc 1 cutoff, ∑ e ∈ Finset.Icc 1 cutoff,
      (divisorCoefficientRat d : ℝ) * (divisorCoefficientRat e : ℝ) /
        (Nat.lcm d e : ℝ)) = 4 + (varianceRat : ℝ) := by
  rw [divisorCoefficient_pair_density,
    Q0SigmaTruncMomentScalars.sum_oddWeightRat_square_mul_totient_cast]

/-- Exact density of the reference square `(g-2)^2`. -/
theorem centered_divisor_density :
    (∑ d ∈ Finset.Icc 1 cutoff, ∑ e ∈ Finset.Icc 1 cutoff,
      (divisorCoefficientRat d : ℝ) * (divisorCoefficientRat e : ℝ) /
        (Nat.lcm d e : ℝ))
      - 4 * (∑ d ∈ Finset.Icc 1 cutoff, (divisorCoefficientRat d : ℝ) / d) + 4
      = (varianceRat : ℝ) := by
  rw [divisorCoefficient_pair_density_eq_four_add_variance, divisorCoefficient_mean_density]
  ring

end
end Goldbach.Cert.MajorArcModules.Q0SigmaTruncDivisorDensity
