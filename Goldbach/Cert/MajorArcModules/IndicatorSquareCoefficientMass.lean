import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coefficient mass after combining two diagonal indicator terms

For idempotent indicators, the diagonal and linear terms in `(∑ i, B i * u i - a)²`
share the coefficient `B i ^ 2 - 2 * a * B i`. If `0 ≤ B i ≤ 2 * a`, combining
those terms before taking absolute values saves `2 * B i ^ 2`. The estimates below
retain this saving at two distinct indices and require no arithmetic input.
-/

namespace Goldbach.Cert.MajorArcModules.IndicatorSquareCoefficientMass

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- Ordered off-diagonal products in the square of a finite sum. -/
def offDiagonalMass (s : Finset ι) (B : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, if i = j then 0 else B i * B j

theorem offDiagonalMass_eq_square_sub_diagonal
    (s : Finset ι) (B : ι → ℝ) :
    offDiagonalMass s B = (∑ i ∈ s, B i) ^ 2 - ∑ i ∈ s, B i ^ 2 := by
  have hsplit :
      (∑ i ∈ s, ∑ j ∈ s, B i * B j)
        = (∑ i ∈ s, B i ^ 2) + offDiagonalMass s B := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, B i * B j)
          = ∑ i ∈ s, (B i ^ 2 + ∑ j ∈ s, if i = j then 0 else B i * B j) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                (∑ j ∈ s, B i * B j)
                    = ∑ j ∈ s,
                        ((if i = j then B i ^ 2 else 0)
                          + (if i = j then 0 else B i * B j)) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        by_cases hij : i = j
                        · subst j
                          simp [pow_two]
                        · simp [hij]
                _ = B i ^ 2 + ∑ j ∈ s, if i = j then 0 else B i * B j := by
                      rw [Finset.sum_add_distrib]
                      simp [hi]
      _ = (∑ i ∈ s, B i ^ 2) + offDiagonalMass s B := by
            rw [Finset.sum_add_distrib]
            rfl
  have hfull : (∑ i ∈ s, ∑ j ∈ s, B i * B j) = (∑ i ∈ s, B i) ^ 2 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, pow_two]
  rw [hfull] at hsplit
  linarith

/-- Exact indicator-square expansion, with each diagonal and linear coefficient combined. -/
theorem indicator_square_expansion
    (s : Finset ι) (B u : ι → ℝ) (a : ℝ)
    (hu : ∀ i ∈ s, u i ^ 2 = u i) :
    ((∑ i ∈ s, B i * u i) - a) ^ 2
      = a ^ 2 + (∑ i ∈ s, (B i ^ 2 - 2 * a * B i) * u i)
          + offDiagonalMass s (fun i => B i * u i) := by
  have hdiag :
      (∑ i ∈ s, (B i * u i) ^ 2) = ∑ i ∈ s, B i ^ 2 * u i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [mul_pow, hu i hi]
  have hlinear :
      (∑ i ∈ s, (B i ^ 2 - 2 * a * B i) * u i)
        = (∑ i ∈ s, B i ^ 2 * u i) - 2 * a * (∑ i ∈ s, B i * u i) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    ring
  rw [offDiagonalMass_eq_square_sub_diagonal, hdiag, hlinear]
  ring

private theorem abs_diagonal_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |b ^ 2 - 2 * a * b| ≤ b ^ 2 + 2 * a * b := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg b], by nlinarith⟩

private theorem abs_diagonal_eq (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ 2 * a) :
    |b ^ 2 - 2 * a * b| = 2 * a * b - b ^ 2 := by
  have hsq : b ^ 2 ≤ 2 * a * b := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]
  rw [abs_of_nonpos (sub_nonpos.mpr hsq)]
  ring

/-- Two selected diagonal coefficients save their self-products before absolute values are taken. -/
theorem diagonal_mass_le_with_two_cancellations
    (s : Finset ι) (B : ι → ℝ) (a : ℝ) (p q : ι)
    (ha : 0 ≤ a) (hB : ∀ i ∈ s, 0 ≤ B i)
    (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q)
    (hBp : B p ≤ 2 * a) (hBq : B q ≤ 2 * a) :
    (∑ i ∈ s, |B i ^ 2 - 2 * a * B i|)
      ≤ (∑ i ∈ s, B i ^ 2) + 2 * a * (∑ i ∈ s, B i)
          - 2 * (B p ^ 2 + B q ^ 2) := by
  have hpoint : ∀ i ∈ s,
      |B i ^ 2 - 2 * a * B i|
        ≤ B i ^ 2 + 2 * a * B i
          - (if i = p then 2 * B i ^ 2 else 0)
          - (if i = q then 2 * B i ^ 2 else 0) := by
    intro i hi
    by_cases hip : i = p
    · subst i
      rw [abs_diagonal_eq a (B p) (hB p hp) hBp]
      simp only [if_true, if_neg hpq]
      linarith
    · by_cases hiq : i = q
      · subst i
        rw [abs_diagonal_eq a (B q) (hB q hq) hBq]
        simp only [if_neg hip, if_true]
        linarith
      · simpa only [if_neg hip, if_neg hiq, sub_zero] using
          abs_diagonal_le a (B i) ha (hB i hi)
  calc
    (∑ i ∈ s, |B i ^ 2 - 2 * a * B i|)
        ≤ ∑ i ∈ s, (B i ^ 2 + 2 * a * B i
            - (if i = p then 2 * B i ^ 2 else 0)
            - (if i = q then 2 * B i ^ 2 else 0)) := Finset.sum_le_sum hpoint
    _ = (∑ i ∈ s, B i ^ 2) + 2 * a * (∑ i ∈ s, B i)
          - 2 * (B p ^ 2 + B q ^ 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            simp only [Finset.sum_ite_eq', hp, hq, if_pos]
            rw [← Finset.mul_sum]
            ring

/-- Absolute coefficient mass of the expanded square, prior to grouping equal indicator products. -/
def coefficientMass (s : Finset ι) (B : ι → ℝ) (a : ℝ) : ℝ :=
  a ^ 2 + (∑ i ∈ s, |B i ^ 2 - 2 * a * B i|) + offDiagonalMass s B

/-- Combining two diagonal/linear terms improves the crude `(a + ∑ B)²` coefficient budget. -/
theorem coefficientMass_le_with_two_cancellations
    (s : Finset ι) (B : ι → ℝ) (a : ℝ) (p q : ι)
    (ha : 0 ≤ a) (hB : ∀ i ∈ s, 0 ≤ B i)
    (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q)
    (hBp : B p ≤ 2 * a) (hBq : B q ≤ 2 * a) :
    coefficientMass s B a
      ≤ (a + ∑ i ∈ s, B i) ^ 2 - 2 * (B p ^ 2 + B q ^ 2) := by
  have hdiag := diagonal_mass_le_with_two_cancellations s B a p q ha hB hp hq hpq hBp hBq
  unfold coefficientMass
  rw [offDiagonalMass_eq_square_sub_diagonal]
  nlinarith

end Goldbach.Cert.MajorArcModules.IndicatorSquareCoefficientMass
