import Mathlib.Analysis.PSeries
import Mathlib.Data.Rat.Cast.Order
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic

/-!
# Elementary lower bound for the finite twin-prime Euler product

These lemmas isolate the finite arithmetic and the elementary product inequality used by the
uniform Ramanujan-window argument.  They do not identify the project's series-defined `C2` with
the infinite Euler product; that analytic identification remains a separate obligation.
-/

namespace Goldbach.Cert.C2EulerProductLowerBound

open scoped BigOperators

/-- Prime factors through a finite cutoff, with the exceptional prime two omitted. -/
def oddPrimesThrough (R : ℕ) : Finset ℕ :=
  (Finset.Icc 3 R).filter Nat.Prime

/-- Computable rational partial twin-prime product. -/
def partialProductRat (R : ℕ) : ℚ :=
  ∏ p ∈ oddPrimesThrough R, (1 - 1 / ((p : ℚ) - 1) ^ 2)

/-- The same partial product as a real number. -/
noncomputable def partialProduct (R : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesThrough R, (1 - 1 / ((p : ℝ) - 1) ^ 2)

theorem partialProduct_eq_rat (R : ℕ) :
    partialProduct R = (partialProductRat R : ℝ) := by
  simp [partialProduct, partialProductRat, Rat.cast_prod]

private theorem partialProductRat_10000_tail_gt :
    (33 : ℚ) / 50 < partialProductRat 10000 * (1 - 1 / 9999) := by
  native_decide

/-- The finite product retains enough margin after the elementary square-tail loss. -/
theorem partialProduct_10000_tail_gt :
    (33 : ℝ) / 50 < partialProduct 10000 * (1 - 1 / 9999) := by
  rw [partialProduct_eq_rat]
  have h := (Rat.cast_lt (K := ℝ)).2 partialProductRat_10000_tail_gt
  push_cast at h
  exact h

/-- Finite Bonferroni/product lower bound; no convergence assumption is needed. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hi0 : 0 ≤ a i := ha0 i (Finset.mem_insert_self i s)
      have hi1 : a i ≤ 1 := ha1 i (Finset.mem_insert_self i s)
      have hs0 : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha0 j (Finset.mem_insert_of_mem hj)
      have hs1 : ∀ j ∈ s, a j ≤ 1 := fun j hj => ha1 j (Finset.mem_insert_of_mem hj)
      have hsum0 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg hs0
      have hmul := mul_le_mul_of_nonneg_left (ih hs0 hs1) (sub_nonneg.mpr hi1)
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      nlinarith [mul_nonneg hi0 hsum0]

/-- A finite prime-tail sum estimate transfers directly to a finite prime-tail product. -/
theorem prime_tail_product_lower (s : Finset ℕ) (hs : ∀ p ∈ s, 3 ≤ p)
    {δ : ℝ} (htail : (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤ δ) :
    1 - δ ≤ ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  apply le_trans (sub_le_sub_left htail 1)
  apply one_sub_sum_le_prod_one_sub
  · intro p hp
    positivity
  · intro p hp
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hs p hp
    have hsq : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    exact (div_le_one (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 2)).2 hsq

/-- The tail estimate used here majorizes primes by all integers, so no prime-counting input is
required. -/
theorem finite_tail_sum_le (s : Finset ℕ) (hs : ∀ p ∈ s, 10000 < p) :
    (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤ 1 / 9999 := by
  classical
  let t := s.image (fun p => p - 1)
  let M := max 10000 (s.sup id)
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (↑s : Set ℕ) := by
    intro a ha b hb hab
    have ha' := hs a ha
    have hb' := hs b hb
    change a - 1 = b - 1 at hab
    omega
  have hsum : (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2)
      = ∑ k ∈ t, ((k : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      have hp1 : 1 ≤ p := by have := hs p hp; omega
      simp [Nat.cast_sub hp1, one_div]
    · exact hinj
  have hsubset : t ⊆ Finset.Ioc 9999 M := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hpR := hs p hp
    have hpM : p ≤ M := le_trans (Finset.le_sup (f := id) hp) (le_max_right _ _)
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  rw [hsum]
  calc
    (∑ k ∈ t, ((k : ℝ) ^ 2)⁻¹)
        ≤ ∑ k ∈ Finset.Ioc 9999 M, ((k : ℝ) ^ 2)⁻¹ := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ ≤ (9999 : ℝ)⁻¹ - (M : ℝ)⁻¹ := by
          apply sum_Ioc_inv_sq_le_sub (by norm_num : (9999 : ℕ) ≠ 0)
          exact le_trans (by norm_num : (9999 : ℕ) ≤ 10000) (le_max_left _ _)
    _ ≤ 1 / 9999 := by
          simpa only [one_div] using
            (sub_le_self ((9999 : ℝ)⁻¹) (by positivity : (0 : ℝ) ≤ (M : ℝ)⁻¹))

theorem finite_tail_product_lower (s : Finset ℕ) (hs : ∀ p ∈ s, 10000 < p) :
    1 - (1 : ℝ) / 9999 ≤ ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  apply prime_tail_product_lower s (fun p hp => by have := hs p hp; omega)
  exact finite_tail_sum_le s hs

/-- Every longer partial product has the same explicit lower bound. -/
theorem partialProduct_ge_fixedLower {R : ℕ} (hR : 10000 ≤ R) :
    partialProduct 10000 * (1 - (1 : ℝ) / 9999) ≤ partialProduct R := by
  classical
  have hsub : oddPrimesThrough 10000 ⊆ oddPrimesThrough R := by
    intro p hp
    simp only [oddPrimesThrough, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, le_trans hp.1.2 hR⟩, hp.2⟩
  have htail : ∀ p ∈ oddPrimesThrough R \ oddPrimesThrough 10000, 10000 < p := by
    intro p hp
    obtain ⟨hpR, hpNot⟩ := Finset.mem_sdiff.mp hp
    simp only [oddPrimesThrough, Finset.mem_filter, Finset.mem_Icc] at hpR hpNot
    by_contra hn
    exact hpNot ⟨⟨hpR.1.1, le_of_not_gt hn⟩, hpR.2⟩
  have hpositive : 0 ≤ partialProduct 10000 := by
    unfold partialProduct
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have hsq : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hdiv : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 :=
      (div_le_one (by positivity : (0 : ℝ) < ((p : ℝ) - 1) ^ 2)).2 hsq
    linarith
  have hm := mul_le_mul_of_nonneg_right
    (finite_tail_product_lower (oddPrimesThrough R \ oddPrimesThrough 10000) htail) hpositive
  have heq := Finset.prod_sdiff (f := fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2) hsub
  calc
    partialProduct 10000 * (1 - (1 : ℝ) / 9999)
        = (1 - (1 : ℝ) / 9999) * partialProduct 10000 := mul_comm _ _
    _ ≤ (∏ p ∈ oddPrimesThrough R \ oddPrimesThrough 10000,
          (1 - 1 / ((p : ℝ) - 1) ^ 2)) * partialProduct 10000 := hm
    _ = partialProduct R := by simpa only [partialProduct] using heq

/-- Any limit of these prime partial products is strictly above `0.66`.

The hypothesis is an ordinary convergence statement.  Applying it to the canonical series-defined
constant requires the independent Ramanujan/Euler-product identification.
-/
theorem lower_of_tendsto {C : ℝ}
    (hlimit : Filter.Tendsto partialProduct Filter.atTop (nhds C)) :
    (33 : ℝ) / 50 < C := by
  have hle : partialProduct 10000 * (1 - (1 : ℝ) / 9999) ≤ C := by
    apply ge_of_tendsto hlimit
    filter_upwards [Filter.eventually_ge_atTop 10000] with R hR
    exact partialProduct_ge_fixedLower hR
  exact lt_of_lt_of_le partialProduct_10000_tail_gt hle

end Goldbach.Cert.C2EulerProductLowerBound
