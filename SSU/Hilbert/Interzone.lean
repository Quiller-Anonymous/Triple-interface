import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Dist

/-!
Hilbert-space almost-orthogonality engine (pure).

This is the SSU package’s project-neutral “interzone” brick:

Let `v j` be a finite family of vectors in a complex Hilbert space `E`. Assume:

* diagonal weights `D j ≥ 0`;
* Gram control `‖⟪v i, v j⟫‖ ≤ a(dist i j) * √(D i) * √(D j)`;
* a uniform row-sum bound `∑_{j∈J} a(dist i j) ≤ C`.

Then:

`‖∑_{j∈J} v j‖² ≤ C * ∑_{j∈J} D j`.

This is standard Cotlar–Stein / Schur-type “almost orthogonality” glue and contains no arithmetic.
-/

namespace SSU
namespace Hilbert

open scoped BigOperators

open Complex

noncomputable section

local notation "⟪" x ", " y "⟫" => inner ℂ x y

private lemma re_sum_le_sum_norm {α : Type*} [DecidableEq α] {s : Finset α} (f : α → ℂ) :
    (∑ a ∈ s, (f a).re) ≤ ∑ a ∈ s, ‖f a‖ := by
  classical
  refine Finset.sum_le_sum ?_
  intro a ha
  exact re_le_norm (f a)

private lemma mul_sqrt_mul_sqrt_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  have h := two_mul_le_add_sq (Real.sqrt a) (Real.sqrt b)
  have hsqa : (Real.sqrt a) ^ 2 = a := by
    simpa [pow_two] using (Real.sq_sqrt ha)
  have hsqb : (Real.sqrt b) ^ 2 = b := by
    simpa [pow_two] using (Real.sq_sqrt hb)
  have h' : 2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
    simpa [pow_two, hsqa, hsqb, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm,
      add_assoc] using h
  nlinarith

/-!
### The core interzone inequality (finite family)

The statement is formulated in an arbitrary complex inner-product space `E`. In applications,
`E` will be an `L²`-type space such as `EuclideanSpace ℂ ι`.
-/

theorem norm_sum_sq_le_of_rowSum_gram_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {J : Finset ℕ} {v : ℕ → E} {D : ℕ → ℝ} {a : ℕ → ℝ} {C : ℝ}
    (hD : ∀ j ∈ J, 0 ≤ D j)
    (ha : ∀ k, 0 ≤ a k)
    (hGram :
      ∀ i ∈ J, ∀ j ∈ J,
        ‖⟪v i, v j⟫‖ ≤ a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j))
    (hRow :
      ∀ i ∈ J, (∑ j ∈ J, a (Nat.dist i j)) ≤ C) :
    ‖∑ j ∈ J, v j‖ ^ 2 ≤ C * ∑ j ∈ J, D j := by
  classical
  have hnorm :
      ‖∑ j ∈ J, v j‖ ^ 2
        =
      (⟪∑ j ∈ J, v j, ∑ j ∈ J, v j⟫).re := by
    simpa [pow_two] using (norm_sq_eq_re_inner (𝕜 := ℂ) (∑ j ∈ J, v j))

  have hinner :
      (⟪∑ j ∈ J, v j, ∑ j ∈ J, v j⟫ : ℂ)
        =
      ∑ i ∈ J, ∑ j ∈ J, ⟪v i, v j⟫ := by
    calc
      (⟪∑ j ∈ J, v j, ∑ j ∈ J, v j⟫ : ℂ)
          = ∑ i ∈ J, ⟪v i, ∑ j ∈ J, v j⟫ := by
              simpa using (sum_inner (𝕜 := ℂ) (E := E) J v (∑ j ∈ J, v j))
      _ = ∑ i ∈ J, ∑ j ∈ J, ⟪v i, v j⟫ := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (inner_sum (𝕜 := ℂ) (E := E) J v (v i))

  have hRe_le :
      (∑ i ∈ J, ∑ j ∈ J, (⟪v i, v j⟫ : ℂ).re)
        ≤
      ∑ i ∈ J, ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖ := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have :
        (∑ j ∈ J, (⟪v i, v j⟫ : ℂ).re) ≤ ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖ :=
      re_sum_le_sum_norm (s := J) (f := fun j => (⟪v i, v j⟫ : ℂ))
    exact this

  have hsumGram :
      ‖∑ j ∈ J, v j‖ ^ 2 ≤ ∑ i ∈ J, ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖ := by
    rw [hnorm, hinner]
    have hre : (∑ i ∈ J, ∑ j ∈ J, ⟪v i, v j⟫).re
        = ∑ i ∈ J, ∑ j ∈ J, (⟪v i, v j⟫ : ℂ).re := by
      simp
    simpa [hre] using hRe_le

  have hsumA :
      (∑ i ∈ J, ∑ j ∈ J, ‖(⟪v i, v j⟫ : ℂ)‖)
        ≤
      ∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hGram i hi j hj

  have hquad :
      (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j))
        ≤
      C * ∑ i ∈ J, D i := by
    have hstep :
        (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * Real.sqrt (D i) * Real.sqrt (D j))
          ≤
        (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * ((D i + D j) / 2)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      have hDi : 0 ≤ D i := hD i hi
      have hDj : 0 ≤ D j := hD j hj
      have hsqrt :
          Real.sqrt (D i) * Real.sqrt (D j) ≤ (D i + D j) / 2 :=
        mul_sqrt_mul_sqrt_le_add_div_two hDi hDj
      have hnonneg : 0 ≤ a (Nat.dist i j) := ha (Nat.dist i j)
      have := mul_le_mul_of_nonneg_left hsqrt hnonneg
      simpa [mul_assoc, mul_left_comm, mul_comm] using this

    have hstep' :
        (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * ((D i + D j) / 2))
          ≤
        C * ∑ i ∈ J, D i := by
      have hCol : ∀ j ∈ J, (∑ i ∈ J, a (Nat.dist i j)) ≤ C := by
        intro j hj
        have :
            (∑ i ∈ J, a (Nat.dist i j)) = ∑ i ∈ J, a (Nat.dist j i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [Nat.dist_comm] using (rfl : a (Nat.dist i j) = a (Nat.dist j i))
        simpa [this] using hRow j hj

      have hdecomp :
          (∑ i ∈ J, ∑ j ∈ J, a (Nat.dist i j) * ((D i + D j) / 2))
            =
          (∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            + (∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹))) := by
        simp [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          mul_assoc, mul_left_comm, mul_comm]

      have hrow1 :
          (∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) := by
        have hterm :
            (∑ i ∈ J, D i * (∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              ≤
            ∑ i ∈ J, D i * (C * ((2 : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hDi : 0 ≤ D i := hD i hi
          have hrowi : (∑ j ∈ J, a (Nat.dist i j)) ≤ C := hRow i hi
          have hrowi' :
              (∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)) ≤ C * ((2 : ℝ)⁻¹) := by
            have hhalf_nonneg : 0 ≤ ((2 : ℝ)⁻¹) := by
              exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)
            have hmul := mul_le_mul_of_nonneg_right hrowi hhalf_nonneg
            have hs :
                (∑ j ∈ J, a (Nat.dist i j)) * ((2 : ℝ)⁻¹)
                  =
                ∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹) := by
              simpa using (Finset.sum_mul J (fun j => a (Nat.dist i j)) ((2 : ℝ)⁻¹))
            simpa [hs] using hmul
          have := mul_le_mul_of_nonneg_left hrowi' hDi
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this
        have hsL :
            (∑ i ∈ J, D i * (∑ j ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              =
            ∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        have hsR :
            (∑ i ∈ J, D i * (C * ((2 : ℝ)⁻¹))) = (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) := by
          simpa using (Finset.sum_mul J (fun i => D i) (C * ((2 : ℝ)⁻¹))).symm
        simpa [hsL, hsR] using hterm

      have hrow2 :
          (∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ j ∈ J, D j) * (C * ((2 : ℝ)⁻¹)) := by
        have hterm :
            (∑ j ∈ J, D j * (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              ≤
            ∑ j ∈ J, D j * (C * ((2 : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hDj : 0 ≤ D j := hD j hj
          have hcolj : (∑ i ∈ J, a (Nat.dist i j)) ≤ C := hCol j hj
          have hcolj' :
              (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)) ≤ C * ((2 : ℝ)⁻¹) := by
            have hhalf_nonneg : 0 ≤ ((2 : ℝ)⁻¹) := by
              exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)
            have hmul := mul_le_mul_of_nonneg_right hcolj hhalf_nonneg
            have hs :
                (∑ i ∈ J, a (Nat.dist i j)) * ((2 : ℝ)⁻¹)
                  =
                ∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹) := by
              simpa using (Finset.sum_mul J (fun i => a (Nat.dist i j)) ((2 : ℝ)⁻¹))
            simpa [hs] using hmul
          have := mul_le_mul_of_nonneg_left hcolj' hDj
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this
        have hsL0 :
            (∑ j ∈ J, D j * (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              =
            ∑ j ∈ J, ∑ i ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        have hsL :
            (∑ j ∈ J, D j * (∑ i ∈ J, a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              =
            ∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
          have hswap :
              (∑ j ∈ J, ∑ i ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
                =
              ∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)) := by
            simpa using
              (Finset.sum_comm (s := J) (t := J)
                (f := fun j i => D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹))))
          exact hsL0.trans hswap
        have hsR :
            (∑ j ∈ J, D j * (C * ((2 : ℝ)⁻¹))) = (∑ j ∈ J, D j) * (C * ((2 : ℝ)⁻¹)) := by
          simpa using (Finset.sum_mul J (fun j => D j) (C * ((2 : ℝ)⁻¹))).symm
        simpa [hsL, hsR] using hterm

      have hsumEq : (∑ j ∈ J, D j) = ∑ i ∈ J, D i := rfl

      have hsum :
          (∑ i ∈ J, ∑ j ∈ J, D i * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
              + (∑ i ∈ J, ∑ j ∈ J, D j * (a (Nat.dist i j) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) + (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) := by
        nlinarith [hrow1, hrow2, hsumEq]

      have hsimp :
          (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹)) + (∑ i ∈ J, D i) * (C * ((2 : ℝ)⁻¹))
            =
          C * ∑ i ∈ J, D i := by
        ring

      simpa [hdecomp, hsimp, add_assoc, add_left_comm, add_comm] using hsum

    exact le_trans hstep hstep'

  exact le_trans hsumGram (le_trans hsumA hquad)

end

end SSU.Hilbert
