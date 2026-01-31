import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.NNReal.Basic
import SSU.Hilbert.DistZ

/-!
Hilbert-space almost-orthogonality engine (pure), indexed by `ℤ`.

This is the SSU package’s project-neutral “interzone” brick, in ledger-friendly form:

Let `v i` be a finite family of vectors in a complex Hilbert space `E`. Assume:

* diagonal weights `D i ≥ 0`;
* Gram control `‖⟪v i, v j⟫‖ ≤ a (distZ i j) * √(D i) * √(D j)` with `a : ℕ → NNReal`;
* a uniform row-sum bound `∑_{j∈J} a(distZ i j) ≤ Crow`.

Then:

`‖∑_{i∈J} v i‖² ≤ Crow * ∑_{i∈J} D i`.
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

theorem norm_sum_sq_le_of_rowSum_gram_boundZ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {J : Finset ℤ} {v : ℤ → E} {D : ℤ → ℝ} {a : ℕ → NNReal} {Crow : ℝ}
    (hD : ∀ j ∈ J, 0 ≤ D j)
    (hGram :
      ∀ i ∈ J, ∀ j ∈ J,
        ‖⟪v i, v j⟫‖ ≤ (a (distZ i j) : ℝ) * Real.sqrt (D i) * Real.sqrt (D j))
    (hRow :
      ∀ i ∈ J, (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ Crow) :
    ‖∑ j ∈ J, v j‖ ^ 2 ≤ Crow * ∑ j ∈ J, D j := by
  classical
  have ha : ∀ k, 0 ≤ (a k : ℝ) := by
    intro k
    exact_mod_cast (show 0 ≤ a k from (a k).property)

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
              exact sum_inner (𝕜 := ℂ) (E := E) J v (∑ j ∈ J, v j)
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
      ∑ i ∈ J, ∑ j ∈ J,
        (a (distZ i j) : ℝ) * Real.sqrt (D i) * Real.sqrt (D j) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hGram i hi j hj

  have hquad :
      (∑ i ∈ J, ∑ j ∈ J,
        (a (distZ i j) : ℝ) * Real.sqrt (D i) * Real.sqrt (D j))
        ≤
      Crow * ∑ i ∈ J, D i := by
    have hstep :
        (∑ i ∈ J, ∑ j ∈ J,
          (a (distZ i j) : ℝ) * Real.sqrt (D i) * Real.sqrt (D j))
          ≤
        (∑ i ∈ J, ∑ j ∈ J,
          (a (distZ i j) : ℝ) * ((D i + D j) / 2)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum ?_
      intro j hj
      have hDi : 0 ≤ D i := hD i hi
      have hDj : 0 ≤ D j := hD j hj
      have hsqrt :
          Real.sqrt (D i) * Real.sqrt (D j) ≤ (D i + D j) / 2 :=
        mul_sqrt_mul_sqrt_le_add_div_two hDi hDj
      have hnonneg : 0 ≤ (a (distZ i j) : ℝ) := ha (distZ i j)
      have := mul_le_mul_of_nonneg_left hsqrt hnonneg
      simpa [mul_assoc, mul_left_comm, mul_comm] using this

    have hstep' :
        (∑ i ∈ J, ∑ j ∈ J,
          (a (distZ i j) : ℝ) * ((D i + D j) / 2))
          ≤
        Crow * ∑ i ∈ J, D i := by
      have hCol : ∀ j ∈ J, (∑ i ∈ J, (a (distZ i j) : ℝ)) ≤ Crow := by
        intro j hj
        have :
            (∑ i ∈ J, (a (distZ i j) : ℝ)) = ∑ i ∈ J, (a (distZ j i) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [distZ_comm]
        simpa [this] using hRow j hj

      have hdecomp :
          (∑ i ∈ J, ∑ j ∈ J, (a (distZ i j) : ℝ) * ((D i + D j) / 2))
            =
          (∑ i ∈ J, ∑ j ∈ J, D i * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
            + (∑ i ∈ J, ∑ j ∈ J, D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹))) := by
        simp [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          mul_assoc, mul_left_comm, mul_comm]

      have hrow1 :
          (∑ i ∈ J, ∑ j ∈ J, D i * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ i ∈ J, D i) * (Crow * ((2 : ℝ)⁻¹)) := by
        have hterm :
            (∑ i ∈ J, D i * (∑ j ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
              ≤
            ∑ i ∈ J, D i * (Crow * ((2 : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          have hDi : 0 ≤ D i := hD i hi
          have hrowi : (∑ j ∈ J, (a (distZ i j) : ℝ)) ≤ Crow := hRow i hi
          have hrowi' :
              (∑ j ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)) ≤ Crow * ((2 : ℝ)⁻¹) := by
            have hhalf_nonneg : 0 ≤ ((2 : ℝ)⁻¹) := by
              exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)
            have hmul := mul_le_mul_of_nonneg_right hrowi hhalf_nonneg
            have hs :
                (∑ j ∈ J, (a (distZ i j) : ℝ)) * ((2 : ℝ)⁻¹)
                  =
                ∑ j ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹) := by
              simpa using (Finset.sum_mul J (fun j => (a (distZ i j) : ℝ)) ((2 : ℝ)⁻¹))
            simpa [hs] using hmul
          have := mul_le_mul_of_nonneg_left hrowi' hDi
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this
        have hsL :
            (∑ i ∈ J, D i * (∑ j ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
              =
            ∑ i ∈ J, ∑ j ∈ J, D i * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        have hsR :
            (∑ i ∈ J, D i * (Crow * ((2 : ℝ)⁻¹))) = (∑ i ∈ J, D i) * (Crow * ((2 : ℝ)⁻¹)) := by
          simpa using (Finset.sum_mul J (fun i => D i) (Crow * ((2 : ℝ)⁻¹))).symm
        simpa [hsL, hsR] using hterm

      have hrow2 :
          (∑ i ∈ J, ∑ j ∈ J, D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ j ∈ J, D j) * (Crow * ((2 : ℝ)⁻¹)) := by
        have hterm :
            (∑ j ∈ J, D j * (∑ i ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
              ≤
            ∑ j ∈ J, D j * (Crow * ((2 : ℝ)⁻¹)) := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hDj : 0 ≤ D j := hD j hj
          have hcolj : (∑ i ∈ J, (a (distZ i j) : ℝ)) ≤ Crow := hCol j hj
          have hcolj' :
              (∑ i ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)) ≤ Crow * ((2 : ℝ)⁻¹) := by
            have hhalf_nonneg : 0 ≤ ((2 : ℝ)⁻¹) := by
              exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)
            have hmul := mul_le_mul_of_nonneg_right hcolj hhalf_nonneg
            have hs :
                (∑ i ∈ J, (a (distZ i j) : ℝ)) * ((2 : ℝ)⁻¹)
                  =
                ∑ i ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹) := by
              simpa using (Finset.sum_mul J (fun i => (a (distZ i j) : ℝ)) ((2 : ℝ)⁻¹))
            simpa [hs] using hmul
          have := mul_le_mul_of_nonneg_left hcolj' hDj
          simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using this
        have hsL0 :
            (∑ j ∈ J, D j * (∑ i ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
              =
            ∑ j ∈ J, ∑ i ∈ J, D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        have hsL :
            (∑ j ∈ J, D j * (∑ i ∈ J, (a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
              =
            ∑ i ∈ J, ∑ j ∈ J, D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)) := by
          have hswap :
              (∑ j ∈ J, ∑ i ∈ J, D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
                =
              ∑ i ∈ J, ∑ j ∈ J, D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)) := by
            simpa using
              (Finset.sum_comm (s := J) (t := J)
                (f := fun j i => D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹))))
          exact hsL0.trans hswap
        have hsR :
            (∑ j ∈ J, D j * (Crow * ((2 : ℝ)⁻¹))) = (∑ j ∈ J, D j) * (Crow * ((2 : ℝ)⁻¹)) := by
          simpa using (Finset.sum_mul J (fun j => D j) (Crow * ((2 : ℝ)⁻¹))).symm
        simpa [hsL, hsR] using hterm

      have hsumEq : (∑ j ∈ J, D j) = ∑ i ∈ J, D i := rfl

      have hsum :
          (∑ i ∈ J, ∑ j ∈ J, D i * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
              + (∑ i ∈ J, ∑ j ∈ J, D j * ((a (distZ i j) : ℝ) * ((2 : ℝ)⁻¹)))
            ≤
          (∑ i ∈ J, D i) * (Crow * ((2 : ℝ)⁻¹)) + (∑ i ∈ J, D i) * (Crow * ((2 : ℝ)⁻¹)) := by
        nlinarith [hrow1, hrow2, hsumEq]

      have hsimp :
          (∑ i ∈ J, D i) * (Crow * ((2 : ℝ)⁻¹)) + (∑ i ∈ J, D i) * (Crow * ((2 : ℝ)⁻¹))
            =
          Crow * ∑ i ∈ J, D i := by
        ring

      simpa [hdecomp, hsimp, add_assoc, add_left_comm, add_comm] using hsum

    exact le_trans hstep hstep'

  exact le_trans hsumGram (le_trans hsumA hquad)

end

end SSU.Hilbert
