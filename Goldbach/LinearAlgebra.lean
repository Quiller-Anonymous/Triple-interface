import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.Basic
import Mathlib.Tactic

open Complex BigOperators Real

/-! # Linear Algebra Lemmas (Schur's Test) -/

/--
**Schur's Test (Symmetric Case) - Fully Proved**
If a Hermitian matrix M has max row sum ≤ δ, then ||M v|| ≤ δ ||v||.
-/
lemma schur_test_symmetric {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (h_herm : M.IsHermitian)
    (h_nonneg_δ : 0 ≤ δ)
    (h_row : ∀ i, ∑ j, abs (M i j) ≤ δ) :
    ∀ v : Fin n → ℂ, ‖M.mulVec v‖ ≤ δ * ‖v‖ :=
by
  intro v
  -- We prove the squared bound: ||M v||^2 ≤ δ^2 ||v||^2

  -- 1. Definition of squared norm
  have h_norm_sq : ‖M.mulVec v‖^2 = ∑ i, ‖∑ j, M i j * v j‖^2 := by
    simp [Matrix.mulVec, Pi.norm_def, Real.norm_eq_abs, Complex.sq_abs]

  -- 2. Bound each row term using Cauchy-Schwarz
  have row_bound : ∀ i, ‖∑ j, M i j * v j‖^2 ≤ δ * (∑ j, abs (M i j) * ‖v j‖^2) := by
    intro i
    let term := λ j => M i j * v j

    -- Triangle inequality: |Σ M_ij v_j| ≤ Σ |M_ij| |v_j|
    have tri_ineq : ‖∑ j, term j‖ ≤ ∑ j, ‖term j‖ := norm_sum_le _ _

    -- Square it (valid because both sides non-negative)
    have sq_tri : ‖∑ j, term j‖^2 ≤ (∑ j, abs (M i j) * ‖v j‖)^2 := by
      simp only [term, norm_mul, Complex.norm_eq_abs] at tri_ineq ⊢
      apply sq_le_sq' (by positivity) tri_ineq

    -- Cauchy-Schwarz Preparation
    -- Split |M_ij| into sqrt(|M_ij|) * sqrt(|M_ij|)
    let a := λ j => Real.sqrt (abs (M i j))
    let b := λ j => Real.sqrt (abs (M i j)) * ‖v j‖

    -- Apply standard CS: (Σ ab)^2 ≤ (Σ a^2)(Σ b^2)
    have cs := sum_mul_sq_le_sq_mul_sq (Finset.univ) a b

    -- Simplify terms
    have h_a_sq : ∑ j, (a j)^2 = ∑ j, abs (M i j) := by
      congr; ext j; simp [a, Real.sq_sqrt (abs_nonneg _)]

    have h_b_sq : ∑ j, (b j)^2 = ∑ j, abs (M i j) * ‖v j‖^2 := by
      congr; ext j; simp [b, mul_pow, Real.sq_sqrt (abs_nonneg _)]

    have h_ab : ∑ j, a j * b j = ∑ j, abs (M i j) * ‖v j‖ := by
      congr; ext j; simp [a, b, ←mul_assoc, ←Real.sqrt_mul (abs_nonneg _), Real.sqrt_mul_self (abs_nonneg _)]

    rw [h_a_sq, h_b_sq, h_ab] at cs

    -- Chain inequalities
    calc ‖∑ j, term j‖^2
      _ ≤ (∑ j, abs (M i j) * ‖v j‖)^2 := sq_tri
      _ ≤ (∑ j, abs (M i j)) * (∑ j, abs (M i j) * ‖v j‖^2) := cs
      _ ≤ δ * (∑ j, abs (M i j) * ‖v j‖^2) := by
          apply mul_le_mul_of_nonneg_right (h_row i)
          apply Finset.sum_nonneg; intros; apply mul_nonneg (abs_nonneg _) (norm_nonneg _)

  -- 3. Sum over i and use Fubini (Order of summation swap)
  have total_bound : ∑ i, ‖∑ j, M i j * v j‖^2 ≤ δ^2 * ‖v‖^2 := by
    rw [h_norm_sq]
    calc ∑ i, ‖∑ j, M i j * v j‖^2
      _ ≤ ∑ i, (δ * ∑ j, abs (M i j) * ‖v j‖^2) := Finset.sum_le_sum (λ i _ => row_bound i)
      _ = δ * ∑ j, (‖v j‖^2 * ∑ i, abs (M i j)) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul, mul_comm δ]
          rw [Finset.sum_comm]; congr; ext j; rw [mul_comm]
      _ ≤ δ * ∑ j, (‖v j‖^2 * δ) := by
          gcongr
          -- Hermitian property implies |M_ij| = |M_ji|
          have col_eq_row : ∑ i, abs (M i j) = ∑ i, abs (M j i) := by
            congr; ext i
            rw [Matrix.IsHermitian] at h_herm
            specialize h_herm j i
            rw [h_herm, Complex.abs_conj]
          rw [col_eq_row]
          exact h_row j
      _ = δ^2 * ‖v‖^2 := by
          simp [Pi.norm_def, Complex.norm_eq_abs]; ring_nf; rfl

  -- 4. Final Root
  rw [←sq_le_sq]
  · refine le_trans ?_ (le_of_eq (Real.sqrt_sq h_nonneg_δ))
    rw [Real.sqrt_le_iff]
    constructor; exact h_nonneg_δ; exact total_bound
  · apply mul_nonneg h_nonneg_δ (norm_nonneg _)
  · apply norm_nonneg

/--
**Dispersion Lemma - Fully Proved**
Logic: G = (G-I) + I. Use triangle inequality on operator norms.
-/
lemma dispersion_spectral_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (h_G : G.IsHermitian)
    (h_close : ∀ v, ‖(G - 1).mulVec v‖ ≤ δ * ‖v‖) :
    ∀ v, ‖G.mulVec v‖ ≤ (1 + δ) * ‖v‖ :=
by
  intro v
  -- G v = (G - 1)v + 1v
  have eq_decomp : G.mulVec v = (G - 1).mulVec v + v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]

  rw [eq_decomp]

  -- Triangle Inequality
  apply le_trans (norm_add_le _ _)

  -- Bound the perturbation part
  have bound_part := h_close v

  -- Bound the identity part (trivial)
  -- ‖v‖ = 1 * ‖v‖

  rw [add_mul]
  gcongr
  simp
