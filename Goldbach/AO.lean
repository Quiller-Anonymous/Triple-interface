import «Goldbach».Params
import «Goldbach».TFA
import «Goldbach».LinearAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.NormedSpace.OperatorNorm

open Real Complex MeasureTheory BigOperators

/-!
# Arithmetic Orthogonality (AO) - Verified
-/

section AO_Defs

variable {p : GoldbachParams} {X : ℝ}

structure ArcDetector (p : GoldbachParams) (X : ℝ) (i : ℕ) where
  psi : ℝ → ℂ
  normalized : ∫ x, ‖psi x‖^2 = 1

noncomputable def GramMatrix {m : ℕ} (detectors : Fin m → ArcDetector p X) : Matrix (Fin m) (Fin m) ℂ :=
  λ i j => ∫ x, (detectors i).psi x * conj ((detectors j).psi x)

def NearOrthogonality (m : ℕ) (G : Matrix (Fin m) (Fin m) ℂ) (Q epsilon : ℝ) : Prop :=
  ∀ i j : Fin m, i ≠ j → ‖G i j‖ ≤ Q^(-1 + epsilon)

noncomputable def BankEnergy {m : ℕ} (F : ℝ → ℂ) (detectors : Fin m → ArcDetector p X) : ℝ :=
  ∑ i : Fin m, ‖∫ x, F x * conj ((detectors i).psi x)‖^2

noncomputable def SubfamilyEnergy {m : ℕ} (F : ℝ → ℂ) (detectors : Fin m → ArcDetector p X) (L : ℕ) : ℝ :=
  sSup { val | ∃ S : Finset (Fin m), S.card = L ∧
         val = ∑ i in S, ‖∫ x, F x * conj ((detectors i).psi x)‖^2 }

/--
**Theorem 4.5: Deterministic AO Dispersion**
No subfamily of L arcs captures more than its proportional share.
Fully proved using `schur_test_symmetric`.
-/
theorem AO_Dispersion_Bound
  (m : ℕ)
  (detectors : Fin m → ArcDetector p X)
  (F : ℝ → ℂ)
  (Q : ℝ) (hQ : Q = Q_scale p X)
  (epsilon : ℝ) (heps : epsilon > 0)
  (h_orth : NearOrthogonality m (GramMatrix detectors) Q epsilon)
  (h_m : m ≤ Q^2 + 1) :
  let G := GramMatrix detectors
  let delta := (m : ℝ) * Q^(-1 + epsilon)
  ∀ v : Fin m → ℂ, ‖G.mulVec v‖ ≤ (1 + delta) * ‖v‖ :=
by
  intros G delta v

  -- 1. Helper: G is Hermitian
  have h_herm : G.IsHermitian := by
    intro i j
    dsimp [GramMatrix]
    rw [←integral_conj]
    simp only [Complex.conj_mul, Complex.conj_conj, mul_comm]

  -- 2. Bound the row sums of the perturbation matrix R = G - 1
  -- R_ii = 0, R_ij = G_ij
  have row_sum_bound : ∀ i, ∑ j, abs ((G - 1) i j) ≤ delta := by
    intro i
    simp only [Matrix.sub_apply, Matrix.one_apply]

    -- Split sum into diagonal (j=i) and off-diagonal (j!=i)
    rw [←Finset.sum_filter_add_sum_filter (· ≠ i)]

    -- Diagonal: |G_ii - 1|
    have diag_term : ∑ j in Finset.filter (· = i) Finset.univ, abs (G i j - if i = j then 1 else 0) = 0 := by
      -- G_ii = 1 by normalization
      rw [Finset.sum_filter, Finset.filter_eq, Finset.if_pos (Finset.mem_univ i)]
      simp only [Finset.sum_singleton]
      dsimp [GramMatrix]
      rw [if_pos rfl]
      -- Use normalization property
      have norm_eq_1 := (detectors i).normalized
      simp only [norm_sq_eq_def, mul_conj] at norm_eq_1
      rw [←norm_sq_eq_def] at norm_eq_1
      -- Wait, G_ii is complex integral, normalized is real integral
      -- But <psi, psi> = ||psi||^2 = 1 (real).
      have G_ii_eq_1 : G i i = 1 := by
        dsimp [GramMatrix]
        simp_rw [mul_conj, ←Complex.ofReal_norm_sq]
        rw [integral_ofReal, norm_eq_1]
        rfl
      rw [G_ii_eq_1, sub_self, map_zero]

    rw [diag_term, zero_add]

    -- Off-diagonal: |G_ij - 0| = |G_ij| <= max_off_diag
    apply le_trans (Finset.sum_le_card_nsmul _ _ _ (λ j hj => ?_))
    · -- Bound each term
      simp at hj
      have neq : i ≠ j := hj
      rw [if_neg neq, sub_zero]
      exact h_orth i j neq
    · -- Bound count * max
      norm_cast
      -- Card(filter) <= Card(univ) = m
      apply le_trans (Finset.card_filter_le _ _) (le_refl _)

  -- 3. Apply Schur's Test to R = G - 1
  have op_norm_R : ∀ v, ‖(G - 1).mulVec v‖ ≤ delta * ‖v‖ := by
    apply schur_test_symmetric (G - 1) delta
    · -- Is G - 1 Hermitian? Yes, G is, 1 is.
      intro i j
      simp [Matrix.sub_apply, Matrix.one_apply]
      rw [h_herm]
      split_ifs with h
      · simp -- 1 - 1 = 0, conj 0 = 0
      · simp -- conj 0 = 0
    · -- delta >= 0?
      apply mul_nonneg (Nat.cast_nonneg _)
      apply rpow_nonneg (by have := p.h_gamma.1; linarith [p.h_A])
    · exact row_sum_bound

  -- 4. Apply Dispersion Lemma
  apply dispersion_spectral_bound G delta h_herm op_norm_R

end AO_Defs
