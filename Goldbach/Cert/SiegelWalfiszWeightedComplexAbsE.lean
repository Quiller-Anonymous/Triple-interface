import Goldbach.Cert.SiegelWalfiszWeightedAbsE
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators

/-!
Complex-valued variant of `SiegelWalfiszWeightedAbsE`.

This mirrors `Goldbach.Cert.SiegelWalfiszWeightedComplex`, but replaces the `PsiBound` hypothesis
with a uniform bound on the SW deviation `E` on the relevant interval.
-/

namespace Goldbach.Cert
namespace SiegelWalfiszWeighted

open scoped BigOperators

noncomputable section

variable (q a : ℕ)

theorem norm_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform
    (g : ℕ → ℂ) {L U : ℕ}
    (hLU : L ≤ U) (hL : 0 < L)
    (hgL : g (L - 1) = 0)
    (M : ℝ)
    (hE_uniform : ∀ {x : ℕ}, x ∈ Finset.Icc (L - 1) U → |E (q := q) (a := a) x| ≤ M) :
    ‖(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * g n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), g n)‖
      ≤
      M * (2 * (‖g U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖))) := by
  classical
  -- Abbreviations to match the existing complex proof.
  set V : ℝ := ‖g U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖)
  set D : ℂ :=
    (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * g n)
      - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), g n)

  -- Real-part bound via the real absE lemma.
  have hRe_core :
      |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * (g n).re)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), (g n).re)|
        ≤ M * (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|)) := by
    have h :=
      abs_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform (q := q) (a := a)
        (g := fun n => (g n).re) (L := L) (U := U)
        hLU hL (by simp [hgL]) M hE_uniform
    simpa using h

  have hIm_core :
      |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * (g n).im)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), (g n).im)|
        ≤ M * (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)) := by
    have h :=
      abs_weightedSum_Ico_sub_mainTerm_le_of_absE_uniform (q := q) (a := a)
        (g := fun n => (g n).im) (L := L) (U := U)
        hLU hL (by simp [hgL]) M hE_uniform
    simpa using h

  -- Compare real/imag variation to complex-norm variation.
  have hRe_var_le :
      |(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|)
        ≤ V := by
    have hU : |(g U).re| ≤ ‖g U‖ := Complex.abs_re_le_norm (g U)
    have hsum :
        (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|)
          ≤ ∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖ := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have : |(g (n + 1) - g n).re| ≤ ‖g (n + 1) - g n‖ :=
        Complex.abs_re_le_norm (g (n + 1) - g n)
      simpa [Complex.sub_re] using this
    exact add_le_add hU (by simpa [V] using hsum)

  have hIm_var_le :
      |(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)
        ≤ V := by
    have hU : |(g U).im| ≤ ‖g U‖ := Complex.abs_im_le_norm (g U)
    have hsum :
        (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)
          ≤ ∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖ := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have : |(g (n + 1) - g n).im| ≤ ‖g (n + 1) - g n‖ :=
        Complex.abs_im_le_norm (g (n + 1) - g n)
      simpa [Complex.sub_im] using this
    exact add_le_add hU (by simpa [V] using hsum)

  -- Bound `‖D‖` via its real and imaginary parts.
  have hD_norm : ‖D‖ ≤ |D.re| + |D.im| := by
    simpa using Complex.norm_le_abs_re_add_abs_im D

  have hD_re :
      |D.re|
        ≤ M * (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|)) := by
    simpa [D, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum, mul_assoc, mul_left_comm,
      mul_comm] using hRe_core

  have hD_im :
      |D.im|
        ≤ M * (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)) := by
    simpa [D, Complex.sub_im, Complex.im_ofReal_mul, Complex.im_sum, mul_assoc, mul_left_comm,
      mul_comm] using hIm_core

  have hSum_reim :
      |D.re| + |D.im| ≤ M * (2 * V) := by
    have hA :
        (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|))
          +
          (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|))
          ≤ 2 * V := by
      have h := add_le_add hRe_var_le hIm_var_le
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using h
    have h1 :
        |D.re| + |D.im|
          ≤
          M * (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|))
            +
            M * (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)) :=
      add_le_add hD_re hD_im
    have h2 :
        M * (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|))
            +
            M * (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|))
          =
        M *
          ((|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|))
            +
            (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|))) := by
      ring
    refine le_trans h1 ?_
    rw [h2]
    -- `M` is nonnegative because it upper-bounds absolute values.
    have hM : 0 ≤ M := by
      have hmem : U ∈ Finset.Icc (L - 1) U := by
        refine Finset.mem_Icc.mpr ?_
        constructor
        · exact le_trans (Nat.sub_le L 1) hLU
        · exact le_rfl
      exact le_trans (by
        -- `0 ≤ |E U|`
        simpa using (abs_nonneg (E (q := q) (a := a) U))) (hE_uniform (x := U) hmem)
    exact mul_le_mul_of_nonneg_left hA hM

  -- Convert from `D` back to the goal statement.
  have : M * (2 * V) = M * (2 * (‖g U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖))) := by
    simp [V]
  refine le_trans hD_norm ?_
  -- Use `D` definition and the bound.
  simpa [D, V, this] using hSum_reim

end

end SiegelWalfiszWeighted
end Goldbach.Cert
