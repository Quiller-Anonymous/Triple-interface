import Goldbach.Cert.SiegelWalfiszWeighted
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators

/-!
Complex-valued variants of the Siegel–Walfisz weighted AP bounds.

`Goldbach.Cert.SiegelWalfiszWeighted` proves the core summation-by-parts bounds for real weights
`g : ℕ → ℝ`.  For major-arc exponential sums, one naturally wants to use complex weights such as
`g(n) = W(n/X) * exp(2π i β n)`.

This file supplies a minimal bridge: a complex-norm bound derived from the real bound by applying it
to real and imaginary parts.
-/

namespace Goldbach.Cert
namespace SiegelWalfiszWeighted

open scoped BigOperators

noncomputable section

variable (q a : ℕ)

theorem norm_weightedSum_Ico_sub_mainTerm_le_of_PsiBound
    {A : ℕ} (hpsi : Goldbach.Cert.SiegelWalfisz.PsiBound A)
    (g : ℕ → ℂ) {L U : ℕ}
    (hLU : L ≤ U) (hL : 0 < L) (hL3 : 3 ≤ (L - 1))
    (hq : 1 ≤ q) (hcop : Nat.Coprime a q)
    (hqlog : (q : ℝ) ≤ (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
    (hgL : g (L - 1) = 0) :
    ‖(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * g n)
        - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), g n)‖
      ≤
      (hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A)
        * (2 * (‖g U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖))) := by
  classical
  -- Main quantities.
  set K : ℝ :=
    hpsi.C * (U : ℝ) / (Real.log ((L - 1 : ℕ) : ℝ)) ^ A
  set V : ℝ := ‖g U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖)
  set D : ℂ :=
    (∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n : ℂ) * g n)
      - ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (∑ n ∈ Finset.Ico L (U + 1), g n)

  have hlog_pos : 0 < Real.log ((L - 1 : ℕ) : ℝ) := by
    have h2 : (2 : ℕ) ≤ (L - 1 : ℕ) := le_trans (by decide : (2 : ℕ) ≤ 3) hL3
    have h2' : (2 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast h2
    have h1 : (1 : ℝ) < ((L - 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2'
    exact Real.log_pos h1
  have hK_nonneg : 0 ≤ K := by
    have hpow_pos : 0 < (Real.log ((L - 1 : ℕ) : ℝ)) ^ A := pow_pos hlog_pos A
    have hmul_nonneg : 0 ≤ hpsi.C * (U : ℝ) := by
      exact mul_nonneg hpsi.C_nonneg (by positivity)
    -- `K = (C * U) / (log(L-1))^A`
    exact (div_nonneg hmul_nonneg (le_of_lt hpow_pos)).trans_eq (by simp [K])

  -- Real-part bound via the real SW lemma.
  have hRe_core :
      |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * (g n).re)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), (g n).re)|
        ≤ K * (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|)) := by
    have h :=
      abs_weightedSum_Ico_sub_mainTerm_le_of_PsiBound (q := q) (a := a) (hpsi := hpsi)
        (g := fun n => (g n).re) (L := L) (U := U)
        hLU hL hL3 hq hcop hqlog (by simp [hgL])
    simpa [K] using h

  have hIm_core :
      |(∑ n ∈ Finset.Ico L (U + 1), (aTerm (q := q) (a := a) n) * (g n).im)
          - (1 / (Nat.totient q : ℝ)) * (∑ n ∈ Finset.Ico L (U + 1), (g n).im)|
        ≤ K * (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)) := by
    have h :=
      abs_weightedSum_Ico_sub_mainTerm_le_of_PsiBound (q := q) (a := a) (hpsi := hpsi)
        (g := fun n => (g n).im) (L := L) (U := U)
        hLU hL hL3 hq hcop hqlog (by simp [hgL])
    simpa [K] using h

  -- Compare the real/imag variation terms to the complex norm variation `V`.
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

  -- Put everything together using `‖z‖ ≤ |re z| + |im z|`.
  have hD_norm : ‖D‖ ≤ |D.re| + |D.im| := by
    simpa using Complex.norm_le_abs_re_add_abs_im D

  have hD_re :
      |D.re|
        ≤ K * (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|)) := by
    -- Expand `D.re` and use `hRe_core`.
    simpa [D, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum, mul_assoc, mul_left_comm,
      mul_comm] using hRe_core

  have hD_im :
      |D.im|
        ≤ K * (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)) := by
    simpa [D, Complex.sub_im, Complex.im_ofReal_mul, Complex.im_sum, mul_assoc, mul_left_comm,
      mul_comm] using hIm_core

  have hSum_reim :
      |D.re| + |D.im| ≤ K * (2 * V) := by
    have hA :
        |(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|)
          +
          (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|))
          ≤ 2 * V := by
      have h := add_le_add hRe_var_le hIm_var_le
      -- rewrite `V + V` as `2 * V`
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using h

    have h1 : |D.re| + |D.im|
        ≤ K *
            (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|))
          + K *
            (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|)) :=
      add_le_add hD_re hD_im

    have h2 :
        K *
            (|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|))
          + K *
            (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|))
          =
        K *
          ((|(g U).re| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).re - (g n).re|))
            +
            (|(g U).im| + (∑ n ∈ Finset.Ico (L - 1) U, |(g (n + 1)).im - (g n).im|))) := by
      ring

    refine le_trans h1 ?_
    rw [h2]
    exact mul_le_mul_of_nonneg_left hA hK_nonneg

  -- Convert from `D` back to the goal statement and use the `V` definition.
  refine le_trans hD_norm ?_
  have : K * (2 * V) = K * (2 * (‖g U‖ + (∑ n ∈ Finset.Ico (L - 1) U, ‖g (n + 1) - g n‖))) := by
    simp [V]
  simpa [D, K, V, this] using hSum_reim

end

end SiegelWalfiszWeighted
end Goldbach.Cert
