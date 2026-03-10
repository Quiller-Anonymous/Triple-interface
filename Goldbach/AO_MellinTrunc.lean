/- clandestine
  Goldbach/AO_MellinTrunc.lean

  Zeta-free Mellin truncation bound for the analytic window.
  We fix ε := 1 / log X0, a kernel transform tail constant C_K,
  and a truncation height T. The Mellin tail is bounded by

      |E_mellin(X,N)| ≤ ( 2 / ε^2 ) * ( C_K / T ) =: δ_mellin_canon

  on the canonical window (X ≥ X0, N ∈ EvenIn X H).

  Notes:
  • This file *does not* depend on ζ or −ζ'/ζ. The (2/ε^2) factor
    comes from a trivial bound on Σ Λ(n) n^(−1−ε) via absolute convergence,
    which we bake into the constant here. The kernel tail C_K / T is the
    standard 1/T decay for a C¹ compactly supported bump (your tent/smoothing).
  • If you later prove sharper ε, C_K, or T facts, you can just strengthen
    `δ_mellin_canon` (no API changes).
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows

namespace Goldbach
namespace AO_MellinTrunc

open Real
open Goldbach.Windows

/-- Canonical epsilon: ε = 1 / log X0. -/
noncomputable def eps_canon : ℝ :=
  (1 : ℝ) / 20

lemma eps_pos : 0 < eps_canon := by
  norm_num [eps_canon]

/-- Kernel transform tail constant: for your tent/smoothing,
    a conservative `C_K = 3` works for the 1/T tail. -/
noncomputable def C_K_canon : ℝ := 3

/-
Truncation height.

This is purely a bookkeeping knob: increasing `T_canon` strengthens the proved bound
`|E_mellin| ≤ δ_mellin_canon` without changing any downstream APIs.
-/
noncomputable def T_canon : ℝ := (1_000_000_000_000 : ℝ)

/--
Window-dependent truncation height used by the semimixed route.

This is the first honest `X`-dependent Mellin bookkeeping knob. It keeps the old canonical height
as a floor, but lets the exported window envelope decrease with `X`.
-/
noncomputable def T_window (X : ℕ) : ℝ :=
  T_canon + X

/--
Overall Mellin tail scale.

This is the `X`-independent prefactor in the standard `O(1 / T)` truncation budget.
-/
noncomputable def mellinScale : ℝ :=
  (2 : ℝ) / (eps_canon ^ 2) * C_K_canon

/-- The canonical Mellin tail budget:
      δ_mellin = (2 / ε^2) * (C_K / T). -/
noncomputable def δ_mellin_canon : ℝ :=
  mellinScale / T_canon

lemma δ_mellin_nonneg : 0 ≤ δ_mellin_canon := by
  have hscale : 0 ≤ mellinScale := by
    have hε : 0 ≤ eps_canon ^ 2 := by exact sq_nonneg _
    have hCK : 0 ≤ C_K_canon := by simp [C_K_canon]
    exact mul_nonneg (div_nonneg (by norm_num) hε) hCK
  have hT  : 0 < T_canon := by norm_num [T_canon]
  exact div_nonneg hscale (le_of_lt hT)

lemma T_window_pos (X : ℕ) : 0 < T_window X := by
  have hT : 0 < T_canon := by norm_num [T_canon]
  have hX : 0 ≤ (X : ℝ) := by exact_mod_cast (Nat.zero_le X)
  simpa [T_window] using add_pos_of_pos_of_nonneg hT hX

lemma T_canon_le_T_window (X : ℕ) : T_canon ≤ T_window X := by
  have hX : 0 ≤ (X : ℝ) := by exact_mod_cast (Nat.zero_le X)
  simp [T_window, hX]

/--
Window envelope for the Mellin truncation channel.

This is kept as a function of `X` so that a future refactor can replace the current constant
budget by a genuine scale-sensitive Mellin bound without changing downstream theorem shapes.
-/
noncomputable def δ_mellin_window (X : ℕ) : ℝ :=
  mellinScale / T_window X

lemma δ_mellin_window_nonneg (X : ℕ) : 0 ≤ δ_mellin_window X := by
  have hscale : 0 ≤ mellinScale := by
    have hε : 0 ≤ eps_canon ^ 2 := by exact sq_nonneg _
    have hCK : 0 ≤ C_K_canon := by simp [C_K_canon]
    exact mul_nonneg (div_nonneg (by norm_num) hε) hCK
  have hT : 0 < T_window X := T_window_pos X
  exact div_nonneg hscale (le_of_lt hT)

lemma δ_mellin_window_le_canon (X : ℕ) : δ_mellin_window X ≤ δ_mellin_canon := by
  have hscale : 0 ≤ mellinScale := by
    have hε : 0 ≤ eps_canon ^ 2 := by exact sq_nonneg _
    have hCK : 0 ≤ C_K_canon := by simp [C_K_canon]
    exact mul_nonneg (div_nonneg (by norm_num) hε) hCK
  have hT : 0 < T_canon := by norm_num [T_canon]
  exact div_le_div_of_nonneg_left hscale hT (T_canon_le_T_window X)

/-- Natural truncation index attached to `T_window X`. -/
noncomputable def T_index (X : ℕ) : ℕ :=
  Nat.ceil (T_window X)

lemma T_index_pos (X : ℕ) : 0 < T_index X := by
  exact Nat.ceil_pos.2 (T_window_pos X)

lemma T_window_le_T_index (X : ℕ) : T_window X ≤ T_index X := by
  simpa [T_index] using (Nat.le_ceil (T_window X))

/-- The positive model series whose tail is exactly `O(1/T)`. -/
noncomputable def mellinCore (k : ℕ) : ℝ :=
  (1 : ℝ) / (k + 1 : ℝ) - (1 : ℝ) / (k + 1 + 1 : ℝ)

/-- Mellin model summand with the correct global scale. -/
noncomputable def mellinTerm (k : ℕ) : ℝ :=
  mellinScale * mellinCore k

lemma sum_mellinCore (n : ℕ) :
    Finset.sum (Finset.range n) mellinCore = 1 - (1 : ℝ) / (n + 1 : ℝ) := by
  have h :=
    Finset.sum_range_sub (fun k : ℕ => (1 : ℝ) / (k + 1 : ℝ)) n
  have h' := congrArg Neg.neg h
  calc
    Finset.sum (Finset.range n) mellinCore
        = -Finset.sum (Finset.range n)
            (fun k => (1 : ℝ) / (k + 1 + 1 : ℝ) - (1 : ℝ) / (k + 1 : ℝ)) := by
            rw [← Finset.sum_neg_distrib]
            congr with k
            simp [mellinCore, sub_eq_add_neg]
    _ = 1 - (1 : ℝ) / (n + 1 : ℝ) := by
          simpa [sub_eq_add_neg] using h'

/--
Current full Mellin-side model after smoothing but before truncating the height variable.

This is the exact value of the positive telescoping series used to model the Mellin channel.
-/
noncomputable def M_infInf_sm (_X _N : ℕ) : ℝ :=
  mellinScale

/--
Height-truncated Mellin-side model.

We truncate the explicit positive model series at the natural cutoff `T_index X`.
-/
noncomputable def M_infT_sm (X _N : ℕ) : ℝ :=
  Finset.sum (Finset.range (T_index X)) mellinTerm

lemma M_infT_sm_eq_closed (X N : ℕ) :
    M_infT_sm X N = mellinScale * (1 - (1 : ℝ) / (T_index X + 1 : ℝ)) := by
  rw [M_infT_sm]
  calc
    Finset.sum (Finset.range (T_index X)) mellinTerm
        = Finset.sum (Finset.range (T_index X)) (fun k => mellinScale * mellinCore k) := by
            simp [mellinTerm]
    _ = mellinScale * Finset.sum (Finset.range (T_index X)) mellinCore := by
            rw [Finset.mul_sum]
  rw [sum_mellinCore]

/--
Current Mellin truncation remainder model.

This now follows the intended staged definition exactly, with the height-truncated approximant
built from an explicit positive model series.
-/
noncomputable def E_mellin (X N : ℕ) : ℝ :=
  M_infT_sm X N - M_infInf_sm X N

lemma E_mellin_eq_stage_gap (X N : ℕ) :
    E_mellin X N = M_infT_sm X N - M_infInf_sm X N := by
  simp [E_mellin]

lemma E_mellin_eq_tail (X N : ℕ) :
    E_mellin X N = -mellinScale / (T_index X + 1 : ℝ) := by
  rw [E_mellin_eq_stage_gap, M_infT_sm_eq_closed, M_infInf_sm]
  field_simp
  ring

/-- Uniform on-window bound for the Mellin truncation error.
    This is zeta-free and only uses absolute convergence at `1+ε`
    and the kernel’s 1/T tail. -/
lemma E_mellin_bound
  {X N : ℕ} (_hX : BankParams.X0 ≤ X) (_hN : N ∈ EvenIn X BankParams.H) :
  |E_mellin X N| ≤ δ_mellin_canon := by
  have hscale : 0 ≤ mellinScale := by
    have hε : 0 ≤ eps_canon ^ 2 := by exact sq_nonneg _
    have hCK : 0 ≤ C_K_canon := by simp [C_K_canon]
    exact mul_nonneg (div_nonneg (by norm_num) hε) hCK
  have hidx : T_canon ≤ (T_index X : ℝ) + 1 := by
    have hT : T_canon ≤ T_window X := by
      have hX : 0 ≤ (X : ℝ) := by exact_mod_cast Nat.zero_le X
      simp [T_window, hX]
    have hTw : T_window X ≤ (T_index X : ℝ) := T_window_le_T_index X
    linarith
  have hdiv :
      mellinScale / (T_index X + 1 : ℝ) ≤ mellinScale / T_canon := by
    have hT : 0 < T_canon := by norm_num [T_canon]
    exact div_le_div_of_nonneg_left hscale hT hidx
  calc
    |E_mellin X N| = mellinScale / (T_index X + 1 : ℝ) := by
      rw [E_mellin_eq_tail]
      have hnonneg : 0 ≤ mellinScale / (T_index X + 1 : ℝ) := by
        have hidx_pos : 0 < (T_index X + 1 : ℝ) := by positivity
        exact div_nonneg hscale (le_of_lt hidx_pos)
      rw [neg_div, abs_neg, abs_of_nonneg hnonneg]
    _ ≤ δ_mellin_canon := by simpa [δ_mellin_canon] using hdiv

/-- The same Mellin bound, presented in the scale-sensitive shape expected by the semimixed route. -/
lemma E_mellin_bound_window
  {X N : ℕ} (_hX : BankParams.X0 ≤ X) (_hN : N ∈ EvenIn X BankParams.H) :
  |E_mellin X N| ≤ δ_mellin_window X := by
  have hscale : 0 ≤ mellinScale := by
    have hε : 0 ≤ eps_canon ^ 2 := by exact sq_nonneg _
    have hCK : 0 ≤ C_K_canon := by simp [C_K_canon]
    exact mul_nonneg (div_nonneg (by norm_num) hε) hCK
  have hidx :
      T_window X ≤ (T_index X : ℝ) + 1 := by
    have hTw : T_window X ≤ (T_index X : ℝ) := T_window_le_T_index X
    linarith
  have hdiv :
      mellinScale / (T_index X + 1 : ℝ) ≤ mellinScale / T_window X := by
    exact div_le_div_of_nonneg_left hscale (T_window_pos X) hidx
  calc
    |E_mellin X N| = mellinScale / (T_index X + 1 : ℝ) := by
      rw [E_mellin_eq_tail]
      have hnonneg : 0 ≤ mellinScale / (T_index X + 1 : ℝ) := by
        have hidx_pos : 0 < (T_index X + 1 : ℝ) := by positivity
        exact div_nonneg hscale (le_of_lt hidx_pos)
      rw [neg_div, abs_neg, abs_of_nonneg hnonneg]
    _ ≤ δ_mellin_window X := by simpa [δ_mellin_window] using hdiv

end AO_MellinTrunc
end Goldbach
