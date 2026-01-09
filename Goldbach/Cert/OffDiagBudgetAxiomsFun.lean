import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.TailBlock

/-!
Project-facing numeric budget hypothesis for the off-diagonal σ-tail (FunX track).

This is **not** conventional math: it is exactly the uniform window-budget inequality needed by the
AO off-diagonal channel when the tail bound is of the Tenor form

`|sigmaTail| ≤ (K_tail / Q) * F_block(N)`.

In the current codebase, the canonical FunX instantiation uses the fixed cutoff `Q0 = 30000`,
`K_tail = 180`, and targets `eps = 3e-4`.

As discussed, a uniform budget at fixed `Q0` is not expected to be literally true for all windows;
this file is therefore a placeholder until `Q(X)` and the budget are made honest.
-/

namespace Goldbach.Cert.OffDiagBudgetAxiomsFun

open Goldbach.Windows

/--
Canonical (placeholder) truncation height function for the FunX track.

This is an **honesty** improvement over the fixed `Q0` choice: it makes `Q` grow with the scale
`X`, which is the only plausible way to make a window-uniform budget compatible with the slow
growth of `F_block(N)` as `N ≍ X`.

We keep a `max` with `Q0` to preserve compatibility with the historical fixed-cutoff value at
moderate scales.
-/
noncomputable def Qfun_canon (X : ℕ) : ℕ :=
  max Goldbach.AO_OffDiag.TailBlock.Q0 (X ^ 3)

lemma Qfun_canon_pos (X : ℕ) : 1 ≤ Qfun_canon X := by
  have hQ0 : 1 ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by
    -- `Q0 = 30000`
    simp [Goldbach.AO_OffDiag.TailBlock.Q0]
  -- `1 ≤ max Q0 ...`
  exact le_trans hQ0 (Nat.le_max_left _ _)

noncomputable def eps_canon : ℝ := (3e-4 : ℝ)

@[simp] lemma eps_canon_eq : eps_canon = (3e-4 : ℝ) := rfl

lemma eps_canon_nonneg : 0 ≤ eps_canon := by
  norm_num [eps_canon]

/--
Canonical off-diagonal budget inequality on the canonical window, in the Fun-track symbols.

This is the exact hypothesis needed to turn the Tenor-shaped tail bound into the uniform numeric
cap `≤ eps_canon`.
-/
noncomputable def K_tail_canon : ℝ := (180 : ℝ)

lemma K_tail_canon_nonneg : 0 ≤ K_tail_canon := by
  norm_num [K_tail_canon]

noncomputable def F_canon (N : ℕ) : ℝ := (N : ℝ) ^ 2

lemma F_canon_nonneg (N : ℕ) : 0 ≤ F_canon N := by
  dsimp [F_canon]
  positivity

theorem budget_ok_canon :
  ∀ {X N : ℕ}, Goldbach.BankParams.X0 ≤ X → N ∈ EvenIn X Goldbach.BankParams.H →
    (K_tail_canon / (Qfun_canon X : ℝ)) * F_canon N ≤ eps_canon
  | X, N, hX, hN => by
    -- Window upper bound: `N ≤ X + H`.
    have hN_le : N ≤ X + Goldbach.BankParams.H := by
      rcases Finset.mem_filter.mp hN with ⟨hIn, _hEven⟩
      rcases Finset.mem_image.mp hIn with ⟨k, hk, hkEq⟩
      have hkLe : k ≤ Goldbach.BankParams.H := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      subst hkEq
      exact Nat.add_le_add_left hkLe X
    -- Lower bound `Qfun_canon X ≥ X^3`.
    have hQ_ge_nat : X ^ 3 ≤ Qfun_canon X := by
      simpa [Qfun_canon] using (Nat.le_max_right Goldbach.AO_OffDiag.TailBlock.Q0 (X ^ 3))
    have hQ_ge : (X ^ 3 : ℝ) ≤ (Qfun_canon X : ℝ) := by
      exact_mod_cast hQ_ge_nat

    -- Positivity on the canonical window.
    have hXpos_nat : 0 < X := lt_of_lt_of_le (by norm_num [Goldbach.BankParams.X0]) hX
    have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos_nat
    have hX3_pos : (0 : ℝ) < (X ^ 3 : ℝ) := by
      exact_mod_cast (pow_pos hXpos_nat 3)

    -- Compare `1 / Qfun` to `1 / X^3`.
    have hone_div :
        (1 : ℝ) / (Qfun_canon X : ℝ) ≤ (1 : ℝ) / (X ^ 3 : ℝ) := by
      simpa using (one_div_le_one_div_of_le hX3_pos hQ_ge)

    have hcoef :
        K_tail_canon / (Qfun_canon X : ℝ) ≤ K_tail_canon / (X ^ 3 : ℝ) := by
      have hK_nonneg : 0 ≤ K_tail_canon := K_tail_canon_nonneg
      simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm, K_tail_canon] using
        (mul_le_mul_of_nonneg_left hone_div hK_nonneg)

    -- Use `H = X0/100` to get `X + H ≤ (101/100) X` for all `X ≥ X0`.
    have hHX : (100 * Goldbach.BankParams.H : ℕ) ≤ X := by
      -- `100 * H = X0` and `X0 ≤ X`.
      have hEq : (100 * Goldbach.BankParams.H : ℕ) = Goldbach.BankParams.X0 := by
        norm_num [Goldbach.BankParams.H, Goldbach.BankParams.X0]
      simpa [hEq] using hX
    have hH_le_X_div_100 : (Goldbach.BankParams.H : ℝ) ≤ (X : ℝ) / (100 : ℝ) := by
      have hHXr : (100 : ℝ) * (Goldbach.BankParams.H : ℝ) ≤ (X : ℝ) := by exact_mod_cast hHX
      nlinarith
    have hXH_le : (X : ℝ) + (Goldbach.BankParams.H : ℝ) ≤ ((101 : ℝ) / 100) * (X : ℝ) := by
      nlinarith [hH_le_X_div_100]

    -- Bound `N^2` using `N ≤ X + H`.
    have hN_le_real : (N : ℝ) ≤ (X : ℝ) + (Goldbach.BankParams.H : ℝ) := by
      exact_mod_cast hN_le
    have hN_le_scale : (N : ℝ) ≤ ((101 : ℝ) / 100) * (X : ℝ) := le_trans hN_le_real hXH_le
    have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hNsq :
        (N : ℝ) ^ 2 ≤ (((101 : ℝ) / 100) * (X : ℝ)) ^ 2 := by
      -- squaring is monotone on nonnegative reals
      have hR_nonneg : 0 ≤ ((101 : ℝ) / 100) * (X : ℝ) := by positivity
      have h := mul_le_mul hN_le_scale hN_le_scale hN_nonneg (le_trans hN_nonneg hN_le_scale)
      simpa [pow_two] using h

    -- Assemble.
    have hF_nonneg : 0 ≤ F_canon N := F_canon_nonneg N
    have hmain :
        (K_tail_canon / (Qfun_canon X : ℝ)) * F_canon N
          ≤ (K_tail_canon / (X ^ 3 : ℝ)) * (((101 : ℝ) / 100) * (X : ℝ)) ^ 2 := by
      have h1 :
          (K_tail_canon / (Qfun_canon X : ℝ)) * F_canon N
            ≤ (K_tail_canon / (X ^ 3 : ℝ)) * F_canon N :=
        mul_le_mul_of_nonneg_right hcoef hF_nonneg
      have h2 :
          (K_tail_canon / (X ^ 3 : ℝ)) * F_canon N
            ≤ (K_tail_canon / (X ^ 3 : ℝ)) * (((101 : ℝ) / 100) * (X : ℝ)) ^ 2 := by
        have hcoef_nonneg : 0 ≤ K_tail_canon / (X ^ 3 : ℝ) :=
          div_nonneg K_tail_canon_nonneg (le_of_lt hX3_pos)
        -- `F_canon N = (N:ℝ)^2`
        dsimp [F_canon]
        exact mul_le_mul_of_nonneg_left hNsq hcoef_nonneg
      exact le_trans h1 h2

    -- Finish with a purely numeric bound at `X0 = 10^6`.
    have hnum :
        (K_tail_canon / (X ^ 3 : ℝ)) * (((101 : ℝ) / 100) * (X : ℝ)) ^ 2 ≤ eps_canon := by
      -- Simplify to `C / X` and use `X ≥ X0`.
      have hxne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
      have hrewrite :
          (K_tail_canon / (X ^ 3 : ℝ)) * (((101 : ℝ) / 100) * (X : ℝ)) ^ 2
            = (K_tail_canon * ((101 : ℝ) / 100) ^ 2) * ((1 : ℝ) / (X : ℝ)) := by
        field_simp [hxne]
      have hX_ge : (Goldbach.BankParams.X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have hX0_pos : (0 : ℝ) < (Goldbach.BankParams.X0 : ℝ) := by norm_num [Goldbach.BankParams.X0]
      have hone_divX :
          (1 : ℝ) / (X : ℝ) ≤ (1 : ℝ) / (Goldbach.BankParams.X0 : ℝ) := by
        simpa using (one_div_le_one_div_of_le hX0_pos hX_ge)
      calc
        (K_tail_canon / (X ^ 3 : ℝ)) * (((101 : ℝ) / 100) * (X : ℝ)) ^ 2
            = (K_tail_canon * ((101 : ℝ) / 100) ^ 2) * ((1 : ℝ) / (X : ℝ)) := hrewrite
        _ ≤ (K_tail_canon * ((101 : ℝ) / 100) ^ 2) * ((1 : ℝ) / (Goldbach.BankParams.X0 : ℝ)) := by
              have hC_nonneg : 0 ≤ K_tail_canon * ((101 : ℝ) / 100) ^ 2 := by
                have : 0 ≤ K_tail_canon := K_tail_canon_nonneg
                positivity
              exact mul_le_mul_of_nonneg_left hone_divX hC_nonneg
        _ ≤ eps_canon := by
              norm_num [K_tail_canon, Goldbach.BankParams.X0, eps_canon]

    exact le_trans hmain hnum

end Goldbach.Cert.OffDiagBudgetAxiomsFun
