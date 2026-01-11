import Goldbach.AO_OffDiag.TenorHypFunX
import Goldbach.Cert.OffDiagBudgetAxiomsFun
import Goldbach.Cert.SigmaTailRealBoundFun

namespace Goldbach.AO_OffDiag.TenorHypFunX

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Canonical bundled off-diagonal hypothesis for the FunX (variable-`Q`) track.

This is *wiring*, not new mathematics:
- we choose `Q(X)` to be the same fixed truncation height `Q0` used on the mainline,
- we choose a conservative tail constant `K_tail = 180` compatible with the current explicit
  majorant route,
- and we set the target window budget to `eps = 3e-4`.

The σ-tail bound is proved (not axiomatized) by combining:
- the explicit reindexing majorant bound (σ-tail ≤ reindex majorant), and
- a crude real upper bound on that explicit majorant (`Goldbach/Cert/SigmaTailRealBoundFun.lean`)
  together with a growing truncation schedule `Q(X)`.

NOTE (honesty): the present canonical record also relies on a *project-specific* placeholder
budget inequality (see `Goldbach/Cert/OffDiagBudgetAxiomsFun.lean`), which is not expected to be
literally true in the current “all windows” quantifier regime; it is a marker for the intended
future replacement (an `X`-dependent `F_block` bound and a matching `Q(X)` choice).
-/

namespace Canon

noncomputable def Qfun (X : ℕ) : ℕ := Goldbach.Cert.OffDiagBudgetAxiomsFun.Qfun_canon X
noncomputable def F (N : ℕ) : ℝ := Goldbach.Cert.OffDiagBudgetAxiomsFun.F_canon N
noncomputable def K_tail : ℝ := Goldbach.Cert.OffDiagBudgetAxiomsFun.K_tail_canon
noncomputable def eps : ℝ := Goldbach.Cert.OffDiagBudgetAxiomsFun.eps_canon

lemma Qfun_pos_on_window {X N : ℕ} (_hX : X0 ≤ X) (_hN : N ∈ EvenIn X H) :
    1 ≤ Qfun X := by
  simpa [Qfun] using Goldbach.Cert.OffDiagBudgetAxiomsFun.Qfun_canon_pos X

lemma K_tail_nonneg : 0 ≤ K_tail := by
  simpa [K_tail] using Goldbach.Cert.OffDiagBudgetAxiomsFun.K_tail_canon_nonneg

lemma F_nonneg (N : ℕ) : 0 ≤ F N := by
  simpa [F] using Goldbach.Cert.OffDiagBudgetAxiomsFun.F_canon_nonneg N

lemma eps_nonneg : 0 ≤ eps := by
  simpa [eps] using Goldbach.Cert.OffDiagBudgetAxiomsFun.eps_canon_nonneg

/-- Canonical `OffDiagHyp` for the FunX track. -/
noncomputable def Hoff : OffDiagHyp where
  Q := Qfun
  F := F
  K_tail := K_tail
  K_tail_nonneg := K_tail_nonneg
  eps := eps
  eps_nonneg := eps_nonneg
  Q_pos_on_window := by
    intro X N hX hN
    exact Qfun_pos_on_window (X := X) (N := N) hX hN
  sigmaTail_bound_on_window := by
    intro X N hX hN
    -- Engineering route: derive the bound from the explicit majorant with the crude `N^2/Q` cap.
    -- From `N ∈ EvenIn X H` and `X0 ≤ X`, extract `N ≠ 0` and `N ≤ Qfun X`.
    have hXpos : 0 < X := lt_of_lt_of_le (by
      -- `X0 = 1_000_000` in this project, so it is positive
      exact Nat.pos_of_ne_zero (by norm_num [Goldbach.BankParams.X0])) hX
    have hXN : X ≤ N := by
      rcases Finset.mem_filter.mp hN with ⟨hIn, _hEven⟩
      rcases Finset.mem_image.mp hIn with ⟨k, _hk, hkEq⟩
      subst hkEq
      exact Nat.le_add_right X k
    have hN0 : N ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le hXpos hXN)
    have hN_le : N ≤ X + Goldbach.BankParams.H := by
      rcases Finset.mem_filter.mp hN with ⟨hIn, _hEven⟩
      rcases Finset.mem_image.mp hIn with ⟨k, hk, hkEq⟩
      have hkLe : k ≤ Goldbach.BankParams.H := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      subst hkEq
      exact Nat.add_le_add_left hkLe X
    have hQ_ge_nat : X ^ 3 ≤ Qfun X := by
      simpa [Qfun, Goldbach.Cert.OffDiagBudgetAxiomsFun.Qfun_canon] using
        (Nat.le_max_right Goldbach.AO_OffDiag.TailBlock.Q0 (X ^ 3))
    have hN_le_Q : N ≤ Qfun X := by
      -- `N ≤ X + H ≤ 2X ≤ X^3 ≤ Qfun X`.
      have hHX0 : Goldbach.BankParams.H ≤ Goldbach.BankParams.X0 := by
        norm_num [Goldbach.BankParams.H, Goldbach.BankParams.X0]
      have hH_le_X : Goldbach.BankParams.H ≤ X := le_trans hHX0 hX
      have hX_ge2 : 2 ≤ X := le_trans (by norm_num [Goldbach.BankParams.X0]) hX
      have h1_le_X : 1 ≤ X := le_trans (by norm_num) hX_ge2
      have hX_le_X2 : X ≤ X ^ 2 := by
        -- `X ≤ X * X` since `1 ≤ X`.
        simpa [pow_two] using (Nat.mul_le_mul_left X h1_le_X)
      have h2_le_X2 : 2 ≤ X ^ 2 := le_trans hX_ge2 hX_le_X2
      have h2X_le_X3 : 2 * X ≤ X ^ 3 := by
        -- multiply `2 ≤ X^2` by `X`
        have := Nat.mul_le_mul_right X h2_le_X2
        -- `2 * X ≤ (X^2) * X = X^3`
        simpa [pow_succ, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
      have hXH_le_2X : X + Goldbach.BankParams.H ≤ 2 * X := by
        -- `X + H ≤ X + X = 2X`
        have : X + Goldbach.BankParams.H ≤ X + X := Nat.add_le_add_left hH_le_X X
        simpa [two_mul] using this
      have hN_le_X3 : N ≤ X ^ 3 := le_trans (le_trans hN_le hXH_le_2X) h2X_le_X3
      exact le_trans hN_le_X3 hQ_ge_nat
    have htail :
        |Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail (Qfun X) N|
          ≤ (180 : ℝ) / (Qfun X : ℝ) * (N : ℝ) ^ 2 :=
      Goldbach.Cert.SigmaTailRealBoundFun.sigmaTail_abs_le_180_div_Q_mul_N_sq
        (Q := Qfun X) (N := N) hN0 hN_le_Q
    simpa [K_tail, F, Goldbach.Cert.OffDiagBudgetAxiomsFun.K_tail_canon,
      Goldbach.Cert.OffDiagBudgetAxiomsFun.F_canon, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using htail
  budget_ok := by
    intro X N hX hN
    -- Project-specific placeholder budget inequality for the canonical window.
    simpa [Qfun, K_tail, eps, F] using
      Goldbach.Cert.OffDiagBudgetAxiomsFun.budget_ok_canon (X := X) (N := N) hX hN

end Canon

end Goldbach.AO_OffDiag.TenorHypFunX
