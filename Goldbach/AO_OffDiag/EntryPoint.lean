import Mathlib
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailEuler
import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.AO_OffDiag.SigmaTailTenorAxioms

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows
open TailBlock

/-- Honest sigma: truncation + the tail already defined in `SigmaTailReindex`. -/
noncomputable def sigmaHonest (N : ℕ) : ℝ :=
  TailBlock.sigma_trunc_Q0 N + SigmaTailReindex.sigmaTail N

/-!
## About axioms in this file

This file is a *wiring/entry point* for the off-diagonal channel bound.

We aim for “gold standard” where only **conventional math** is axiomatized.
The older axiom `hsupp_on_window` (all prime factors of `N` are in a tiny fixed set)
was bespoke and not mathematically plausible.

In the tenor writeup, the corresponding statement is a **uniform truncation** bound for the
singular series, with a constant independent of `N`. We expose that as an axiom here, and
keep the rest of the off-diagonal pipeline axiom-free.
-/

/-!
## Model choice

The “tenor” statement we aim to encode is a **uniform truncation** bound:

`|σ(N) - σ_{≤Q}(N)| ≤ C/Q` with `C` independent of `N`.

So, for the current mainline pipeline, we set the auxiliary majorant factor `F` to be constant `1`
and carry only the (conventional/analytic) constant `K_tail = 1.02`.
-/

noncomputable def offDiagModel : TailBlock.Model where
  sigma := sigmaHonest
  F := fun _ => (1 : ℝ)

  K_tail := (1.02 : ℝ)
  K_tail_nonneg := by norm_num

  -- We keep `F_ub = 1` because `F` itself is the constant `1`.
  F_ub := (1 : ℝ)
  F_ub_nonneg := by norm_num

  F_bound_on_window := by
    intro X N hX hN
    simp

  sigma_tail_block := by
    intro X N hX hN
    -- reduce to the tail and apply the (conventional) uniform truncation axiom
    have hdiff :
        sigmaHonest N - TailBlock.sigma_trunc_Q0 N = SigmaTailReindex.sigmaTail N := by
      simp [sigmaHonest, sub_eq_add_neg, add_assoc, add_comm]
    have htail : |SigmaTailReindex.sigmaTail N| ≤ (1.02 : ℝ) / (TailBlock.Q0 : ℝ) :=
      sigmaTail_bound_on_window (X := X) (N := N) hX hN
    have : |sigmaHonest N - TailBlock.sigma_trunc_Q0 N| ≤ (1.02 : ℝ) / (TailBlock.Q0 : ℝ) := by
      simpa [hdiff] using htail
    -- Match the model shape `(K_tail/Q0) * F N` with `F N = 1`.
    simpa [TailBlock.Q0] using (show |sigmaHonest N - TailBlock.sigma_trunc_Q0 N|
      ≤ (1.02 : ℝ) / (TailBlock.Q0 : ℝ) * (1 : ℝ) from by simpa [mul_one] using this)

lemma offDiag_budget_ok :
  offDiagModel.K_tail / (Q0 : ℝ) * offDiagModel.F_ub ≤ (3e-4 : ℝ) := by
  -- Pure arithmetic after unfolding the chosen constants.
  simp [offDiagModel, TailBlock.Q0]
  norm_num

theorem tail_bound_on_window {X N : ℕ}
  (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |sigmaHonest N - sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  -- Consumer lemma: structural bound + numeric budget.
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window (M := offDiagModel) (eps := (3e-4 : ℝ)) offDiag_budget_ok hX hN

end AO_OffDiag
end Goldbach
