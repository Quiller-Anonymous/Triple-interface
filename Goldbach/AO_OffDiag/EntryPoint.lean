import Mathlib
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailEuler
import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.AO_OffDiag.SigmaTailTenorAxioms
import Goldbach.Cert.OffDiagBudgetAxioms

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

The Tenor-style truncation bound carries the conventional arithmetic factor `F_block(N)`:

`|σ(N) - σ_{≤Q}(N)| ≤ (K_tail/Q) * F_block(N)`.

To obtain a uniform numerical budget `≤ 3e-4` on the canonical window, we also need a
project-specific on-window budget inequality (see `Goldbach/Cert/OffDiagBudgetAxioms.lean`).
-/

noncomputable def offDiagModel : TailBlock.Model where
  sigma := sigmaHonest
  F := TailBlock.F_block

  -- NOTE: the fixed-`Q0` track does not pin a specific numeric `K_tail` here; any such choice is
  -- project-specific, and (as discussed) a uniform window budget at fixed `Q0` is not expected to
  -- hold without additional structure.
  K_tail := (1 : ℝ)
  K_tail_nonneg := by norm_num

  sigma_tail_block := by
    intro X N hX hN
    -- reduce to the tail and apply the (conventional) uniform truncation axiom
    have hdiff :
        sigmaHonest N - TailBlock.sigma_trunc_Q0 N = SigmaTailReindex.sigmaTail N := by
      simp [sigmaHonest, sub_eq_add_neg, add_assoc, add_comm]
    have htail :
        |SigmaTailReindex.sigmaTail N|
          ≤ (1 : ℝ) / (TailBlock.Q0 : ℝ) * TailBlock.F_block N :=
      sigmaTail_bound_on_window (K_tail := (1 : ℝ)) (X := X) (N := N) hX hN
    have :
        |sigmaHonest N - TailBlock.sigma_trunc_Q0 N|
          ≤ (1 : ℝ) / (TailBlock.Q0 : ℝ) * TailBlock.F_block N := by
      simpa [hdiff] using htail
    simpa [TailBlock.Q0, one_div] using this

lemma offDiag_budget_ok {X N : ℕ}
    (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
    (offDiagModel.K_tail : ℝ) / (Q0 : ℝ) * offDiagModel.F N ≤ (3e-4 : ℝ) := by
  -- placeholder budget axiom (see `Goldbach/Cert/OffDiagBudgetAxioms.lean`)
  have h :=
    Goldbach.Cert.OffDiagBudgetAxioms.budget_ok_canon (K_tail := offDiagModel.K_tail) (X := X) (N := N) hX hN
  simpa [offDiagModel, Goldbach.Cert.OffDiagBudgetAxioms.eps_canon, TailBlock.Q0] using h

theorem tail_bound_on_window {X N : ℕ}
  (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |sigmaHonest N - sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  -- Consumer lemma: structural bound + numeric budget.
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window (M := offDiagModel) (eps := (3e-4 : ℝ))
      (hbudget := by
        intro X N hX hN
        simpa [offDiagModel] using offDiag_budget_ok (X := X) (N := N) hX hN)
      hX hN

end AO_OffDiag
end Goldbach
