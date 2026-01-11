import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.TailBlock

/-!
Project-facing numeric budget hypothesis for the off-diagonal σ-tail (fixed-`Q0` track).

This is **not** conventional math: it is the uniform window-budget inequality needed by the
off-diagonal channel when the tail bound is of the Tenor form

`|sigmaTail| ≤ (K_tail / Q0) * F_block(N)`.

As discussed, a uniform budget at fixed `Q0` is not expected to be literally true for all windows;
this file is therefore a placeholder until `Q(X)` and the budget are made honest.

LEGACY FILE NOT IN PIPELINE
-/

namespace Goldbach.Cert.OffDiagBudgetAxioms

open Goldbach.Windows

noncomputable def eps_canon : ℝ := (3e-4 : ℝ)

@[simp] lemma eps_canon_eq : eps_canon = (3e-4 : ℝ) := rfl

lemma eps_canon_nonneg : 0 ≤ eps_canon := by
  norm_num [eps_canon]

/--
Project-facing numeric budget hypothesis on the canonical window (fixed cutoff `Q0`).

This file does *not* fix a specific “Tenor constant”: any such choice is project-specific, and the
fixed-`Q0` regime is not expected to yield a clean uniform window budget without additional work.
-/
axiom budget_ok_canon (K_tail : ℝ) :
  ∀ {X N : ℕ}, Goldbach.BankParams.X0 ≤ X → N ∈ EvenIn X Goldbach.BankParams.H →
    (K_tail / (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ))
        * Goldbach.AO_OffDiag.TailBlock.F_block N ≤ eps_canon

end Goldbach.Cert.OffDiagBudgetAxioms
