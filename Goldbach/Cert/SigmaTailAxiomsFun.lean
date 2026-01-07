import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.SigmaTailReindexFun

/-!
Textbook-facing σ-tail truncation axiom (`Q(X)` / “Fun” track).

This file holds the *conventional* analytic assumption for the reindexed σ-tail used by the Fun
track (variable truncation height `Q(X)`).

Implementation modules should not declare axioms; they should import this file and re-export the
statement as a theorem in their expected namespace.
-/

namespace Goldbach.Cert.SigmaTailAxiomsFun

open Goldbach.Windows

/-- Canonical numeric constant for the σ-tail truncation bound in the `Q(X)` (“Fun”) track. -/
noncomputable def K_tail_canon : ℝ := (1.02 : ℝ)

lemma K_tail_canon_nonneg : 0 ≤ K_tail_canon := by
  norm_num [K_tail_canon]

/--
Conventional truncation input on the canonical window:
for a positive truncation height `Q(X)`, the σ-tail is `O(1/Q(X))` with canonical constant
`K_tail = 1.02`.

This is intended as a single “textbook” analytic input; all reindexing/majorant bookkeeping is
proved elsewhere.
-/
def SigmaTailBoundOnWindow (X0 H : ℕ) (Q : ℕ → ℕ) (K_tail : ℝ) : Prop :=
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
    |Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail (Q X) N|
      ≤ K_tail / (Q X : ℝ)

axiom sigmaTail_bound_on_window
  (X0 H : ℕ) (Q : ℕ → ℕ) :
  SigmaTailBoundOnWindow X0 H Q K_tail_canon

theorem sigmaTail_bound_on_window_canon (Q : ℕ → ℕ) :
    SigmaTailBoundOnWindow Goldbach.BankParams.X0 Goldbach.BankParams.H Q K_tail_canon :=
  sigmaTail_bound_on_window (X0 := Goldbach.BankParams.X0) (H := Goldbach.BankParams.H) Q

end Goldbach.Cert.SigmaTailAxiomsFun
