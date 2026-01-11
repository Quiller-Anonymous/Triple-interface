import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.Cert.SigmaTailExplicitBoundFun

/-!
Textbook-facing σ-tail truncation axiom (`Q(X)` / “Fun” track).

This file defines the *textbook-shaped* statement we ultimately want for the reindexed σ-tail used
by the Fun track (variable truncation height `Q(X)`).

Status note:
- The **canonical FunX pipeline no longer depends on any pinned “tiny constant / Q” σ-tail axiom**; it uses the
  explicit majorant route (`Goldbach/Cert/SigmaTailRealBoundFun.lean`) together with a growing
  truncation schedule `Q(X)` and a separate numeric budget lemma.
- We keep this file purely as a *specification layer* for the “Tenor-shaped” σ-tail statement.
-/

namespace Goldbach.Cert.SigmaTailAxiomsFun

open Goldbach.Windows

/--
Conventional truncation input on the canonical window:
for a positive truncation height `Q(X)`, the σ-tail is `O(F(N)/Q(X))` with canonical constant
`K_tail`, where the conventional arithmetic factor is `F(N) = F_block(N)`.

This is intended as a single “textbook” analytic input; all reindexing/majorant bookkeeping is
proved elsewhere.
-/
def SigmaTailBoundOnWindow (X0 H : ℕ) (Q : ℕ → ℕ) (K_tail : ℝ) : Prop :=
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
    |Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail (Q X) N|
      ≤ K_tail / (Q X : ℝ) * Goldbach.AO_OffDiag.TailBlockFun.F_block N

/-!
### Reduced “constants obligation”

The core analytic work (reindexing + Euler tail control) already produces an explicit
`ENNReal` divisor-sum majorant for `|sigmaTail|` (see `Goldbach/Cert/SigmaTailExplicitBoundFun.lean`).

To obtain the Tenor-shaped bound `|sigmaTail| ≤ (K_tail/Q) * F_block`, what remains is to
upper-bound that explicit majorant by the desired right-hand side on the canonical window.
-/

/-- Property: the explicit ENNReal majorant is bounded by `(K_tail/Q(X)) * F_block(N)` on a window. -/
def ExplicitMajorantBoundOnWindow (X0 H : ℕ) (Q : ℕ → ℕ) (K_tail : ℝ) : Prop :=
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → 1 ≤ Q X →
    (Goldbach.Cert.SigmaTailExplicitBoundFun.explicitMajorantENN (Q X) N).toReal
      ≤ K_tail / (Q X : ℝ) * Goldbach.AO_OffDiag.TailBlockFun.F_block N

end Goldbach.Cert.SigmaTailAxiomsFun
