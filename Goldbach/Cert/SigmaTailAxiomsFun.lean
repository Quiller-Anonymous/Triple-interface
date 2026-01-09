import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.TailBlockFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.Cert.SigmaTailExplicitBoundFun

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
for a positive truncation height `Q(X)`, the σ-tail is `O(F(N)/Q(X))` with canonical constant
`K_tail = 1.02`, where the conventional arithmetic factor is `F(N) = F_block(N)`.

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

/-- Project-facing calibration axiom for the canonical window (placeholder for the constants work). -/
axiom explicitMajorant_bound_on_window_canon (Q : ℕ → ℕ) :
  ExplicitMajorantBoundOnWindow Goldbach.BankParams.X0 Goldbach.BankParams.H Q K_tail_canon

theorem sigmaTail_bound_on_window_canon (Q : ℕ → ℕ) :
    SigmaTailBoundOnWindow Goldbach.BankParams.X0 Goldbach.BankParams.H Q K_tail_canon := by
  intro X N hX hN hQ

  -- From `N ∈ EvenIn X H` and `X0 ≤ X`, extract `N ≠ 0` (needed by the explicit majorant lemma).
  have hXpos : 0 < X := lt_of_lt_of_le (by
    -- `X0 = 1_000_000` in this project, so it is positive
    exact Nat.pos_of_ne_zero (by norm_num [Goldbach.BankParams.X0])) hX
  have hXN : X ≤ N := by
    rcases Finset.mem_filter.mp hN with ⟨hIn, _hEven⟩
    rcases Finset.mem_image.mp hIn with ⟨k, _hk, hkEq⟩
    subst hkEq
    exact Nat.le_add_right X k
  have hN0 : N ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le hXpos hXN)

  have htail :
      |Goldbach.AO_OffDiag.SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (Goldbach.Cert.SigmaTailExplicitBoundFun.explicitMajorantENN (Q X) N).toReal :=
    Goldbach.Cert.SigmaTailExplicitBoundFun.sigmaTail_abs_le_explicit (Q := Q X) (N := N) hN0

  have hmaj :
      (Goldbach.Cert.SigmaTailExplicitBoundFun.explicitMajorantENN (Q X) N).toReal
        ≤ K_tail_canon / (Q X : ℝ) * Goldbach.AO_OffDiag.TailBlockFun.F_block N :=
    explicitMajorant_bound_on_window_canon (Q := Q) (X := X) (N := N) hX hN hQ

  exact le_trans htail hmaj

end Goldbach.Cert.SigmaTailAxiomsFun
