import Mathlib
import Goldbach.AO_OffDiag.TailBlockFunX
import Goldbach.AO_OffDiag.SigmaTailReindexFun

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows

/-!
Tenor-parallel off-diagonal construction at variable truncation `Q(X)`, using an
`X`-dependent sigma witness.

Key benefit: we can define

`sigma X N := sigma_trunc (Q X) N + sigmaTail (Q X) N`

so the identity `sigma - trunc = tail` is definitional (no axiom needed).
-/

namespace EntryPointTenorFunX

open TailBlockFun
open TailBlockFunX
open SigmaTailReindexFun

/-- The definitional “honest sigma witness” at truncation height `Q(X)`. -/
noncomputable def sigmaHonest (Q : ℕ → ℕ) (X N : ℕ) : ℝ :=
  TailBlockFun.sigma_trunc (Q X) N + SigmaTailReindexFun.sigmaTail (Q X) N

/-- Definitional tail identity for `sigmaHonest`. -/
lemma sigmaHonest_sub_trunc (Q : ℕ → ℕ) (X N : ℕ) :
    sigmaHonest Q X N - TailBlockFun.sigma_trunc (Q X) N = SigmaTailReindexFun.sigmaTail (Q X) N := by
  simp [sigmaHonest, sub_eq_add_neg, add_assoc, add_comm]

/--
Derived `sigma_tail_block` inequality for `sigmaHonest` from:
the definitional tail identity and a Tenor-style truncation bound for `sigmaTail` on the window.
-/
theorem sigma_tail_block_sigmaHonest
  (Q : ℕ → ℕ) (K_tail : ℝ)
  (sigmaTail_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
  |sigmaHonest Q X N - TailBlockFun.sigma_trunc (Q X) N|
    ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
  have h1 :
      |sigmaHonest Q X N - TailBlockFun.sigma_trunc (Q X) N|
        = |SigmaTailReindexFun.sigmaTail (Q X) N| := by
    simpa [sigmaHonest_sub_trunc]
  exact (by
    simpa [h1] using sigmaTail_bound_on_window (X := X) (N := N) hX hN)

/--
Build an `X`-dependent tail-block model using `sigmaHonest`.
-/
noncomputable def offDiagModel
  (Q : ℕ → ℕ)
  (Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X)
  (F_ub : ℝ)
  (F_ub_nonneg : 0 ≤ F_ub)
  (F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      TailBlockFun.F_block N ≤ F_ub)
  (K_tail : ℝ)
  (sigmaTail_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N)
  (K_tail_nonneg : 0 ≤ K_tail) :
  TailBlockFunX.Model where
  Q := Q
  Q_pos_on_window := Q_pos_on_window
  sigma := sigmaHonest Q
  F := TailBlockFun.F_block
  K_tail := K_tail
  K_tail_nonneg := K_tail_nonneg
  F_ub := F_ub
  F_ub_nonneg := F_ub_nonneg
  F_bound_on_window := by
    intro X N hX hN
    exact F_bound_on_window (X := X) (N := N) hX hN
  sigma_tail_block := by
    intro X N hX hN
    exact sigma_tail_block_sigmaHonest (Q := Q) (K_tail := K_tail)
      (sigmaTail_bound_on_window := sigmaTail_bound_on_window) hX hN

end EntryPointTenorFunX

end AO_OffDiag
end Goldbach
