import Mathlib
import Goldbach.AO_OffDiag.TailBlockFun

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows

namespace EntryPointFun

open TailBlockFun

/-!
Parallel “Tenor-style” off-diagonal entry point.

The existing file `Goldbach/AO_OffDiag/EntryPoint.lean` hard-codes the truncation height `Q0`.
Tenor’s main text uses a scale-dependent truncation `Q = Q(X)` (typically `Q = H^γ` with
`H = (log X)^A`).

This module exposes the **structural** API for an off-diagonal tail bound at variable height,
leaving the analytic derivation (reindexing + Euler tail control) to be ported later.
-/

/--
Structural off-diagonal model at variable truncation `Q(X)`.

Inputs are deliberately “honest shape”:
- `Q_pos_on_window`: `Q(X) ≥ 1` on the canonical window;
- `F_bound_on_window`: a uniform `F_block` bound on the window (purely multiplicative size);
- `sigma_tail_block`: the actual tail inequality at truncation height `Q(X)` (analytic content).

Everything here is just packaging/wiring.
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
  (K_tail_nonneg : 0 ≤ K_tail)
  (sigma : ℕ → ℝ)
  (sigma_tail_block :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |sigma N - TailBlockFun.sigma_trunc (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N) :
  TailBlockFun.Model where
  Q := Q
  Q_pos_on_window := Q_pos_on_window
  sigma := sigma
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
    exact sigma_tail_block (X := X) (N := N) hX hN

/-- Structural tail bound on the canonical window, for the constructed model. -/
theorem tail_bound_on_window_structural
  (Q : ℕ → ℕ)
  (Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X)
  (F_ub : ℝ)
  (F_ub_nonneg : 0 ≤ F_ub)
  (F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      TailBlockFun.F_block N ≤ F_ub)
  (K_tail : ℝ)
  (K_tail_nonneg : 0 ≤ K_tail)
  (sigma : ℕ → ℝ)
  (sigma_tail_block :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |sigma N - TailBlockFun.sigma_trunc (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |sigma N - TailBlockFun.sigma_trunc (Q X) N|
    ≤ (K_tail : ℝ) / (Q X : ℝ) * (F_ub : ℝ) := by
  simpa [offDiagModel] using
    TailBlockFun.tail_bound_on_window_structural
      (M := offDiagModel Q Q_pos_on_window F_ub F_ub_nonneg F_bound_on_window K_tail K_tail_nonneg
        sigma sigma_tail_block)
      (X := X) (N := N) hX hN

end EntryPointFun

end AO_OffDiag
end Goldbach

