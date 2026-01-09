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
- `sigma_tail_block`: the actual tail inequality at truncation height `Q(X)` (analytic content).

Everything here is just packaging/wiring.
-/
noncomputable def offDiagModel
  (Q : ℕ → ℕ)
  (Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X)
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
  sigma_tail_block := by
    intro X N hX hN
    exact sigma_tail_block (X := X) (N := N) hX hN

end EntryPointFun

end AO_OffDiag
end Goldbach
