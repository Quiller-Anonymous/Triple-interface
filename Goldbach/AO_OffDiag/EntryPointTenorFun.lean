import Mathlib
import Goldbach.AO_OffDiag.EntryPointFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows

/-!
Tenor-parallel off-diagonal instantiation at truncation height `Q(X)`.

This file is the “next layer” after `TailBlockFun`/`EntryPointFun`: it shows how one would
derive the model's `sigma_tail_block` bound from a reindexing tail bound plus a window
comparison between the reindex majorant and `F_block`.

We keep the genuinely analytic comparisons as axioms for now (conventional-math obligations),
and keep everything else as definitional rewrites + triangle/monotonicity.
-/

namespace EntryPointTenorFun

open TailBlockFun
open SigmaTailReindexFun

/-- A sigma-decomposition fact: the difference between the true `sigma` and truncation is the tail. -/
axiom sigma_sub_trunc_eq_tail_on_window
  (sigma : ℕ → ℝ) (Q : ℕ → ℕ)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    sigma N - TailBlockFun.sigma_trunc (Q X) N = SigmaTailReindexFun.sigmaTail (Q X) N

/--
Analytic comparison on the window:
the reindexing majorant is controlled by `(K_tail / Q(X)) * F_block N`.
-/
axiom reindexMajorant_bound_on_window
  (Q : ℕ → ℕ) (K_tail : ℝ)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    (SigmaTailReindexFun.reindexMajorantENN (Q X) N).toReal
      ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N

/--
Derived `sigma_tail_block` inequality from:
`(sigma - trunc) = tail`, the certified reindex tail bound, and the window majorant comparison.
-/
theorem sigma_tail_block_from_reindex
  (sigma : ℕ → ℝ) (Q : ℕ → ℕ) (K_tail : ℝ)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
  |sigma N - TailBlockFun.sigma_trunc (Q X) N|
    ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
  have hdiff :
      sigma N - TailBlockFun.sigma_trunc (Q X) N = SigmaTailReindexFun.sigmaTail (Q X) N :=
    sigma_sub_trunc_eq_tail_on_window (sigma := sigma) (Q := Q) hX hN
  have h1 :
      |sigma N - TailBlockFun.sigma_trunc (Q X) N| = |SigmaTailReindexFun.sigmaTail (Q X) N| := by
    simpa [hdiff]
  have htail :
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (SigmaTailReindexFun.reindexMajorantENN (Q X) N).toReal :=
    SigmaTailReindexFun.tail_reindex_bound (Q := Q X) (N := N)
  have hmaj :
      (SigmaTailReindexFun.reindexMajorantENN (Q X) N).toReal
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
    simpa using reindexMajorant_bound_on_window (Q := Q) (K_tail := K_tail) (X := X) (N := N) hX hN
  exact le_trans (by simpa [h1] using htail) hmaj

/--
Convenience constructor: build an `EntryPointFun.offDiagModel` once you supply:
* `Q(X)` and positivity on the window,
* the uniform `F_block` bound on the window,
* `sigma` and the tail comparison derived above,
* the budget inequality (often proved separately).
-/
noncomputable def offDiagModel
  (sigma : ℕ → ℝ)
  (Q : ℕ → ℕ)
  (Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X)
  (F_ub : ℝ)
  (F_ub_nonneg : 0 ≤ F_ub)
  (F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      TailBlockFun.F_block N ≤ F_ub)
  (K_tail : ℝ)
  (K_tail_nonneg : 0 ≤ K_tail) :
  TailBlockFun.Model :=
  EntryPointFun.offDiagModel
    (Q := Q)
    (Q_pos_on_window := Q_pos_on_window)
    (F_ub := F_ub)
    (F_ub_nonneg := F_ub_nonneg)
    (F_bound_on_window := F_bound_on_window)
    (K_tail := K_tail)
    (K_tail_nonneg := K_tail_nonneg)
    (sigma := sigma)
    (sigma_tail_block := by
      intro X N hX hN
      exact sigma_tail_block_from_reindex (sigma := sigma) (Q := Q) (K_tail := K_tail) hX hN)

end EntryPointTenorFun

end AO_OffDiag
end Goldbach

