import Mathlib
import Goldbach.AO_OffDiag.EntryPointFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.Cert.FBlockConventional

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

/-!
NOTE (honesty): the identity `(sigma - trunc) = tail` is *not* a conventional-math theorem
unless `sigma` is defined to be the full singular-series sum of the `sigmaTerm` used to define
`SigmaTailReindexFun.sigmaTail`.

We therefore do **not** axiomatize it globally here. If you want a definitional version, use the
`EntryPointTenorFunX` approach instead, where `sigmaHonest` is defined as `trunc + tail`.
-/

/-- Hypothesis form of the decomposition identity (use as an argument, not an axiom). -/
def SigmaSubTruncEqTailOnWindow (sigma : ℕ → ℝ) (Q : ℕ → ℕ) : Prop :=
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    sigma N - TailBlockFun.sigma_trunc (Q X) N = SigmaTailReindexFun.sigmaTail (Q X) N

/--
Derived `sigma_tail_block` inequality from:
`(sigma - trunc) = tail` and a Tenor-style truncation bound for `sigmaTail` on the window.
-/
theorem sigma_tail_block_from_reindex
  (sigma : ℕ → ℝ) (Q : ℕ → ℕ) (K_tail : ℝ)
  (hsigma : SigmaSubTruncEqTailOnWindow sigma Q)
  (sigmaTail_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H → 1 ≤ Q X →
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H)
  (hQ : 1 ≤ Q X) :
  |sigma N - TailBlockFun.sigma_trunc (Q X) N|
    ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
  have hdiff :
      sigma N - TailBlockFun.sigma_trunc (Q X) N = SigmaTailReindexFun.sigmaTail (Q X) N :=
    hsigma hX hN
  have h1 :
      |sigma N - TailBlockFun.sigma_trunc (Q X) N| = |SigmaTailReindexFun.sigmaTail (Q X) N| := by
    simpa [hdiff]
  have htail :
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N :=
    sigmaTail_bound_on_window (X := X) (N := N) hX hN hQ
  exact (by simpa [h1] using htail)

/--
Convenience constructor: build an `EntryPointFun.offDiagModel` once you supply:
* `Q(X)` and positivity on the window,
* `sigma` and the tail comparison derived above,
* the budget inequality (often proved separately).
-/
noncomputable def offDiagModel
  (sigma : ℕ → ℝ)
  (Q : ℕ → ℕ)
  (hsigma : SigmaSubTruncEqTailOnWindow sigma Q)
  (Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X)
  (K_tail : ℝ)
  (K_tail_nonneg : 0 ≤ K_tail)
  (sigmaTail_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H → 1 ≤ Q X →
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N)
  : TailBlockFun.Model :=
  EntryPointFun.offDiagModel
    (Q := Q)
    (Q_pos_on_window := Q_pos_on_window)
    (K_tail := K_tail)
    (K_tail_nonneg := K_tail_nonneg)
    (sigma := sigma)
    (sigma_tail_block := by
      intro X N hX hN
      have hQ : 1 ≤ Q X := Q_pos_on_window (X := X) (N := N) hX hN
      exact sigma_tail_block_from_reindex (sigma := sigma) (Q := Q) (K_tail := K_tail)
        (hsigma := hsigma) (sigmaTail_bound_on_window := sigmaTail_bound_on_window) hX hN hQ)

end EntryPointTenorFun

end AO_OffDiag
end Goldbach
