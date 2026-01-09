import Mathlib
import Goldbach.AO_OffDiag.EntryPointFun
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.AO_OffDiag.SigmaTailTenorAxiomsFun
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
open SigmaTailTenorAxiomsFun

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
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H)
  (hQ : 1 ≤ Q X)
  (hK : SigmaTailTenorAxiomsFun.K_tail_canon ≤ K_tail) :
  |sigma N - TailBlockFun.sigma_trunc (Q X) N|
    ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
  have hdiff :
      sigma N - TailBlockFun.sigma_trunc (Q X) N = SigmaTailReindexFun.sigmaTail (Q X) N :=
    hsigma hX hN
  have h1 :
      |sigma N - TailBlockFun.sigma_trunc (Q X) N| = |SigmaTailReindexFun.sigmaTail (Q X) N| := by
    simpa [hdiff]
  have htail :
      |SigmaTailReindexFun.sigmaTail (Q X) N| ≤ (K_tail : ℝ) / (Q X : ℝ) := by
    exact
      SigmaTailTenorAxiomsFun.sigmaTail_bound_on_window (Q := Q) (K_tail := K_tail) hK hX hN hQ
  -- Turn the uniform bound into the old `* F_block` shape by using `1 ≤ F_block N`.
  have hN0 : N ≠ 0 := by
    have hXpos : 0 < X := lt_of_lt_of_le (by
      exact Nat.pos_of_ne_zero (by norm_num [Goldbach.BankParams.X0])) hX
    have hXN : X ≤ N := by
      rcases Finset.mem_filter.mp hN with ⟨hIn, _hEven⟩
      rcases Finset.mem_image.mp hIn with ⟨k, _hk, hkEq⟩
      subst hkEq
      exact Nat.le_add_right X k
    exact Nat.ne_of_gt (lt_of_lt_of_le hXpos hXN)
  have hF_ge_one : (1 : ℝ) ≤ TailBlockFun.F_block N := by
    have hEq :=
      Goldbach.Cert.FBlockConventional.F_block_eq_nat_div_totient (N := N) hN0
    have hφpos : 0 < Nat.totient N := Nat.totient_pos.2 (Nat.pos_of_ne_zero hN0)
    have hφle : Nat.totient N ≤ N := Nat.totient_le N
    have hpos : (0 : ℝ) < (Nat.totient N : ℝ) := by exact_mod_cast hφpos
    have hle : (Nat.totient N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hφle
    have hone_div : (1 : ℝ) / (N : ℝ) ≤ (1 : ℝ) / (Nat.totient N : ℝ) := by
      simpa using (one_div_le_one_div_of_le hpos hle)
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hone_div hNnonneg
    have hratio : (1 : ℝ) ≤ (N : ℝ) / (Nat.totient N : ℝ) := by
      -- simplify `N * (1/N) ≤ N * (1/φ(N))`
      simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using hmul
    simpa [hEq] using hratio
  have hcoef_nonneg : 0 ≤ (K_tail : ℝ) / (Q X : ℝ) := by
    have hQnonneg : 0 ≤ (Q X : ℝ) := by exact_mod_cast (Nat.zero_le (Q X))
    -- We don't assume `K_tail ≥ 0` globally here; use `K_tail_canon_nonneg` and `hK`.
    have hKnonneg : 0 ≤ (K_tail : ℝ) :=
      le_trans SigmaTailTenorAxiomsFun.K_tail_canon_nonneg hK
    exact div_nonneg hKnonneg hQnonneg
  have hscale :
      (K_tail : ℝ) / (Q X : ℝ) ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N := by
    -- multiply `1 ≤ F_block N` by the nonnegative coefficient
    simpa [one_mul] using (mul_le_mul_of_nonneg_left hF_ge_one hcoef_nonneg)
  have htail' :
      |SigmaTailReindexFun.sigmaTail (Q X) N|
        ≤ (K_tail : ℝ) / (Q X : ℝ) * TailBlockFun.F_block N :=
    le_trans htail hscale
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
  (K_tail_canon_le : SigmaTailTenorAxiomsFun.K_tail_canon ≤ K_tail)
  TailBlockFun.Model :=
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
        (hsigma := hsigma) hX hN hQ K_tail_canon_le)

end EntryPointTenorFun

end AO_OffDiag
end Goldbach
