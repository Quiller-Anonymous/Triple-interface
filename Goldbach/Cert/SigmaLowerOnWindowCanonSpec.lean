import Goldbach.AO_SigmaPos
import Goldbach.Cert.BpAltNonnegUpToQ0Cert
import Goldbach.Cert.SigmaTruncQ0_S2Reduction
import Goldbach.Cert.SigmaTruncQ0At2Cert

/-!
σ lower bound: canonical on-window certificate boundary (Option B).

For the FunX pipeline, downstream closure needs a uniform positive lower bound on the σ-model
`Goldbach.AO_SigmaModel.sigma` on the canonical window `X ≥ X0`, `N ∈ EvenIn X H`.

At “gold grade” this should be discharged by conventional arithmetic (positivity and an explicit
lower bound for the singular series in the repo’s normalization).  In this repo we now *discharge*
the needed bound via the global S2 route:

* `Goldbach/Cert/BpAltNonnegUpToQ0Cert.lean` supplies the (finite, Lean-checked) certificate input
  `BpAltNonnegUpToQ0`;
* `Goldbach/Cert/SigmaTruncQ0_S2Reduction.lean` turns that input into the global inequality
  `33/25 ≤ TailBlock.sigma_trunc_Q0 N` for all nonzero even `N`;
* this file scales the truncated-series bound into a lower bound for `AO_SigmaModel.sigma`.
-/

namespace Goldbach.Cert.SigmaLowerOnWindowCanonSpec

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.AO_OffDiag

noncomputable section

/-!
Option B: certify an explicit lower bound for the **truncated** singular series and then scale it
into the repo’s σ-model.
-/

-- A concrete lower bound for the truncated singular series on the canonical window.
-- (Use a rational `33/25` for `1.32` to keep proofs arithmetic-friendly.)
noncomputable def σmin_trunc_canon : ℝ := (33 : ℝ) / 25

-- Sanity: the chosen bound is (provably) below the coprime/parity-locus value `σ≤Q0(2)`.
-- This is **not** the global σ-lower bound; it just pins the numeric constant to an in-repo check.
private lemma sigma_trunc_Q0_two_ge_σmin_trunc_canon :
    σmin_trunc_canon ≤ TailBlock.sigma_trunc_Q0 2 := by
  simpa [σmin_trunc_canon] using
    (Goldbach.Cert.SigmaTruncQ0At2Cert.sigma_trunc_Q0_two_ge_33_25 :
      (33 : ℝ) / 25 ≤ TailBlock.sigma_trunc_Q0 2)

theorem sigma_trunc_lb_on_window_canon :
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      σmin_trunc_canon ≤ TailBlock.sigma_trunc_Q0 N := by
  intro X N hX hN
  -- Unpack evenness from the window definition.
  have hIsEven : Goldbach.Windows.IsEven N := (Finset.mem_filter.mp hN).2
  have hEven : Even N := Goldbach.Windows.even_of_isEven hIsEven
  -- `N` is positive because `N ∈ IccShift X H` and `X0 ≤ X`.
  have hIn : N ∈ Goldbach.Windows.IccShift X H := (Finset.mem_filter.mp hN).1
  have hXN : X ≤ N := by
    classical
    unfold Goldbach.Windows.IccShift at hIn
    rcases Finset.mem_image.mp hIn with ⟨k, _hk, rfl⟩
    exact Nat.le_add_right X k
  have hN0 : N ≠ 0 := by
    have hX0N : X0 ≤ N := le_trans hX hXN
    have hX0pos : 0 < X0 := by
      -- `X0 = 10^6` is a positive numeral (from `Goldbach.BankParams`).
      norm_num [Goldbach.BankParams.X0]
    exact ne_of_gt (lt_of_lt_of_le hX0pos hX0N)
  -- Apply the global S2 reduction (no window pinning).
  have hS2 :
      (33 : ℝ) / 25 ≤ TailBlock.sigma_trunc_Q0 N :=
    Goldbach.Cert.SigmaTruncQ0_S2Reduction.S2.sigma_trunc_Q0_ge_33_25_of_BpAltNonnegUpToQ0
      Goldbach.Cert.BpAltNonnegUpToQ0Cert.bpAltNonnegUpToQ0 hN0 hEven
  simpa [σmin_trunc_canon] using hS2

private lemma mass_even_pos : 0 < Goldbach.AO_SigmaModel.Canon.mass_even := by
  -- With canonical numerals (`H = 10000`), this is a positive rational.
  dsimp [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
    Goldbach.AO_SigmaModel.Canon.Ucut]
  norm_num [Goldbach.BankParams.H]

noncomputable def σmin_canon : ℝ :=
  (1 / 800 : ℝ) * Goldbach.AO_SigmaModel.Canon.mass_even * σmin_trunc_canon

private lemma σmin_canon_pos : 0 < σmin_canon := by
  have h1 : (0 : ℝ) < (1 / 800 : ℝ) := by norm_num
  have h2 : 0 < Goldbach.AO_SigmaModel.Canon.mass_even := mass_even_pos
  have h3 : 0 < σmin_trunc_canon := by
    dsimp [σmin_trunc_canon]
    norm_num
  dsimp [σmin_canon]
  nlinarith

instance sigmaLowerOnWindow_canon : Goldbach.AO_SigmaPos.SigmaLowerOnWindow where
  σmin := σmin_canon
  σmin_pos := σmin_canon_pos
  sigma_even_lb_on_window := by
    intro X N hX hN
    have htrunc :
        σmin_trunc_canon ≤ TailBlock.sigma_trunc_Q0 N :=
      sigma_trunc_lb_on_window_canon (X := X) (N := N) hX hN
    have hcoef_nonneg :
        0 ≤ (1 / 800 : ℝ) * Goldbach.AO_SigmaModel.Canon.mass_even := by
      have h1 : (0 : ℝ) ≤ (1 / 800 : ℝ) := by norm_num
      have h2 : 0 ≤ Goldbach.AO_SigmaModel.Canon.mass_even := le_of_lt mass_even_pos
      nlinarith
    -- Scale the truncation lower bound into the σ-model lower bound.
    have :
        σmin_canon ≤ Goldbach.AO_SigmaModel.sigma N := by
      -- `sigma N = coef * sigma_trunc_Q0 N` and `σmin_canon = coef * σmin_trunc_canon`.
      dsimp [Goldbach.AO_SigmaModel.sigma, σmin_canon]
      exact mul_le_mul_of_nonneg_left htrunc hcoef_nonneg
    simpa [Goldbach.AO_SigmaPos.sigma] using this

end

end Goldbach.Cert.SigmaLowerOnWindowCanonSpec
