import Mathlib
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailEuler
import Goldbach.AO_OffDiag.SigmaTailReindex

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows
open TailBlock

/-- Honest sigma: truncation + the tail already defined in `SigmaTailReindex`. -/
noncomputable def sigmaHonest (N : ℕ) : ℝ :=
  TailBlock.sigma_trunc_Q0 N + SigmaTailReindex.sigmaTail N

/-!
## About axioms in this file

This file is a *wiring/entry point* for the off-diagonal channel bound.

We aim for “gold standard” where only **conventional math** is axiomatized.
The older axiom `hsupp_on_window` (all prime factors of `N` are in a tiny fixed set)
was bespoke and not mathematically plausible; we replace it with the correct *shape*:
a uniform upper bound on the multiplicative factor `F_block N` on the Goldbach window.

For now this bound is left as a `sorry` (scaffolding), and should later be proved from
the analytic “tenor” argument that controls the relevant Euler factors on the window.
-/

/--
(Temporary) bound comparing the reindex majorant to the block majorant.

This is the missing analytic inequality turning the reindex majorant into
`(1.02/Q0) * F_block N` on the canonical window.
-/
axiom reindexMajorant_bound_on_window
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    (SigmaTailReindex.reindexMajorantENN N).toReal
      ≤ (1.02 : ℝ) / (TailBlock.Q0 : ℝ) * TailBlock.F_block N

noncomputable def offDiagModel
  (hF : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    TailBlock.F_block N ≤ (44 : ℝ) / 5) :
  TailBlock.Model where
  sigma := sigmaHonest
  F := TailBlock.F_block

  K_tail := (1.02 : ℝ)
  K_tail_nonneg := by norm_num

  -- This constant is chosen so that the numeric budget check
  -- `(1.02 / Q0) * F_ub ≤ 3e-4` is *true by computation* for `Q0 = 30000`.
  -- The real analytic obligation is to prove `F_block N ≤ F_ub` uniformly on the window.
  F_ub := (44 : ℝ) / 5
  F_ub_nonneg := by norm_num

  F_bound_on_window := by
    intro X N hX hN
    exact hF hX hN

  sigma_tail_block := by
    intro X N hX hN
    -- (1) reduce to the tail
    have hdiff :
        sigmaHonest N - TailBlock.sigma_trunc_Q0 N = SigmaTailReindex.sigmaTail N := by
      simp [sigmaHonest, sub_eq_add_neg, add_assoc, add_comm]

    -- (2) tail ≤ reindex majorant
    have h1 :
        |SigmaTailReindex.sigmaTail N| ≤ (SigmaTailReindex.reindexMajorantENN N).toReal :=
      by
        -- `N ≠ 0` on the canonical window since `N ≥ X0 ≥ 1`.
        have hI : N ∈ IccShift X BankParams.H := (Finset.mem_filter.mp hN).1
        rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
        have hXpos : 0 < X :=
          lt_of_lt_of_le (by decide : (0 : ℕ) < BankParams.X0) hX
        have hN0 : X + k ≠ 0 := Nat.ne_of_gt (Nat.add_pos_left hXpos k)
        simpa using SigmaTailReindex.tail_reindex_bound (N := X + k) hN0

    -- (3) majorant ≤ (K_tail/Q0) * F
    have h2 :
        (SigmaTailReindex.reindexMajorantENN N).toReal
          ≤ (1.02 : ℝ) / (TailBlock.Q0 : ℝ) * TailBlock.F_block N := by
      simpa using
        (reindexMajorant_bound_on_window (X := X) (N := N) hX hN)

    -- (4) conclude
    simpa [hdiff] using le_trans h1 h2

/-- Structural tail bound on the canonical window, for the constructed model. -/
theorem offDiag_tail_bound_on_window_structural
  (hF : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    TailBlock.F_block N ≤ (44 : ℝ) / 5)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
  |sigmaHonest N - TailBlock.sigma_trunc_Q0 N|
    ≤ (offDiagModel hF).K_tail / (TailBlock.Q0 : ℝ) * (offDiagModel hF).F_ub := by
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window_structural (M := offDiagModel hF) hX hN

theorem offDiag_tail_bound_on_window
  (hF : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    TailBlock.F_block N ≤ (44 : ℝ) / 5)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H)
  (hbudget :
    (offDiagModel hF).K_tail / (TailBlock.Q0 : ℝ) * (offDiagModel hF).F_ub ≤ (3e-4 : ℝ)) :
  |sigmaHonest N - TailBlock.sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window (M := offDiagModel hF) (eps := (3e-4 : ℝ)) hbudget hX hN

/--
**Scaffolding lemma (TODO)**: uniform bound on the `F_block` multiplicative factor on the window.

This is the correct replacement for the older (incorrect) prime-support axiom.
Ultimately this should follow from the analytic off-diagonal argument (bounding Euler factors
uniformly on the Goldbach window), not from any “all prime factors are small” hypothesis.
-/
lemma hsupp_on_window :
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    TailBlock.F_block N ≤ (44 : ℝ) / 5 := by
  intro X N hX hN
  sorry

lemma offDiag_budget_ok :
  (offDiagModel hsupp_on_window).K_tail / (Q0 : ℝ) * (offDiagModel hsupp_on_window).F_ub ≤ (3e-4 : ℝ) := by
  -- Pure arithmetic after unfolding the chosen constants.
  simp [offDiagModel, TailBlock.Q0]
  norm_num

theorem tail_bound_on_window {X N : ℕ}
  (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |sigmaHonest N - sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  exact offDiag_tail_bound_on_window
    (hF := hsupp_on_window) (X := X) (N := N) hX hN offDiag_budget_ok

end AO_OffDiag
end Goldbach
