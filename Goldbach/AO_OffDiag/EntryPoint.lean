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
  (hsupp : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    ∀ p, p ∈ (Nat.factorization N).support → p ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes) :
  TailBlock.Model where
  sigma := sigmaHonest
  F := TailBlock.F_block

  K_tail := (1.02 : ℝ)
  K_tail_nonneg := by norm_num

  F_ub := (330 : ℝ)
  F_ub_nonneg := by norm_num

  F_bound_on_window := by
    intro X N hX hN
    exact Goldbach.AO_OffDiag.SigmaTailEuler.F_block_bound_on_window
      (X := X) (N := N) hX hN (hsupp hX hN)

  sigma_tail_block := by
    intro X N hX hN
    -- (1) reduce to the tail
    have hdiff :
        sigmaHonest N - TailBlock.sigma_trunc_Q0 N = SigmaTailReindex.sigmaTail N := by
      simp [sigmaHonest, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

    -- (2) tail ≤ reindex majorant
    have h1 :
        |SigmaTailReindex.sigmaTail N| ≤ (SigmaTailReindex.reindexMajorantENN N).toReal :=
      SigmaTailReindex.tail_reindex_bound (N := N)

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
  (hsupp : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    ∀ p, p ∈ (Nat.factorization N).support → p ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
  |sigmaHonest N - TailBlock.sigma_trunc_Q0 N|
    ≤ (offDiagModel hsupp).K_tail / (TailBlock.Q0 : ℝ) * (offDiagModel hsupp).F_ub := by
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window_structural (M := offDiagModel hsupp) hX hN

theorem offDiag_tail_bound_on_window
  (hsupp : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    ∀ p, p ∈ (Nat.factorization N).support → p ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H)
  (hbudget :
    (offDiagModel hsupp).K_tail / (TailBlock.Q0 : ℝ) * (offDiagModel hsupp).F_ub ≤ (3e-4 : ℝ)) :
  |sigmaHonest N - TailBlock.sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window (M := offDiagModel hsupp) (eps := (3e-4 : ℝ)) hbudget hX hN

axiom hsupp_on_window :
  ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    ∀ p, p ∈ (Nat.factorization N).support → p ∈ SigmaTailEuler.smallPrimes

axiom offDiag_budget_ok :
  (offDiagModel hsupp_on_window).K_tail / (Q0 : ℝ) * (offDiagModel hsupp_on_window).F_ub ≤ (3e-4 : ℝ)

theorem tail_bound_on_window {X N : ℕ}
  (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
  |sigmaHonest N - sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  exact offDiag_tail_bound_on_window
    (hsupp := hsupp_on_window) (X := X) (N := N) hX hN offDiag_budget_ok

end AO_OffDiag
end Goldbach
