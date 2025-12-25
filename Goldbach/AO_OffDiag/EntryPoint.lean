import Mathlib
import Goldbach.AO_Core
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailEuler
import Goldbach.AO_OffDiag.SigmaTailReindex

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows
open TailBlock

/--
AO_OffDiag entry point (honest): build a `TailBlock.Model` assuming a prime-support hypothesis
for `N` (needed to bound `F_block` by the certified constant `330`).

This avoids claiming that `EvenIn X H` alone implies a uniform bound for `F_block`.
-/
noncomputable def offDiagModel
  (hsupp : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    ∀ p, p ∈ (Nat.factorization N).support → p ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes) :
  TailBlock.Model where
  sigma := Goldbach.AO_Core.sigma
  F := TailBlock.F_block

  -- Tail constant placeholder (will be replaced in Steps 2–4 by Euler/reindex analysis)
  K_tail := (1.02 : ℝ)
  K_tail_nonneg := by norm_num

  -- Window bound constant for `F_block` under `hsupp`
  F_ub := (330 : ℝ)
  F_ub_nonneg := by norm_num

  F_bound_on_window := by
    intro X N hX hN
    -- Use Step 1 lemma from SigmaTailEuler with the supplied support hypothesis.
    exact Goldbach.AO_OffDiag.SigmaTailEuler.F_block_bound_on_window
      (X := X) (N := N) hX hN (hsupp hX hN)

  sigma_tail_block := by
    intro X N hX hN
    -- This is where the reindex/Euler tail analysis (Steps 2–4) goes.
    -- Ultimately: prove `|sigma - trunc| ≤ (K_tail/Q0) * F_block`.
    sorry

/-- Structural tail bound on the canonical window, for the constructed model. -/
theorem offDiag_tail_bound_on_window_structural
  (hsupp : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    ∀ p, p ∈ (Nat.factorization N).support → p ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
  |Goldbach.AO_Core.sigma N - TailBlock.sigma_trunc_Q0 N|
    ≤ (offDiagModel hsupp).K_tail / (TailBlock.Q0 : ℝ) * (offDiagModel hsupp).F_ub := by
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window_structural (M := offDiagModel hsupp) hX hN

/--
Numeric tail bound on the canonical window, for the constructed model, assuming an explicit budget.
-/
theorem offDiag_tail_bound_on_window
  (hsupp : ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
    ∀ p, p ∈ (Nat.factorization N).support → p ∈ Goldbach.AO_OffDiag.SigmaTailEuler.smallPrimes)
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H)
  (hbudget :
    (offDiagModel hsupp).K_tail / (TailBlock.Q0 : ℝ) * (offDiagModel hsupp).F_ub ≤ (3e-4 : ℝ)) :
  |Goldbach.AO_Core.sigma N - TailBlock.sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  simpa [offDiagModel] using
    TailBlock.tail_bound_on_window (M := offDiagModel hsupp) (eps := (3e-4 : ℝ)) hbudget hX hN

end AO_OffDiag
end Goldbach
