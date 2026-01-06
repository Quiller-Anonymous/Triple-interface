import Goldbach.CompleteTenorFunX
import Goldbach.Cert.LogBounds
import Goldbach.AO_MajorSwapTenorAxiomsFunX

/-!
Canonical “parallel FunX” budget hypotheses.

This file is meant to be the *paper-facing* checklist for the remaining analytic inputs needed to
run the FunX (variable-`Q`) parallel track end-to-end without additional user-supplied hypotheses.

At the moment these are still explicit assumptions; the intention is to replace them by:
1) a proved/numerically-checked bound for `ε < cAO(caps Hoff)`, and
2) a proved/numerically-checked window budget bound `hBudget`.
-/

namespace Goldbach

open Goldbach.Windows

namespace ParallelFunXCanon

/-- The canonical FunX off-diagonal package (already wired in `TenorHypFunX_Canon`). -/
noncomputable abbrev Hoff : Goldbach.AO_OffDiag.TenorHypFunX.OffDiagHyp :=
  Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff

/-- The canonical closure constant for this instantiation (`σ₀ − δAO`). -/
noncomputable abbrev c0 : ℝ :=
  Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)

/-- Remaining numerical hypotheses for the canonical FunX parallel track. -/
class BudgetHyp : Prop where
  /-- Major-arc swap bound on the window (feeds `δAO_gap_bound`). -/
  innerSwap : Goldbach.ParallelTenorFunX.InnerSwapOnWindow
  /-- `ε < c0` for the canonical instantiation. -/
  eps_lt_c0 : (0.01 : ℝ) < c0
  /-- Global window budget used by `CompleteTenorFunX`. -/
  budget :
    ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ EvenIn X (10_000 : ℕ) →
      Goldbach.BG_Calib.δbridge_canon
        + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
        + @Goldbach.ParallelTenorFunX.δAO_gap_bound innerSwap Hoff ≤ (0.01 : ℝ)

/-!
We treat the *major-arc swap bound* as the remaining hard analytic input for the FunX track.

The rest of the `BudgetHyp` package is intended to be routine numerical bookkeeping once:
- the Mellin truncation model is calibrated, and
- basic numeric bounds on `Real.log X0` are in place.
-/

-- Remaining hard analytic input (paper-facing): inner swap bound on the window.
-- This is provided by a conventional major-arc axiom in `Goldbach/AO_MajorSwapTenorAxiomsFunX.lean`.
noncomputable def instInnerSwapOnWindow : Goldbach.ParallelTenorFunX.InnerSwapOnWindow :=
  by infer_instance

namespace Budget

open scoped BigOperators
open Real

private lemma logX0_nonneg : 0 ≤ Real.log (Goldbach.BankParams.X0 : ℝ) := by
  have : (1 : ℝ) ≤ (Goldbach.BankParams.X0 : ℝ) := by
    exact_mod_cast (by decide : (1 : ℕ) ≤ Goldbach.BankParams.X0)
  exact Real.log_nonneg this

private lemma δ_mellin_canon_le : Goldbach.AO_MellinTrunc.δ_mellin_canon ≤ (1176 : ℝ) / 10 ^ 6 := by
  -- δ_mellin = (2/eps^2)*(C_K/T) = 6*(log X0)^2 / 1e6, and log X0 ≤ 14
  have hlog : Real.log (Goldbach.BankParams.X0 : ℝ) ≤ 14 := Goldbach.Cert.log_X0_le
  have hlog0 : 0 ≤ Real.log (Goldbach.BankParams.X0 : ℝ) := logX0_nonneg
  have hsq : (Real.log (Goldbach.BankParams.X0 : ℝ)) ^ 2 ≤ (14 : ℝ) ^ 2 := by
    -- square is monotone on `ℝ≥0`
    nlinarith [hlog, hlog0]
  -- unfold δ_mellin_canon and bound each factor
  have : Goldbach.AO_MellinTrunc.δ_mellin_canon
      = (6 : ℝ) * (Real.log (Goldbach.BankParams.X0 : ℝ)) ^ 2 / (10 ^ 6 : ℝ) := by
    -- Expand and simplify the definition (everything is definitional).
    simp [Goldbach.AO_MellinTrunc.δ_mellin_canon, Goldbach.AO_MellinTrunc.eps_canon,
      Goldbach.AO_MellinTrunc.C_K_canon, Goldbach.AO_MellinTrunc.T_canon, Goldbach.BankParams.X0,
      div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm]
    ring
  -- apply the square bound
  rw [this]
  have h6 : 0 ≤ (6 : ℝ) := by norm_num
  have hden : 0 < (10 ^ 6 : ℝ) := by norm_num
  have hden' : 0 ≤ (10 ^ 6 : ℝ) := le_of_lt hden
  have hmul : (6 : ℝ) * (Real.log (Goldbach.BankParams.X0 : ℝ)) ^ 2
      ≤ (6 : ℝ) * (14 : ℝ) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hsq h6
  have hdiv :
      ((6 : ℝ) * (Real.log (Goldbach.BankParams.X0 : ℝ)) ^ 2) / (10 ^ 6 : ℝ)
        ≤ ((6 : ℝ) * (14 : ℝ) ^ 2) / (10 ^ 6 : ℝ) := by
    exact div_le_div_of_nonneg_right hmul hden'
  -- final numeric simplification: 6*14^2 = 1176
  have : ((6 : ℝ) * (14 : ℝ) ^ 2) / (10 ^ 6 : ℝ) = (1176 : ℝ) / 10 ^ 6 := by
    norm_num
  exact le_trans hdiv (by simpa [this])

end Budget

-- Canonical numeric budget package (derived from the log bound axiom + bookkeeping).
private lemma c0_def :
    c0
      = Goldbach.AO_SigmaPos.sigma0
          - Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
  simp [c0, Goldbach.AO_Major.cAO]

private lemma sigma0_eq : Goldbach.AO_SigmaPos.sigma0 = (0.05 : ℝ) := by
  -- sigma0 is δAO(sigma_caps)+c0, and sigma_caps has all deltas = 0.
  simp [Goldbach.AO_SigmaPos.sigma0, Goldbach.AO_SigmaModel.sigma0, Goldbach.AO_SigmaModel.c0,
    Goldbach.AO_SigmaModel.sigma_caps, Goldbach.AO_AssembleEnvelope.δAO]

private lemma δAO_canon_le :
    Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) ≤ (23 : ℝ) / 10 ^ 4 := by
  -- Expand δAO and caps; bound the Mellin term using the log bound axiom.
  have hδm : Goldbach.AO_MellinTrunc.δ_mellin_canon ≤ (1176 : ℝ) / 10 ^ 6 :=
    Budget.δ_mellin_canon_le
  -- `Hoff.eps = 3e-4` for the canonical record
  have heps : Hoff.eps = (3e-4 : ℝ) := by
    -- unfold the canonical record
    simp [Hoff, Goldbach.AO_OffDiag.TenorHypFunX.Canon.Hoff, Goldbach.AO_OffDiag.TenorHypFunX.Canon.eps]
  -- Closed-form value for the tail constant
  have htail : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  -- Kernel cap term is tiny
  have hkernel :
      ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed ≤ (1 : ℝ) / 10 ^ 6 := by
    -- This is a pure numeric inequality once `C_tail_closed` is rewritten.
    -- `norm_num` is robust here because everything is rational.
    have :
        ((1252 : ℝ) / 10 ^ 6) * ((99 : ℝ) / 1020100) ≤ (1 : ℝ) / 10 ^ 6 := by
      norm_num
    simpa [htail] using this

  -- Now expand δAO(caps Hoff) and bound termwise.
  have hδ :
      Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
        =
        (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.AO_MellinTrunc.δ_mellin_canon
          + (0.0008 : ℝ)
          + Hoff.eps := by
    simp [Goldbach.AO_AssembleEnvelope.δAO, Goldbach.AO_InstantiateTenorFunX.caps, heps,
      Goldbach.AO_MellinTrunc.δ_mellin_canon, Goldbach.AO_MellinTrunc.eps_canon,
      Goldbach.AO_MellinTrunc.C_K_canon, Goldbach.AO_MellinTrunc.T_canon]

  -- Finish with numeric arithmetic (all remaining constants are rational).
  rw [hδ]
  nlinarith [hkernel, hδm, heps]

theorem eps_lt_c0_canon : (0.01 : ℝ) < c0 := by
  -- c0 = 0.05 - δAO, and δAO ≤ 0.0023.
  have hδ : Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) ≤ (23 : ℝ) / 10 ^ 4 :=
    δAO_canon_le
  have hc0 : c0 = (0.05 : ℝ) - Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
    simp [c0_def, sigma0_eq, sub_eq_add_neg]
  -- now finish numerically
  nlinarith [hc0, hδ]

theorem budget_canon :
    ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ EvenIn X (10_000 : ℕ) →
      Goldbach.BG_Calib.δbridge_canon
        + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
        + @Goldbach.ParallelTenorFunX.δAO_gap_bound instInnerSwapOnWindow Hoff ≤ (0.01 : ℝ) := by
  intro X N hX hN
  -- bound payload_cap by the window numeric cap
  have hcap : Goldbach.BG_Bank.payload_cap X N ≤ (1252 : ℝ) / 10 ^ 6 := by
    simpa [Goldbach.BG_Bank.X0, Goldbach.BG_Bank.H, Goldbach.BankParams.X0, Goldbach.BankParams.H] using
      (Goldbach.BG_Bank.payload_cap_window_num (X := X) (N := N) hX hN)
  have htail : Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by nlinarith [htail]
  have htailterm :
      Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed
        ≤ ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed :=
    mul_le_mul_of_nonneg_right hcap htail_nonneg

  -- bound δAO(caps Hoff) and hence δAO_gap_bound
  have hδAO : Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) ≤ (23 : ℝ) / 10 ^ 4 :=
    δAO_canon_le

  have hgap :
      @Goldbach.ParallelTenorFunX.δAO_gap_bound instInnerSwapOnWindow Hoff
        ≤ Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
          + Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
    -- by definition
    simp [Goldbach.ParallelTenorFunX.δAO_gap_bound]

  -- numeric evaluation of the remaining rational constants
  have hbridge_num : Goldbach.BG_Calib.δbridge_canon ≤ (389 : ℝ) / 10 ^ 5 := by
    -- δbridge_canon is a rational expression in H and Ucut
    norm_num [Goldbach.BG_Calib.δbridge_canon, Goldbach.BG_Calib.Mswap_canon, Goldbach.BG_Calib.Cpp_canon,
      Goldbach.BG_Calib.ρ_canon, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  have hswap_num :
      Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon ≤ (3565 : ℝ) / 10 ^ 6 := by
    -- δ_major_canon is definitionally the canonical major-arc swap cap.
    simpa [Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon] using
      (by
        norm_num [Goldbach.BG_Calib.Mswap_canon, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H] :
          ((2 * (Goldbach.BankParams.H : ℝ) + 1) / (Goldbach.BG_Identity.Ucut : ℝ)) * Goldbach.BG_Calib.Mswap_canon
            ≤ (3565 : ℝ) / 10 ^ 6)
  have htail_num : ((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed ≤ (2 : ℝ) / 10 ^ 6 := by
    -- very crude but sufficient
    nlinarith [htail]

  -- assemble
  have :=
    calc
      Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + @Goldbach.ParallelTenorFunX.δAO_gap_bound instInnerSwapOnWindow Hoff
          ≤ Goldbach.BG_Calib.δbridge_canon
              + (((1252 : ℝ) / 10 ^ 6) * Goldbach.BG_Identity.C_tail_closed)
              + (Goldbach.AO_AssembleEnvelope.δAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff)
                  + Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon) := by
                nlinarith [htailterm, hgap]
      _ ≤ (389 : ℝ) / 10 ^ 5 + (2 : ℝ) / 10 ^ 6 + ((23 : ℝ) / 10 ^ 4 + (3565 : ℝ) / 10 ^ 6) := by
            nlinarith [hbridge_num, htail_num, hδAO, hswap_num]
      _ ≤ (0.01 : ℝ) := by norm_num
  exact this

instance instBudgetHyp : BudgetHyp where
  innerSwap := instInnerSwapOnWindow
  eps_lt_c0 := eps_lt_c0_canon
  budget := by
    intro X N hX hN
    simpa using budget_canon (X := X) (N := N) hX hN

/-- Canonical FunX track, with the remaining numeric hypotheses packaged as a single assumption. -/
theorem goldbach_from_tenorFunX_fun_auto
    [Goldbach.BG_Calib.WeightsBridgeHyp]
    (hBase : FiniteBaseUpTo 1_000_000) :
    ∀ n, Even n → 4 ≤ n → GoldbachRep n := by
  classical
  haveI : BudgetHyp := instBudgetHyp
  haveI : Goldbach.ParallelTenorFunX.InnerSwapOnWindow := BudgetHyp.innerSwap
  have hεlt : (0.01 : ℝ) < Goldbach.AO_Major.cAO (Goldbach.AO_InstantiateTenorFunX.caps Hoff) := by
    simpa [c0] using (BudgetHyp.eps_lt_c0)
  have hBudget :
      ∀ {X N : ℕ}, (1_000_000 : ℕ) ≤ X → N ∈ EvenIn X (10_000 : ℕ) →
        Goldbach.BG_Calib.δbridge_canon
          + (Goldbach.BG_Bank.payload_cap X N * Goldbach.BG_Identity.C_tail_closed)
          + Goldbach.ParallelTenorFunX.δAO_gap_bound (Hoff := Hoff) ≤ (0.01 : ℝ) := by
    intro X N hX hN
    -- use the budget field, which was stated with the explicit `innerSwap` instance argument
    exact (BudgetHyp.budget (X := X) (N := N) hX hN)
  exact Goldbach.goldbach_from_tenorFunX_fun_autoHoff
    (hεlt := hεlt) (hBudget := by intro X N hX hN; exact hBudget hX hN) (hBase := hBase)

end ParallelFunXCanon

end Goldbach
