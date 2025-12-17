import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger
import Twin.AnalyticCore
import Twin.CLSFromL2
import Twin.MajorArcPin  -- <-- add this import

noncomputable section
open scoped BigOperators

namespace Twin.AnalyticFromPaper
open Twin Twin.GoalAPI

/-- Concrete parameters from the paper. -/
def P : Params := Twin.PaperParams.P

/-- Banked minor-arc remainder (placeholder; fill later). -/
def emin : ℕ → ℝ := fun _ => 0

/-- Desmoothing / prime-power correction (placeholder; fill later). -/
def eds  : ℕ → ℝ := fun _ => 0

/-- CLS from an L² hypothesis (thin wrapper so we can keep the math modular). -/
theorem cls_bound : Twin.AnalyticCore.CLSBound P emin := by
 have hL2 : Twin.CLSFromL2.Bound P emin := /* your Kuznetsov+CLS L² bound (paper §12–§13) */
 exact Twin.CLSFromL2.toCLS_withSlack_fromL2 hL2


/-- Desmoothing/prime-power budget from §4: window sum of `eds` ≤ (eps·SS)·(H+1)/3. -/
theorem desmooth_bound : Twin.AnalyticCore.DesmoothBound P eds := by
  classical
  intro X hX
  -- with eds = 0, LHS is 0
  have hzero : Twin.Ledger.windowSum X P.H eds = 0 := by
    unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
    simp [eds]

  -- use Params fields
  have h_eps_nonneg : 0 ≤ (P.eps : ℝ) := le_of_lt P.eps_pos
  have hS_ge3 : ∀ p ∈ P.S, 3 ≤ p := P.S_ge_three   -- ← PASTE THIS LINE HERE

  -- SS ≥ 0 via strict positivity from S ≥ 3
  have hSS_nonneg : 0 ≤ Twin.truncSingularSeries P.S := by
    exact le_of_lt (Twin.truncSingularSeries_pos_of_all_ge_three (S := P.S) hS_ge3)

  -- (H+1) ≥ 0
  have h_H_nonneg : 0 ≤ (P.H + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le P.H)

  -- RHS ≥ 0, so 0 ≤ RHS
  have rhs_nonneg :
      0 ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) / 3 := by
    have : 0 ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) :=
      mul_nonneg (mul_nonneg h_eps_nonneg hSS_nonneg) h_H_nonneg
    simpa using div_nonneg this (by norm_num : (0 : ℝ) ≤ 3)

  simpa [hzero] using rhs_nonneg

@[inline] def gate_pointwise_cert
  (P : GoalAPI.Params) (emin eds : ℕ → ℝ) :
  AnalyticCore.GatePointwise P emin eds :=
  Twin.MajorArcPin.gateCert P emin eds

end Twin.AnalyticFromPaper
