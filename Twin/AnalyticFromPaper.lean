import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger
import Twin.AnalyticCore
import Twin.CLSFromL2
import Twin.MajorArcPin
import Twin.MajorArc.Pin
import Twin.MajorArc.SWUniform
import Twin.SW.Defs

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

/-- CLS bound obtained from the zero-case L² estimate. -/
theorem cls_bound : Twin.AnalyticCore.CLSBound P emin := by
  -- `emin = 0`, so re-use the zero L² bound from `Twin.CLSL2`.
  have hL2 : Twin.CLSL2.Bound P emin := by
    simpa [emin] using Twin.CLSL2.fromZero (P := P)
  exact Twin.CLSFromL2.toCLS (P := P) (e := emin) hL2


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

/-- Gate inequality obtained *from inputs*: CLS, desmoothing, and a smooth
major-arc estimate.  This has the "baseline-conditional" shape that we
eventually want, but for now it still delegates to the pinned major-arc
axiom via `Twin.MajorArc.gate_pointwise_of_SME_CLS`. -/
theorem gate_pointwise_of_SME
  {A B : ℝ} {Λ : ℕ → ℝ} {W Ŵ : ℝ → ℝ}
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W Ŵ)
  (spec : Twin.MajorArc.GateSpec P) :
  AnalyticCore.GatePointwise P emin eds :=
by
  -- Currently we ignore the extra hypotheses and transparently use the
  -- pinned gate axiom.  The statement is ready for a future honest proof.
  simpa using
    Twin.MajorArc.gate_pointwise_of_SME_CLS
      (P := P) (emin := emin) (eds := eds)
      (hCLS := cls_bound) (hDesm := desmooth_bound)
      sme spec

/-- Legacy wrapper: the concrete `gate_pointwise` used by the bricks
instance.  For now this still calls the pinned axiom directly, so the
logical strength of the project is unchanged.  Once a real SW-based proof
of `gate_pointwise_of_SME` is available, this definition is the natural
place to switch it over. -/
@[inline] def gate_pointwise :
    AnalyticCore.GatePointwise P emin eds :=
  Twin.MajorArcPin.gate_pointwise P emin eds

end Twin.AnalyticFromPaper
