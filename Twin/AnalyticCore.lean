/-
  Twin/AnalyticCore.lean
  Minimal interfaces for the three analytic facts used by the pipeline.
-/
import Mathlib
import Twin.GoalAPI
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger

noncomputable section
open scoped BigOperators

namespace Twin.AnalyticCore
open Twin Twin.GoalAPI

variable (P : Params)

/-- CLS (Type II) bound on the banked minor-arcs, *uniform in shift*. -/
structure CLSBound (emin : ℕ → ℝ) : Prop where
  bound :
    ∀ ⦃X⦄, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun n => |emin n|)
        ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) / 3

/-- Desmoothing / prime-power budget, *uniform in shift*. -/
structure DesmoothBound (eds : ℕ → ℝ) : Prop where
  bound :
    ∀ ⦃X⦄, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H eds
        ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) / 3
/-- Pinned gate inequality, pointwise in `k ≤ H`, *uniform in* `X ≥ X0`. -/

structure GatePointwise (emin eds : ℕ → ℝ) : Prop where
  bound :
    ∀ ⦃X k⦄, P.X0 ≤ X → k ≤ P.H →
      (1 - P.eps) * Twin.truncSingularSeries P.S
        ≤ Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
          + emin (X + k) + eds (X + k)
          + (P.eps * Twin.truncSingularSeries P.S) / 3

namespace Twin
namespace AnalyticCore

structure CLSBoundWithSlack (P : GoalAPI.Params) (e : ℕ → ℝ) : Prop where
  bound :
    ∀ {X}, P.X0 ≤ X →
      Ledger.windowSum X P.H (fun n => |e n|)
        ≤ P.eps * truncSingularSeries P.S * ((↑P.H : ℝ) + 1) / 3
          + Real.sqrt ((↑P.H : ℝ) + 1) * Real.sqrt (P.err X)

/-- If the slack vanishes pointwise, the zero-slack CLS follows. -/
theorem CLS_of_withSlack_zero
  {P : GoalAPI.Params} {e : ℕ → ℝ}
  (h : CLSBoundWithSlack P e)
  (h0 : ∀ X, P.err X = 0) :
  CLSBound P e := by
  classical
  refine ⟨?_⟩
  intro X hX
  -- just re-associate the product to match the target shape
  simpa [h0 X, Real.sqrt_zero, add_comm, add_left_comm, add_assoc,
         mul_comm, mul_left_comm, mul_assoc]
    using (h.bound (X := X) hX)

end AnalyticCore
end Twin
