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
import Twin.LedgerExtra

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

namespace DesmoothBound

variable {P}

/-- Trivial desmoothing budget: taking `eds = 0` satisfies the `/3` window bound. -/
theorem fromZero (P : Params) : DesmoothBound P (fun _ => (0 : ℝ)) := by
  classical
  refine ⟨?_⟩
  intro X hX
  have hLHS : Twin.Ledger.windowSum X P.H (fun _ => (0 : ℝ)) = 0 := by
    unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
    simp
  have eps_nonneg : 0 ≤ P.eps := P.eps_nonneg
  have ss_nonneg : 0 ≤ Twin.truncSingularSeries P.S :=
    Twin.truncSingularSeries_nonneg_of_ge_three (S := P.S) P.S_ge_three
  have hH_nonneg : 0 ≤ (P.H + 1 : ℝ) := by exact_mod_cast Nat.zero_le (P.H + 1)
  have hRHS_nonneg :
      0 ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) / 3 := by
    have : 0 ≤ P.eps * Twin.truncSingularSeries P.S * (P.H + 1) :=
      mul_nonneg (mul_nonneg eps_nonneg ss_nonneg) hH_nonneg
    exact div_nonneg this (by norm_num)
  simpa [hLHS] using hRHS_nonneg

end DesmoothBound
/-- Pinned gate inequality, pointwise in `k ≤ H`, *uniform in* `X ≥ X0`. -/

structure GatePointwise (emin eds : ℕ → ℝ) : Prop where
  bound :
    ∀ ⦃X k⦄, P.X0 ≤ X → k ≤ P.H →
      (1 - P.eps) * Twin.truncSingularSeries P.S
        ≤ Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
          + emin (X + k) + eds (X + k)
          + (P.eps * Twin.truncSingularSeries P.S) / 3

/-- Pinned gate inequality, in *window-sum* form:
`(1-ε)·SS·(H+1)` is bounded above by the localized twin mass plus the windowed
error contributions (minor arcs, desmoothing, and the uniform tail cap). -/
structure GateOnWindow (emin eds : ℕ → ℝ) : Prop where
  bound :
    ∀ ⦃X⦄, P.X0 ≤ X →
      (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds
          + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3

namespace GateOnWindow

variable {P}

/-- Sum the pointwise pinned gate inequality over `k=0..H` to obtain the
window-sum gate inequality. -/
theorem of_pointwise {emin eds : ℕ → ℝ}
  (h : GatePointwise P emin eds) :
  GateOnWindow P emin eds := by
  classical
  refine ⟨?_⟩
  intro X hX
  -- abbreviations
  set SS : ℝ := Twin.truncSingularSeries P.S
  set cap : ℝ := (P.eps * SS) / 3
  set S : Finset ℕ := Finset.range (P.H + 1)

  have hsum :
      S.sum (fun k => (1 - P.eps) * SS)
        ≤ S.sum (fun k =>
            Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
            + emin (X + k) + eds (X + k) + cap) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.mp hk
      exact Nat.lt_succ_iff.mp this
    simpa [SS, cap] using (h.bound (X := X) (k := k) hX hk_le)

  -- rewrite the LHS as `(H+1) * ((1-ε)·SS)`
  have hLHS :
      S.sum (fun _ => (1 - P.eps) * SS)
        = ((P.H : ℝ) + 1) * ((1 - P.eps) * SS) := by
    simp [S, Nat.cast_add, Nat.cast_one]

  -- rewrite the RHS in terms of `localizedTwinMass` and `windowSum`
  have hMass :
      S.sum (fun k => Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k))
        = Twin.Bridge.localizedTwinMass X P.H := by
    simp [Twin.Bridge.localizedTwinMass, S]

  have hEmin :
      S.sum (fun k => emin (X + k)) = Twin.Ledger.windowSum X P.H emin := by
    simp [Twin.Ledger.windowSum, Twin.Ledger.windowSumN, S]

  have hEds :
      S.sum (fun k => eds (X + k)) = Twin.Ledger.windowSum X P.H eds := by
    simp [Twin.Ledger.windowSum, Twin.Ledger.windowSumN, S]

  have hCap :
      S.sum (fun _ => cap) = ((P.H : ℝ) + 1) * cap := by
    simp [S, Nat.cast_add, Nat.cast_one, cap]

  have hRHS :
      S.sum (fun k =>
          Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
          + emin (X + k) + eds (X + k) + cap)
        =
        Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds
          + ((P.H : ℝ) + 1) * cap := by
    -- expand the sum of additions and rewrite each component
    simp [S, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm, hMass, hEmin, hEds, hCap]

  -- finish by rewriting both sides of `hsum`
  have hsum' :
      ((P.H : ℝ) + 1) * ((1 - P.eps) * SS)
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds
          + ((P.H : ℝ) + 1) * cap := by
    simpa [hLHS, hRHS] using hsum

  -- rewrite `((H+1) * cap)` into the canonical `(eps*SS) * (H+1) / 3` form
  -- and commute to match the target.
  simpa [cap, SS, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv,
    add_assoc, add_comm, add_left_comm] using hsum'

end GateOnWindow

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
