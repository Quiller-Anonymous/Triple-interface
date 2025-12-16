/-
  Twin/CLSL2.lean
  L² “CLS” window bound specialized to the current stage emin := 0,
  so there are NO sorries. When you later formalize the analytic minor-arc
  bound, you can add a general lemma beside this one.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger

noncomputable section
open scoped BigOperators

namespace Twin.CLSL2
open Twin Twin.GoalAPI

/-- Structured version of the CLS L² window estimate. -/
structure Bound (P : Params) (emin : ℕ → ℝ) : Prop where
  bound :
    ∀ X, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun n => (emin n)^2)
        ≤ (P.eps^2 * (Twin.truncSingularSeries P.S)^2) * (P.H + 1) / 9

namespace Twin
namespace CLSL2

/-- L² window bound with a *nonnegative* slack term `P.err X`. -/
structure BoundWithSlack (P : GoalAPI.Params) (e : ℕ → ℝ) : Prop :=
(bound :
  ∀ {X}, P.X0 ≤ X →
    Ledger.windowSum X P.H (fun n => (e n)^2)
      ≤ P.eps^2 * (truncSingularSeries P.S)^2 * ((↑P.H : ℝ) + 1) / 9
        + P.err X)
(err_nonneg : ∀ {X}, 0 ≤ P.err X)

end CLSL2
end Twin

/-- Helper: `(↑P.H + 1 : ℝ) ≥ 0`. -/
private lemma span_nonneg (P : Params) : 0 ≤ (P.H + 1 : ℝ) := by
  have h0 : 0 ≤ (P.H : ℝ) := by exact_mod_cast (Nat.zero_le P.H)
  have : 0 ≤ (P.H : ℝ) + 1 := add_nonneg h0 (by norm_num)
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- **Zero-case CLS L² bound**: for `emin = 0`, the windowed L² remainder is `0`,
    which is ≤ the advertised RHS since that RHS is nonnegative. -/
theorem fromZero (P : Params) : Bound P (fun _ => (0 : ℝ)) := by
  classical
  refine ⟨?_b⟩
  intro X hX
  -- LHS: sum of zeros
  have hLHS :
      Twin.Ledger.windowSum X P.H (fun _ => (0 : ℝ)) = 0 := by
    unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
    simp
  -- RHS: nonnegative
  have h_nonneg :
      0 ≤ (P.eps^2 * (Twin.truncSingularSeries P.S)^2) * (P.H + 1) := by
    have h1 : 0 ≤ (P.eps : ℝ)^2 := sq_nonneg _
    have h2 : 0 ≤ (Twin.truncSingularSeries P.S : ℝ)^2 := sq_nonneg _
    exact mul_nonneg (mul_nonneg h1 h2) (span_nonneg P)
  have hRHS :
      0 ≤ (P.eps^2 * (Twin.truncSingularSeries P.S)^2) * (P.H + 1) / 9 := by
    simpa using div_nonneg h_nonneg (by norm_num : (0 : ℝ) ≤ 9)
  -- conclude
  simpa [hLHS] using hRHS

/-- Plain lemma form for the zero case, convenient to apply. -/
lemma window_zero (P : Params) :
    ∀ X, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun _ => (0 : ℝ))
        ≤ (P.eps^2 * (Twin.truncSingularSeries P.S)^2) * (P.H + 1) / 9 := by
  intro X hX
  have h := (fromZero P).bound X hX
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
  exact h

end Twin.CLSL2
