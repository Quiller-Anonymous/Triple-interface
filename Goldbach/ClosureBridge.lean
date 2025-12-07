import Mathlib
import Goldbach.Rep
import Goldbach.Windows
import Goldbach.AnalyticPointwise
import Goldbach.Base.FiniteBaseDefs

-- If Lean can't find `le_div_iff`, uncomment the next line:
-- import Mathlib.Algebra.Order.Field

open Nat Goldbach.Rep Goldbach.Windows Goldbach.Base Goldbach.Analytic

namespace Goldbach.Bridge

/-- Pointwise closure over the even window `[X, X+H]`. -/
def ClosurePointwise (X H : ℕ) (S c0 ε : ℝ) : Prop :=
  (0 < S) ∧ (0 < c0) ∧ (ε < c0) ∧
  ∀ {N}, N ∈ EvenIn X H → ((R N : ℝ) / S) ≥ c0 - ε

lemma closurePointwise_to_rep
  {X H : ℕ} {S c0 ε : ℝ}
  (h : ClosurePointwise X H S c0 ε) :
  ∀ {N}, N ∈ EvenIn X H →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hN
  rcases h with ⟨hSpos, hc0pos, hεlt, hpt⟩
  have bound' : c0 - ε ≤ (R N : ℝ) / S := by simpa using hpt hN

  -- Multiply both sides by S ≥ 0, then simplify ((a / S) * S) = a using S ≠ 0.
  have lower : (c0 - ε) * S ≤ (R N : ℝ) := by
    have hSnonneg : 0 ≤ S := le_of_lt hSpos
    have t := mul_le_mul_of_nonneg_right bound' hSnonneg
    have hSne : S ≠ 0 := ne_of_gt hSpos
    -- t : (c0 - ε) * S ≤ ((R N : ℝ) / S) * S
    -- simplify RHS:
    simpa [div_mul_eq_mul_div, hSne] using t

  have posConst : 0 < c0 - ε := sub_pos.mpr hεlt
  have hRposℝ : 0 < (R N : ℝ) := lt_of_lt_of_le (mul_pos posConst hSpos) lower
  have hRne : R N ≠ 0 := by
    intro h0; have : (R N : ℝ) = 0 := by simpa [h0]
    exact (ne_of_gt hRposℝ) this
  have hRpos : 0 < R N := Nat.pos_of_ne_zero hRne
  exact (R_pos_iff_exists_pair (N:=N)).1 hRpos

/-- Global version: pointwise closure holds for all `X ≥ X₀`. -/
def GlobalClosurePointwise (X₀ H : ℕ) (S c0 ε : ℝ) : Prop :=
  ∀ ⦃X⦄, X₀ ≤ X → ClosurePointwise X H S c0 ε

/-- Finite base (either an axiom or a checked certificate). -/
def FiniteBase (X₀ : ℕ) : Prop :=
  ∀ ⦃N⦄, IsEven N → 4 ≤ N → N ≤ X₀ →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- Final bridge (conditional): finite base + global pointwise window closure ⇒ Goldbach. -/
theorem goldbach_from_global_pointwise
  {X₀ H : ℕ} {S c0 ε : ℝ}
  (finiteBase : FiniteBase X₀)
  (gclosure : GlobalClosurePointwise X₀ H S c0 ε) :
  ∀ ⦃N⦄, IsEven N → 4 ≤ N →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hEven h4
  by_cases hN : N ≤ X₀
  · exact finiteBase hEven h4 hN
  ·
    have hXN : X₀ ≤ N := le_of_not_ge hN
    have hpt := gclosure (X:=N) hXN
    have : N ∈ EvenIn N H := Goldbach.Windows.mem_EvenIn_self hEven
    exact closurePointwise_to_rep hpt this

theorem goldbach_conditional
    (w : Goldbach.Analytic.PointwiseWitness) :
    ∀ {N : ℕ}, Nat.Even N → w.X0 ≤ N → GoldbachRep N :=
by
  intro N hEven hge
  -- use the bridge lemma directly from the Bridge namespace:
  exact Goldbach.Bridge.pointwise_to_rep (X0 := w.X0) (H := w.H)
    (S := w.S) (c0 := w.c0) (ε := w.ε)
    w.global hEven hge

namespace Goldbach.Bridge
  export Goldbach.ClosureBridge (pointwise_to_rep)
end Goldbach.Bridge

end Goldbach.Bridge
