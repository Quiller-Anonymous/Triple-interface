import Mathlib
import Goldbach.Rep
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs
-- DO NOT import any Goldbach.Analytic* module here

open Nat
open Goldbach
open Goldbach.Windows   -- IsEven, EvenIn, mem_EvenIn_self
open Goldbach.Base      -- GoldbachRep / FiniteBaseUpTo
open Goldbach.Rep

namespace Goldbach.Bridge

/--
Scale-dependent pointwise closure over the even window `[X, X + H(X)]`.

This is the “parallel” interface meant to match Tenor’s main-text regime where the bandwidth
`H` is allowed to vary with scale `X`.
-/
def ClosurePointwiseFun (X : ℕ) (H : ℕ → ℕ) (S c0 ε : ℝ) : Prop :=
  (0 < S) ∧ (0 < c0) ∧ (ε < c0) ∧
  ∀ {N}, N ∈ EvenIn X (H X) → ((R N : ℝ) / S) ≥ c0 - ε

lemma closurePointwiseFun_to_rep
  {X : ℕ} {H : ℕ → ℕ} {S c0 ε : ℝ}
  (h : ClosurePointwiseFun X H S c0 ε) :
  ∀ {N}, N ∈ EvenIn X (H X) →
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
    simpa [div_mul_eq_mul_div, hSne] using t

  have posConst : 0 < c0 - ε := sub_pos.mpr hεlt
  have hRposℝ : 0 < (R N : ℝ) := lt_of_lt_of_le (mul_pos posConst hSpos) lower
  have hRne : R N ≠ 0 := by
    intro h0
    have : (R N : ℝ) = 0 := by simp [h0]
    exact (ne_of_gt hRposℝ) this
  have hRpos : 0 < R N := Nat.pos_of_ne_zero hRne
  exact (R_pos_iff_exists_pair (N := N)).1 hRpos

/-- Scale-dependent global version: for every `X ≥ X₀`, closure holds on window width `H(X)`. -/
def GlobalClosurePointwiseFun (X₀ : ℕ) (H : ℕ → ℕ) (S c0 ε : ℝ) : Prop :=
  ∀ ⦃X⦄, X₀ ≤ X → ClosurePointwiseFun X H S c0 ε

/--
Final bridge (conditional, scale-dependent):
finite base up to `X₀` + global closure with varying window widths ⇒ Goldbach.
-/
theorem goldbach_from_global_pointwise_fun
  {X₀ : ℕ} {H : ℕ → ℕ} {S c0 ε : ℝ}
  (finiteBase : Goldbach.Base.FiniteBaseUpTo X₀)
  (gclosure : GlobalClosurePointwiseFun X₀ H S c0 ε) :
  ∀ ⦃N⦄, IsEven N → 4 ≤ N →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hEven h4
  by_cases hN : N ≤ X₀
  · exact finiteBase (Goldbach.Windows.even_of_isEven hEven) h4 hN
  ·
    have hXN : X₀ ≤ N := le_of_not_ge hN
    have hpt := gclosure (X := N) hXN
    have : N ∈ EvenIn N (H N) := Goldbach.Windows.mem_EvenIn_self hEven
    exact closurePointwiseFun_to_rep (X := N) (H := H) hpt this

end Goldbach.Bridge
