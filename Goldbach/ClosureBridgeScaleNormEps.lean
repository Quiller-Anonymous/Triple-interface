import Mathlib
import Goldbach.ClosureBridge
import Goldbach.BG_Identity
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs

open Nat
open Goldbach
open Goldbach.Windows
open Goldbach.Base
open scoped BigOperators

namespace Goldbach.Bridge

/--
Scale-sensitive pointwise closure with variable normalization scale `S(X)` and variable slack
`ε(X)`.

This is the third additive normalization route: the closure margin, normalization scale, and slack
are all allowed to vary with the outer scale parameter `X`.
-/
def ClosurePointwiseScaleNormEps
    (X : ℕ) (H : ℕ → ℕ) (S c0 eps : ℕ → ℝ) : Prop :=
  (0 < S X) ∧ (0 < c0 X) ∧ (eps X < c0 X) ∧
  ∀ {N}, N ∈ EvenIn X (H X) → ((Goldbach.BG_Identity.R_bank X N) / (S X)) ≥ c0 X - eps X

lemma closurePointwiseScaleNormEps_to_rep
  {X : ℕ} {H : ℕ → ℕ} {S c0 eps : ℕ → ℝ}
  (h : ClosurePointwiseScaleNormEps X H S c0 eps) :
  ∀ {N}, N ∈ EvenIn X (H X) →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hN
  rcases h with ⟨hSpos, hc0pos, hεlt, hpt⟩
  have bound' : c0 X - eps X ≤ (Goldbach.BG_Identity.R_bank X N) / (S X) := by
    simpa using hpt hN
  have lower : (c0 X - eps X) * (S X) ≤ Goldbach.BG_Identity.R_bank X N := by
    have hSnonneg : 0 ≤ S X := le_of_lt hSpos
    have t := mul_le_mul_of_nonneg_right bound' hSnonneg
    have hSne : S X ≠ 0 := ne_of_gt hSpos
    simpa [div_mul_eq_mul_div, hSne] using t
  have posConst : 0 < c0 X - eps X := sub_pos.mpr hεlt
  have hRpos : 0 < Goldbach.BG_Identity.R_bank X N :=
    lt_of_lt_of_le (mul_pos posConst hSpos) lower
  exact Goldbach.Bridge.closurePointwise_to_rep
    (X := X) (H := H X) (S := S X) (c0 := c0 X) (ε := eps X)
    (by
      refine ⟨hSpos, hc0pos, hεlt, ?_⟩
      intro N hN
      simpa using (hpt (N := N) hN))
    (N := N) (by simpa using hN)

/-- Global variable-scale closure with variable slack on all windows `X ≥ X₀`. -/
def GlobalClosurePointwiseScaleNormEps
    (X₀ : ℕ) (H : ℕ → ℕ) (S c0 eps : ℕ → ℝ) : Prop :=
  ∀ ⦃X⦄, X₀ ≤ X → ClosurePointwiseScaleNormEps X H S c0 eps

/-- Final bridge for the variable-scale, variable-slack normalization route. -/
theorem goldbach_from_global_pointwise_scaleNormEps
  {X₀ : ℕ} {H : ℕ → ℕ} {S c0 eps : ℕ → ℝ}
  (finiteBase : Goldbach.Base.FiniteBaseUpTo X₀)
  (gclosure : GlobalClosurePointwiseScaleNormEps X₀ H S c0 eps) :
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
    exact closurePointwiseScaleNormEps_to_rep (X := N) (H := H) hpt this

end Goldbach.Bridge
