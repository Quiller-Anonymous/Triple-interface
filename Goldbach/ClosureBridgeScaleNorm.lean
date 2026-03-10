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
Scale-sensitive pointwise closure with variable normalization scale `S(X)`.

This is the next normalization-aware extension of `ClosurePointwiseScale`: both the closure margin
`c0` and the normalization scale `S` are allowed to vary with the scale parameter `X`.
-/
def ClosurePointwiseScaleNorm
    (X : ℕ) (H : ℕ → ℕ) (S c0 : ℕ → ℝ) (ε : ℝ) : Prop :=
  (0 < S X) ∧ (0 < c0 X) ∧ (ε < c0 X) ∧
  ∀ {N}, N ∈ EvenIn X (H X) → ((Goldbach.BG_Identity.R_bank X N) / (S X)) ≥ c0 X - ε

lemma closurePointwiseScaleNorm_to_rep
  {X : ℕ} {H : ℕ → ℕ} {S c0 : ℕ → ℝ} {ε : ℝ}
  (h : ClosurePointwiseScaleNorm X H S c0 ε) :
  ∀ {N}, N ∈ EvenIn X (H X) →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hN
  rcases h with ⟨hSpos, hc0pos, hεlt, hpt⟩
  have bound' : c0 X - ε ≤ (Goldbach.BG_Identity.R_bank X N) / (S X) := by
    simpa using hpt hN
  have lower : (c0 X - ε) * (S X) ≤ Goldbach.BG_Identity.R_bank X N := by
    have hSnonneg : 0 ≤ S X := le_of_lt hSpos
    have t := mul_le_mul_of_nonneg_right bound' hSnonneg
    have hSne : S X ≠ 0 := ne_of_gt hSpos
    simpa [div_mul_eq_mul_div, hSne] using t
  have posConst : 0 < c0 X - ε := sub_pos.mpr hεlt
  have hRpos : 0 < Goldbach.BG_Identity.R_bank X N :=
    lt_of_lt_of_le (mul_pos posConst hSpos) lower
  exact Goldbach.Bridge.closurePointwise_to_rep
    (X := X) (H := H X) (S := S X) (c0 := c0 X) (ε := ε)
    (by
      refine ⟨hSpos, hc0pos, hεlt, ?_⟩
      intro N hN
      simpa using (hpt (N := N) hN))
    (N := N) (by simpa using hN)

/-- Global variable-scale closure on all windows `X ≥ X₀`. -/
def GlobalClosurePointwiseScaleNorm
    (X₀ : ℕ) (H : ℕ → ℕ) (S c0 : ℕ → ℝ) (ε : ℝ) : Prop :=
  ∀ ⦃X⦄, X₀ ≤ X → ClosurePointwiseScaleNorm X H S c0 ε

/--
Final bridge for the variable-scale normalization route.
-/
theorem goldbach_from_global_pointwise_scaleNorm
  {X₀ : ℕ} {H : ℕ → ℕ} {S c0 : ℕ → ℝ} {ε : ℝ}
  (finiteBase : Goldbach.Base.FiniteBaseUpTo X₀)
  (gclosure : GlobalClosurePointwiseScaleNorm X₀ H S c0 ε) :
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
    exact closurePointwiseScaleNorm_to_rep (X := N) (H := H) hpt this

end Goldbach.Bridge

