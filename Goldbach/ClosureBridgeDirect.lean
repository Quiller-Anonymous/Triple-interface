import Mathlib
import Goldbach.ClosureBridge
import Goldbach.Windows
import Goldbach.Base.FiniteBaseDefs

open Nat
open Goldbach
open Goldbach.Windows
open Goldbach.Base
open scoped BigOperators

namespace Goldbach.Bridge

/--
Direct pointwise closure with no forced factorization `c0(X) * S(X)`.

This is intended as a replacement surface for the next normalization pass: the user supplies a
direct lower term `L(X)` and a direct additive gap `Δ(X)`, and closure only asks for positivity of
`L(X) - Δ(X)` together with a pointwise lower bound for `R_bank`.
-/
def ClosurePointwiseDirect
    (X : ℕ) (H : ℕ → ℕ) (L Δ : ℕ → ℝ) : Prop :=
  (0 ≤ Δ X) ∧ (0 < L X - Δ X) ∧
  ∀ {N}, N ∈ EvenIn X (H X) → Goldbach.BG_Identity.R_bank X N ≥ L X - Δ X

lemma closurePointwiseDirect_to_rep
  {X : ℕ} {H : ℕ → ℕ} {L Δ : ℕ → ℝ}
  (h : ClosurePointwiseDirect X H L Δ) :
  ∀ {N}, N ∈ EvenIn X (H X) →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N := by
  classical
  intro N hN
  rcases h with ⟨hΔnn, hgap, hpt⟩
  have hLpos : 0 < L X := by
    have hΔle : Δ X < L X := by
      simpa [sub_pos] using hgap
    exact lt_of_le_of_lt hΔnn hΔle
  have hcl : ClosurePointwise X (H X) (1 : ℝ) (L X) (Δ X) := by
    refine ⟨by norm_num, hLpos, ?_, ?_⟩
    · simpa [sub_pos] using hgap
    · intro n hn
      have hraw := hpt hn
      simpa using hraw
  exact closurePointwise_to_rep hcl (by simpa using hN)

/-- Global direct closure on all windows `X ≥ X₀`. -/
def GlobalClosurePointwiseDirect
    (X₀ : ℕ) (H : ℕ → ℕ) (L Δ : ℕ → ℝ) : Prop :=
  ∀ ⦃X⦄, X₀ ≤ X → ClosurePointwiseDirect X H L Δ

/-- Final bridge for the direct lower-term closure route. -/
theorem goldbach_from_global_pointwise_direct
  {X₀ : ℕ} {H : ℕ → ℕ} {L Δ : ℕ → ℝ}
  (finiteBase : Goldbach.Base.FiniteBaseUpTo X₀)
  (gclosure : GlobalClosurePointwiseDirect X₀ H L Δ) :
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
    exact closurePointwiseDirect_to_rep (X := N) (H := H) hpt this

end Goldbach.Bridge
