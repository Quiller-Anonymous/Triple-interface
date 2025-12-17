import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.Compat

namespace Goldbach.BankPieces

open Real
open Goldbach
open Goldbach.Windows
open Goldbach.Rep
open scoped BigOperators
open Goldbach.Compat

class BankAbsDeviation (X0 H : ℕ) (S ε : ℝ) (M : ℕ → ℝ) : Prop :=
  (bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H → |(R N : ℝ) - M N| ≤ ε * S)
/--
`lower_bound` no longer depends on a specific lemma name.
It takes `absDeviation` as an argument: any proof that for each
`X, N` in the window we have `|R N - M N| ≤ ε * S`.
-/
lemma lower_bound
    (X0 H : ℕ) (S ε : ℝ) (M R : ℕ → ℝ)
    (absDeviation :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
        |(R N : ℝ) - M N| ≤ ε * S) :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
      M N ≤ (R N : ℝ) + ε * S := by
  intro X N hX hN
  -- start from the absolute-deviation bound provided by the caller
  have h := absDeviation hX hN
  -- use the left half of `abs_le`:  -(ε*S) ≤ (R - M)
  have h_left : -(ε * S) ≤ (R N : ℝ) - M N := (abs_le.mp h).1
  -- add M to both sides:  M - εS ≤ R
  have h1 := add_le_add_right h_left (M N)
  have h2 : M N - ε * S ≤ (R N : ℝ) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
  -- add εS to both sides:  M ≤ R + εS
  have h3 := add_le_add_right h2 (ε * S)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h3

/-- From `|R − M| ≤ εS` we get the one-sided lower bound `R ≥ M − εS`. -/
lemma bank_lower
  {X0 H : ℕ} {S ε : ℝ} (M : ℕ → ℝ)
  [BankAbsDeviation X0 H S ε M] :
  ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
    (R N : ℝ) ≥ M N - ε * S := by
  intro X N hX hN
  -- pull the absolute-deviation bound from the typeclass:
  have h := (BankAbsDeviation.bound (X0:=X0) (H:=H) (S:=S) (ε:=ε) (M:=M) (X:=X) (N:=N) hX hN)
  -- |R - M| ≤ εS  ⇒  -(εS) ≤ (R - M)
  have h_left : -(ε * S) ≤ (R N : ℝ) - M N := (abs_le.mp h).1
  -- add M N to both sides; RHS simplifies to R N
  have h' := add_le_add_right h_left (M N)
  -- tidy both sides
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

/-- Symmetric upper bound: from `|R − M| ≤ εS` we get `M ≤ R + εS`. -/
lemma bank_upper
  {X0 H : ℕ} {S ε : ℝ} (M : ℕ → ℝ)
  [BankAbsDeviation X0 H S ε M] :
  ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
    M N ≤ (R N : ℝ) + ε * S := by
  intro X N hX hN
  -- absolute-deviation bound, again via the typeclass:
  have h := (BankAbsDeviation.bound (X0:=X0) (H:=H) (S:=S) (ε:=ε) (M:=M) (X:=X) (N:=N) hX hN)
  -- use the left half:  -(εS) ≤ (R - M)
  have h_left : -(ε * S) ≤ (R N : ℝ) - M N := (abs_le.mp h).1
  -- add M to both sides:  M - εS ≤ R
  have h1 := add_le_add_right h_left (M N)
  have h2 : M N - ε * S ≤ (R N : ℝ) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
  -- add εS to both sides:  M ≤ R + εS
  have h3 := add_le_add_right h2 (ε * S)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h3

end Goldbach.BankPieces
