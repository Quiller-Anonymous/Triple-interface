/-
  Goldbach/BankPieces.lean

  Analytic leaf for the bank–projection control in the absolute-deviation form:
      |(R N) - M N| ≤ ε * S     on N ∈ EvenIn X H.

  We also derive the one-sided lower bound
      R N ≥ M N - ε * S
  which is the shape the bridge uses.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.Rep

namespace Goldbach.BankPieces

open Real
open Goldbach
open Goldbach.Windows
open Goldbach.Rep

/-- **Tenor bank–projection absolute deviation** (BG/TFA leaf).
    Replace this axiom with your full BG/TFA proof when ready. -/
axiom bank_abs_deviation
  {X0 H : ℕ} {S ε : ℝ} (M : ℕ → ℝ) :
  ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
    |(R N : ℝ) - M N| ≤ ε * S

/-- From `|R − M| ≤ εS` we get the one-sided lower bound `R ≥ M − εS`. -/
lemma bank_lower
  {X0 H : ℕ} {S ε : ℝ} (M : ℕ → ℝ) :
  ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
    (R N : ℝ) ≥ M N - ε * S := by
  intro X N hX hN
  have h := bank_abs_deviation (X0:=X0) (H:=H) (S:=S) (ε:=ε) M (X:=X) (N:=N) hX hN
  -- |R - M| ≤ εS  ⇒  -(εS) ≤ (R - M)
  have h_left : -(ε * S) ≤ (R N : ℝ) - M N := (abs_le.mp h).1
  -- add M N to both sides; RHS simplifies to R N
  have h' := add_le_add_right h_left (M N)
  -- tidy both sides
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'

/-- Optional symmetric upper bound: `M ≤ R + εS`. -/
lemma bank_upper
  {X0 H : ℕ} {S ε : ℝ} (M : ℕ → ℝ) :
  ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
    M N ≤ (R N : ℝ) + ε * S := by
  intro X N hX hN
  -- start from the absolute-deviation bound
  have h := bank_abs_deviation (X0:=X0) (H:=H) (S:=S) (ε:=ε) M (X:=X) (N:=N) hX hN
  -- use the *left* half:  -(εS) ≤ (R - M)
  have h_left : -(ε * S) ≤ (R N : ℝ) - M N := (abs_le.mp h).1
  -- add M to both sides:  M - εS ≤ R
  have h1 := add_le_add_right h_left (M N)
  have h2 : M N - ε * S ≤ (R N : ℝ) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
  -- add εS to both sides:  M ≤ R + εS
  have h3 := add_le_add_right h2 (ε * S)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h3

end Goldbach.BankPieces
