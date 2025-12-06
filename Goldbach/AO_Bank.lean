/-
  Goldbach/AO_Bank.lean

  Algebraic step only: turn an absolute-deviation control
      |(R N) - M N| ≤ ε * S
  into the one-sided bank–projection lower bound
      (R N) ≥ M N - ε * S.

  The absolute deviation comes from `Goldbach/BankPieces.lean`.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.BankPieces   -- provides the analytic leaf

namespace Goldbach.AO_Bank

open Real
open Goldbach
open Goldbach.Windows
open Goldbach.Rep

/-- From `|x - y| ≤ t` we get the lower one-sided bound `x ≥ y - t`. -/
lemma lower_from_absdev {x y t : ℝ}
    (h : |x - y| ≤ t) : x ≥ y - t := by
  have h₁ : -t ≤ x - y := (abs_le.mp h).1
  -- add `y` to both sides
  have := add_le_add_right h₁ y     -- y + (-t) ≤ x
  simpa [sub_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm

/-- From `|x - y| ≤ t` we also get `x ≤ y + t`. (Not used by the bridge, but handy.) -/
lemma upper_from_absdev {x y t : ℝ}
    (h : |x - y| ≤ t) : x ≤ y + t := by
  have h₂ : x - y ≤ t := (abs_le.mp h).2
  have := add_le_add_right h₂ y
  simpa [sub_eq, add_comm, add_left_comm, add_assoc] using this

/-- **Bank lower bound** from the Tenor absolute deviation leaf. -/
theorem bank_projection_lb
  {X0 H : ℕ} {S ε : ℝ} (M : ℕ → ℝ) :
  ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
    (R N : ℝ) ≥ M N - ε * S := by
  intro X N hX hN
  have h := Goldbach.BankPieces.bank_abs_deviation
              (X0:=X0) (H:=H) (S:=S) (ε:=ε) (M:=M) (X:=X) (N:=N) hX hN
  simpa using lower_from_absdev (x := (R N : ℝ)) (y := M N) (t := ε * S) h

/-- (Optional) the matching *upper* bank bound, derived algebraically. -/
theorem bank_projection_ub
  {X0 H : ℕ} {S ε : ℝ} (M : ℕ → ℝ) :
  ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
    (R N : ℝ) ≤ M N + ε * S := by
  intro X N hX hN
  have h := Goldbach.BankPieces.bank_abs_deviation
              (X0:=X0) (H:=H) (S:=S) (ε:=ε) (M:=M) (X:=X) (N:=N) hX hN
  simpa using upper_from_absdev (x := (R N : ℝ)) (y := M N) (t := ε * S) h

end Goldbach.AO_Bank
