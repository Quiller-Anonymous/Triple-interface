/-
  Twin/TargetsFromBricks.lean
  From the paper bricks to the GoalAPI targets.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperBricks
import Twin.SingularSeries
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger

noncomputable section

namespace Twin.TargetsFromBricks

open Twin
open Twin.GoalAPI
open Twin.PaperBricks

/-- Replace the `err` field of a Params record. -/
def withErr (P : Params) (err' : ℕ → ℝ) : Params := { P with err := err' }

/-- The error profile built from the bricks: |emin| + eds + constant tail cap. -/
def errFrom (P : Params) (b : Bricks P) : ℕ → ℝ :=
  fun n => (b.E.absEmin n) + (b.E.eds n) + (P.eps * truncSingularSeries P.S) / 3

/-- Pointwise spectral–null from the bricks (no window sums needed). -/
theorem spectralNull_from_bricks
  {P : Params} (b : Bricks P) :
  SpectralNullOnWindow (withErr P (errFrom P b)) := by
  intro X hX k hk
  -- Abbreviations to keep the algebra readable.
  set SS   : ℝ := truncSingularSeries P.S
  set J    : ℝ := Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
  set u    : ℝ := b.E.emin (X + k)
  set v    : ℝ := b.E.eds  (X + k)
  set cap  : ℝ := (P.eps * SS) / 3
  -- From the bricks: (1 - ε)·SS ≤ J + u + v + cap
  have h := b.gate_major_min (X := X) hX (k := k) hk
  -- Upgrade u to |u| on the RHS: u ≤ |u|
  have huu : u ≤ |u| := by
    simpa [u] using le_abs_self (b.E.emin (X + k))
  -- Add (v + cap) to both sides, then add J to both sides,
  -- and reassociate/commute to get: J + u + v + cap ≤ J + |u| + v + cap
  have hu' : J + u + v + cap ≤ J + |u| + v + cap := by
    have := add_le_add_right huu (v + cap)
    have := add_le_add_left this J
    simpa [add_assoc, add_comm, add_left_comm, J, u, v, cap] using this
  -- Transitivity: (1 - ε)·SS ≤ J + |u| + v + cap
  have hfinal : (1 - P.eps) * SS ≤ J + |u| + v + cap := le_trans h hu'
  -- Turn it into the desired "minus err ≤ J" form using `sub_le_iff_le_add`.
  have hgoal : (1 - P.eps) * SS - (|u| + v + cap) ≤ J := by
    have : J + |u| + v + cap = J + (|u| + v + cap) := by ring
    rw [this] at hfinal
    exact (sub_le_iff_le_add).2 hfinal
  -- Unfold definitions to match the GoalAPI statement.
  simpa [withErr, errFrom, ErrorPieces.absEmin,
         SS, J, u, v, cap,
         add_assoc, add_comm, add_left_comm] using hgoal

end Twin.TargetsFromBricks
