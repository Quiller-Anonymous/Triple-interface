/-
  Twin/Rep.lean
  Representation notion: a twin prime pair (p, p+2) with p in a given window.
-/
import Mathlib
import Twin.Windows

open Twin.Windows

namespace Twin

/-- `TwinPairAt p` means `p` and `p+2` are both prime. -/
def TwinPairAt (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Existence of a twin pair with the first prime inside the window `[X, X+H]`. -/
def ExistsTwinInWindow (X H : ℕ) : Prop :=
  ∃ p : ℕ, InWindow X H p ∧ TwinPairAt p

end Twin
