/-
  Twin/Windows.lean
  Minimal window utilities for twin primes; independent of Goldbach.Windows.
-/
import Mathlib

namespace Twin.Windows

/-- `InWindow X H n` means `n` lies in the short window `[X, X+H]`. -/
def InWindow (X H n : ℕ) : Prop := X ≤ n ∧ n ≤ X + H

@[simp] lemma inWindow_self {X H : ℕ} : InWindow X H X := by
  exact And.intro le_rfl (Nat.le_add_right _ _)

/-- Convenience constructor. -/
lemma of_mem_of_le {X H n : ℕ} (hX : X ≤ n) (hn : n ≤ X + H) :
    InWindow X H n := And.intro hX hn

end Twin.Windows
