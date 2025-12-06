-- Goldbach/FiniteBase.lean
import Mathlib
import Goldbach.Windows

namespace Goldbach.FiniteBase

/-- Certificate that every even `N` in `[4, X₀]` has a Goldbach decomposition. -/
def Cert (X₀ : ℕ) :=
  ∀ ⦃N : ℕ⦄, Goldbach.Windows.IsEven N → 4 ≤ N → N ≤ X₀ →
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

-- Keep this commented if you want true finite-conditional status:
-- axiom finiteBaseAxiom (X₀ : ℕ) : Cert X₀

end Goldbach.FiniteBase
