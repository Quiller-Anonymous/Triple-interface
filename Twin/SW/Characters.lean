import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-- Dirichlet characters modulo `q` with complex values. -/
abbrev DirichletCharacter (q : ℕ) := _root_.DirichletCharacter ℂ q

namespace DirichletCharacter

variable {q : ℕ}

/-- Evaluate a Dirichlet character on a natural number by reducing modulo `q`. -/
@[simp] def evalNat (χ : DirichletCharacter q) (n : ℕ) : ℂ := χ (n : ZMod q)

end DirichletCharacter

end Twin.SW
