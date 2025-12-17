-- Twin/SW/NewUniform.lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Topology.Algebra.InfiniteSum
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Totient

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-- Additive character `e(t) = exp(2π i t)`. -/
@[simp] def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- Smoothed Λ-model exponential sum with our fixed conventions. -/
def sumValue (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H : ℝ) (α : ℝ) : ℂ :=
  ∑' n : ℕ,
    Complex.ofReal (Λ n * W ((n.toReal - X) / H))
    * Complex.exp (2 * Real.pi * Complex.I * (α * n))

/-- Ramanujan factor μ(q)/φ(q) as a real number. -/
@[simp] def muOverPhi (q : ℕ) : ℝ :=
  ((Nat.moebius q : ℤ).toReal) / (Nat.totient q : ℝ)

/-- Major-arc main term with fixed normalization. -/
def mainTerm (W_hat : ℝ → ℝ) (X H α : ℝ) (a q : ℕ) : ℂ :=
  Complex.ofReal (muOverPhi q)
  * Complex.exp (2 * Real.pi * Complex.I * ((α - (a : ℝ)/q) * X))
  * Complex.ofReal (X * W_hat (H * (α - (a : ℝ)/q)))

end Twin.SW
