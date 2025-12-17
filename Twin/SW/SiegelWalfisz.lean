-- Twin/SW/SiegelWalfisz.lean
import Twin.SW.Characters
import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.NumberTheory.ArithmeticFunction

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-- Dirichlet characters modulo `q` with complex values. -/
abbrev DirichletCharacter (q : ℕ) := _root_.DirichletCharacter ℂ q

/-- Twisted Chebyshev function `ψ(x, χ) = ∑_{n≤x} Λ(n) χ(n)`. -/
def twistedPsi {q : ℕ} (χ : DirichletCharacter q) (x : ℝ) : ℂ :=
  ∑ n in Finset.Icc 1 ⌊x⌋₊,
    (Complex.ofReal (Nat.vonMangoldt n)) * χ.evalNat n

/-- Uniform Siegel–Walfisz in the polylogarithmic range: for fixed `A,B > 0`,
and all `x ≥ 3`, uniformly for `1 ≤ q ≤ (log x)^B`, we have
`|ψ(x, χ)| ≪ x / (log x)^A` with an (ineffective) constant depending on `A,B`. -/
class SiegelWalfisz (A B : ℝ) : Prop :=
  (C : ℝ)
  (bound :
    ∀ ⦃x : ℝ⦄, 3 ≤ x →
    ∀ ⦃q : ℕ⦄, 1 ≤ q ∧ (q : ℝ) ≤ (Real.log x)^B →
    ∀ (χ : DirichletCharacter q),
      Complex.abs (twistedPsi χ x)
        ≤ C * x / (Real.log x)^A)

end Twin.SW
