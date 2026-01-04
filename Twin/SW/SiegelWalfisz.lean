-- Twin/SW/SiegelWalfisz.lean
import Twin.SW.Characters
import Mathlib.Data.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.VonMangoldt

noncomputable section

namespace Twin.SW

/-- Twisted Chebyshev function `ψ(x, χ) = ∑_{n≤x} Λ(n) χ(n)`. -/
def twistedPsi {q : ℕ} (χ : DirichletCharacter q) (x : ℝ) : ℂ :=
  (Finset.Icc 1 ⌊x⌋₊).sum (fun n =>
    (Complex.ofReal (ArithmeticFunction.vonMangoldt n)) * χ.evalNat n)

/-- Uniform Siegel–Walfisz in the polylogarithmic range: for fixed `A,B > 0`,
and all `x ≥ 3`, uniformly for `1 ≤ q ≤ (log x)^B`, we have
`|ψ(x, χ)| ≪ x / (log x)^A` with an (ineffective) constant depending on `A,B`. -/
class SiegelWalfisz (A B : ℝ) where
  (C : ℝ)
  (bound :
    ∀ ⦃x : ℝ⦄, 3 ≤ x →
    ∀ ⦃q : ℕ⦄, 1 ≤ q ∧ (q : ℝ) ≤ Real.rpow (Real.log x) B →
    ∀ (χ : DirichletCharacter q),
      ‖twistedPsi χ x‖
        ≤ C * x / Real.rpow (Real.log x) A)

end Twin.SW
