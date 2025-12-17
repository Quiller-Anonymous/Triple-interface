-- Twin/SW/Defs.lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log

open scoped BigOperators

namespace Twin.SW

/-- Additive character: e(t) = exp(2π i t). -/
@[inline] def χ_add (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * t)

/-- Smoothed prime exponential sum centered at `X` with scale `H` and phase `α`. -/
def sumValue (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H α : ℝ) : ℂ :=
  ∑' n : ℕ,
    Complex.ofReal (Λ n * W ((n.toReal - X) / H)) * χ_add (α * n)

/-- Major-arc main term near `a/q` with `(a,q)=1`.  Here `Ŵ` is the
Fourier transform of `W`, normalized so that `Ŵ(0) = ∫ W`. -/
def mainTerm (Ŵ : ℝ → ℝ) (X H α : ℝ) (a q : ℕ) : ℂ :=
  let coeff : ℝ := (Nat.mobius q : ℤ).toReal / (Nat.totient q : ℝ)
  Complex.ofReal coeff
  * χ_add ((α - (a : ℝ)/q) * X)
  * Complex.ofReal (X * Ŵ (H * (α - (a : ℝ)/q)))

/-- Uniform smoothed major-arc estimate at scale `H` for the model
`Λ, W, Ŵ`.  For fixed `A,B>0`, this records a polylogarithmic major-arc
box, a starting point `X0`, and a global constant `C` such that, on all
major arcs `|α - a/q| ≤ δ/(H+1)` with `1 ≤ q ≤ (log X)^B`, the
smoothed exponential sum is within `≪ C · X/(log X)^A` of its expected
main term. -/
structure SmoothMajorArcEstimate
  (A B : ℝ) (Λ : ℕ → ℝ) (W Ŵ : ℝ → ℝ) : Prop :=
  (δ   : ℝ)
  (δ_pos : 0 < δ)
  (X0  : ℝ)
  (C   : ℝ)
  (bound :
    ∀ {X H : ℝ}, X0 ≤ X → 1 ≤ H →
    ∀ {q a : ℕ}, 1 ≤ q → (q : ℝ) ≤ (Real.log X)^B → Nat.Coprime a q →
    ∀ {α : ℝ}, |α - (a : ℝ)/q| ≤ δ / (H + 1) →
      Complex.abs
        (sumValue Λ W X H α
          - mainTerm Ŵ X H α a q)
        ≤ C * (X / (Real.log X)^A))

end Twin.SW
