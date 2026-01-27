-- Twin/SW/Defs.lean
import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Twin.SW

/-- Additive character: e(t) = exp(2π i t). -/
@[inline] def χ_add (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * t)

/-- Smoothed prime exponential sum centered at `X` with scale `H` and phase `α`. -/
def sumValue (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H α : ℝ) : ℂ :=
  ∑' n : ℕ,
    Complex.ofReal (Λ n * W (((n : ℝ) - X) / H)) * χ_add (α * (n : ℝ))

/-- Major-arc main term near `a/q` with `(a,q)=1`.  Here `W_hat` is the
Fourier transform of `W`, normalized so that `W_hat(0) = ∫ W`. -/
@[simp] def muOverPhi (q : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℝ) / (Nat.totient q : ℝ)

def mainTerm (W_hat : ℝ → ℝ) (X H α : ℝ) (a q : ℕ) : ℂ :=
  Complex.ofReal (muOverPhi q)
  * χ_add ((α - (a : ℝ) / q) * X)
  * Complex.ofReal (H * W_hat (H * (α - (a : ℝ) / q)))

/-- Uniform smoothed major-arc estimate at scale `H` for the model
`Λ, W, W_hat`.  For fixed `A,B>0`, this records a polylogarithmic major-arc
box, a starting point `X0`, and a global constant `C` such that, on all
    major arcs `|α - a/q| ≤ δ/(H+1)` with `1 ≤ q ≤ (log H)^B`, the
    smoothed exponential sum is within `≪ C · H/(log X)^A` of its expected
main term. -/
structure SmoothMajorArcEstimate
  (A B : ℝ) (Λ : ℕ → ℝ) (W W_hat : ℝ → ℝ) where
  δ   : ℝ
  δ_pos : 0 < δ
  X0  : ℝ
  C   : ℝ
  bound :
    ∀ {X H : ℝ}, X0 ≤ X → 1 ≤ H →
    ∀ {q a : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.rpow (Real.log H) B → Nat.Coprime a q →
    ∀ {α : ℝ}, |α - (a : ℝ)/q| ≤ δ / (H + 1) →
      ‖sumValue Λ W X H α - mainTerm W_hat X H α a q‖
        ≤ C * (H / Real.rpow (Real.log X) A)

end Twin.SW
