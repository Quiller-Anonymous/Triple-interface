import Goldbach.Cert.MajorArcExponentialPrelude
import Mathlib.Analysis.Fourier.AddCircle

/-!
Major arcs (Step 7, sigma-agnostic): Fourier orthogonality on `AddCircle 1`.

To connect exponential sums to additive constraints (and eventually to correlation sums),
we need the basic identity that the normalized Haar integral of a nontrivial character is `0`.

Mathlib provides this most naturally via Fourier analysis on the additive circle `AddCircle T`.
Here we specialize to `T = 1`.
-/

namespace Goldbach.Cert
namespace MajorArcStep7FourierOrthogonality

open scoped Real
open scoped InnerProductSpace

open Complex MeasureTheory

noncomputable section

open AddCircle

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private abbrev UC : Type := AddCircle (1 : ℝ)

private abbrev μ : Measure UC := AddCircle.haarAddCircle (T := (1 : ℝ))

/-- Our character `e(x) = exp(2π i x)` agrees with `fourier 1` on `AddCircle 1`. -/
lemma e_eq_fourier_one (x : ℝ) :
    Goldbach.Cert.MajorArcExponential.e x = fourier (T := (1 : ℝ)) (1 : ℤ) (x : UC) := by
  -- Expand both sides and compare the explicit exponential formulas.
  unfold Goldbach.Cert.MajorArcExponential.e
  have hf :
      fourier (T := (1 : ℝ)) (1 : ℤ) (x : UC) =
        Complex.exp (2 * π * Complex.I * (1 : ℤ) * x / (1 : ℝ)) := by
    simpa using (fourier_coe_apply (T := (1 : ℝ)) (n := (1 : ℤ)) (x := x))
  -- simplify `(/1)` and the integer cast
  simpa [hf, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma integral_fourier_eq_zero {n : ℤ} (hn : n ≠ 0) :
    (∫ t : UC, (fourier (T := (1 : ℝ)) n t : ℂ) ∂μ) = 0 := by
  -- Use orthogonality of the Fourier monomials in `L²(AddCircle 1)`.
  have hn' : (-n : ℤ) ≠ 0 := neg_ne_zero.mpr hn
  have horth := (orthonormal_fourier (T := (1 : ℝ)))
  have hinner :
      ⟪fourierLp (T := (1 : ℝ)) (p := (2 : ℝ≥0∞)) (-n),
          fourierLp (T := (1 : ℝ)) (p := (2 : ℝ≥0∞)) (0 : ℤ)⟫_ℂ = 0 := by
    simpa [hn'] using horth (-n) (0 : ℤ)

  -- Unfold `fourierLp` to `toLp` and rewrite the `L²` inner product as an integral.
  have hinner' :
      ⟪toLp (E := ℂ) (p := (2 : ℝ≥0∞)) μ ℂ (fourier (T := (1 : ℝ)) (-n)),
          toLp (E := ℂ) (p := (2 : ℝ≥0∞)) μ ℂ (fourier (T := (1 : ℝ)) (0 : ℤ))⟫_ℂ = 0 := by
    simpa [fourierLp, μ] using hinner
  -- `ContinuousMap.inner_toLp` gives the integral formula for this inner product.
  rw [ContinuousMap.inner_toLp μ (fourier (T := (1 : ℝ)) (-n)) (fourier (T := (1 : ℝ)) (0 : ℤ))] at hinner'

  have hconj : ∀ t : UC,
      Complex.conj (fourier (T := (1 : ℝ)) (-n) t) = fourier (T := (1 : ℝ)) n t := by
    intro t
    have hneg :
        fourier (T := (1 : ℝ)) (-n) t = Complex.conj (fourier (T := (1 : ℝ)) n t) := by
      simpa using (fourier_neg (T := (1 : ℝ)) (n := n) (x := t))
    -- take conjugates
    simpa using congrArg Complex.conj hneg

  -- Simplify `fourier 0 = 1` and the conjugation identity.
  simpa [fourier_zero, hconj, μ] using hinner'

lemma integral_fourier (n : ℤ) :
    (∫ t : UC, (fourier (T := (1 : ℝ)) n t : ℂ) ∂μ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [μ, fourier_zero]
  · simpa [hn, integral_fourier_eq_zero (n := n) hn, μ]

end

end MajorArcStep7FourierOrthogonality
end Goldbach.Cert
