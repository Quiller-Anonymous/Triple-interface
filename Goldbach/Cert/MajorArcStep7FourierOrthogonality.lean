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
  -- Use orthogonality of the Fourier monomials in `L²(AddCircle 1)` (paired with `fourier 0 = 1`).
  have horth := (orthonormal_fourier (T := (1 : ℝ)))
  have h0n : (0 : ℤ) ≠ n := by
    simpa [eq_comm] using hn
  have hinner :
      inner (fourierLp (T := (1 : ℝ)) 2 (0 : ℤ)) (fourierLp (T := (1 : ℝ)) 2 n) = 0 := by
    simpa [h0n] using horth (0 : ℤ) n

  have hinner' :
      inner
          (toLp (E := ℂ) (p := (2 : ℝ≥0∞)) μ ℂ (fourier (T := (1 : ℝ)) (0 : ℤ)))
          (toLp (E := ℂ) (p := (2 : ℝ≥0∞)) μ ℂ (fourier (T := (1 : ℝ)) n)) = 0 := by
    simpa [AddCircle.fourierLp, μ] using hinner

  -- Rewrite the `L²` inner product as an integral and simplify.
  rw [ContinuousMap.inner_toLp μ (fourier (T := (1 : ℝ)) (0 : ℤ)) (fourier (T := (1 : ℝ)) n)] at hinner'
  simpa [fourier_zero, μ] using hinner'

lemma integral_fourier (n : ℤ) :
    (∫ t : UC, (fourier (T := (1 : ℝ)) n t : ℂ) ∂μ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [μ, fourier_zero]
  · simpa [hn, integral_fourier_eq_zero (n := n) hn, μ]

end

end MajorArcStep7FourierOrthogonality
end Goldbach.Cert
