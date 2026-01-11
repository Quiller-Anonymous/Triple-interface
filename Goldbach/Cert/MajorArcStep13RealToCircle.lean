import Goldbach.Cert.MajorArcStep12ShiftedExpSums
import Goldbach.Cert.MajorArcStep2ExpSums

/-!
Major arcs (Step 13, sigma-agnostic): connect real frequencies (`e`, `gExp`) to circle characters.

Steps 2–6 are phrased using the real additive character
`e(x) = exp(2π i x)` and the weight `gExp β n = e(β * n)`.

Steps 7–12 introduce Fourier analysis on `AddCircle 1`, where the corresponding characters are
`fourier (T := 1) k : AddCircle 1 → ℂ`.

This file records the compatibility on embedded reals: for `x : ℝ`,
`fourier k (x : AddCircle 1) = e(k*x)`. As a consequence, the circle exponential sum `expSum` from
Step 12 agrees with the usual real-frequency exponential sum when evaluated at `(x : AddCircle 1)`.
-/

namespace Goldbach.Cert
namespace MajorArcStep13RealToCircle

open scoped BigOperators

open Complex AddCircle

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral

noncomputable section

lemma fourier_coe_eq_e (k : ℤ) (x : ℝ) :
    (fourier (T := (1 : ℝ)) k (x : UC) : ℂ) = e ((k : ℝ) * x) := by
  -- Unfold both sides to the explicit exponential formulas.
  have hf :
      (fourier (T := (1 : ℝ)) k (x : UC) : ℂ)
        =
      Complex.exp (2 * Real.pi * Complex.I * k * x / (1 : ℝ)) := by
    simpa using (fourier_coe_apply (T := (1 : ℝ)) (n := k) (x := x))
  -- Normalize `/ 1` and reorder factors to match `e`.
  -- `e y = exp(I * (2πy))`.
  simp [MajorArcExponential.e, hf, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma expSum_coe_eq_sum_gExp (X N : ℕ) (x : ℝ) :
    expSum X N (x : UC)
      =
    ∑ n ∈ s N, aTerm X n * MajorArcStep2ExpSums.gExp x n := by
  classical
  unfold expSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  -- Convert `fourier (n:ℤ) (x:UC)` to `e ((n:ℝ)*x)` and then to `gExp x n = e (x*(n:ℝ))`.
  have hfour : (fourier (T := (1 : ℝ)) (n : ℤ) (x : UC) : ℂ) = e ((n : ℝ) * x) :=
    fourier_coe_eq_e (k := (n : ℤ)) (x := x)
  -- `gExp x n = e (x * (n:ℝ))`; commute the real multiplication.
  simp [MajorArcStep2ExpSums.gExp, hfour, mul_comm, mul_left_comm, mul_assoc]

end

end MajorArcStep13RealToCircle
end Goldbach.Cert

