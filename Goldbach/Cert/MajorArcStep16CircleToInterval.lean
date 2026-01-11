import Goldbach.Cert.MajorArcStep12ShiftedExpSums
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
Major arcs (Step 16, sigma-agnostic): parameterize Haar integrals on `AddCircle 1` by `[0,1]`.

Steps 10–12 express the smoothed correlation as a double integral over `UC = AddCircle 1` with
respect to the normalized Haar measure `μ = AddCircle.haarAddCircle`.

To use the real major-arc set from Step 14 (`majorArcSet` on `ℝ`) and to split “major/minor”
contributions, we want to rewrite these Haar integrals as interval integrals on `ℝ` over `[0,1]`.

This file supplies that bridge, without committing to any specific major-arc parameters.
-/

namespace Goldbach.Cert
namespace MajorArcStep16CircleToInterval

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled
open Goldbach.Cert.MajorArcStep12ShiftedExpSums

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma integral_μ_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : UC → E) :
    (∫ x : UC, f x ∂μ) = ∫ t in (0 : ℝ)..(1 : ℝ), f t := by
  -- First replace the normalized Haar integral by the standard `volume` integral on `AddCircle 1`.
  have hhaar : (∫ x : UC, f x ∂μ) = ∫ x : UC, f x := by
    -- `AddCircle.integral_haarAddCircle` states `∫ f ∂haarAddCircle = 1⁻¹ • ∫ f`,
    -- and for `T = 1` the scaling is trivial.
    simpa [μ] using (AddCircle.integral_haarAddCircle (T := (1 : ℝ)) (f := f))
  -- Then parameterize the `volume` integral by the interval integral on `[0,1]`.
  have hvol : (∫ x : UC, f x) = ∫ t in (0 : ℝ)..(1 : ℝ), f t := by
    -- `AddCircle.intervalIntegral_preimage` gives the forward direction.
    simpa [zero_add] using
      (AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (t := (0 : ℝ)) (f := f)).symm
  exact hhaar.trans hvol

/-- Step 12's shifted-frequency correlation integral rewritten as a double interval integral on `[0,1]`. -/
theorem corr_integral_eq_doubleIntervalIntegral (X N : ℕ) :
    corr_integral X N
      =
    ∫ β in (0 : ℝ)..(1 : ℝ),
      kernelPolyC (β : UC) *
        (∫ α in (0 : ℝ)..(1 : ℝ),
            (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
              * expSum X N ((α : UC) - (β : UC))
              * expSum X N ((α : UC) + (β : UC))) := by
  classical
  -- Start from Step 12's shifted integrand.
  rw [corr_integral_eq_shifted (X := X) (N := N)]
  -- Convert the outer Haar integral to an interval integral.
  rw [integral_μ_eq_intervalIntegral (f := fun β : UC =>
    kernelPolyC β *
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            * expSum X N (α - β)
            * expSum X N (α + β)
        ∂μ))]
  -- Convert the inner Haar integral pointwise (for each `β`) to an interval integral.
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro β hβ
  have hin :
      (∫ α : UC,
          (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
            * expSum X N (α - (β : UC))
            * expSum X N (α + (β : UC))
        ∂μ)
        =
      ∫ α in (0 : ℝ)..(1 : ℝ),
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
          * expSum X N ((α : UC) - (β : UC))
          * expSum X N ((α : UC) + (β : UC)) := by
    simpa using (integral_μ_eq_intervalIntegral (f := fun α : UC =>
      (fourier (T := (1 : ℝ)) (-(N : ℤ)) α : ℂ)
        * expSum X N (α - (β : UC))
        * expSum X N (α + (β : UC))))
  -- Avoid `simp` here: it tries to cancel the `kernelPolyC` factor via `mul_eq_mul_left_iff`.
  exact congrArg (fun z : ℂ => kernelPolyC (β : UC) * z) hin

end

end MajorArcStep16CircleToInterval
end Goldbach.Cert
