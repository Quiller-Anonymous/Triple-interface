import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled

/-!
`Q0MinorNormalizationBridge` packages the algebraic normalization seam behind the `Q0` minor
split.

The two useful outputs are:

* `RΛ_smooth_cast_eq_norm_mul_major_plus_minor`: the normalized smooth count equals the global
  scalar times the `Q0` major piece plus the `Q0` minor piece;
* `RΛ_smooth_cast_sub_norm_mul_major_Q0_eq_norm_mul_minor_Q0`: after subtracting the normalized
  `Q0` major contribution, the remainder is exactly the normalized `Q0` minor contribution.

No analytic estimate is proved here.  This file only combines existing normalization and
major/minor-splitting theorems.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled

noncomputable section

/-- The global scalar relating `RΛ_smooth` to the unnormalized correlation integral. -/
def q0NormFactor (N : ℕ) : ℂ :=
  (((1 / 800 : ℝ) * (1 / (Real.log (N : ℝ)) ^ 2)) : ℂ)

/--
Combine the global `RΛ_smooth` normalization with the `Q0` major/minor decomposition of
`corr_integral`.
-/
theorem RΛ_smooth_cast_eq_norm_mul_major_plus_minor
    (X N : ℕ) (Δ : ℝ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)) :
    (Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N : ℂ)
      =
    q0NormFactor N
      *
        (Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N Δ
          + corr_integral_minor_Q0 X N Δ) := by
  rw [RΛ_smooth_cast_eq_norm_mul_corr_integral (X := X) (N := N)]
  rw [corr_integral_eq_major_Q0_add_minor_Q0
    (X := X) (N := N) (Δ := Δ) hInner hOuterMaj hOuterMin]
  simp [q0NormFactor]

/--
After subtracting the normalized `Q0`-major term, what remains is exactly the normalized
`Q0`-minor term.
-/
theorem RΛ_smooth_cast_sub_norm_mul_major_Q0_eq_norm_mul_minor_Q0
    (X N : ℕ) (Δ : ℝ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                (fun α =>
                  Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)) :
    (Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N : ℂ)
        - q0NormFactor N
            * Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N Δ
      =
    q0NormFactor N * corr_integral_minor_Q0 X N Δ := by
  rw [RΛ_smooth_cast_eq_norm_mul_major_plus_minor
    (X := X) (N := N) (Δ := Δ) hInner hOuterMaj hOuterMin]
  ring

end

end Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
