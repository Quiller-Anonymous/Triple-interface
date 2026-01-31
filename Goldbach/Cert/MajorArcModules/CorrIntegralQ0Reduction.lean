import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcStep16CircleToInterval
import Goldbach.Cert.MajorArcStep24IntegralExtraction

/-!
`MajorArcModules/CorrIntegralQ0Reduction` provides a simple, certificate-friendly decomposition
step for the unnormalized complex correlation integral `corr_integral`.

It does **not** prove any analytic estimates; it only packages triangle-inequality bookkeeping:

to bound `‖corr_integral X N - corrModel X N‖`, it suffices to bound

1. the “non-`Q0`” part `‖corr_integral X N - corr_integral_major_Q0 X N Δ‖`, and
2. the `Q0` major-arc deviation `‖corr_integral_major_Q0 X N Δ - corrModel X N‖`.

The certificate route can then focus on producing explicit numeric bounds for these two terms.
-/

namespace Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

/-!
### A `Q0` split for the correlation integral

We split the inner α-integral using the measurable set `majorArcSetQ0 X Δ` (Step 24k), without
mentioning the polylog “textbook” major-arc parameters.
-/

noncomputable def corr_integral_minor_Q0 (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (0 : ℝ)..(1 : ℝ),
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
      (∫ α in (0 : ℝ)..(1 : ℝ),
        (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)

theorem corr_integral_eq_major_Q0_add_minor_Q0
    (X N : ℕ) (Δ : ℝ)
    (hInner : ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)) :
    corr_integral X N = corr_integral_major_Q0 X N Δ + corr_integral_minor_Q0 X N Δ := by
  -- This is the same argument as Step 17, but with `majorArcSetQ0` in place of the textbook set.
  have h16' :
      corr_integral X N
        =
      ∫ β in (0 : ℝ)..(1 : ℝ),
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ), innerIntegrand X N β α) := by
    simpa [Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand] using
      (Goldbach.Cert.MajorArcStep16CircleToInterval.corr_integral_eq_doubleIntervalIntegral
        (X := X) (N := N))
  -- Rewrite the inner integral pointwise using the indicator split.
  have hRewrite :
      (∫ β in (0 : ℝ)..(1 : ℝ),
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ), innerIntegrand X N β α))
        =
      (∫ β in (0 : ℝ)..(1 : ℝ),
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          ((∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α)
            +
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro β _hβ
    have hs : MeasurableSet (majorArcSetQ0 X Δ) :=
      majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
    have hsplit :=
      Goldbach.Cert.MajorArcStep17MajorMinorSplit.intervalIntegral_eq_major_add_minor
        (s := majorArcSetQ0 X Δ) hs (f := fun α : ℝ => innerIntegrand X N β α) (hInner β)
    exact
      congrArg
        (fun z : ℂ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
              (β : MajorArcStep7FourierOrthogonality.UC) * z)
        hsplit

  have hCorr :
      corr_integral X N
        =
      (∫ β in (0 : ℝ)..(1 : ℝ),
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          ((∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α)
            +
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))) := by
    simpa using h16'.trans hRewrite

  -- Split the outer integral of the sum.
  have hSplit :
      (∫ β in (0 : ℝ)..(1 : ℝ),
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          ((∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α)
            +
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)))
        =
      (∫ β in (0 : ℝ)..(1 : ℝ),
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
        +
      (∫ β in (0 : ℝ)..(1 : ℝ),
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)) := by
    -- Convert `K * (A+B)` to `(K*A) + (K*B)` under the integral, then use linearity.
    have hcongr :
        (∫ β in (0 : ℝ)..(1 : ℝ),
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
            ((∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α)
              +
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)))
          =
        ∫ β in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
            +
            (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro β _hβ
      simp [mul_add, mul_assoc]
    -- Now split the integral of the sum.
    have hsum :
        (∫ β in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
            +
            (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)))
          =
        (∫ β in (0 : ℝ)..(1 : ℝ),
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
          +
        (∫ β in (0 : ℝ)..(1 : ℝ),
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)) := by
      -- Use `intervalIntegral.integral_add` and the supplied integrability.
      simpa [Pi.add_apply] using
        (intervalIntegral.integral_add (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
          (f := fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
          (g := fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))
          hOuterMaj hOuterMin)
    simpa [hcongr] using hsum

  -- Combine `hCorr` with the split and unfold the two pieces.
  have h := hCorr.trans hSplit
  simpa [corr_integral_major_Q0, MajorArcStep26Q0MajorArcIntegral.innerMajorQ0,
    corr_integral_minor_Q0, mul_assoc] using h

/-!
### Triangle inequality reduction for `corr_integral - corrModel`
-/

theorem norm_corr_integral_sub_corrModel_le_of_two_bounds
    {X N : ℕ} {Δ : ℝ} {ε₁ ε₂ : ℝ}
    (h₁ : ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁)
    (h₂ : ‖corr_integral_major_Q0 X N Δ - corrModel X N‖ ≤ ε₂) :
    ‖corr_integral X N - corrModel X N‖ ≤ ε₁ + ε₂ := by
  -- `corr - model = (corr - major) + (major - model)`.
  have hdecomp :
      corr_integral X N - corrModel X N
        =
      (corr_integral X N - corr_integral_major_Q0 X N Δ)
        +
      (corr_integral_major_Q0 X N Δ - corrModel X N) := by
    ring
  -- Apply triangle inequality and then the two bounds.
  have hnormEq :
      ‖corr_integral X N - corrModel X N‖
        =
      ‖(corr_integral X N - corr_integral_major_Q0 X N Δ)
          + (corr_integral_major_Q0 X N Δ - corrModel X N)‖ := by
    simpa using congrArg (fun z : ℂ => ‖z‖) hdecomp
  rw [hnormEq]
  refine le_trans ?_ (add_le_add h₁ h₂)
  simpa using
    (norm_add_le (corr_integral X N - corr_integral_major_Q0 X N Δ)
      (corr_integral_major_Q0 X N Δ - corrModel X N))

end

end Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
