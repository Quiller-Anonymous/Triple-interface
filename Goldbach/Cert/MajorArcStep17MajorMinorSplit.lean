import Goldbach.Cert.MajorArcStep16CircleToInterval
import Goldbach.Cert.MajorArcStep15Parameters
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Major arcs (Step 17, sigma-agnostic): major/minor decomposition on `[0,1]`.

Step 16 rewrites the shifted-frequency correlation integral as a double interval integral on `[0,1]`.
This file supplies the standard measure-theory plumbing to split the inner `α`-integral into
major and minor contributions using indicator functions, assuming interval-integrability of the
relevant integrands.
-/

namespace Goldbach.Cert
namespace MajorArcStep17MajorMinorSplit

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep11RLSmoothIntegralScaled
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep15Parameters
open Goldbach.Cert.MajorArcStep16CircleToInterval

noncomputable section

/-- The Step 16 inner `α`-integrand (shifted-frequency form), for fixed `β`. -/
def innerIntegrand (X N : ℕ) (β α : ℝ) : ℂ :=
  (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
    * expSum X N ((α : UC) - (β : UC))
    * expSum X N ((α : UC) + (β : UC))

lemma intervalIntegrable_indicator_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume (0 : ℝ) (1 : ℝ)) :
    IntervalIntegrable (s.indicator f) volume (0 : ℝ) (1 : ℝ) := by
  refine ⟨?_, ?_⟩
  · exact (hf.1.indicator hs)
  · exact (hf.2.indicator hs)

/-- Interval-integrability of the complementary indicator, derived from interval-integrability. -/
lemma intervalIntegrable_indicator_compl_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume (0 : ℝ) (1 : ℝ)) :
    IntervalIntegrable (sᶜ.indicator f) volume (0 : ℝ) (1 : ℝ) :=
  intervalIntegrable_indicator_of_intervalIntegrable (s := sᶜ) hs.compl hf

/-- On `[0,1]`, the interval integral splits as “major + minor” via indicators. -/
theorem intervalIntegral_eq_major_add_minor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume (0 : ℝ) (1 : ℝ)) :
    (∫ x in (0 : ℝ)..(1 : ℝ), f x)
      =
    (∫ x in (0 : ℝ)..(1 : ℝ), s.indicator f x)
      +
    (∫ x in (0 : ℝ)..(1 : ℝ), sᶜ.indicator f x) := by
  have hMaj : IntervalIntegrable (s.indicator f) volume (0 : ℝ) (1 : ℝ) :=
    intervalIntegrable_indicator_of_intervalIntegrable (s := s) hs hf
  have hMin : IntervalIntegrable (sᶜ.indicator f) volume (0 : ℝ) (1 : ℝ) :=
    intervalIntegrable_indicator_compl_of_intervalIntegrable (s := s) hs hf
  -- Rewrite `f` as the sum of its indicator pieces, then use linearity of the interval integral.
  have hsum : s.indicator f + sᶜ.indicator f = f :=
    Set.indicator_self_add_compl s f
  -- `∫ f = ∫ (maj+min) = ∫ maj + ∫ min`.
  calc
    (∫ x in (0 : ℝ)..(1 : ℝ), f x)
        =
      ∫ x in (0 : ℝ)..(1 : ℝ), (s.indicator f + sᶜ.indicator f) x := by
        -- use `hsum.symm : f = maj+min`
        simpa [hsum] using (congrArg (fun g : ℝ → E => ∫ x in (0 : ℝ)..(1 : ℝ), g x) hsum.symm)
    _ =
      (∫ x in (0 : ℝ)..(1 : ℝ), s.indicator f x)
        +
      (∫ x in (0 : ℝ)..(1 : ℝ), sᶜ.indicator f x) := by
        -- `intervalIntegral.integral_add` expects pointwise `f x + g x`.
        simpa [Pi.add_apply] using
          (intervalIntegral.integral_add (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
            (f := fun x => s.indicator f x) (g := fun x => sᶜ.indicator f x) hMaj hMin)

/-- For fixed `β`, the inner integral in Step 16 splits into major + minor (textbook major arcs). -/
theorem innerIntegral_eq_major_add_minor
    (X N : ℕ) (B : ℕ) (Δ : ℝ) (β : ℝ)
    (hFull : IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ)) :
    (∫ α in (0 : ℝ)..(1 : ℝ), innerIntegrand X N β α)
      =
    (∫ α in (0 : ℝ)..(1 : ℝ),
        (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α)
      +
    (∫ α in (0 : ℝ)..(1 : ℝ),
        (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α) := by
  have hs : MeasurableSet (majorArcSetTextbook X B Δ) :=
    measurableSet_majorArcSetTextbook (X := X) (B := B) (Δ := Δ)
  simpa [innerIntegrand] using
    (intervalIntegral_eq_major_add_minor (s := majorArcSetTextbook X B Δ) hs (f := fun α => innerIntegrand X N β α)
      hFull)

/-- Major-arc contribution to `corr_integral` (Step 16 form) using textbook major arcs in `α`. -/
noncomputable def corr_integral_major (X N : ℕ) (B : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (0 : ℝ)..(1 : ℝ),
    kernelPolyC (β : UC) *
      (∫ α in (0 : ℝ)..(1 : ℝ),
        (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α)

/-- Minor-arc contribution to `corr_integral` (Step 16 form) using textbook major arcs in `α`. -/
noncomputable def corr_integral_minor (X N : ℕ) (B : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (0 : ℝ)..(1 : ℝ),
    kernelPolyC (β : UC) *
      (∫ α in (0 : ℝ)..(1 : ℝ),
        (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)

/--
Under interval-integrability hypotheses, the Step 16 correlation integral splits as
`corr_integral = corr_integral_major + corr_integral_minor`.
-/
theorem corr_integral_eq_major_add_minor
    (X N : ℕ) (B : ℕ) (Δ : ℝ)
    (hInner : ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      IntervalIntegrable
        (fun β : ℝ =>
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      IntervalIntegrable
        (fun β : ℝ =>
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))
        volume (0 : ℝ) (1 : ℝ)) :
    corr_integral X N = corr_integral_major X N B Δ + corr_integral_minor X N B Δ := by
  -- Start from Step 16’s double-interval formula.
  have h16 := corr_integral_eq_doubleIntervalIntegral (X := X) (N := N)
  -- Rewrite the inner integral pointwise using `innerIntegral_eq_major_add_minor`.
  have hRewrite :
      (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ), innerIntegrand X N β α))
        =
      (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          ((∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α)
            +
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro β hβ
    have hβ' := innerIntegral_eq_major_add_minor (X := X) (N := N) (B := B) (Δ := Δ) (β := β) (hInner β)
    -- Multiply the equality by `kernelPolyC (β:UC)`.
    exact congrArg (fun z : ℂ => kernelPolyC (β : UC) * z) hβ'

  -- Combine Step 16 with the inner rewrite, then split the outer integral by linearity.
  have hCorr :
      corr_integral X N
        =
      (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          ((∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α)
            +
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))) := by
    -- `h16` gives the double-interval expression with `innerIntegrand`.
    -- Note `innerIntegrand` is definitionally the same as the displayed product.
    -- We rewrite the right-hand side using `hRewrite`.
    -- (Avoid `simp` cancellation around `kernelPolyC`.)
    simpa [innerIntegrand] using h16.trans hRewrite

  -- Distribute `kernelPolyC` across the sum and split the outer interval integral.
  have hSplit :
      (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          ((∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α)
            +
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)))
        =
      (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α))
        +
      (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)) := by
    -- First rewrite `kernelPolyC * (A+B)` as `(kernelPolyC*A) + (kernelPolyC*B)` under the integral,
    -- then use linearity of the interval integral.
    have hcongr :
        (∫ β in (0 : ℝ)..(1 : ℝ),
          kernelPolyC (β : UC) *
            ((∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α)
              +
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)))
          =
        ∫ β in (0 : ℝ)..(1 : ℝ),
          (kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α))
            +
            (kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro β hβ
      simp [mul_add, add_mul, mul_assoc]

    -- Now split the integral of the sum.
    have hAdd :=
      (intervalIntegral.integral_add (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
        (f := fun β : ℝ =>
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α))
        (g := fun β : ℝ =>
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))
        hOuterMaj hOuterMin)

    -- Combine the congruence rewrite with the additivity lemma.
    simpa [Pi.add_apply] using hcongr.trans hAdd

  -- Finish by unfolding the major/minor definitions.
  calc
    corr_integral X N
        =
      (∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          ((∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ).indicator (fun α => innerIntegrand X N β α) α)
            +
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (majorArcSetTextbook X B Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))) := hCorr
    _ =
      corr_integral_major X N B Δ + corr_integral_minor X N B Δ := by
      simpa [corr_integral_major, corr_integral_minor] using hSplit

end

end MajorArcStep17MajorMinorSplit
end Goldbach.Cert
