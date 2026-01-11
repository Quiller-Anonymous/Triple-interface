import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Major arcs (Step 26, sigma-agnostic): package the `Q0` major-arc integral extraction.

Step 24k (`MajorArcStep24IntegralExtraction`) proves an **α-integral extraction** lemma for the
finite `Q0` major-arc union:

`∫ (majorArcSetQ0 X Δ).indicator f = ∑_{q≤Q0} ∑_{a∈Rcop q} ∫ (arcSetTextbook X q a Δ).indicator f`.

This file lifts that extraction into the **outer β-integral** that appears in the correlation
integral, defining the corresponding `Q0`-major-arc piece and rewriting it as a finite `(q,a)` sum.
No analytic estimates are proved here; this is purely measure-theory bookkeeping.
-/

namespace Goldbach.Cert
namespace MajorArcStep26Q0MajorArcIntegral

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

-- Match the ambient circle used in the major-arc integral pipeline.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private abbrev Q0 : ℕ := AO_OffDiag.TailBlock.Q0

/-!
### The `Q0`-major-arc inner α-integral
-/

/-- The α-integral appearing in the `Q0`-major-arc piece of the correlation integral. -/
noncomputable def innerMajorQ0 (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ),
    (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α

theorem innerMajorQ0_eq_sum
    (X N : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ) (β : ℝ)
    (hInt : IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ)) :
    innerMajorQ0 X N Δ β
      =
    ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
      ∫ α in (0 : ℝ)..(1 : ℝ),
        (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α := by
  simpa [innerMajorQ0] using
    (Goldbach.Cert.MajorArcStep24IntegralExtraction.intervalIntegral_majorArcSetQ0_indicator_eq_sum
      (X := X) (Δ := Δ) (hsep := hsep) (f := fun α : ℝ => innerIntegrand X N β α) hInt)

/-!
### The `Q0`-major-arc piece of the correlation integral
-/

/--
The correlation integral restricted to the finite `Q0` major arcs in `α` (for a fixed width `Δ`).

This is an auxiliary object: it is *not* the same as `corr_integral_major`, which uses the
polylogarithmic textbook major arcs `majorArcSetTextbook X B Δ`.
-/
noncomputable def corr_integral_major_Q0 (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * innerMajorQ0 X N Δ β

theorem corr_integral_major_Q0_eq_sum
    (X N : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ)
    (hInner : ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ (Finset.Icc (1 : ℕ) Q0), ∀ a ∈ (Rcop q),
        IntervalIntegrable
          (fun β : ℝ =>
            kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    corr_integral_major_Q0 X N Δ
      =
    ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
      ∫ β in (0 : ℝ)..(1 : ℝ),
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α) := by
  classical
  -- Rewrite the inner α-integral by Step 24k extraction, then swap the β-integral with the finite sums.
  unfold corr_integral_major_Q0
  have hRewrite :
      (fun β : ℝ => kernelPolyC (β : UC) * innerMajorQ0 X N Δ β)
        =
      fun β : ℝ =>
        ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α) := by
    funext β
    have hβ := innerMajorQ0_eq_sum (X := X) (N := N) (Δ := Δ) hsep β (hInner β)
    -- Multiply through by `kernelPolyC (β:UC)` and distribute over the finite sums.
    -- `simp` is safe here: it only normalizes finite sums/products.
    simpa [hβ, innerMajorQ0, mul_assoc, Finset.mul_sum, Finset.sum_mul] using
      congrArg (fun z : ℂ => kernelPolyC (β : UC) * z) hβ

  -- Reduce to an interval integral of a finite sum.
  have hInt :
      (∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * innerMajorQ0 X N Δ β)
        =
      ∫ β in (0 : ℝ)..(1 : ℝ),
        (∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) := by
    simpa [hRewrite]

  -- Interval-integrability for the `q`-level inner sums (derived from `hOuter`).
  have hq_int :
      ∀ q ∈ (Finset.Icc (1 : ℕ) Q0),
        IntervalIntegrable
          (fun β : ℝ =>
            ∑ a ∈ (Rcop q),
              kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ) := by
    intro q hq
    -- integrable for each `a`, hence for the finite sum
    have ha_int :
        ∀ a ∈ (Rcop q),
          IntervalIntegrable
            (fun β : ℝ =>
              kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
            volume (0 : ℝ) (1 : ℝ) := by
      intro a ha
      exact hOuter q hq a ha
    have hsum :
        IntervalIntegrable
          (∑ a ∈ (Rcop q), fun β : ℝ =>
            kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ) :=
      IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (s := Rcop q)
        (f := fun a β =>
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
        ha_int
    -- rewrite the sum-of-functions into the function returning a sum
    have hfun :
        (∑ a ∈ (Rcop q), fun β : ℝ =>
            kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
          =
        (fun β : ℝ =>
          ∑ a ∈ (Rcop q),
            kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) := by
      funext β
      simp
    simpa [hfun] using hsum

  -- Swap β-integral with the finite sums (`q` then `a`).
  rw [hInt]
  calc
    (∫ β in (0 : ℝ)..(1 : ℝ),
        (∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)))
        =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0),
        ∫ β in (0 : ℝ)..(1 : ℝ),
          (∑ a ∈ (Rcop q),
            kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) := by
        -- swap outer integral with the `q`-sum
        simpa using
          (intervalIntegral.integral_finset_sum
            (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
            (s := Finset.Icc (1 : ℕ) Q0)
            (f := fun q β =>
              ∑ a ∈ (Rcop q),
                kernelPolyC (β : UC) *
                  (∫ α in (0 : ℝ)..(1 : ℝ),
                    (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
            hq_int)
    _ =
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
        ∫ β in (0 : ℝ)..(1 : ℝ),
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α) := by
        -- now swap the inner integral with the `a`-sum for each `q`
        refine Finset.sum_congr rfl ?_
        intro q hq
        have ha_int :
            ∀ a ∈ (Rcop q),
              IntervalIntegrable
                (fun β : ℝ =>
                  kernelPolyC (β : UC) *
                    (∫ α in (0 : ℝ)..(1 : ℝ),
                      (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
                volume (0 : ℝ) (1 : ℝ) := by
          intro a ha
          exact hOuter q hq a ha
        simpa using
          (intervalIntegral.integral_finset_sum
            (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
            (s := Rcop q)
            (f := fun a β =>
              kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
            ha_int)

end

end MajorArcStep26Q0MajorArcIntegral
end Goldbach.Cert

