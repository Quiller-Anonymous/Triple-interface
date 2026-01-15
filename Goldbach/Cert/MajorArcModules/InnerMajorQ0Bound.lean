import Goldbach.Cert.MajorArcModules.ArcSetBounds
import Goldbach.Cert.MajorArcModules.IntegralPipeline

/-!
Reduction lemma for bounding `innerMajorQ0` via per-arc pointwise bounds.

This is a bookkeeping step for the offline/turnkey major-arc route:
it combines the `Q0`-arc extraction (`MajorArcStep26Q0MajorArcIntegral.innerMajorQ0_eq_sum`)
with the elementary arc-length estimate in `MajorArcModules.ArcSetBounds`.
-/

namespace Goldbach.Cert.MajorArcModules.InnerMajorQ0Bound

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcModules.ArcSetBounds
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
If one can bound `‖innerIntegrand X N β α‖` uniformly on each textbook arc
`arcSetTextbook X q a Δ` by a constant `C q a`, then `innerMajorQ0 X N Δ β` is bounded by the
corresponding explicit finite sum of arc-length contributions.

This lemma is purely measure-theoretic bookkeeping; it does not use any analytic number theory.
-/
theorem norm_innerMajorQ0_le_sum_arc_bounds
    {X N : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hXpos : 0 < X) {β : ℝ}
    (hsep : SepQ0 X Δ)
    (hInt : IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (C : ℕ → ℕ → ℝ)
    (hC0 :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, 0 ≤ C q a)
    (hC :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          ∀ α : ℝ, α ∈ arcSetTextbook X q a Δ → ‖innerIntegrand X N β α‖ ≤ C q a) :
    ‖innerMajorQ0 X N Δ β‖
      ≤
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
      (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
  classical
  -- Expand `innerMajorQ0` as a finite `(q,a)` sum of arc integrals.
  have hsum :=
    (innerMajorQ0_eq_sum (X := X) (N := N) (Δ := Δ) hsep (β := β) hInt)
  -- Bound the norm of the sum by summing bounds for each `(q,a)` term.
  rw [hsum]
  -- outer `q`-sum
  have hq :
      ‖∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            ∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖
        ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ‖∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            ∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖ := by
    simpa using
      (norm_sum_le (s := Finset.Icc (1 : ℕ) Q0)
        (f := fun q =>
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            ∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))

  refine le_trans hq ?_
  refine Finset.sum_le_sum ?_
  intro q hqIcc
  -- inner `a`-sum
  have ha :
      ‖∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖
        ≤
      ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        ‖∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖ := by
    simpa using
      (norm_sum_le (s := Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q)
        (f := fun a =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))

  refine le_trans ha ?_
  -- bound each arc integral using `ArcSetBounds`
  refine Finset.sum_le_sum ?_
  intro a haRcop
  have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hqIcc).1
  have hterm :
      ‖∫ α in (0 : ℝ)..(1 : ℝ),
          (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖
        ≤
      (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
    refine
      norm_intervalIntegral_indicator_arcSetTextbook_le
        (X := X) (q := q) (a := a) (Δ := Δ) (C := C q a)
        hΔ hq1 hXpos (hC0 q hqIcc a haRcop) ?_
    · -- pointwise bound on the arc
      intro α hα
      exact hC q hqIcc a haRcop α hα
  exact hterm

end

end Goldbach.Cert.MajorArcModules.InnerMajorQ0Bound
