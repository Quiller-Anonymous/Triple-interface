import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcModules.MinorQ0Bound

/-!
`MajorArcModules/Q0MinorBound` packages the Step-3 obligation for the turnkey `Q0` route.

The `Q0` reduction asks for a uniform bound

`‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁`

on the canonical window.  This file records the natural “minor-arc” analytic input that implies
such a bound:

uniform pointwise bounds on the shifted exponential sums `expSum X N (α±β)` on the complement of
the finite `Q0` major-arc set `majorArcSetQ0 X Δ`.

No genuine cancellation estimate is proved here; we only provide the reduction from the pointwise
minor-arc bounds to the required `ε₁` deviation bound (using the existing plumbing lemmas).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorBound

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction

open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.MinorQ0Bound

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-!
### Interface: pointwise `expSum` minor-arc bounds on `majorArcSetQ0ᶜ`
-/

/--
Pointwise minor-arc hypothesis for the `Q0`-split:
uniform bounds on the two shifted exponential sums on the **complement** of `majorArcSetQ0 X Δ`,
for all `β`.
-/
structure Q0MinorExpSumBound (Δ M : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ∀ {β α : ℝ},
          α ∈ (majorArcSetQ0 X Δ)ᶜ →
            ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M ∧
            ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M

/-!
### Target: the `ε₁` deviation bound for the turnkey route
-/

/--
`Q0`-minor deviation bound: the exact statement required as the `ε₁` input for the turnkey `Q0`
route (`TurnkeyFromQ0`).
-/
structure Q0MinorDeviationBound (Δ ε₁ : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁

/-!
### Reduction: pointwise `expSum` bounds ⇒ `ε₁` bound

This reduction uses two ingredients:
- the formal decomposition lemma `corr_integral_eq_major_Q0_add_minor_Q0` (under integrability);
- the Step-25-style minor bound reduction `MinorQ0Bound.norm_corr_integral_minor_Q0_le_kernelCap_mul_sq_of_expSum_bound`.
-/

theorem q0MinorDeviationBound_of_expSum_bound
    {Δ M : ℝ} (hM : 0 ≤ M) (hExp : Q0MinorExpSumBound Δ M)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorDeviationBound Δ (kernelCap * (M ^ 2)) := by
  refine ⟨?_⟩
  intro X N hX hN

  -- Use the formal `Q0` split to rewrite the deviation as the `Q0`-minor piece.
  have hSplit :
      corr_integral X N
        =
      corr_integral_major_Q0 X N Δ + corr_integral_minor_Q0 X N Δ :=
    corr_integral_eq_major_Q0_add_minor_Q0
      (X := X) (N := N) (Δ := Δ)
      (hInner := fun β => hInner (X := X) (N := N) hX hN β)
      (hOuterMaj := hOuterMaj (X := X) (N := N) hX hN)
      (hOuterMin := hOuterMin (X := X) (N := N) hX hN)

  have hdiff :
      corr_integral X N - corr_integral_major_Q0 X N Δ
        =
      corr_integral_minor_Q0 X N Δ := by
    -- `corr - major = (major + minor) - major = minor`.
    calc
      corr_integral X N - corr_integral_major_Q0 X N Δ
          =
        (corr_integral_major_Q0 X N Δ + corr_integral_minor_Q0 X N Δ)
          -
        corr_integral_major_Q0 X N Δ := by
          simpa [hSplit]
      _ = corr_integral_minor_Q0 X N Δ := by
          ring

  -- Bound the `Q0`-minor piece via pointwise `expSum` bounds.
  have hminor :
      ‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * (M ^ 2) := by
    have hsub :
        ∀ {β α : ℝ},
          α ∈ (majorArcSetQ0 X Δ)ᶜ →
            ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M := by
      intro β α hα
      exact (hExp.bound (X := X) (N := N) hX hN (β := β) (α := α) hα).1
    have hadd :
        ∀ {β α : ℝ},
          α ∈ (majorArcSetQ0 X Δ)ᶜ →
            ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M := by
      intro β α hα
      exact (hExp.bound (X := X) (N := N) hX hN (β := β) (α := α) hα).2
    exact
      MinorQ0Bound.norm_corr_integral_minor_Q0_le_kernelCap_mul_sq_of_expSum_bound
        (X := X) (N := N) (Δ := Δ) (M := M) (hM := hM)
        (hsub := fun {β α} hα => hsub (β := β) (α := α) hα)
        (hadd := fun {β α} hα => hadd (β := β) (α := α) hα)

  -- Finish: rewrite the deviation as the minor piece and apply the bound.
  simpa [hdiff] using hminor

end

end Goldbach.Cert.MajorArcModules.Q0MinorBound

