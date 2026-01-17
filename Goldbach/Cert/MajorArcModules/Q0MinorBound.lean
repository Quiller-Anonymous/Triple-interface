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

open scoped BigOperators Interval

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
### Target: the `ε₁` deviation bound for the turnkey route

`Q0`-minor deviation bound: the exact statement required as the `ε₁` input for the turnkey `Q0`
route (`TurnkeyFromQ0`).
-/

structure Q0MinorDeviationBound (Δ ε₁ : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁

/-!
### Interface (TT*/energy-friendly): an `ℓ²` bound over the `N` window

For the `ε₁` (Q0-complement) piece, a realistic analytic engine is often an `L²`/TT* estimate
over the *finite* `N`-window `EvenIn X H`. This avoids asking for pointwise bounds in `α`.

This interface records such an energy bound, and we provide a purely algebraic reduction from it
to the pointwise `ε₁` bound needed by the turnkey route.
-/

/--
Energy bound (TT*/large-sieve friendly) for the `Q0`-minor deviation, on the canonical `N` window:

`∑_{N ∈ EvenIn X H} ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖^2 ≤ E`.

This is a *finite* sum, so it is certificate-friendly (can be checked in `ℚ` after reduction).
-/
structure Q0MinorEnergyBound (Δ E : ℝ) : Prop where
  bound :
    ∀ {X : ℕ},
      X0 ≤ X →
        (∑ N ∈ EvenIn X H, ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ^ 2) ≤ E

/--
Energy bound ⇒ pointwise bound: if the `ℓ²` energy over the window is bounded by `E`, and
`E ≤ ε₁^2`, then the pointwise `ε₁` bound holds on the same window.
-/
theorem q0MinorDeviationBound_of_energy_bound
    {Δ E ε₁ : ℝ} (hε₁ : 0 ≤ ε₁)
    (hE : Q0MinorEnergyBound Δ E) (hEε : E ≤ ε₁ ^ 2) :
    Q0MinorDeviationBound Δ ε₁ := by
  refine ⟨?_⟩
  intro X N hX hN
  -- Avoid binder-name clashes by fixing the summand as a separate function.
  let f : ℕ → ℝ := fun N0 => ‖corr_integral X N0 - corr_integral_major_Q0 X N0 Δ‖ ^ 2
  have hsum : (∑ N0 ∈ EvenIn X H, f N0) ≤ E := by
    simpa [f] using (hE.bound (X := X) hX)
  have hNmem : N ∈ EvenIn X H := hN
  have hterm_le_sum :
      f N ≤ ∑ N0 ∈ EvenIn X H, f N0 := by
    -- `f N ≤ ∑_{N∈S} f N` for nonnegative `f`.
    refine Finset.single_le_sum (s := EvenIn X H) (f := f) ?_ hNmem
    intro N0 hN0
    exact sq_nonneg (‖corr_integral X N0 - corr_integral_major_Q0 X N0 Δ‖)
  have hsq :
      ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ^ 2 ≤ ε₁ ^ 2 := by
    simpa [f] using le_trans (le_trans hterm_le_sum hsum) hEε
  have habs :
      |‖corr_integral X N - corr_integral_major_Q0 X N Δ‖| ≤ |ε₁| := (sq_le_sq).1 hsq
  -- Both sides are nonnegative, so the absolute values drop.
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hε₁] using habs

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
### Interface (optional): `L²` energy bounds on `majorArcSetQ0ᶜ`

The sup-norm hypothesis `Q0MinorExpSumBound` is typically too strong to be provable in practice.
This interface asks for a uniform bound on **restricted** `L²` energies
`∫_{Ι 0 1} |expSum(α±β)|²` over the `Q0`-complement set. This is a purely measure-theoretic
reduction using Cauchy–Schwarz in `α`; it may or may not be strong enough for the eventual
analytic discharge, depending on what cancellation input is available.
-/

structure Q0MinorExpSumL2Bound (Δ M2 : ℝ) : Prop where
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          MemLp
              (fun α : ℝ =>
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) - (β : UC))‖) α)
              2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
            ∧
          (∫ α in Ι (0 : ℝ) (1 : ℝ),
              ((majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) - (β : UC))‖) α) ^ 2)
            ≤ M2
            ∧
          MemLp
              (fun α : ℝ =>
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) + (β : UC))‖) α)
              2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
            ∧
          (∫ α in Ι (0 : ℝ) (1 : ℝ),
              ((majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) + (β : UC))‖) α) ^ 2)
            ≤ M2

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
          simp [hSplit]
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

theorem q0MinorDeviationBound_of_expSum_l2_bound
    {Δ M2 : ℝ} (hM2 : 0 ≤ M2) (hExp : Q0MinorExpSumL2Bound Δ M2)
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
    Q0MinorDeviationBound Δ (kernelCap * M2) := by
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
    calc
      corr_integral X N - corr_integral_major_Q0 X N Δ
          =
        (corr_integral_major_Q0 X N Δ + corr_integral_minor_Q0 X N Δ)
          -
        corr_integral_major_Q0 X N Δ := by
          simp [hSplit]
      _ = corr_integral_minor_Q0 X N Δ := by
          ring

  have hminor :
      ‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * M2 := by
    have hsub :
        ∀ β : ℝ,
          MemLp
              (fun α : ℝ =>
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) - (β : UC))‖) α)
              2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
            ∧
          (∫ α in Ι (0 : ℝ) (1 : ℝ),
              ((majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) - (β : UC))‖) α) ^ 2)
            ≤ M2 := by
      intro β
      have hβ := (hExp.bound (X := X) (N := N) hX hN β)
      exact ⟨hβ.1, hβ.2.1⟩
    have hadd :
        ∀ β : ℝ,
          MemLp
              (fun α : ℝ =>
                (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) + (β : UC))‖) α)
              2 (volume.restrict (Ι (0 : ℝ) (1 : ℝ)))
            ∧
          (∫ α in Ι (0 : ℝ) (1 : ℝ),
              ((majorArcSetQ0 X Δ)ᶜ.indicator (fun α => ‖expSum X N ((α : UC) + (β : UC))‖) α) ^ 2)
            ≤ M2 := by
      intro β
      have hβ := (hExp.bound (X := X) (N := N) hX hN β)
      exact ⟨hβ.2.2.1, hβ.2.2.2⟩
    exact
      MinorQ0Bound.norm_corr_integral_minor_Q0_le_kernelCap_mul_of_expSum_l2_bound
        (X := X) (N := N) (Δ := Δ) (M2 := M2) (hM2 := hM2) (hsub := hsub) (hadd := hadd)

  -- Finish: rewrite the deviation as the minor piece and apply the bound.
  simpa [hdiff] using hminor

end

end Goldbach.Cert.MajorArcModules.Q0MinorBound
