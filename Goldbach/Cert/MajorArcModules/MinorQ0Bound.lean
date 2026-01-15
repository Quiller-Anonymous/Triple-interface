import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcStep25MinorArcBound

/-!
`MajorArcModules/MinorQ0Bound` provides a Step-25-style *reduction* for the `Q0`-complement piece
`corr_integral_minor_Q0` (defined in `MajorArcModules/CorrIntegralQ0Reduction`).

It does **not** prove a genuine minor-arc estimate (which would require cancellation).  Instead,
it shows:

if the shifted exponential sums are uniformly bounded by `M` on `((majorArcSetQ0 X Δ)ᶜ)`, then
`‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * M^2`.

This is part of the offline/turnkey “MajorArcModules” staging area.
-/

namespace Goldbach.Cert.MajorArcModules.MinorQ0Bound

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral

noncomputable section

-- Match the `UC` used throughout the major-arc integral pipeline.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

-- Reuse the Step-25 kernel cap (which is purely project-defined, not analytic).
noncomputable abbrev kernelCap : ℝ := Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap

lemma kernelCap_nonneg : 0 ≤ kernelCap :=
  Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap_nonneg

lemma norm_kernelPolyC_le_kernelCap (x : UC) :
    ‖kernelPolyC x‖ ≤ kernelCap := by
  simpa [kernelCap] using
    (Goldbach.Cert.MajorArcStep25MinorArcBound.norm_kernelPolyC_le_kernelCap (x := x))

/-- The α-integral appearing in the definition of `corr_integral_minor_Q0`. -/
noncomputable def innerMinorQ0 (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ),
    (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α

lemma corr_integral_minor_Q0_eq (X N : ℕ) (Δ : ℝ) :
    corr_integral_minor_Q0 X N Δ
      =
    ∫ β in (0 : ℝ)..(1 : ℝ), kernelPolyC (β : UC) * innerMinorQ0 X N Δ β := by
  rfl

/--
If both shifted exponential sums are uniformly bounded by `M` on the **`Q0`-minor arcs**, then the
corresponding α-integral is bounded by `M^2`.

This is the `majorArcSetQ0` analogue of
`Goldbach.Cert.MajorArcStep25MinorArcBound.norm_innerMinor_le_sq_of_expSum_bound`.
-/
theorem norm_innerMinorQ0_le_sq_of_expSum_bound
    (X N : ℕ) (Δ : ℝ) (M : ℝ) (hM : 0 ≤ M) (β : ℝ)
    (hsub : ∀ {α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M)
    (hadd : ∀ {α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M) :
    ‖innerMinorQ0 X N Δ β‖ ≤ M ^ 2 := by
  -- Reuse the Step-25 argument verbatim: it only depends on the set defining the indicator.
  have hconst :
      ∀ α ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖(majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α‖ ≤ M ^ 2 := by
    intro α _hαI
    by_cases hα : α ∈ (majorArcSetQ0 X Δ)ᶜ
    · have hI :
          ‖innerIntegrand X N β α‖ ≤ M ^ 2 := by
        have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 := by
          simp [fourier_apply]
        have hmul :
            ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M ^ 2 := by
          have h1 : ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M := hsub (α := α) hα
          have h2 : ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M := hadd (α := α) hα
          have : ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M * M :=
            mul_le_mul h1 h2 (norm_nonneg _) hM
          simpa [pow_two] using this
        calc
          ‖innerIntegrand X N β α‖
              =
            ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                  * expSum X N ((α : UC) - (β : UC))
                  * expSum X N ((α : UC) + (β : UC))‖ := by
                  rfl
          _ =
            ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
              * ‖expSum X N ((α : UC) - (β : UC))‖
              * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp [mul_assoc]
          _ = 1 * ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                rw [hfour]
          _ = ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp
          _ ≤ M ^ 2 := hmul
      simpa [Set.indicator_of_mem hα] using hI
    · have h0 : (0 : ℝ) ≤ M ^ 2 := by nlinarith [sq_nonneg M]
      have h0' : ‖(0 : ℂ)‖ ≤ M ^ 2 := by simpa using h0
      simpa [Set.indicator_of_notMem hα] using h0'

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := M ^ 2)
      (f := fun α : ℝ =>
        (majorArcSetQ0 X Δ)ᶜ.indicator (fun α => innerIntegrand X N β α) α)
      hconst
  simpa [innerMinorQ0] using h

/--
Minor-arc bound reduction for `corr_integral_minor_Q0`:
if the shifted exponential sums are uniformly bounded by `M` on `((majorArcSetQ0 X Δ)ᶜ)`,
then `‖corr_integral_minor_Q0‖ ≤ kernelCap * M^2`.
-/
theorem norm_corr_integral_minor_Q0_le_kernelCap_mul_sq_of_expSum_bound
    (X N : ℕ) (Δ : ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hsub : ∀ {β α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) - (β : UC))‖ ≤ M)
    (hadd : ∀ {β α : ℝ}, α ∈ (majorArcSetQ0 X Δ)ᶜ →
      ‖expSum X N ((α : UC) + (β : UC))‖ ≤ M) :
    ‖corr_integral_minor_Q0 X N Δ‖ ≤ kernelCap * (M ^ 2) := by
  have houter :
      ∀ β ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖kernelPolyC (β : UC) * innerMinorQ0 X N Δ β‖ ≤ kernelCap * (M ^ 2) := by
    intro β _hβI
    have hK : ‖kernelPolyC (β : UC)‖ ≤ kernelCap :=
      norm_kernelPolyC_le_kernelCap (x := (β : UC))
    have hI : ‖innerMinorQ0 X N Δ β‖ ≤ M ^ 2 :=
      norm_innerMinorQ0_le_sq_of_expSum_bound
        (X := X) (N := N) (Δ := Δ) (M := M) (hM := hM) (β := β)
        (hsub := fun {α} hα => hsub (β := β) (α := α) hα)
        (hadd := fun {α} hα => hadd (β := β) (α := α) hα)
    calc
      ‖kernelPolyC (β : UC) * innerMinorQ0 X N Δ β‖
          = ‖kernelPolyC (β : UC)‖ * ‖innerMinorQ0 X N Δ β‖ := by
              simp
      _ ≤ kernelCap * (M ^ 2) := by
              exact mul_le_mul hK hI (norm_nonneg _) (kernelCap_nonneg)

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := kernelCap * (M ^ 2))
      (f := fun β : ℝ => kernelPolyC (β : UC) * innerMinorQ0 X N Δ β)
      houter
  simpa [corr_integral_minor_Q0_eq, innerMinorQ0] using h

end

end Goldbach.Cert.MajorArcModules.MinorQ0Bound
