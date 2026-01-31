import Goldbach.Cert.MajorArcModules.Q0MajorBound
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

/-!
`MajorArcModules/Q0MajorBoundFromSplit` packages the β-splitting reduction into an inhabitant of
`Q0MajorDeviationBound`.

This is still “analytic-boundary facing”: it asks for two uniform bounds (small-β and large-β),
plus interval-integrability of the β-integrand.  Once these inputs are provided (proved or
certificate-checked), it yields the `Q0` major-arc deviation bound in the exact interface shape
used by the turnkey route.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorBoundFromSplit

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.Q0MajorBound
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private noncomputable def βIntegrand (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β

theorem q0MajorDeviationBound_of_small_large
    (Δ εs εl : ℝ)
    (hInt :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          IntervalIntegrable (βIntegrand X N Δ) volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hSmall :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral_major_Q0_small X N Δ - corrModel X N‖ ≤ εs)
    (hLarge :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl) :
    Q0MajorDeviationBound Δ (εs + εl) := by
  refine ⟨?_⟩
  intro X N hX hN
  have hdecomp :
      corr_integral_major_Q0 X N Δ
        =
      corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ :=
    corr_integral_major_Q0_eq_small_add_large (X := X) (N := N) (Δ := Δ) (hInt hX hN)
  exact
    norm_corr_integral_major_Q0_sub_corrModel_le_of_small_large
      (X := X) (N := N) (Δ := Δ) (εs := εs) (εl := εl)
      hdecomp (hSmall hX hN) (hLarge hX hN)

end

end Goldbach.Cert.MajorArcModules.Q0MajorBoundFromSplit
