import Goldbach.BankPieces.Cert.RawScaleFrozenClosure
import Goldbach.Cert.MajorArcModules.Q0MinorBound

namespace Goldbach.BankPieces.Cert.RawScaleFrozenGapCertificates

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.BankPieces.Cert.RawScaleFrozenClosure
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.Q0MinorBound

noncomputable section

/--
`corr_integral - corr_integral_major_Q0_small` is controlled by the `Q0`-minor/complement deviation
plus the large-`β` tail.
-/
theorem norm_corr_integral_sub_majorQ0Small_le_of_minor_large
    {X N : ℕ} {Δ ηminor ηlarge : ℝ}
    (hminor :
      ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
          - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N Δ‖ ≤ ηminor)
    (hdecomp :
      Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N Δ
        = corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ)
    (hlarge : ‖corr_integral_major_Q0_large X N Δ‖ ≤ ηlarge) :
    ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
        - corr_integral_major_Q0_small X N Δ‖ ≤ ηminor + ηlarge := by
  calc
    ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
        - corr_integral_major_Q0_small X N Δ‖
      =
        ‖(Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
              - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N Δ)
            + corr_integral_major_Q0_large X N Δ‖ := by
          rw [hdecomp]
          ring_nf
    _ ≤
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N Δ‖
          + ‖corr_integral_major_Q0_large X N Δ‖ := by
          exact norm_add_le _ _
    _ ≤ ηminor + ηlarge := add_le_add hminor hlarge

/--
Full frozen-gap certificate assembled from:

1. the `Q0`-minor/complement deviation,
2. the large-`β` tail,
3. the frozen small-`β` model gap.
-/
theorem norm_corr_integral_sub_frozenWeightedMainTermKappaC_le_of_minor_large_small
    {X N : ℕ} {ηminor ηlarge ηsmall : ℝ}
    (hminor :
      ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
          - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)‖
        ≤ ηminor)
    (hdecomp :
      Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)
        =
      corr_integral_major_Q0_small X N (1 : ℝ) + corr_integral_major_Q0_large X N (1 : ℝ))
    (hlarge : ‖corr_integral_major_Q0_large X N (1 : ℝ)‖ ≤ ηlarge)
    (hsmall :
      ‖corr_integral_major_Q0_small X N (1 : ℝ)
          - Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge.frozenWeightedMainTermKappaC X N‖
        ≤ ηsmall) :
    ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
        - Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge.frozenWeightedMainTermKappaC X N‖
      ≤ ηminor + ηlarge + ηsmall := by
  have hrest :
      ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
          - corr_integral_major_Q0_small X N (1 : ℝ)‖ ≤ ηminor + ηlarge :=
    norm_corr_integral_sub_majorQ0Small_le_of_minor_large hminor hdecomp hlarge
  have hfull :
      ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
          - Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge.frozenWeightedMainTermKappaC X N‖
        ≤ (ηminor + ηlarge) + ηsmall :=
    norm_corr_integral_sub_frozenWeightedMainTermKappaC_le_of_rest_small hrest hsmall
  simpa [add_assoc] using hfull

/--
Window-uniform frozen-gap certificate from a window-uniform `Q0`-minor deviation certificate, a
window-uniform large-`β` tail, and a window-uniform frozen small-`β` gap.
-/
theorem norm_corr_integral_sub_frozenWeightedMainTermKappaC_le_on_window
    (ηminor ηlarge ηsmall : ℕ → ℝ)
    (hMinor :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)‖
          ≤ ηminor X)
    (hLarge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral_major_Q0_large X N (1 : ℝ)‖ ≤ ηlarge X)
    (hSmall :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖corr_integral_major_Q0_small X N (1 : ℝ)
            - Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge.frozenWeightedMainTermKappaC X N‖
          ≤ ηsmall X)
    (hInt :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        IntervalIntegrable
          (βIntegrand X N (1 : ℝ))
          MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge.frozenWeightedMainTermKappaC X N‖
        ≤ ηminor X + ηlarge X + ηsmall X := by
  intro X N hX hN
  have hdecomp :
      Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)
        =
      corr_integral_major_Q0_small X N (1 : ℝ) + corr_integral_major_Q0_large X N (1 : ℝ) :=
    by
      exact corr_integral_major_Q0_eq_small_add_large (X := X) (N := N) (Δ := (1 : ℝ)) (hInt hX hN)
  exact
    norm_corr_integral_sub_frozenWeightedMainTermKappaC_le_of_minor_large_small
      (hMinor hX hN) hdecomp (hLarge hX hN) (hSmall hX hN)

end

end Goldbach.BankPieces.Cert.RawScaleFrozenGapCertificates
