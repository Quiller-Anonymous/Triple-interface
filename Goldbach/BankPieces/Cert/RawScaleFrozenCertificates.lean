import Goldbach.AO_SigmaModel
import Goldbach.BankPieces.Cert.RawScaleFrozenClosure
import Goldbach.BankPieces.Cert.RawScaleFrozenGapCertificates

namespace Goldbach.BankPieces.Cert.RawScaleFrozenCertificates

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.BankPieces.Cert.RawScaleFrozenClosure
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge
open Goldbach.BankPieces.Cert.RawScaleWeightedKernel
open Goldbach.BankPieces.Cert.IntegralScaleClosureGate
open Goldbach.BankPieces.Cert.RawScaleFrozenGapCertificates

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/--
The recommended scalar-certificate target for the frozen route.

This keeps the archimedean normalization on the `X`-scale first: a deterministic kernel factor
times `(\log X)^2 * mass_even`, minus an explicit scalar error budget.
-/
noncomputable def frozenScalarXCenteredTarget
    (cKer ηscalar : ℕ → ℝ) (X : ℕ) : ℝ :=
  cKer X * (Real.log (X : ℝ)) ^ 2 * Goldbach.AO_SigmaModel.Canon.mass_even - ηscalar X

/-- Default `X`-centered scalar target for the frozen route, with kernel constant `1`. -/
noncomputable def frozenScalarXCenteredTargetOne
    (ηscalar : ℕ → ℝ) (X : ℕ) : ℝ :=
  frozenScalarXCenteredTarget (fun _ => (1 : ℝ)) ηscalar X

/-- Translate an `X`-centered scalar certificate into a lower bound for the frozen `κ`-model. -/
theorem frozenWeightedMainTermKappaC_re_lower_of_XCenteredScalarCert_seriesTail
    (cKer ηscalar : ℕ → ℝ)
    (hκconst_nonneg : 0 ≤ kappaSeriesR 1 - (90 : ℝ) / Q0)
    (hScalar_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        0 ≤ frozenScalarXCenteredTarget cKer ηscalar X)
    (hScalar :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        frozenScalarXCenteredTarget cKer ηscalar X
          ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N)) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      (frozenScalarXCenteredTarget cKer ηscalar X * (kappaSeriesR 1 - (90 : ℝ) / Q0)) / (X : ℝ)
        ≤ Complex.re (frozenWeightedMainTermKappaC X N) := by
  intro X N hX hN
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ BankParams.X0) hX
  have hN0 : N ≠ 0 := by
    have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H := (Finset.mem_filter.mp hN).1
    have hXN : X ≤ N := by
      rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
      exact Nat.le_add_right X k
    have hX0 : 0 < X := lt_of_lt_of_le (by decide : 0 < BankParams.X0) hX
    exact Nat.ne_of_gt (lt_of_lt_of_le hX0 hXN)
  exact
    frozenWeightedMainTermKappaC_re_lower_of_beta_kappa_lower
      (X := X) (N := N) hX1
      (hScalar_nonneg hX) hκconst_nonneg
      (hScalar hX hN)
      (kappaLeQ0R_ge_kappaSeriesR_one_sub_ninety_div N hN0)

/--
Certificate-form positivity theorem for the frozen route.

Inputs:
- an `X`-centered scalar certificate for `Re ((2 : ℂ) * frozenBetaScalarC N)`;
- a full frozen-main-term gap certificate on the corr-integral scale;
- the existing `R_bank`/`conv_ref` bridge budget.
-/
theorem R_bank_pos_of_frozenRoute_XCenteredScalarCert_seriesTail
    (cKer ηscalar η εb : ℕ → ℝ)
    (hκconst_nonneg : 0 ≤ kappaSeriesR 1 - (90 : ℝ) / Q0)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hScalar_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        0 ≤ frozenScalarXCenteredTarget cKer ηscalar X)
    (hScalar :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        frozenScalarXCenteredTarget cKer ηscalar X
          ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N))
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        η X + εb X
          < (frozenScalarXCenteredTarget cKer ηscalar X
              * (kappaSeriesR 1 - (90 : ℝ) / Q0)) / (X : ℝ))
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - frozenWeightedMainTermKappaC X N‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  exact
    R_bank_pos_of_frozenWeightedMainTermKappaC_seriesTail
      (cβ := frozenScalarXCenteredTarget cKer ηscalar)
      (η := η) (εb := εb)
      hκconst_nonneg hεb_nonneg hsum_lt hScalar_nonneg hScalar hCorr hBridge hX hN

/-- Specialization of the scalar certificate to the default kernel constant `1`. -/
theorem frozenWeightedMainTermKappaC_re_lower_of_XCenteredScalarCertOne_seriesTail
    (ηscalar : ℕ → ℝ)
    (hκconst_nonneg : 0 ≤ kappaSeriesR 1 - (90 : ℝ) / Q0)
    (hScalar_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        0 ≤ frozenScalarXCenteredTargetOne ηscalar X)
    (hScalar :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        frozenScalarXCenteredTargetOne ηscalar X
          ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N)) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      (frozenScalarXCenteredTargetOne ηscalar X * (kappaSeriesR 1 - (90 : ℝ) / Q0)) / (X : ℝ)
        ≤ Complex.re (frozenWeightedMainTermKappaC X N) := by
  intro X N hX hN
  simpa [frozenScalarXCenteredTargetOne] using
    (frozenWeightedMainTermKappaC_re_lower_of_XCenteredScalarCert_seriesTail
      (cKer := fun _ => (1 : ℝ)) (ηscalar := ηscalar)
      hκconst_nonneg hScalar_nonneg hScalar hX hN)

/--
Final positivity wrapper for the frozen route with:

* kernel constant fixed to `1`,
* scalar certificate on the `X`-centered target,
* full frozen-gap certificate assembled from `ηminor + ηlarge + ηsmall`.
-/
theorem R_bank_pos_of_frozenRoute_XCenteredScalarCertOne_fullGap_seriesTail
    (ηscalar ηminor ηlarge ηsmall εb : ℕ → ℝ)
    (hκconst_nonneg : 0 ≤ kappaSeriesR 1 - (90 : ℝ) / Q0)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hScalar_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        0 ≤ frozenScalarXCenteredTargetOne ηscalar X)
    (hScalar :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        frozenScalarXCenteredTargetOne ηscalar X
          ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N))
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        (ηminor X + ηlarge X + ηsmall X) + εb X
          < (frozenScalarXCenteredTargetOne ηscalar X
              * (kappaSeriesR 1 - (90 : ℝ) / Q0)) / (X : ℝ))
    (hMinor :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)‖
          ≤ ηminor X)
    (hLarge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_large X N (1 : ℝ)‖
          ≤ ηlarge X)
    (hSmall :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
            - frozenWeightedMainTermKappaC X N‖ ≤ ηsmall X)
    (hInt :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        IntervalIntegrable
          (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.βIntegrand X N (1 : ℝ))
          MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  let η : ℕ → ℝ := fun X => ηminor X + ηlarge X + ηsmall X
  have hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - frozenWeightedMainTermKappaC X N‖ ≤ η X := by
    intro X N hX hN
    simpa [η, add_assoc] using
      (norm_corr_integral_sub_frozenWeightedMainTermKappaC_le_on_window
        (ηminor := ηminor) (ηlarge := ηlarge) (ηsmall := ηsmall)
        hMinor hLarge hSmall hInt hX hN)
  exact
    R_bank_pos_of_frozenRoute_XCenteredScalarCert_seriesTail
      (cKer := fun _ => (1 : ℝ)) (ηscalar := ηscalar) (η := η) (εb := εb)
      hκconst_nonneg hεb_nonneg hScalar_nonneg hScalar
      (by
        intro X hX
        simpa [η, add_assoc] using hsum_lt (X := X) hX)
      hCorr hBridge hX hN

end

end Goldbach.BankPieces.Cert.RawScaleFrozenCertificates
