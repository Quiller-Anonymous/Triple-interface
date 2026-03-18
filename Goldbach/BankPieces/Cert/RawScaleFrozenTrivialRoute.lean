import Goldbach.BankPieces.Cert.RawScaleFrozenCertificates
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarCertificate
import Goldbach.BankPieces.Cert.RawScaleFrozenTrivialSmallBeta
import Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec

namespace Goldbach.BankPieces.Cert.RawScaleFrozenTrivialRoute

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.BankPieces.Cert.RawScaleFrozenCertificates
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarCertificate
open Goldbach.BankPieces.Cert.RawScaleFrozenTrivialSmallBeta
open Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0
private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/--
End-to-end positivity wrapper for the frozen `κ` route using the current coarse small-`β`
certificate.

This is the intended basepoint diagnostic theorem: instantiate closure once with the trivial freeze
budget before attempting any sharper small-`β` analysis.
-/
theorem R_bank_pos_of_frozenRoute_XCenteredScalarCertOne_trivialSmall_seriesTail
    (ηscalar ηminor ηlarge ηres εb : ℕ → ℝ)
    (hκconst_nonneg : 0 ≤ Goldbach.BankPieces.Cert.RawScaleWeightedKernel.kappaSeriesR 1 - (90 : ℝ) / Q0)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hScalar_nonneg :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        0 ≤ frozenScalarXCenteredTargetOne ηscalar X)
    (hScalar :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        frozenScalarXCenteredTargetOne ηscalar X
          ≤ Complex.re ((2 : ℂ) * Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze.frozenBetaScalarC N))
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        (ηminor X + ηlarge X + etaSmallFrozenTrivial ηres X) + εb X
          < (frozenScalarXCenteredTargetOne ηscalar X
              * (Goldbach.BankPieces.Cert.RawScaleWeightedKernel.kappaSeriesR 1 - (90 : ℝ) / Q0)) / (X : ℝ))
    (hMinor :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)‖
          ≤ ηminor X)
    (hLarge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_large X N (1 : ℝ)‖
          ≤ ηlarge X)
    (hsep :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
            MeasureTheory.volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
                Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                  (∫ α in (0 : ℝ)..(1 : ℝ),
                    (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                      (fun α =>
                        Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
            MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hRes :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖
          ≤ ηres X)
    (hInt :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        IntervalIntegrable
          (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.βIntegrand X N (1 : ℝ))
          MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ Goldbach.BankPieces.Cert.IntegralScaleClosureGate.convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  exact
    R_bank_pos_of_frozenRoute_XCenteredScalarCertOne_fullGap_seriesTail
      (ηscalar := ηscalar) (ηminor := ηminor) (ηlarge := ηlarge)
      (ηsmall := etaSmallFrozenTrivial ηres) (εb := εb)
      hκconst_nonneg hεb_nonneg hScalar_nonneg hScalar hsum_lt
      hMinor hLarge
      (by
        intro X N hX hN
        exact
          norm_corr_integral_major_Q0_small_sub_frozenWeightedMainTermKappaC_le_trivial
            (ηres := ηres) hX hN (hsep hX) (hInner hX hN) (hOuter hX hN) (hRes hX hN))
      hInt hBridge hX hN

/--
Canonical `Q0`-route specialization of the frozen `κ` closure wrapper:

* `ηminor = 4` from `Q0TwoBoundsSpec.q0Minor_bound`,
* `ηlarge = 2` from `Q0TwoBoundsSpec.q0Major_large_bound`,
* scalar certificate fixed to the proved zero-error `X`-centered version,
* small-`β` budget given by the current coarse trivial-freeze package.

What remains explicit is exactly what the current repo does not yet discharge on this route:

* the `κ`-margin nonnegativity input,
* the bridge budget `εb`,
* the final numerical gate inequality,
* the small-`β` residual/extraction hypotheses.
-/
theorem R_bank_pos_of_frozenRoute_q0Minor4_q0Large2_trivialSmall_seriesTail
    (ηres εb : ℕ → ℝ)
    (hκconst_nonneg :
      0 ≤ Goldbach.BankPieces.Cert.RawScaleWeightedKernel.kappaSeriesR 1 - (90 : ℝ) / Q0)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        (((4 : ℝ) + (2 : ℝ) + etaSmallFrozenTrivial ηres X) + εb X)
          < (frozenScalarXCenteredTargetOne (fun _ => 0) X
              * (Goldbach.BankPieces.Cert.RawScaleWeightedKernel.kappaSeriesR 1 - (90 : ℝ) / Q0))
              / (X : ℝ))
    (hsep :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
            MeasureTheory.volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
                Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                  (∫ α in (0 : ℝ)..(1 : ℝ),
                    (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                      (fun α =>
                        Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
            MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
              Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hRes :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖
          ≤ ηres X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ Goldbach.BankPieces.Cert.IntegralScaleClosureGate.convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have hMinor :
      ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
          - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)‖
        ≤ (4 : ℝ) := by
    simpa [Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon,
      Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.C,
      Goldbach.Cert.MajorArcModules.Q0CertData.cert] using
      (q0Minor_bound.bound (X := X) (N := N) hX hN)
  have hLarge :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_large X N (1 : ℝ)‖
        ≤ (2 : ℝ) := by
    simpa [Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon,
      Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert.εl,
      Goldbach.Cert.MajorArcModules.Q0MajorTailCertData.data] using
      (q0Major_large_bound.bound (X := X) (N := N) hX hN)
  have hInt :
      IntervalIntegrable
        (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.βIntegrand X N (1 : ℝ))
        MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ) := by
    simpa [Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon,
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.βIntegrand,
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.betaIntegrand] using
      (q0Major_integrable.integrable (X := X) (N := N) hX hN)
  exact
    R_bank_pos_of_frozenRoute_XCenteredScalarCertOneZero_fullGap_seriesTail
      (ηminor := fun _ => (4 : ℝ))
      (ηlarge := fun _ => (2 : ℝ))
      (ηsmall := etaSmallFrozenTrivial ηres)
      (εb := εb)
      hκconst_nonneg
      hεb_nonneg
      (by
        intro X hX
        simpa [add_assoc, add_left_comm, add_comm] using hsum_lt (X := X) hX)
      (by
        intro X N hX hN
        simpa [Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon,
          Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.C,
          Goldbach.Cert.MajorArcModules.Q0CertData.cert] using
          (q0Minor_bound.bound (X := X) (N := N) hX hN))
      (by
        intro X N hX hN
        simpa [Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon,
          Goldbach.Cert.MajorArcModules.Q0MajorTailFromCert.εl,
          Goldbach.Cert.MajorArcModules.Q0MajorTailCertData.data] using
          (q0Major_large_bound.bound (X := X) (N := N) hX hN))
      (by
        intro X N hX hN
        exact
          norm_corr_integral_major_Q0_small_sub_frozenWeightedMainTermKappaC_le_trivial
            (ηres := ηres) hX hN (hsep hX) (hInner hX hN) (hOuter hX hN) (hRes hX hN))
      (by
        intro X N hX hN
        simpa [Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0.Δ_canon,
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.βIntegrand,
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.betaIntegrand] using
          (q0Major_integrable.integrable (X := X) (N := N) hX hN))
      hBridge
      hX hN

end

end Goldbach.BankPieces.Cert.RawScaleFrozenTrivialRoute
