import Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaQGap

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
open Goldbach.BankPieces.Cert.ProjectedConstGapBridge

open scoped BigOperators Interval

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0
private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/--
Small-`β` weighted gap theorem at the `q`-dependent scalar level.

This is the theorem surface needed before collapsing to a common scalar `A(X,N)`:
the extracted shell is compared to the `q`-dependent model `smallBetaModelWeightedQ Aq`,
while the finite `(q,a)` residual is kept as a separate pure error term.
-/
theorem norm_corr_integral_major_Q0_small_sub_smallBetaModelWeightedQ_le_of_extracted_residual
    (Aq : ℕ → ℕ → ℕ → ℝ)
    {X N : ℕ} {Δ ηextract ηres : ℝ}
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X Δ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hextract :
      ‖smallBetaExtractedWeighted X N Δ - smallBetaModelWeightedQ Aq X N‖ ≤ ηextract)
    (hres :
      ‖smallBetaResidualWeighted X N Δ‖ ≤ ηres) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
        - smallBetaModelWeightedQ Aq X N‖
      ≤ ηextract + ηres := by
  rw [corr_integral_major_Q0_small_eq_extracted_add_residual
    (X := X) (N := N) (Δ := Δ) hsep hInner hOuter]
  calc
    ‖(smallBetaExtractedWeighted X N Δ + smallBetaResidualWeighted X N Δ)
        - smallBetaModelWeightedQ Aq X N‖
      =
    ‖(smallBetaExtractedWeighted X N Δ - smallBetaModelWeightedQ Aq X N)
        + smallBetaResidualWeighted X N Δ‖ := by
          ring_nf
    _ ≤ ‖smallBetaExtractedWeighted X N Δ - smallBetaModelWeightedQ Aq X N‖
          + ‖smallBetaResidualWeighted X N Δ‖ := by
            simpa using
              norm_add_le
                (smallBetaExtractedWeighted X N Δ - smallBetaModelWeightedQ Aq X N)
                (smallBetaResidualWeighted X N Δ)
    _ ≤ ηextract + ηres := add_le_add hextract hres

/--
Collapse the `q`-dependent small-`β` model to a common scalar model after the extracted/residual
decomposition has already been separated.

This theorem is the exact bridge from the honest `Aq(X,N,q)` stage to the later common-scalar
stage `A(X,N) * qa_mainTerm_Q0C(N)`.
-/
theorem norm_corr_integral_major_Q0_small_sub_smallBetaModelWeighted_le_of_q_extract_residual_scalar
    (Aq : ℕ → ℕ → ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    {X N : ℕ} {Δ ηextract ηres ηA : ℝ}
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X Δ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hextract :
      ‖smallBetaExtractedWeighted X N Δ - smallBetaModelWeightedQ Aq X N‖ ≤ ηextract)
    (hres :
      ‖smallBetaResidualWeighted X N Δ‖ ≤ ηres)
    (hAq :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        |Aq X N q - A X N| ≤ ηA) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
        - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
      ≤ ηextract + ηres + Goldbach.AO_WeightMass.weight_mass X * (ηA * qaPhaseUpperConst) := by
  calc
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
        - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
      ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
            - smallBetaModelWeightedQ Aq X N‖
          + ‖smallBetaModelWeightedQ Aq X N
              - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖ := by
            calc
              ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
                  - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
                =
              ‖(Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
                    - smallBetaModelWeightedQ Aq X N)
                  + (smallBetaModelWeightedQ Aq X N
                    - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N)‖ := by
                    ring_nf
              _ ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
                      - smallBetaModelWeightedQ Aq X N‖
                    + ‖smallBetaModelWeightedQ Aq X N
                        - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖ := by
                          simpa using
                            norm_add_le
                              (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N Δ
                                - smallBetaModelWeightedQ Aq X N)
                              (smallBetaModelWeightedQ Aq X N
                                - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N)
    _ ≤ (ηextract + ηres)
          + Goldbach.AO_WeightMass.weight_mass X * (ηA * ProjectedConstGapBridge.qaPhaseUpperConst) := by
            gcongr
            · exact
                norm_corr_integral_major_Q0_small_sub_smallBetaModelWeightedQ_le_of_extracted_residual
                  (Aq := Aq) hsep hInner hOuter hextract hres
            · exact
                norm_smallBetaModelWeightedQ_sub_smallBetaModelWeighted_le_of_uniform_scalar_gap
                  (Aq := Aq) (A := A) hAq
    _ = ηextract + ηres
          + Goldbach.AO_WeightMass.weight_mass X * (ηA * ProjectedConstGapBridge.qaPhaseUpperConst) := by
          ring

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaQGap
