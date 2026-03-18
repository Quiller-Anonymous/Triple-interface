import Goldbach.BankPieces.Cert.RawScaleSmallBetaModel
import Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction
import Goldbach.Cert.MajorArcModules.BetaInterval
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.MainTermQ0
open Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC
private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- Residual phase for the `α+β` side on a textbook arc. -/
noncomputable def betaPlusResidual (q a : ℕ) (α β : ℝ) : ℝ :=
  (α - (a : ℝ) / (q : ℝ)) + β

/-- Residual phase for the `α-β` side on a textbook arc. -/
noncomputable def betaMinusResidual (q a : ℕ) (α β : ℝ) : ℝ :=
  (α - (a : ℝ) / (q : ℝ)) - β

/-- Unweighted Step-21 main-term sum on the `α+β` side. -/
noncomputable def smallBetaV1 (N q a : ℕ) (α β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp (betaPlusResidual q a α β) n

/-- Unweighted Step-21 main-term sum on the `α-β` side. -/
noncomputable def smallBetaV2 (N q a : ℕ) (α β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp (betaMinusResidual q a α β) n

/-- Local `μ/φ` main term on the `α+β` side. -/
noncomputable def smallBetaM1 (N q a : ℕ) (α β : ℝ) : ℂ :=
  ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (ArithmeticFunction.moebius q : ℂ) * smallBetaV1 N q a α β

/-- Local `μ/φ` main term on the `α-β` side. -/
noncomputable def smallBetaM2 (N q a : ℕ) (α β : ℝ) : ℂ :=
  ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) * (ArithmeticFunction.moebius q : ℂ) * smallBetaV2 N q a α β

/--
Local extracted small-`β` main term on a single textbook arc.

This is the exact object produced by the Step-21 local approximation before any attempt to factor
the resulting finite `(q,a)` sum through a single scalar times `qa_mainTerm_Q0C`.
-/
noncomputable def smallBetaLocalMainTerm (_X N q a : ℕ) (α β : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
    * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
    * (smallBetaM1 N q a α β * smallBetaM2 N q a α β)

/--
The fully extracted weighted small-`β` main term obtained by replacing the true integrand on each
textbook arc with the Step-21 local main term and summing/integrating over the finite `Q0` arcs.
-/
noncomputable def smallBetaExtractedWeighted (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      betaSmallSet.indicator (fun β : ℝ =>
        ∫ α in (0 : ℝ)..(1 : ℝ),
          (arcSetTextbook X q a Δ).indicator (fun α => smallBetaLocalMainTerm X N q a α β) α) β

/--
Residual between the exact extracted small-`β` shell and the Step-21 local main term shell.

This is defined after the `α`-integration and `β`-integration, so the exact decomposition theorem
below is purely algebraic once `corr_integral_major_Q0_small` has been rewritten as the finite
`(q,a)` shell from `Q0MajorSmallExtraction`.
-/
noncomputable def smallBetaResidualWeighted (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
    ((∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        betaSmallSet.indicator (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
      -
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        betaSmallSet.indicator (fun β : ℝ =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => smallBetaLocalMainTerm X N q a α β) α) β))

theorem corr_integral_major_Q0_small_eq_extracted_add_residual
    (X N : ℕ) (Δ : ℝ)
    (hsep : SepQ0 X Δ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ) :
    corr_integral_major_Q0_small X N Δ
      =
    smallBetaExtractedWeighted X N Δ + smallBetaResidualWeighted X N Δ := by
  rw [corr_integral_major_Q0_small_eq_sum (X := X) (N := N) (Δ := Δ) hsep hInner hOuter]
  unfold smallBetaExtractedWeighted smallBetaResidualWeighted
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro q hq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro a ha
  abel

theorem norm_corr_integral_major_Q0_small_sub_smallBetaModelWeighted_le_of_extracted_residual
    (A : ℕ → ℕ → ℝ)
    {X N : ℕ} {Δ ηextract ηres : ℝ}
    (hsep : SepQ0 X Δ)
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hextract :
      ‖smallBetaExtractedWeighted X N Δ
          - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖ ≤ ηextract)
    (hres :
      ‖smallBetaResidualWeighted X N Δ‖ ≤ ηres) :
    ‖corr_integral_major_Q0_small X N Δ
        - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
      ≤ ηextract + ηres := by
  rw [corr_integral_major_Q0_small_eq_extracted_add_residual
    (X := X) (N := N) (Δ := Δ) hsep hInner hOuter]
  calc
    ‖(smallBetaExtractedWeighted X N Δ + smallBetaResidualWeighted X N Δ)
        - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
      =
    ‖(smallBetaExtractedWeighted X N Δ
          - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N)
        + smallBetaResidualWeighted X N Δ‖ := by
          ring_nf
    _ ≤ ‖smallBetaExtractedWeighted X N Δ
            - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N‖
          + ‖smallBetaResidualWeighted X N Δ‖ := by
            simpa using
              norm_add_le
                (smallBetaExtractedWeighted X N Δ
                  - Goldbach.BankPieces.Cert.RawScaleSmallBetaModel.smallBetaModelWeighted A X N)
                (smallBetaResidualWeighted X N Δ)
    _ ≤ ηextract + ηres := add_le_add hextract hres

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted
