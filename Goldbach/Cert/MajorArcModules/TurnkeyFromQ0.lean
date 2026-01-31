import Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
import Goldbach.Cert.MajorArcModules.TurnkeyFromCorrIntegral

/-!
`MajorArcModules/TurnkeyFromQ0` is a small combination lemma for the turnkey certificate route.

It packages the most certificate-friendly reduction:

to prove `TurnkeyMajorArcCanon`, it suffices to provide **two uniform bounds**:

1. a bound for the “outside `Q0`” deviation `‖corr_integral - corr_integral_major_Q0‖`, and
2. a bound for the `Q0` major-arc deviation `‖corr_integral_major_Q0 - corrModel‖`,

and then feed their sum into the normalization lemma
`MajorArcModules.TurnkeyFromCorrIntegral.turnkey_of_corr_integral_bound`.
-/

namespace Goldbach.Cert.MajorArcModules.TurnkeyFromQ0

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.CorrIntegralQ0Reduction
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.TurnkeyCanon
open Goldbach.Cert.MajorArcModules.TurnkeyFromCorrIntegral

noncomputable section

theorem turnkey_of_q0_two_bounds
    (Δ ε₁ ε₂ : ℝ)
    (h₁ :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral X N - corr_integral_major_Q0 X N Δ‖ ≤ ε₁)
    (h₂ :
      ∀ {X N : ℕ},
        X0 ≤ X → N ∈ EvenIn X H →
          ‖corr_integral_major_Q0 X N Δ - corrModel X N‖ ≤ ε₂)
    (hε : (1 / 135200 : ℝ) * (ε₁ + ε₂) ≤ δ_major_canon) :
    TurnkeyMajorArcCanon := by
  refine
    turnkey_of_corr_integral_bound (ε := ε₁ + ε₂)
      (hCorr := ?_) (hε := hε)
  intro X N hX hN
  exact
    norm_corr_integral_sub_corrModel_le_of_two_bounds
      (h₁ (X := X) (N := N) hX hN)
      (h₂ (X := X) (N := N) hX hN)

end

end Goldbach.Cert.MajorArcModules.TurnkeyFromQ0
