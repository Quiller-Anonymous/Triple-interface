import Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert
import Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute

/-!
Turn checked ε₁ SSU and Type-I certificate payloads into the split-ledger route.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSplitFromCert

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

theorem normalizedEnergy_of_certBounds
    (hSSU : canonicalExpansion.NonzeroModeEnergyBound Q0MinorSSUFromCert.U)
    (hTI : canonicalExpansion.ZeroModeEnergyBound Q0MinorTypeIFromCert.U) :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2)
        ≤
      normFactorSq X
        * ((2 * Q0MinorSSUFromCert.A2) * ((H : ℝ) / (X : ℝ))
            + (2 * Q0MinorTypeIFromCert.A3) / ((H : ℝ) * ((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)) := by
  exact normalizedEnergy_of_splitCerts
    (split := canonicalExpansion.residualSplit)
    (hSSU := Q0MinorSSUFromCert.ssuCert_of_upperBound hSSU)
    (hTI := Q0MinorTypeIFromCert.typeICert_of_upperBound hTI)

theorem rawLedger_of_certBounds
    (hSSU : canonicalExpansion.NonzeroModeEnergyBound Q0MinorSSUFromCert.U)
    (hTI : canonicalExpansion.ZeroModeEnergyBound Q0MinorTypeIFromCert.U)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon).indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon)ᶜ.indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorRawEnergyLedger Δ_canon (2 * Q0MinorSSUFromCert.A2) (2 * Q0MinorTypeIFromCert.A3) := by
  exact rawLedger_of_splitCerts
    (split := canonicalExpansion.residualSplit)
    (hSSU := Q0MinorSSUFromCert.ssuCert_of_upperBound hSSU)
    (hTI := Q0MinorTypeIFromCert.typeICert_of_upperBound hTI)
    (hInner := hInner) (hOuterMaj := hOuterMaj) (hOuterMin := hOuterMin)

end

end Goldbach.Cert.MajorArcModules.Q0MinorSplitFromCert
