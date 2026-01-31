import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
import Goldbach.Cert.MajorArcModules.IntegralPipeline

/-!
Bridge: dyadic Gram decay (SSU/interzone “engine”) ⇒ ε₁ ledger engine.

This file is deterministic glue: it packages the existing two-step route

`dyadic Gram decay + diagonal ledger` → `Q0MinorLeverBundle` → `Q0MinorEnergyLedgerEngine`.

It is intended as the adapter point where future SSU work (proved in `SSU/`) can be connected to
the Goldbach ε₁ interface without touching the turnkey pipeline.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineFromDyadicGramDecay

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerFromInterzone
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels

noncomputable section

theorem ledgerEngine_of_dyadicGramDecay
    {Δ : ℝ} {a : ℕ → ℝ} {C2 C3 : ℝ}
    (hDy : Q0MinorDyadicGramDecay Δ a C2 C3)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ =>
              Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
            volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                  (fun α : ℝ =>
                    Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
                  α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                  (fun α : ℝ =>
                    Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
                  α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterZone :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ j ∈ (JX X : Finset ℕ),
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                  (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (zoneSet X Δ j).indicator
                    (fun α : ℝ =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
                    α))
            volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorEnergyLedgerEngine Δ ((CrowOf a) * C2) ((CrowOf a) * C3) := by
  have hLever :
      Q0MinorLeverBundle Δ a (CrowOf a) C2 C3 :=
    leverBundle_of_dyadicGramDecay
      (Δ := Δ) (a := a) (C2 := C2) (C3 := C3) hDy hInner hOuterMaj hOuterMin hOuterZone
  have hLedger :
      Q0MinorEnergyLedgerEngine Δ ((CrowOf a) * C2) ((CrowOf a) * C3) :=
    ledgerEngine_of_leverBundle (Δ := Δ) (a := a) (Crow := (CrowOf a)) (C2 := C2) (C3 := C3) hLever
  simpa [mul_assoc] using hLedger

theorem ledgerEngine_of_dyadicGramDecayPoly
    {Δ : ℝ} {C : ℝ} {p : ℕ} {C2 C3 : ℝ}
    (hDy : Q0MinorDyadicGramDecayPoly Δ C p C2 C3)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ =>
              Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
            volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
                  (fun α : ℝ =>
                    Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
                  α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ.indicator
                  (fun α : ℝ =>
                    Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
                  α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterZone :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ j ∈ (JX X : Finset ℕ),
          IntervalIntegrable
            (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                  (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (zoneSet X Δ j).indicator
                    (fun α : ℝ =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
                    α))
            volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorEnergyLedgerEngine Δ ((CrowOf (aPoly C p)) * C2) ((CrowOf (aPoly C p)) * C3) :=
  ledgerEngine_of_dyadicGramDecay (Δ := Δ) (a := aPoly C p) (C2 := C2) (C3 := C3)
    hDy.to_Q0MinorDyadicGramDecay hInner hOuterMaj hOuterMin hOuterZone

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineFromDyadicGramDecay
