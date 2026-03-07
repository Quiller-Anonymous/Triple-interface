import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineFromDyadicGramDecay
import Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Bridge module for the ε₁ minor-energy seam.

This file is deterministic plumbing: it shows how to obtain the certified ledger engine
`Q0MinorEnergyLedgerEngine Δ_canon C2 C3` from a calibrated dyadic Gram-decay witness.

Analytic content is isolated in one input record (`CalibratedDyadicGramDecayPoly`):
- a dyadic Gram-decay polynomial witness at `Δ_canon`,
- calibration inequalities placing the derived ledger constants under the certified `C2,C3`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineFromDyadicGramDecay
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
Calibrated dyadic Gram-decay input on `Δ_canon`, sufficient to produce the certified
ledger engine constants `C2,C3`.
-/
structure CalibratedDyadicGramDecayPoly where
  C : ℝ
  p : ℕ
  C2raw : ℝ
  C3raw : ℝ
  hDy :
    Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw
  hC2cal :
    (CrowOf (aPoly C p)) * C2raw ≤ C2
  hC3cal :
    (CrowOf (aPoly C p)) * C3raw ≤ C3

/--
From a calibrated dyadic Gram-decay witness, we obtain the certified ε₁ ledger engine on the
canonical width `Δ_canon`.
-/
theorem ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly
    (hCal : CalibratedDyadicGramDecayPoly) :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 := by
  have hBase :
      Q0MinorEnergyLedgerEngine Δ_canon
        ((CrowOf (aPoly hCal.C hCal.p)) * hCal.C2raw)
        ((CrowOf (aPoly hCal.C hCal.p)) * hCal.C3raw) :=
    ledgerEngine_of_dyadicGramDecayPoly
      (Δ := Δ_canon) (C := hCal.C) (p := hCal.p)
      (C2 := hCal.C2raw) (C3 := hCal.C3raw) hCal.hDy
      (hInner := fun {X N} hX hN β =>
        Q0MinorOuterIntegrableResource.hInner (X := X) (N := N) hX hN β)
      (hOuterMaj := fun {X N} hX hN =>
        Q0MinorOuterIntegrableResource.hOuterMaj (X := X) (N := N) hX hN Δ_canon)
      (hOuterMin := fun {X N} hX hN =>
        Q0MinorOuterIntegrableResource.hOuterMin (X := X) (N := N) hX hN Δ_canon)
      (hOuterZone := fun {X N} hX hN j hj =>
        Q0MinorOuterIntegrableResource.hOuterZone (X := X) (N := N) hX hN Δ_canon j)
  have hC2_nonneg : 0 ≤ C2 := le_trans hBase.C2_nonneg hCal.hC2cal
  have hC3_nonneg : 0 ≤ C3 := le_trans hBase.C3_nonneg hCal.hC3cal
  exact
    ledgerEngine_mono
      (Δ := Δ_canon)
      (C2' := (CrowOf (aPoly hCal.C hCal.p)) * hCal.C2raw)
      (C3' := (CrowOf (aPoly hCal.C hCal.p)) * hCal.C3raw)
      (C2 := C2) (C3 := C3)
      hBase hCal.hC2cal hCal.hC3cal hC2_nonneg hC3_nonneg

/--
Certified ε₁ energy bound (cap `16`) obtained from a calibrated dyadic Gram-decay witness.
-/
theorem q0Minor_energyBound16_of_calibratedDyadicGramDecayPoly
    (hCal : CalibratedDyadicGramDecayPoly) :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ_canon 16 :=
  energyBound16_of_ledger_engine
    (Δ := Δ_canon)
    (ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly hCal)

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
