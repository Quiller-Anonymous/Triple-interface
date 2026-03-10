import Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget

/-!
`Q0MinorCalibration` packages the final deterministic/numeric step of the `ε₁` route.

Once the mathematician provides explicit TT* constants

* `C, p` for off-diagonal shell decay,
* `C2raw, C3raw` for the diagonal ledger,

the only remaining work is to verify the two Crow calibration inequalities. This file packages
that final step and immediately derives the Goldbach bridge witness and certified ledger engine.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorCalibration

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAnalyticTarget
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
Final numeric calibration package for the `ε₁` TT* route.
-/
structure Q0MinorCalibrationBounds (C : ℝ) (p : ℕ) (C2raw C3raw : ℝ) : Prop where
  hC2cal : (Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms.CrowOf
      (Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms.aPoly C p)) * C2raw ≤ C2
  hC3cal : (Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms.CrowOf
      (Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms.aPoly C p)) * C3raw ≤ C3

/--
TT* analytic control plus numeric calibration yields the exact remaining bridge witness.
-/
def calibratedDyadicGramDecayPoly_of_ttstar_and_calibration
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hTT : Q0MinorTTStarPolyDecay Δ_canon C p C2raw C3raw)
    (hCal : Q0MinorCalibrationBounds C p C2raw C3raw) :
    CalibratedDyadicGramDecayPoly :=
  calibratedDyadicGramDecayPoly_of_ttstar
    (C := C) (p := p) (C2raw := C2raw) (C3raw := C3raw)
    hTT hCal.hC2cal hCal.hC3cal

/--
Pipeline helper: TT* analytic control plus numeric calibration immediately yields the certified
`ε₁` ledger engine.
-/
theorem ssu_minor_energy_ledger_engine_of_ttstar_and_calibration
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hTT : Q0MinorTTStarPolyDecay Δ_canon C p C2raw C3raw)
    (hCal : Q0MinorCalibrationBounds C p C2raw C3raw) :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 :=
  ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly
    (calibratedDyadicGramDecayPoly_of_ttstar_and_calibration hTT hCal)

end

end Goldbach.Cert.MajorArcModules.Q0MinorCalibration
