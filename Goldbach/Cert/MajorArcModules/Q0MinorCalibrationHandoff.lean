import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
`Q0MinorCalibrationHandoff` is the mathematician-facing handoff for the final `ep-1` seam.

At this stage, the only remaining project-pinned ingredient is numerical calibration:

* `CrowOf (aPoly C p) * C2raw ≤ C2`
* `CrowOf (aPoly C p) * C3raw ≤ C3`

Once those inequalities are supplied for a dyadic polynomial Gram-decay witness at `Δ_canon`,
the certified `ε₁` ledger engine follows deterministically.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorCalibrationHandoff

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
Conventional-math handoff target:
calibration inequalities for certified caps `C2 = 160`, `C3 = 144000000`.
-/
def CalibrationTarget
    (C : ℝ) (p : ℕ) (C2raw C3raw : ℝ) : Prop :=
  (CrowOf (aPoly C p)) * C2raw ≤ C2 ∧
  (CrowOf (aPoly C p)) * C3raw ≤ C3

/--
Deterministic closure theorem:
dyadic polynomial Gram-decay + calibration inequalities imply the certified `ε₁` ledger engine.
-/
theorem ledgerEngine_of_dyadicPoly_and_calibration
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw)
    (hCal : CalibrationTarget C p C2raw C3raw) :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 := by
  exact
    ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly
      ⟨C, p, C2raw, C3raw, hDy, hCal.1, hCal.2⟩

end

end Goldbach.Cert.MajorArcModules.Q0MinorCalibrationHandoff

