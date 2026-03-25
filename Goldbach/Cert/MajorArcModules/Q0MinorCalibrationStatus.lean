import Goldbach.Cert.MajorArcModules.Q0MinorCalibrationHandoff
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelEngine

/-!
`Q0MinorCalibrationStatus` is a small status module for the corrected ε₁ route.

After the weighted-channel cleanup, the live route-visible minor object is

`minorResidual = zeroMode + meanChannel`.

That decomposition is already enough to recover the existing turnkey ε₁ engine with the certified
constants. So the remaining work on the pinned `Q0` route is no longer a decomposition problem.
It is the calibration problem isolated in `Q0MinorCalibrationHandoff`:

* produce a dyadic polynomial Gram-decay witness at `Δ_canon`, and
* verify the two calibration inequalities placing the raw constants under the certified caps.

This file packages that conclusion as theorem-facing handoff lemmas.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorCalibrationStatus

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0MinorCalibrationHandoff
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicConventionalAxioms
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelEngine
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
Current ε₁ route summary: the weighted-channel cleanup already recovers the certified ledger engine.
-/
theorem current_weightedChannel_route_gives_ledgerEngine :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 :=
by
  have hC2 :
      (2 * Q0MinorSSUFromCert.A2 : ℝ) = C2 := by
    norm_num [Q0MinorEnergyFromLedgerCert.C2, Q0MinorSSUFromCert.A2,
      Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data,
      Goldbach.Cert.MajorArcModules.Q0MinorSSUCertData.data]
  have hC3 :
      (2 * Q0MinorTypeIFromCert.A3 : ℝ) = C3 := by
    norm_num [Q0MinorEnergyFromLedgerCert.C3, Q0MinorTypeIFromCert.A3,
      Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data,
      Goldbach.Cert.MajorArcModules.Q0MinorTypeICertData.data]
  simpa [hC2, hC3] using ledgerEngine_of_currentWeightedChannelCerts

/--
Current ε₁ route summary at the energy-bound level (`cap = 16`).
-/
theorem current_weightedChannel_route_gives_energyBound16 :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ_canon 16 :=
  energyBound16_of_currentWeightedChannelCerts

/--
Mathematician-facing remaining ε₁ seam:
once a dyadic polynomial witness and calibration target are supplied, the certified ledger engine
follows deterministically.
-/
theorem ledgerEngine_of_remainingCalibrationTarget
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw)
    (hCal : CalibrationTarget C p C2raw C3raw) :
    Q0MinorEnergyLedgerEngine Δ_canon C2 C3 :=
  ledgerEngine_of_dyadicPoly_and_calibration hDy hCal

/--
Equivalent `cap = 16` consequence of the remaining calibration target.
-/
theorem energyBound16_of_remainingCalibrationTarget
    {C : ℝ} {p : ℕ} {C2raw C3raw : ℝ}
    (hDy : Q0MinorDyadicGramDecayPoly Δ_canon C p C2raw C3raw)
    (hCal : CalibrationTarget C p C2raw C3raw) :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ_canon 16 :=
  energyBound16_of_ledger_engine
    (ledgerEngine_of_remainingCalibrationTarget hDy hCal)

end

end Goldbach.Cert.MajorArcModules.Q0MinorCalibrationStatus
