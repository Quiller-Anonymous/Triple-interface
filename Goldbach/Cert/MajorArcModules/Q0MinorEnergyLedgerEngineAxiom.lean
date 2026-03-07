import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
import Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Tool-axiom seam for ε₁ (minor / Q0-complement) in the turnkey `Q0` route.

This isolates the remaining analytic input needed by the *certificate glue*
`Q0MinorEnergyFromLedgerCert`, at the calibrated dyadic-bridge layer.

Polished-gold policy: this should eventually be discharged in-repo from the SSU/interzone
lever-bundle machinery (possibly still assuming project-neutral SSU tool axioms).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineAxiom

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineBridge
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/--
Remaining analytic seam: a calibrated dyadic Gram-decay witness at `Δ_canon`.
-/
axiom ssu_minor_energy_calibratedDyadicGramDecayPoly :
  CalibratedDyadicGramDecayPoly

/--
The turnkey-facing ledger engine, derived deterministically from the calibrated bridge witness.
-/
theorem ssu_minor_energy_ledger_engine :
  Q0MinorEnergyLedgerEngine Δ_canon C2 C3 :=
  ssu_minor_energy_ledger_engine_of_calibratedDyadicGramDecayPoly
    ssu_minor_energy_calibratedDyadicGramDecayPoly

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedgerEngineAxiom
