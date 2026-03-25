import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
import Goldbach.Cert.MajorArcModules.Q0MinorSplitEngine
import Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelCerts

/-!
Bridge from the weighted-channel minor decomposition back to the existing turnkey minor-energy
engine interface.

This file is deterministic bookkeeping only. It shows that the new route-visible decomposition

`minorResidual = zeroMode + meanChannel`

can be consumed by the same raw-ledger / energy-engine interfaces already used by the pinned `Q0`
route.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelEngine

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
open Goldbach.Cert.MajorArcModules.Q0MinorSplitEngine
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelCerts
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

theorem ledgerEngine_of_currentWeightedChannelCerts :
    Q0MinorEnergyLedgerEngine Δ_canon
      (2 * Q0MinorSSUFromCert.A2)
      (2 * Q0MinorTypeIFromCert.A3) := by
  exact
    ledgerEngine_of_rawLedger <|
      rawLedger_of_currentWeightedChannelCerts
        (hInner := fun {X N} hX hN β =>
          Q0MinorOuterIntegrableResource.hInner (X := X) (N := N) hX hN β)
        (hOuterMaj := fun {X N} hX hN =>
          Q0MinorOuterIntegrableResource.hOuterMaj (X := X) (N := N) hX hN Δ_canon)
        (hOuterMin := fun {X N} hX hN =>
          Q0MinorOuterIntegrableResource.hOuterMin (X := X) (N := N) hX hN Δ_canon)

theorem energyBound16_of_currentWeightedChannelCerts :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ_canon 16 := by
  have hC2 :
      (2 * Q0MinorSSUFromCert.A2 : ℝ) = Q0MinorEnergyFromLedgerCert.C2 := by
    norm_num [Q0MinorEnergyFromLedgerCert.C2, Q0MinorSSUFromCert.A2,
      Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data,
      Goldbach.Cert.MajorArcModules.Q0MinorSSUCertData.data]
  have hC3 :
      (2 * Q0MinorTypeIFromCert.A3 : ℝ) = Q0MinorEnergyFromLedgerCert.C3 := by
    norm_num [Q0MinorEnergyFromLedgerCert.C3, Q0MinorTypeIFromCert.A3,
      Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData.data,
      Goldbach.Cert.MajorArcModules.Q0MinorTypeICertData.data]
  have hLedger :
      Q0MinorEnergyLedgerEngine Δ_canon
        Q0MinorEnergyFromLedgerCert.C2
        Q0MinorEnergyFromLedgerCert.C3 := by
    simpa [hC2, hC3] using ledgerEngine_of_currentWeightedChannelCerts
  exact energyBound16_of_ledger_engine (Δ := Δ_canon) hLedger

end

end Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelEngine
