import Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
import Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
import Goldbach.Cert.MajorArcModules.Q0MinorSplitFromCert

/-!
Bridge from the split ε₁ certificate route back to the existing turnkey energy-engine interface.

This file is purely deterministic:

* a raw full-packet ledger bound already has the right shape for `Q0MinorEnergyLedgerEngine`;
* the outer-integrability hypotheses are supplied by `Q0MinorOuterIntegrableResource`;
* therefore split SSU + Type-I cert bounds can be turned into the legacy cap-16 interface.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSplitEngine

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0MinorSplitFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

theorem ledgerEngine_of_rawLedger
    {Δ C2 C3 : ℝ} (hRaw : Q0MinorRawEnergyLedger Δ C2 C3) :
    Q0MinorEnergyLedgerEngine Δ C2 C3 := by
  refine ⟨hRaw.C2_nonneg, hRaw.C3_nonneg, ?_, ?_, ?_, ?_⟩
  · intro X N hX hN β
    exact Q0MinorOuterIntegrableResource.hInner (X := X) (N := N) hX hN β
  · intro X N hX hN
    exact Q0MinorOuterIntegrableResource.hOuterMaj (X := X) (N := N) hX hN Δ
  · intro X N hX hN
    exact Q0MinorOuterIntegrableResource.hOuterMin (X := X) (N := N) hX hN Δ
  · intro X hX
    simpa [minorPacketEnergy_eq_sum (X := X) (Δ := Δ)] using hRaw.bound (X := X) hX

theorem ledgerEngine_of_certBounds
    (hSSU : canonicalExpansion.NonzeroModeEnergyBound Q0MinorSSUFromCert.U)
    (hTI : canonicalExpansion.ZeroModeEnergyBound Q0MinorTypeIFromCert.U) :
    Q0MinorEnergyLedgerEngine Δ_canon
      (2 * Q0MinorSSUFromCert.A2)
      (2 * Q0MinorTypeIFromCert.A3) := by
  refine ledgerEngine_of_rawLedger ?_
  exact rawLedger_of_certBounds
    (hSSU := hSSU) (hTI := hTI)
    (hInner := fun {X N} hX hN β =>
      Q0MinorOuterIntegrableResource.hInner (X := X) (N := N) hX hN β)
    (hOuterMaj := fun {X N} hX hN =>
      Q0MinorOuterIntegrableResource.hOuterMaj (X := X) (N := N) hX hN Δ_canon)
    (hOuterMin := fun {X N} hX hN =>
      Q0MinorOuterIntegrableResource.hOuterMin (X := X) (N := N) hX hN Δ_canon)

theorem ledgerEngine_of_ssuCertBound
    (hSSU : canonicalExpansion.NonzeroModeEnergyBound Q0MinorSSUFromCert.U) :
    Q0MinorEnergyLedgerEngine Δ_canon
      (2 * Q0MinorSSUFromCert.A2)
      (2 * Q0MinorTypeIFromCert.A3) :=
  ledgerEngine_of_certBounds hSSU Q0MinorTypeIFromCert.zeroModeEnergyBound

theorem energyBound16_of_certBounds
    (hSSU : canonicalExpansion.NonzeroModeEnergyBound Q0MinorSSUFromCert.U)
    (hTI : canonicalExpansion.ZeroModeEnergyBound Q0MinorTypeIFromCert.U) :
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
      Q0MinorEnergyLedgerEngine Δ_canon Q0MinorEnergyFromLedgerCert.C2 Q0MinorEnergyFromLedgerCert.C3 := by
    simpa [hC2, hC3] using
      (ledgerEngine_of_certBounds hSSU hTI)
  exact energyBound16_of_ledger_engine (Δ := Δ_canon) hLedger

theorem energyBound16_of_ssuCertBound
    (hSSU : canonicalExpansion.NonzeroModeEnergyBound Q0MinorSSUFromCert.U) :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ_canon 16 :=
  energyBound16_of_certBounds hSSU Q0MinorTypeIFromCert.zeroModeEnergyBound

end

end Goldbach.Cert.MajorArcModules.Q0MinorSplitEngine
