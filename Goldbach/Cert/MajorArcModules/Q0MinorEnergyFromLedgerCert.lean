import Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec
import Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData

/-!
`MajorArcModules/Q0MinorEnergyFromLedgerCert` wires the generated ε₁-ledger constants certificate
into the ε₁ engine interface.

This file contains **no analytic number theory**: it only says that if an analytic proof provides a
`Q0MinorEnergyLedgerEngine` with the certified constants, then ε₁ (energy ≤ 16) follows.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MinorEngineSpec
open Goldbach.Cert.MajorArcModules.Q0MinorEnergyLedger
open Goldbach.Cert.MajorArcModules.Q0MinorLedgerCert
open Goldbach.Cert.MajorArcModules.Q0MinorLedgerCertData

noncomputable section

abbrev C2 : ℝ := (data.C2 : ℝ)
abbrev C3 : ℝ := (data.C3 : ℝ)

lemma data_valid' : data.Valid := data_valid

/--
If an analytic proof supplies the ledger-shaped ε₁ engine with the certificate’s constants, then
we get the uniform ε₁ energy bound with cap `16`.
-/
theorem engine16_of_ledger_engine {Δ : ℝ} (h : Q0MinorEnergyLedgerEngine Δ C2 C3) :
    Q0MinorEnergyEngine Δ 16 := by
  -- `data_valid` is generated and checked by `native_decide`.
  simpa [C2, C3] using
    (Data.engine16_of_ledger_of_valid (Δ := Δ) (d := data) h data_valid')

/-- The turnkey-facing ε₁ interface: `Q0MinorEnergyBound Δ 16`. -/
theorem energyBound16_of_ledger_engine {Δ : ℝ} (h : Q0MinorEnergyLedgerEngine Δ C2 C3) :
    Goldbach.Cert.MajorArcModules.Q0MinorBound.Q0MinorEnergyBound Δ 16 :=
  q0MinorEnergyBound_of_engine (Δ := Δ) (E := (16 : ℝ)) (engine16_of_ledger_engine (Δ := Δ) h)

end

end Goldbach.Cert.MajorArcModules.Q0MinorEnergyFromLedgerCert

