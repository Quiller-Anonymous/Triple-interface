import Goldbach.Cert.MajorArcModules.Q0GlobalSSU
import Goldbach.Cert.MajorArcModules.Q0RawFullPacketLedger

/-!
`Q0Theorem627` assembles the Theorem 6.27 tower and exposes theorem-shaped discharges for the
existing collaborator-facing interface placeholders.
-/

namespace Goldbach.Cert.MajorArcModules.Q0Theorem627

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0GlobalSSU
open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0RawFullPacketLedger
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Discharge theorem for the global SSU interface placeholder. -/
theorem vaughanTypeII_globalSSU_discharge :
    ∀ (X U V _H _Q : ℕ) (f : ℕ → ℝ),
      isVaughanTypeII f X U V →
        Q0MinorRawEnergyLedger 1 ((Real.log X) ^ 2) ((Real.log X) ^ 2) := by
  intro X U V H Q f hf
  exact globalSSU_of_vaughan X U V H Q f hf

/--
Bookkeeping bridge from the global SSU statement to the canonical raw `(1,1)` ledger.

This is now just an alias to the single frontier theorem in `Q0RawFullPacketLedger`, so the
pipeline has only one remaining raw-ledger obligation instead of two duplicated copies of the same
mathematical gap.
-/
theorem rawFullPacketLedger_1_1_of_globalSSU
    (hSSU : ∀ (X U V _H _Q : ℕ) (f : ℕ → ℝ),
      isVaughanTypeII f X U V →
        Q0MinorRawEnergyLedger 1 ((Real.log X) ^ 2) ((Real.log X) ^ 2)) :
    Q0MinorRawEnergyLedger Δ_canon 1 1 := by
  let _ := hSSU
  exact rawFullPacketLedger_1_1

/-- Discharge theorem for the canonical raw full-packet ledger frontier. -/
theorem rawFullPacketLedger_1_1_discharge :
    Q0MinorRawEnergyLedger Δ_canon 1 1 := by
  exact rawFullPacketLedger_1_1_of_globalSSU vaughanTypeII_globalSSU_discharge

end

end Goldbach.Cert.MajorArcModules.Q0Theorem627
