import Goldbach.Cert.MajorArcModules.Q0GlobalSSU
import Goldbach.Cert.MajorArcModules.Q0RawFullPacketLedger

/-!
`Q0Theorem627` preserves theorem-shaped compatibility wrappers around the older Theorem 6.27
interfaces. These wrappers do not constitute an application to the balanced von Mangoldt
remainder; the raw `(1,1)` endpoint remains axiom-backed.
-/

namespace Goldbach.Cert.MajorArcModules.Q0Theorem627

open Goldbach

open Goldbach.Cert.MajorArcModules.Q0GlobalSSU
open Goldbach.Cert.MajorArcModules.Q0MinorPacketOrthogonalityCore
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0RawFullPacketLedger
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- Compatibility discharge for the global SSU interface placeholder. -/
theorem vaughanTypeII_globalSSU_discharge :
    ∀ (X U V _H _Q : ℕ) (f : ℕ → ℝ),
      isVaughanTypeII f X U V →
        Q0MinorRawEnergyLedger 1 ((Real.log X) ^ 2) ((Real.log X) ^ 2) := by
  intro X U V H Q f hf
  exact globalSSU_of_vaughan X U V H Q f hf

/--
Compatibility bridge to the canonical raw `(1,1)` ledger.

The argument intentionally does not use `hSSU`; it returns the independent axiom-backed ledger.
Consequently this theorem must not be cited as evidence that global SSU proves that ledger.
-/
theorem rawFullPacketLedger_1_1_of_globalSSU
    (hSSU : ∀ (X U V _H _Q : ℕ) (f : ℕ → ℝ),
      isVaughanTypeII f X U V →
        Q0MinorRawEnergyLedger 1 ((Real.log X) ^ 2) ((Real.log X) ^ 2)) :
    Q0MinorRawEnergyLedger Δ_canon 1 1 := by
  let _ := hSSU
  exact rawFullPacketLedger_1_1

/-- Compatibility export of the axiom-backed canonical raw full-packet ledger. -/
theorem rawFullPacketLedger_1_1_discharge :
    Q0MinorRawEnergyLedger Δ_canon 1 1 := by
  exact rawFullPacketLedger_1_1_of_globalSSU vaughanTypeII_globalSSU_discharge

end

end Goldbach.Cert.MajorArcModules.Q0Theorem627
