import Mathlib
import Twin.GoalAPI
import Twin.Ledger
import Twin.Bridge
import Twin.SingularSeries
import Twin.TwinMain

/-!
Goldbach/TwinTIObjects.lean
===========================

Goldbach-side *placeholder* for the twin-primes TI (triple-interface) outputs.

This module intentionally does not modify any `Twin/*` code. It provides names for the
objects a future Goldbach/TI engine should export to the Twin pipeline:

* `ti_emin`, `ti_eds` : error terms on `ℕ`
* three uniform-on-window inequalities matching `Twin.HasTwinTI`

At the moment these are stated as axioms. The purpose is to give a stable namespace and
API shape so that later work can replace these axioms by genuine Goldbach-derived theorems.
-/

noncomputable section
open scoped BigOperators

namespace Goldbach
namespace TI.TwinTI

open Twin

/-- The concrete Twin parameters we export to (paper params). -/
abbrev P : Twin.GoalAPI.Params := Twin.Main.P

/-- Minor-arc / CLS error term exported from the Goldbach TI engine (twins specialization). -/
axiom ti_emin : ℕ → ℝ

/-- Desmoothing / prime-power budget term exported from the Goldbach TI engine (twins specialization). -/
axiom ti_eds : ℕ → ℝ

/-- Minor-arc L² window bound (uniform in `X ≥ X0`). -/
axiom l2_minor_onWindow :
  ∀ {X}, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (ti_emin n) ^ 2)
      ≤ P.eps ^ 2 * (Twin.truncSingularSeries P.S) ^ 2 * ((P.H : ℝ) + 1) / 9

/-- Desmoothing / prime-power budget bound (uniform in `X ≥ X0`). -/
axiom desmooth_onWindow :
  ∀ {X}, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H ti_eds
      ≤ P.eps * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1) / 3

/-- Pinned gate inequality on the window (uniform in `X ≥ X0`). -/
axiom pinned_onWindow :
  ∀ {X}, P.X0 ≤ X →
    (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
      ≤ Twin.Bridge.localizedTwinMass X P.H
        + Twin.Ledger.windowSum X P.H ti_emin
        + Twin.Ledger.windowSum X P.H ti_eds
        + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3

end TwinTI
end TI
end Goldbach
