import Mathlib
import Twin.GoalAPI
import Twin.Ledger
import Twin.Bridge
import Twin.TIAdapter
import Goldbach.TI.TwinTIObjects

/-!
Goldbach/TwinExports.lean
=========================

Goldbach-side interface for exporting (eventually Goldbach-derived) analytic inputs to the
Twin-primes project, without modifying any `Twin/*` files.

Design goal:
* Provide a stable, non-typeclass record with exactly the fields Twin expects (the `HasTwinTI`
  obligations), so `Goldbach/TI/TwinInstance.lean` can be a thin adapter.
* Today, the implementation is backed by the Goldbach-side TI placeholders in `Goldbach/TI/TwinTIObjects.lean`.
* Later, we can replace those axioms by genuinely Goldbach-derived theorems, while keeping the adapter stable.
-/

noncomputable section
open scoped BigOperators

namespace Goldbach
namespace TI.TwinExports

open Twin

/-- The parameters we export for (currently the canonical paper params). -/
abbrev P : Twin.GoalAPI.Params := Goldbach.TI.TwinTI.P

/-- A non-typeclass record packaging the TI outputs expected by Twin. -/
structure TIExports (P : Twin.GoalAPI.Params) where
  emin : ℕ → ℝ
  eds  : ℕ → ℝ
  l2_minor :
    ∀ {X}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun n => (emin n) ^ 2)
        ≤ P.eps ^ 2 * (Twin.truncSingularSeries P.S) ^ 2 * ((P.H : ℝ) + 1) / 9
  desmooth :
    ∀ {X}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H eds
        ≤ P.eps * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1) / 3
  pinned :
    ∀ {X}, P.X0 ≤ X →
      (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds
          + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3

/-- Convert packaged exports into the typeclass interface `Twin.HasTwinTI`. -/
noncomputable def TIExports.toHasTwinTI {P : Twin.GoalAPI.Params} (E : TIExports P) :
    Twin.HasTwinTI P :=
  { emin := E.emin
    eds := E.eds
    l2_minor := by intro X hX; simpa using (E.l2_minor (X := X) hX)
    desmooth := by intro X hX; simpa using (E.desmooth (X := X) hX)
    pinned := by intro X hX; simpa using (E.pinned (X := X) hX) }

/-!
## Goldbach-derived exports (twins)

This is the intended long-run wiring: the Twin pipeline consumes a `Twin.HasTwinTI` instance,
while the Goldbach side exports a small bundle of TI outputs.

At the moment, the exported functions and bounds are still *derived from* the Twin checklist
hypotheses (see `Twin/ChecklistAxioms.lean`), via `Goldbach/TI/TwinTIObjects.lean`.
This keeps all Twin-facing assumptions on the Goldbach side so that Twin can remain stable
while the TI layer is developed.
-/

/-- The Goldbach/TI engine exports packaged in the `TIExports` record. -/
noncomputable def GoldbachDerivedExports
    [Twin.ChecklistSme.InstSWBound]
    [Twin.ChecklistAxioms.DsFourierAtSumBudget] [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget]
    [Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := Goldbach.TI.TwinTI.ti_sme)]
    [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := Goldbach.TI.TwinTI.ti_sme)]
    [Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := Goldbach.TI.TwinTI.ti_sme)] :
    TIExports P :=
  { emin := Goldbach.TI.TwinTI.ti_emin
    eds := Goldbach.TI.TwinTI.ti_eds
    l2_minor := by
      intro X hX
      simpa using (Goldbach.TI.TwinTI.l2_minor_onWindow (X := X) hX)
    desmooth := by
      intro X hX
      simpa using (Goldbach.TI.TwinTI.desmooth_onWindow (X := X) hX)
    pinned := by
      intro X hX
      simpa using (Goldbach.TI.TwinTI.pinned_onWindow (X := X) hX) }

end TwinExports
end TI
end Goldbach
