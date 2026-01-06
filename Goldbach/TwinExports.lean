import Mathlib
import Twin.GoalAPI
import Twin.Ledger
import Twin.Bridge
import Twin.TIAdapter
import Twin.ChecklistAxioms
import Twin.ChecklistSme

/-!
Goldbach/TwinExports.lean
=========================

Goldbach-side interface for exporting (eventually Goldbach-derived) analytic inputs to the
Twin-primes project, without modifying any `Twin/*` files.

Design goal:
* Provide a stable, non-typeclass record with exactly the fields Twin expects (the `HasTwinTI`
  obligations), so `Goldbach/TwinInstance.lean` can be a thin adapter.
* Today, the implementation is simply a wrapper around `Twin.ChecklistAxioms` / `Twin.ChecklistSme`.
* Later, we can replace `checklistExports` by a genuinely Goldbach-derived construction, while keeping
  the adapter stable.
-/

noncomputable section
open scoped BigOperators

namespace Goldbach
namespace TwinExports

open Twin

/-- The parameters we export for (currently the canonical paper params). -/
abbrev P : Twin.GoalAPI.Params := Twin.Main.P

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
## Current implementation (reuses the Twin checklist)

This is intentionally the only implementation shipped on the Goldbach side right now.
It introduces no new axioms: it just re-exports the existing Twin checklist axioms.
-/

/-- The checklist smooth-major-arc estimate used to define `emin`. -/
noncomputable abbrev ti_sme :
    Twin.MajorArc.SmoothMajorArcEstimate
      Twin.ChecklistModel.A Twin.ChecklistModel.B
      Twin.ChecklistModel.Λ Twin.ChecklistModel.W Twin.ChecklistModel.W_hat :=
  Twin.ChecklistSme.sme

/-- The checklist `emin` function (minor-arc error term). -/
noncomputable abbrev ti_emin : ℕ → ℝ :=
  Twin.ChecklistAxioms.emin (sme := ti_sme)

/-- The checklist `eds` function (desmoothing / prime-power budget term). -/
noncomputable abbrev ti_eds : ℕ → ℝ :=
  Twin.ChecklistAxioms.eds

/-- Pack the Twin checklist into `TIExports` (Goldbach-side export record). -/
noncomputable def checklistExports : TIExports P := by
  classical
  refine
    { emin := ti_emin
      eds := ti_eds
      l2_minor := ?_
      desmooth := ?_
      pinned := ?_ }
  · intro X hX
    simpa [ti_emin] using
      (Twin.ChecklistAxioms.l2_minor_onWindow_raw (sme := ti_sme) (X := X) hX)
  · intro X hX
    simpa [ti_eds] using (Twin.ChecklistAxioms.desmooth_onWindow_raw (X := X) hX)
  · intro X hX
    -- `gate_onWindow` is derived from the (axiomatized) pinned-major evaluation + transfer.
    have hX' : Twin.ChecklistAxioms.P.X0 ≤ X := by
      simpa [P, Twin.Main.P, Twin.ChecklistAxioms.P] using hX
    simpa [ti_emin, ti_eds, P, Twin.Main.P, Twin.ChecklistAxioms.P] using
      ((Twin.ChecklistAxioms.gate_onWindow (sme := ti_sme)).bound (X := X) hX')

end TwinExports
end Goldbach
