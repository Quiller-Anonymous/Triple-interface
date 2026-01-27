import Mathlib
import Twin.GoalAPI
import Twin.Ledger
import Twin.Bridge
import Twin.SingularSeries
import Twin.TwinMain
import Twin.ChecklistAxioms
import Twin.ChecklistSme

/-!
Goldbach/TwinTIObjects.lean
===========================

Goldbach-side *placeholder* for the twin-primes TI (triple-interface) outputs.

This module intentionally does not modify any `Twin/*` code. It provides names for the
objects a future Goldbach/TI engine should export to the Twin pipeline:

* `ti_emin`, `ti_eds` : error terms on `ℕ`
* three uniform-on-window inequalities matching `Twin.HasTwinTI`

Current status:
* These outputs are **derived** from the Twin checklist development (`Twin.ChecklistAxioms`
  instantiated at `Twin.ChecklistSme.sme`), so all remaining analytic inputs are explicit
  hypotheses (typeclass parameters) rather than in-repo `axiom` declarations.

Long-run plan:
* Replace the definitions/lemmas below by genuinely Goldbach-derived TI outputs, keeping the
  same names and statements to avoid churn elsewhere.
-/

noncomputable section
open scoped BigOperators

namespace Goldbach
namespace TI.TwinTI

open Twin

/-- The concrete Twin parameters we export to (paper params). -/
abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P

/-!
We treat the Twin checklist analytic inputs as explicit hypotheses (typeclass parameters).
This keeps the Goldbach↔Twin hook axiom-free.
-/

variable [Twin.ChecklistSme.InstSWBound]

noncomputable abbrev ti_sme :
    Twin.MajorArc.SmoothMajorArcEstimate
      Twin.ChecklistModel.A Twin.ChecklistModel.B
      Twin.ChecklistModel.Λ Twin.ChecklistModel.W Twin.ChecklistModel.W_hat :=
  Twin.ChecklistSme.sme

/-- Minor-arc / CLS error term exported from the Goldbach TI engine (twins specialization). -/
noncomputable abbrev ti_emin : ℕ → ℝ :=
  Twin.ChecklistAxioms.emin (sme := ti_sme)

/-- Desmoothing / prime-power budget term exported from the Goldbach TI engine (twins specialization). -/
noncomputable abbrev ti_eds : ℕ → ℝ :=
  Twin.ChecklistAxioms.eds

/-- Minor-arc L² window bound (uniform in `X ≥ X0`). -/
theorem l2_minor_onWindow :
  [Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := ti_sme)] →
  ∀ {X}, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (ti_emin n) ^ 2)
      ≤ P.eps ^ 2 * (Twin.fullTruncSingularSeries P.S) ^ 2 * ((P.H : ℝ) + 1) / 9
:= by
  intro _hMinor
  intro X hX
  -- This is exactly the checklist lemma specialized to `ti_sme`; no unfolding of `emin` needed.
  simpa [P, Twin.ChecklistAxioms.P, Twin.ChecklistAxioms.SS, Twin.fullTruncSingularSeries] using
    (Twin.ChecklistAxioms.l2_minor_onWindow (sme := ti_sme) (X := X) hX)

/-- Desmoothing / prime-power budget bound (uniform in `X ≥ X0`). -/
theorem desmooth_onWindow :
  [Twin.ChecklistAxioms.DsFourierAtSumBudget] → [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget] →
  ∀ {X}, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H ti_eds
      ≤ P.eps * Twin.fullTruncSingularSeries P.S * ((P.H : ℝ) + 1) / 3
:= by
  intro _hF _hPP
  intro X hX
  simpa [P, Twin.ChecklistAxioms.P, Twin.ChecklistAxioms.SS, Twin.fullTruncSingularSeries] using
    (Twin.ChecklistAxioms.desmooth_onWindow (X := X) hX)

/-- Pinned gate inequality on the window (uniform in `X ≥ X0`). -/
theorem pinned_onWindow :
  [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := ti_sme)] →
  [Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := ti_sme)] →
  ∀ {X}, P.X0 ≤ X →
    (1 - P.eps) * Twin.fullTruncSingularSeries P.S * ((P.H : ℝ) + 1)
      ≤ Twin.Bridge.localizedTwinMass X P.H
        + Twin.Ledger.windowSum X P.H ti_emin
        + Twin.Ledger.windowSum X P.H ti_eds
        + (P.eps * Twin.fullTruncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3
:= by
  intro _hSW _hMain
  intro X hX
  have hX' : Twin.ChecklistAxioms.P.X0 ≤ X := by
    simpa [P, Twin.ChecklistAxioms.P] using hX
  have hsmeX0 : Twin.ChecklistSme.sme.X0 ≤ (Twin.ChecklistAxioms.P.X0 : ℝ) := by
    -- `Twin.ChecklistSme.X0 = 3` while `Twin.ChecklistAxioms.P.X0 = Twin.PaperParams.X0 = 10000`.
    have hsme : Twin.ChecklistSme.sme.X0 = (3 : ℝ) := by
      simp [ti_sme, Twin.ChecklistSme.sme, Twin.MajorArc.SmoothMajorArcEstimate.ofSW,
        Twin.ChecklistSme.instSW, Twin.ChecklistSme.X0]
    have hNat : (3 : ℕ) ≤ Twin.ChecklistAxioms.P.X0 := by
      simpa [Twin.ChecklistAxioms.P, Twin.PaperParams.P, Twin.PaperParams.X0] using
        (show (3 : ℕ) ≤ Twin.PaperParams.X0 from by
          norm_num [Twin.PaperParams.X0])
    have hReal : (3 : ℝ) ≤ (Twin.ChecklistAxioms.P.X0 : ℝ) := by
      exact_mod_cast hNat
    simpa [hsme] using hReal
  simpa [P, Twin.ChecklistAxioms.P, Twin.ChecklistAxioms.SS, Twin.fullTruncSingularSeries] using
    ((Twin.ChecklistAxioms.gate_onWindow (sme := ti_sme) hsmeX0).bound (X := X) hX')

end TwinTI
end TI
end Goldbach
