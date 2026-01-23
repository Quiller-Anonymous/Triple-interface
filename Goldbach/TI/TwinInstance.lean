import Mathlib
import Twin.PaperParams
import Twin.TwinMain
import Twin.TIAdapter
import Twin.Bridge
import Twin.Ledger
import Twin.SingularSeries
import Twin.ChecklistAxioms
import Twin.ChecklistSme
import Goldbach.TI.TwinExports

/-!
Goldbach/TwinInstance.lean
==========================

This module is the intended bridge point for exporting **Twin-primes** analytic inputs
from the (eventual) Goldbach/Triple-Interface stack into the `Twin.HasTwinTI` interface.

Status (current):
* We provide a `Twin.HasTwinTI` instance by *reusing* the canonical Twin checklist
  objects (`Twin.ChecklistAxioms`, `Twin.ChecklistSme`) as a temporary stand-in for
  Goldbach-derived TI outputs.
* This file introduces no additional axioms; it just repackages the Twin checklist
  into the interface expected by `Twin.TIAdapter`.

When the Goldbach/TI layer exports genuine Twin-primes analytic bounds, replace the
definitions/lemmas below with Goldbach-derived ones (being careful to avoid import cycles).
-/

noncomputable section
open scoped BigOperators

namespace Goldbach.TI.TwinInstance

open Twin

abbrev P : Twin.GoalAPI.Params := Goldbach.TI.TwinExports.P

noncomputable abbrev ti_eds : ℕ → ℝ := Twin.ChecklistAxioms.eds

theorem ti_desmooth
    [Twin.ChecklistAxioms.DsFourierAtSumBudget]
    [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget] :
    ∀ {X : ℕ}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H ti_eds
        ≤ P.eps * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1) / 3 := by
  intro X hX
  simpa [ti_eds] using (Twin.ChecklistAxioms.desmooth_onWindow_raw (X := X) hX)

section

/-
All Twin-facing TI objects below are currently derived from the Twin checklist route.
To keep this bridge axiom-free, we treat the (conventional) SW major-arc input and the
remaining checklist budgets as explicit typeclass hypotheses.
-/

variable [Twin.ChecklistSme.InstSWBound]

noncomputable abbrev ti_sme :
    Twin.MajorArc.SmoothMajorArcEstimate
      Twin.ChecklistModel.A Twin.ChecklistModel.B
      Twin.ChecklistModel.Λ Twin.ChecklistModel.W Twin.ChecklistModel.W_hat :=
  Twin.ChecklistSme.sme

noncomputable abbrev ti_emin : ℕ → ℝ :=
  Twin.ChecklistAxioms.emin (sme := ti_sme)

theorem ti_l2_minor
    [Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := ti_sme)] :
    ∀ {X : ℕ}, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun n => (ti_emin n) ^ 2)
        ≤ P.eps ^ 2 * (Twin.truncSingularSeries P.S) ^ 2 * ((P.H : ℝ) + 1) / 9 := by
  intro X hX
  simpa [ti_emin] using
    (Twin.ChecklistAxioms.l2_minor_onWindow_raw (sme := ti_sme) (X := X) hX)

theorem ti_pinned
    [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := ti_sme)]
    [Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := ti_sme)] :
    ∀ {X : ℕ}, P.X0 ≤ X →
      (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H ti_emin
          + Twin.Ledger.windowSum X P.H ti_eds
          + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3 := by
  intro X hX
  have hX' : Twin.ChecklistAxioms.P.X0 ≤ X := by
    simpa [P, Twin.Main.P, Twin.ChecklistAxioms.P] using hX
  have h_sme_bound : ti_sme.X0 ≤ (Twin.ChecklistAxioms.P.X0 : ℝ) := by
    -- `ti_sme.X0 = 3` while `Twin.ChecklistAxioms.P.X0 = Twin.PaperParams.X0 = 10000`.
    have hsme : ti_sme.X0 = (3 : ℝ) := by
      simp [ti_sme, Twin.ChecklistSme.sme, Twin.MajorArc.SmoothMajorArcEstimate.ofSW,
        Twin.ChecklistSme.instSW, Twin.ChecklistSme.X0]
    have hNat : (3 : ℕ) ≤ Twin.ChecklistAxioms.P.X0 := by
      simpa [Twin.ChecklistAxioms.P, Twin.PaperParams.P, Twin.PaperParams.X0] using
        (show (3 : ℕ) ≤ Twin.PaperParams.X0 from by
          norm_num [Twin.PaperParams.X0])
    have hReal : (3 : ℝ) ≤ (Twin.ChecklistAxioms.P.X0 : ℝ) := by
      exact_mod_cast hNat
    simpa [hsme] using hReal
  simpa [ti_emin, ti_eds, P, Twin.Main.P, Twin.ChecklistAxioms.P] using
    ((Twin.ChecklistAxioms.gate_onWindow (sme := ti_sme) h_sme_bound).bound (X := X) hX')

noncomputable instance
    [Twin.ChecklistAxioms.DsFourierAtSumBudget] [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget]
    [Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := ti_sme)]
    [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := ti_sme)]
    [Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := ti_sme)] :
    Twin.HasTwinTI P := by
  let E : Goldbach.TI.TwinExports.TIExports P := by
    simpa [Goldbach.TI.TwinExports.P, P] using (Goldbach.TI.TwinExports.GoldbachDerivedExports)
  exact E.toHasTwinTI

end

end Goldbach.TI.TwinInstance
