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
  axioms/objects (`Twin.ChecklistAxioms`, `Twin.ChecklistSme`).
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

/-!
Current implementation strategy
-------------------------------

Until the Goldbach/TI layer exports genuine Twin-primes analytic bounds, we *reuse* the
canonical Twin checklist objects (`Twin.ChecklistAxioms`) as the source of a `HasTwinTI`
instance. This removes the redundant "scrapbook axioms" that previously lived here:
the only remaining axioms are the paper-facing checklist axioms inside `Twin/ChecklistAxioms.lean`
and `Twin/ChecklistSme.lean`.

When the TI proofs exist, replace `ti_*` below with Goldbach-derived definitions/lemmas.
-/

noncomputable abbrev ti_eds  : ℕ → ℝ := Twin.ChecklistAxioms.eds
noncomputable abbrev ti_sme :
    Twin.MajorArc.SmoothMajorArcEstimate
      Twin.ChecklistModel.A Twin.ChecklistModel.B
      Twin.ChecklistModel.Λ Twin.ChecklistModel.W Twin.ChecklistModel.W_hat :=
  Twin.ChecklistSme.sme

noncomputable abbrev ti_emin : ℕ → ℝ := Twin.ChecklistAxioms.emin (sme := ti_sme)

theorem ti_l2_minor :
  ∀ {X : ℕ}, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (ti_emin n)^2)
      ≤ P.eps^2 * (Twin.truncSingularSeries P.S)^2 * ((P.H : ℝ) + 1) / 9 := by
  intro X hX
  simpa [ti_emin] using (Twin.ChecklistAxioms.l2_minor_onWindow_raw (sme := ti_sme) (X := X) hX)

theorem ti_desmooth :
  ∀ {X : ℕ}, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H ti_eds
      ≤ P.eps * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1) / 3 := by
  intro X hX
  simpa [ti_eds] using (Twin.ChecklistAxioms.desmooth_onWindow_raw (X := X) hX)

theorem ti_pinned :
  ∀ {X : ℕ}, P.X0 ≤ X →
    (1 - P.eps) * Twin.truncSingularSeries P.S * ((P.H : ℝ) + 1)
      ≤ Twin.Bridge.localizedTwinMass X P.H
        + Twin.Ledger.windowSum X P.H ti_emin
        + Twin.Ledger.windowSum X P.H ti_eds
        + (P.eps * Twin.truncSingularSeries P.S) * ((P.H : ℝ) + 1) / 3 := by
  intro X hX
  -- `gate_onWindow` is derived from the (axiomatized) pinned-major evaluation + transfer.
  have hX' : Twin.ChecklistAxioms.P.X0 ≤ X := by
    simpa [P, Twin.Main.P, Twin.ChecklistAxioms.P] using hX
  have h_sme_bound : ti_sme.X0 ≤ ↑Twin.ChecklistAxioms.P.X0 := by
    -- `ti_sme.X0 = 3` while `Twin.ChecklistAxioms.P.X0 = Twin.PaperParams.X0 = 10000`.
    have hsme : ti_sme.X0 = (3 : ℝ) := by
      simp [ti_sme, Twin.ChecklistSme.sme, Twin.MajorArc.SmoothMajorArcEstimate.ofSW,
        Twin.ChecklistSme.instSW, Twin.ChecklistSme.X0]
    have hNat : (3 : ℕ) ≤ Twin.ChecklistAxioms.P.X0 := by
      -- unfold the concrete paper parameters
      simpa [Twin.ChecklistAxioms.P, Twin.PaperParams.P, Twin.PaperParams.X0] using
        (show (3 : ℕ) ≤ Twin.PaperParams.X0 from by
          norm_num [Twin.PaperParams.X0])
    have hReal : (3 : ℝ) ≤ (Twin.ChecklistAxioms.P.X0 : ℝ) := by
      exact_mod_cast hNat
    simpa [hsme] using hReal
  simpa [ti_emin, ti_eds, P, Twin.Main.P, Twin.ChecklistAxioms.P] using
    ((Twin.ChecklistAxioms.gate_onWindow (sme := ti_sme) h_sme_bound).bound (X := X) hX')

noncomputable instance : Twin.HasTwinTI P := by
  -- Route through the Goldbach-side export record so we can swap in Goldbach-derived
  -- TI outputs later without changing the adapter shape.
  let E : Goldbach.TI.TwinExports.TIExports P := by
    simpa [Goldbach.TI.TwinExports.P, P] using (Goldbach.TI.TwinExports.GoldbachDerivedExports)
  exact E.toHasTwinTI

end Goldbach.TI.TwinInstance
