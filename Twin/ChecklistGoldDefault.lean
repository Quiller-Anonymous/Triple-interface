import Twin.ChecklistGold
import Twin.ChecklistSmeFoolsGold

/-!
Twin/ChecklistGoldDefault.lean
==============================

Specialize the parameterized checklist theorem `Twin.ChecklistGold.twins_in_all_large_windows_of_sme`
to the repo-default frozen-model `sme := Twin.ChecklistSme.sme`.

This file is the only place where the conventional SW major-arc axiom
`Twin/ChecklistSmeFoolsGold.lean` is imported to provide a convenience (“fool's gold”)
instantiation of the checklist hypotheses for the frozen model.
-/

namespace Twin.ChecklistGold

noncomputable section

open Twin

/-- Compatibility for the repo-default frozen-model `sme`: its SW threshold is below the paper basepoint `P.X0`. -/
lemma sme_X0_le_PX0 : (Twin.ChecklistSme.sme.X0) ≤ (P.X0 : ℝ) := by
  -- `Twin.ChecklistSme.X0 = 3` while `P.X0 = 10000` for the fixed paper parameters.
  have hsme : Twin.ChecklistSme.sme.X0 = (3 : ℝ) := by
    simp [Twin.ChecklistSme.sme, Twin.MajorArc.SmoothMajorArcEstimate.ofSW,
      Twin.ChecklistSme.instSW, Twin.ChecklistSme.X0]
  have hPX : (3 : ℝ) ≤ (P.X0 : ℝ) := by
    have hNat : (3 : ℕ) ≤ P.X0 := by
      -- `P.X0` unfolds to `Twin.PaperParams.X0 = 10000`.
      simpa [Twin.ChecklistGold.P, Twin.ChecklistTargets.P, Twin.ChecklistAssumptions.P, Twin.Main.P,
        Twin.PaperParams.P, Twin.PaperParams.X0] using
        (show (3 : ℕ) ≤ Twin.PaperParams.X0 from by
          norm_num [Twin.PaperParams.X0])
    exact_mod_cast hNat
  simpa [hsme] using hPX

/-- The bundled checklist obligations, using the repo-default frozen-model `sme`. -/
def O' : Twin.ChecklistTargets.Obligations :=
  ((O Twin.ChecklistSme.sme sme_X0_le_PX0).toObligations)

/-- Checklist default theorem (conditional on the axiom bundle in `Twin/ChecklistSmeFoolsGold.lean`). -/
theorem twins_in_all_large_windows :
    ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
  twins_in_all_large_windows_of_sme Twin.ChecklistSme.sme sme_X0_le_PX0

end

end Twin.ChecklistGold
