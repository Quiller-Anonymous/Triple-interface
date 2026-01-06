import Twin.ChecklistGold
import Twin.ChecklistSme

/-!
Twin/ChecklistGoldDefault.lean
==============================

Specialize the parameterized checklist theorem `Twin.ChecklistGold.twins_in_all_large_windows_of_sme`
to the repo-default frozen-model `sme := Twin.ChecklistSme.sme`.

This file is the only place where the conventional SW major-arc axiom
`Twin.ChecklistSme.instSW_bound` is pulled into the “gold status” surface.
-/

namespace Twin.ChecklistGold

noncomputable section

open Twin

/-- The bundled checklist obligations, using the repo-default frozen-model `sme`. -/
def O' : Twin.ChecklistTargets.Obligations :=
  ((O Twin.ChecklistSme.sme).toObligations)

/-- Gold-status theorem (conditional on the conventional analytic axioms). -/
theorem twins_in_all_large_windows :
    ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
  twins_in_all_large_windows_of_sme Twin.ChecklistSme.sme

end

end Twin.ChecklistGold

