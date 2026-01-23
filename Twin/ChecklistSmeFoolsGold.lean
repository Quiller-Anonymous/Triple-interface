import Twin.ChecklistSme
import Twin.ChecklistAxioms

/-!
Twin/ChecklistSmeFoolsGold.lean
===============================

This module provides a *convenience* “fool's gold” instantiation of the Twin checklist inputs:
we postulate the conventional analytic bounds as explicit `axiom`s and register the corresponding
typeclass instances.

This file is **not** imported by the gold-status entrypoint (`Twin/Gold.lean`). It exists so you
can experiment with the end-to-end Twin pipeline without immediately formalizing the full analytic
proofs.
-/

namespace Twin.ChecklistSme

noncomputable section

open Twin

/-!
### Conventional analytic inputs (postulated as axioms)

These are the same six conventional analytic obligations previously carried directly in
`Twin/ChecklistSme.lean`; they have been moved here so the “gold” import graph is axiom-free.
-/

axiom instSW_bound :
  ∀ {X H : ℝ}, X0 ≤ X → 1 ≤ H →
    ∀ {q a : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.rpow (Real.log X) B → Nat.Coprime a q →
    ∀ {α : ℝ}, |α - (a : ℝ)/q| ≤ δ / (H + 1) →
      ‖Twin.SW.sumValue Lambda Wwin X H α - Twin.SW.mainTerm What X H α a q‖
        ≤ C * (X / Real.rpow (Real.log X) A)

instance : InstSWBound :=
  ⟨instSW_bound⟩

axiom pinnedMajors_SW_error_envelope_budget :
  Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme)

instance : Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme) :=
  pinnedMajors_SW_error_envelope_budget

axiom pinnedMajors_mainTerm_eval :
  Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme)

instance : Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme) :=
  pinnedMajors_mainTerm_eval

axiom minorMassAt_sq_sum_bigIcc_budget :
  Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme)

instance : Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) :=
  minorMassAt_sq_sum_bigIcc_budget

axiom dsFourierAt_sum_bigIcc_budget :
  Twin.ChecklistAxioms.DsFourierAtSumBudget

instance : Twin.ChecklistAxioms.DsFourierAtSumBudget :=
  dsFourierAt_sum_bigIcc_budget

axiom dsPrimePowerAt_sum_bigIcc_budget :
  Twin.ChecklistAxioms.DsPrimePowerAtSumBudget

instance : Twin.ChecklistAxioms.DsPrimePowerAtSumBudget :=
  dsPrimePowerAt_sum_bigIcc_budget

end

end Twin.ChecklistSme

