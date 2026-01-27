import Twin.ChecklistSme
import Twin.ChecklistAxioms
import Twin.PinnedMajorsMainTermModel
import Twin.MinorArcSupBound

/-!
Twin/ChecklistSmeDefaultAxioms.lean
===============================

This module provides a *convenience default* instantiation of the Twin checklist inputs:
we postulate the conventional analytic bounds as explicit `axiom`s and register the corresponding
typeclass instances.

This file is **not** imported by the hypothesis-only entrypoint (`Twin/ChecklistEntrypoint.lean`).
It exists so you can run the end-to-end checklist pipeline on the frozen model without immediately
formalizing the full analytic proofs.
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
    ∀ {q a : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.rpow (Real.log H) B → Nat.Coprime a q →
    ∀ {α : ℝ}, |α - (a : ℝ)/q| ≤ δ / (H + 1) →
      ‖Twin.SW.sumValue Lambda Wwin X H α - Twin.SW.mainTerm What X H α a q‖
        ≤ C * (H / Real.rpow (Real.log X) A)

instance : InstSWBound :=
  ⟨instSW_bound⟩

axiom pinnedMajors_SW_error_envelope_budget :
  Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme)

instance : Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme) :=
  pinnedMajors_SW_error_envelope_budget

/-!
Pinned majors main-term evaluation (Core 2).

We no longer postulate the core statement directly. Instead we postulate the decomposed
`PinnedMajorsMainTermModel` package (deterministic model identity + two numeric bounds),
and derive `PinnedMajorsMainTermEval` from it.
-/

axiom pinnedMajors_mainTerm_model :
  Twin.ChecklistAxioms.PinnedMajorsMainTermModel (sme := sme)

instance : Twin.ChecklistAxioms.PinnedMajorsMainTermModel (sme := sme) :=
  pinnedMajors_mainTerm_model

instance : Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme) :=
  Twin.ChecklistAxioms.pinnedMajorsMainTermEval_of_model (sme := sme)

axiom minorArc_supBound :
  Twin.ChecklistAxioms.MinorArcSupBound (sme := sme)

instance : Twin.ChecklistAxioms.MinorArcSupBound (sme := sme) :=
  minorArc_supBound

instance : Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) :=
  Twin.ChecklistAxioms.minorMassAtSqSumBudget_of_supBound (sme := sme)

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
