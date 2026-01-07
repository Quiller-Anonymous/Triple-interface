import Twin.ChecklistGoldDefault

/-
  Twin/Gold.lean

  Twin “gold status” entrypoint:
  an end-to-end large-window twin theorem, conditional only on the explicit
  conventional axioms listed in `Twin/ChecklistGold.lean` (and `Twin/ChecklistSme.lean`).

  This file is meant to be *imported* by user-facing umbrella modules.
-/

namespace Twin.Gold

noncomputable section

open Twin

/-- End-to-end large-window twin theorem (checklist route, gold assumptions). -/
theorem twins_in_all_large_windows :
    ∀ {X : ℕ}, Twin.Main.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.Main.P.H :=
  Twin.ChecklistGold.twins_in_all_large_windows

-- Optional: same theorem, but parameterized by an arbitrary `sme` (useful for axiom audits).
theorem twins_in_all_large_windows_of_sme
  (sme : Twin.MajorArc.SmoothMajorArcEstimate
    Twin.ChecklistTargets.A Twin.ChecklistTargets.B
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What)
  [Twin.ChecklistAxioms.DsFourierAtSumBudget] [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget]
  [Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme)]
  [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
  [Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme)] :
  sme.X0 ≤ (Twin.Main.P.X0 : ℝ) →
    ∀ {X : ℕ}, Twin.Main.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.Main.P.H :=
by
  intro hsmeX0 X hX
  have hsmeX0' : sme.X0 ≤ (Twin.ChecklistGold.P.X0 : ℝ) := by
    simpa [Twin.ChecklistGold.P, Twin.Main.P] using hsmeX0
  have hX' : Twin.ChecklistGold.P.X0 ≤ X := by
    simpa [Twin.ChecklistGold.P, Twin.Main.P] using hX
  exact Twin.ChecklistGold.twins_in_all_large_windows_of_sme sme hsmeX0' (X := X) hX'

end

end Twin.Gold
