import Twin.ChecklistGold

/-
  Twin/Gold.lean

  Twin “gold status” entrypoint:
  an end-to-end large-window twin theorem whose remaining analytic inputs are explicit
  *hypotheses* (typeclass parameters), not in-repo `axiom` declarations.

  For a convenience “fool's gold” instantiation that postulates those hypotheses as
  explicit `axiom`s, see `Twin/ChecklistGoldDefault.lean`.

  This file is meant to be *imported* by user-facing umbrella modules.
-/

namespace Twin.Gold

noncomputable section

open Twin

/-!
`Twin.ChecklistGold.twins_in_all_large_windows_of_sme` is already the gold-grade statement:
it is axiom-free and only assumes the standard analytic inputs as explicit hypotheses.
-/

/-- End-to-end large-window twin theorem (checklist route, gold-grade hypotheses). -/
theorem twins_in_all_large_windows
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
  exact Twin.ChecklistGold.twins_in_all_large_windows_of_sme sme hsmeX0' (X := X) hX

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
