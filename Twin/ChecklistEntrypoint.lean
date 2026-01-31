import Twin.ChecklistRoute
import Twin.PinnedMajorsMainTermModel
import Twin.MinorArcDispersionEnergy

/-
  Twin/ChecklistEntrypoint.lean

  Twin checklist entrypoint (hypothesis-only):
  an end-to-end large-window twin theorem whose remaining analytic inputs are explicit
  *hypotheses* (typeclass parameters), not in-repo `axiom` declarations.

  For a convenience default instantiation that postulates those hypotheses as
  explicit `axiom`s, see `Twin/ChecklistEntrypointDefault.lean`.

  This file is meant to be *imported* by user-facing umbrella modules.
-/

namespace Twin.ChecklistEntrypoint

noncomputable section

open Twin

/-!
`Twin.ChecklistRoute.twins_in_all_large_windows_of_sme` is already the core checklist statement:
it is axiom-free and only assumes the standard analytic inputs as explicit hypotheses.
-/

/-- End-to-end large-window twin theorem (checklist route; hypothesis-only). -/
theorem twins_in_all_large_windows
  (sme : Twin.MajorArc.SmoothMajorArcEstimate
    Twin.ChecklistTargets.A Twin.ChecklistTargets.B
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What)
  [Twin.ChecklistAxioms.DsFourierAtSumBudget] [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget]
  [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
  [Twin.ChecklistAxioms.PinnedMajorsMainTermModel (sme := sme)]
  [Twin.ChecklistAxioms.MinorArcDispersionEnergyBound (sme := sme)] :
  sme.X0 ≤ (Twin.Main.P.X0 : ℝ) →
    ∀ {X : ℕ}, Twin.Main.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.Main.P.H :=
by
  intro hsmeX0 X hX
  -- Convert the conventional “dispersion energy” hypothesis into the exact checklist Core 1 budget.
  haveI : Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) :=
    Twin.ChecklistAxioms.minorMassAtSqSumBudget_of_dispersionEnergy (sme := sme)
  have hsmeX0' : sme.X0 ≤ (Twin.ChecklistRoute.P.X0 : ℝ) := by
    simpa [Twin.ChecklistRoute.P, Twin.Main.P] using hsmeX0
  have hX' : Twin.ChecklistRoute.P.X0 ≤ X := by
    simpa [Twin.ChecklistRoute.P, Twin.Main.P] using hX
  exact Twin.ChecklistRoute.twins_in_all_large_windows_of_sme sme hsmeX0' (X := X) hX

-- Optional: same theorem, but parameterized by an arbitrary `sme` (useful for axiom audits).
theorem twins_in_all_large_windows_of_sme
  (sme : Twin.MajorArc.SmoothMajorArcEstimate
    Twin.ChecklistTargets.A Twin.ChecklistTargets.B
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What)
  [Twin.ChecklistAxioms.DsFourierAtSumBudget] [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget]
  [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme)]
  [Twin.ChecklistAxioms.PinnedMajorsMainTermModel (sme := sme)]
  [Twin.ChecklistAxioms.MinorArcDispersionEnergyBound (sme := sme)] :
  sme.X0 ≤ (Twin.Main.P.X0 : ℝ) →
    ∀ {X : ℕ}, Twin.Main.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.Main.P.H :=
by
  intro hsmeX0 X hX
  haveI : Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) :=
    Twin.ChecklistAxioms.minorMassAtSqSumBudget_of_dispersionEnergy (sme := sme)
  have hsmeX0' : sme.X0 ≤ (Twin.ChecklistRoute.P.X0 : ℝ) := by
    simpa [Twin.ChecklistRoute.P, Twin.Main.P] using hsmeX0
  have hX' : Twin.ChecklistRoute.P.X0 ≤ X := by
    simpa [Twin.ChecklistRoute.P, Twin.Main.P] using hX
  exact Twin.ChecklistRoute.twins_in_all_large_windows_of_sme sme hsmeX0' (X := X) hX'

end

end Twin.ChecklistEntrypoint
