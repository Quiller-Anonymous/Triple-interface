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
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What) :
    ∀ {X : ℕ}, Twin.Main.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.Main.P.H :=
  Twin.ChecklistGold.twins_in_all_large_windows_of_sme sme

end

end Twin.Gold
