import Twin.ChecklistRouteDefault

/-!
Twin/ChecklistEntrypointDefault.lean
=====================

This is the **default end-to-end Twin entrypoint** used for the repository build.

It specializes the checklist pipeline to the repo-default frozen model `sme := Twin.ChecklistSme.sme`
and therefore *imports the default axiom bundle* from `Twin/ChecklistSmeDefaultAxioms.lean`
via `Twin/ChecklistRouteDefault.lean`.

For the hypothesis-only entrypoint, see `Twin/ChecklistEntrypoint.lean`.
-/

namespace Twin.ChecklistEntrypointDefault

noncomputable section

open Twin

/-- End-to-end large-window twin theorem for the repo-default frozen model.

This theorem is only as strong as the axioms imported by `Twin/ChecklistRouteDefault.lean`.
-/
theorem twins_in_all_large_windows :
    ∀ {X : ℕ}, Twin.ChecklistRoute.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.ChecklistRoute.P.H :=
  Twin.ChecklistRoute.twins_in_all_large_windows

end

end Twin.ChecklistEntrypointDefault
