import Twin.ChecklistTargets
import Twin.ChecklistAxioms

/-
  Twin/ChecklistGold.lean

  “Gold status” (Twin, checklist route):
  we allow *conventional* analytic inputs to be postulated as axioms (with citations),
  and then the remaining wiring is fully machine-checked.

  This file does NOT touch Goldbach.
-/

namespace Twin.ChecklistGold

noncomputable section

open Twin

abbrev P : Twin.GoalAPI.Params := Twin.ChecklistTargets.P
abbrev SS : ℝ := Twin.ChecklistTargets.SS

/-
Conventional analytic inputs (postulated):

We follow the intended “analytic `majMass`” checklist route:
`majMass X` is the checklist “major-arc mass” used by `Twin.Main.windows_largeX_of_checklist`.

Current status (easiest-first development):
- `Twin.ChecklistAxioms.majMassAnalytic` is the literal major-arc integral definition (paper §11/§14).
- `Twin.ChecklistAxioms.majMass` is set to `majMassAnalytic` (paper-faithful choice).
  The remaining paper-facing input on the **pinned majors** side is the raw inequality
  `Twin.ChecklistAxioms.pinnedMajors_lower_raw`; `Twin.ChecklistAxioms.h_lower` is derived from it,
  and `Twin.ChecklistAxioms.h_transfer` is now proved from the analytic definitions of `emin/eds`.

Paper anchor for `Twin.ChecklistAxioms.gate_onWindow` (equivalently, the derived `pinnedMajors_lower`):
  §14.2 “Pinned major arcs, and closing the gate”, combined with
  Lemma 14.5 (Fourier tail control) and Corollary 12.8 (orthogonality / bank margin).

Exact inequality to import (MajorArcLower form):
  for all `X ≥ P.X0`,
    majMass X ≥ (1 - P.eps) * SS * ((P.H:ℝ)+1) - (P.eps * SS) * ((P.H:ℝ)+1) / 3.

Here `SS := truncSingularSeries(P.S)` is fixed (paper §11.1), and the `/3` term is the tail cap
coming from the pin Fourier-tail and orthogonality bookkeeping.
-/

open Twin.ChecklistAxioms

-- We fix the `sme` and `ss_pos` fields to the repo-defaults, so the remaining
-- conventional obligations are exactly the four window-inequalities + `emin/eds/majMass`.
def O
  (sme : Twin.MajorArc.SmoothMajorArcEstimate
    Twin.ChecklistTargets.A Twin.ChecklistTargets.B
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What) :
  Twin.ChecklistTargets.ObligationsExplicit :=
{ sme := sme
, emin := Twin.ChecklistAxioms.emin
, eds := Twin.ChecklistAxioms.eds
, majMass := Twin.ChecklistAxioms.majMass
, l2_minor_onWindow := Twin.ChecklistAxioms.l2_minor_onWindow
, desmooth_onWindow := Twin.ChecklistAxioms.desmooth_onWindow
, routing_onWindow := Twin.ChecklistAxioms.routing_onWindow
, pinnedMajors_lower := Twin.ChecklistAxioms.pinnedMajors_lower
, ss_pos := Twin.PaperParams.ss_pos
}

/-- The bundled checklist obligations (SME defaults to `Twin.ChecklistSme.sme`). -/
def O' : Twin.ChecklistTargets.Obligations :=
  ((O Twin.ChecklistSme.sme).toObligations)

/-- Gold-status theorem, but *parameterized by* an arbitrary `sme`.

This is useful for axiom audits: the checklist route does not inspect `sme` directly; it is
present to track the analytic model in the paper-facing interfaces. -/
theorem twins_in_all_large_windows_of_sme
  (sme : Twin.MajorArc.SmoothMajorArcEstimate
    Twin.ChecklistTargets.A Twin.ChecklistTargets.B
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What) :
    ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
by
  intro X hX
  exact
    Twin.ChecklistTargets.windows_largeX_all_windows (O := (O sme).toObligations)
      (X := X) (by simpa [P] using hX)

/-- Gold-status theorem (conditional on the conventional analytic axioms above). -/
theorem twins_in_all_large_windows :
    ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
  twins_in_all_large_windows_of_sme Twin.ChecklistSme.sme

end

end Twin.ChecklistGold
