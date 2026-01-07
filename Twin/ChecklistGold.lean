import Twin.ChecklistTargets
import Twin.ChecklistAxioms

/-
  Twin/ChecklistGold.lean

  “Gold status” (Twin, checklist route):
  we allow *conventional* analytic inputs to be postulated as axioms (with citations),
  and then the remaining wiring is fully machine-checked.

  This file is the **parameterized** checklist theorem: it assumes an arbitrary
  `SmoothMajorArcEstimate` input `sme` and does not commit to any particular
  choice of `sme` (so axiom audits can isolate which obligations truly depend on it).

  The default frozen-model `sme` (and the specialization to it) lives in
  `Twin/ChecklistGoldDefault.lean`.

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
  The remaining paper-facing input on the **pinned majors** side is the evaluation axiom
  split into `Twin.ChecklistAxioms.pinnedMajors_SW_error_raw` (SW approximation on majors) and
  `Twin.ChecklistAxioms.pinnedMajors_mainTerm_eval_raw` (singular-series main-term evaluation);
  `Twin.ChecklistAxioms.pinnedMajors_eval_raw` and `Twin.ChecklistAxioms.h_lower` are derived.
  `Twin.ChecklistAxioms.h_transfer` is proved from the analytic definitions of `emin/eds`.

  On the desmoothing side, the `/3` budget is decomposed into:
  - Fourier inversion + smooth/sharp window comparison: `dsFourierInv_sum_bigIcc_raw` (Fourier inversion budget)
    and `dsFourierWindow_sum_bigIcc_raw` (the window-comparison budget),
  - prime-power disposal: `dsPrimePower_sum_bigIcc_raw` (the window-summed prime-power budget),
  and the combined `/3` inequality is derived by finitary triangle inequalities.

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
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What)
  (hsmeX0 : sme.X0 ≤ (P.X0 : ℝ)) :
  Twin.ChecklistTargets.ObligationsExplicit :=
{ sme := sme
, emin := Twin.ChecklistAxioms.emin (sme := sme)
, eds := Twin.ChecklistAxioms.eds
, majMass := Twin.ChecklistAxioms.majMass (sme := sme)
, l2_minor_onWindow := Twin.ChecklistAxioms.l2_minor_onWindow (sme := sme)
, desmooth_onWindow := Twin.ChecklistAxioms.desmooth_onWindow
, routing_onWindow := Twin.ChecklistAxioms.routing_onWindow (sme := sme)
, pinnedMajors_lower := by
    intro X hX
    have hsmeX0' : sme.X0 ≤ (Twin.ChecklistAxioms.P.X0 : ℝ) := by
      -- `Twin.ChecklistTargets.P` is definitionally `Twin.PaperParams.P`.
      simpa [P, Twin.ChecklistTargets.P, Twin.ChecklistAssumptions.P, Twin.Main.P, Twin.ChecklistAxioms.P,
        Twin.PaperParams.P] using hsmeX0
    have hX' : Twin.ChecklistAxioms.P.X0 ≤ X := by
      simpa [P, Twin.ChecklistTargets.P, Twin.ChecklistAssumptions.P, Twin.Main.P, Twin.ChecklistAxioms.P,
        Twin.PaperParams.P] using hX
    simpa [SS, Twin.ChecklistTargets.SS, Twin.ChecklistAssumptions.SS, Twin.ChecklistAxioms.SS,
      P, Twin.ChecklistTargets.P, Twin.ChecklistAssumptions.P, Twin.Main.P, Twin.ChecklistAxioms.P,
      Twin.PaperParams.P] using
      (Twin.ChecklistAxioms.pinnedMajors_lower (sme := sme) hsmeX0' (X := X) hX')
, ss_pos := Twin.PaperParams.ss_pos
}

/-- Gold-status theorem, but *parameterized by* an arbitrary `sme`.

This is useful for axiom audits: the checklist route does not inspect `sme` directly; it is
present to track the analytic model in the paper-facing interfaces. -/
theorem twins_in_all_large_windows_of_sme
  (sme : Twin.MajorArc.SmoothMajorArcEstimate
    Twin.ChecklistTargets.A Twin.ChecklistTargets.B
    Twin.ChecklistTargets.Lambda Twin.ChecklistTargets.Wwin Twin.ChecklistTargets.What) :
  sme.X0 ≤ (P.X0 : ℝ) →
    ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
by
  intro hsmeX0
  intro X hX
  exact
    Twin.ChecklistTargets.windows_largeX_all_windows (O := (O sme hsmeX0).toObligations)
      (X := X) (by simpa [P] using hX)

end

end Twin.ChecklistGold
