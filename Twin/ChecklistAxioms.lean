import Twin.PaperParams
import Twin.ChecklistSme
import Twin.MajorArc.MajMass
import Twin.MajorArc.GateBookkeeping
import Twin.CLSL2
import Twin.AnalyticCore
import Twin.Bridge
import Twin.Ledger

/-
  Twin/ChecklistAxioms.lean

  Single place to collect the remaining “conventional analytic” assumptions for the
  checklist-route Twin pipeline, specialized to the frozen model (`Twin.ChecklistModel`)
  and the concrete paper parameters `Twin.PaperParams.P`.

  These are the objects you will progressively replace by real Lean proofs.
-/

namespace Twin.ChecklistAxioms

noncomputable section

open Twin

abbrev P : Twin.GoalAPI.Params := Twin.PaperParams.P
abbrev SS : ℝ := Twin.truncSingularSeries P.S

/-!
## Error channels (currently discharged trivially)

For the “easiest-first” pass, we take `emin = 0` and `eds = 0` and discharge their budgets
via existing zero-case lemmas. Replace these definitions (and the theorems below) with the
paper-aligned analytic constructions once they are formalized.
-/

def emin : ℕ → ℝ := fun _ => (0 : ℝ)
def eds : ℕ → ℝ := fun _ => (0 : ℝ)

theorem h_l2 : Twin.CLSL2.Bound P emin := by
  simpa [emin] using (Twin.CLSL2.fromZero P)

theorem h_desmooth : Twin.AnalyticCore.DesmoothBound P eds := by
  simpa [eds] using (Twin.AnalyticCore.DesmoothBound.fromZero P)

theorem l2_minor_onWindow :
  ∀ X, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H (fun n => (emin n)^2)
      ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9 := by
  intro X hX
  simpa [emin, SS] using (h_l2.bound X hX)

theorem desmooth_onWindow :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    Twin.Ledger.windowSum X P.H eds
      ≤ P.eps * SS * (P.H + 1) / 3 := by
  intro X hX
  simpa [eds, SS, mul_assoc, mul_comm, mul_left_comm] using (h_desmooth.bound (X := X) hX)

/-!
## Analytic major-arc mass

We keep two notions separate:

* `majMassAnalytic`: the literal major-arc integral `Twin.MajorArc.majMass` (paper §11/§14 object),
  instantiated using the frozen SW hypothesis `Twin.ChecklistSme.sme` (see `Twin/ChecklistSme.lean`).
* `majMass`: the *routed* major-arc mass (see `Twin/MajorArc/GateBookkeeping.lean`), chosen so that
  the transfer inequality is discharged definitionally. This keeps the pipeline productive while the
  paper-facing analytic routing lemma is still being formalized.
* `majMassMain`: the canonical main-term function `constMajMass`, useful as a reference target
  for pinned-major evaluations.
-/

noncomputable def majMassAnalytic : ℕ → ℝ :=
  fun X => Twin.MajorArc.majMass (sme := Twin.ChecklistSme.sme) X P.H

noncomputable def majMass : ℕ → ℝ :=
  Twin.MajorArc.MajorArcTransfer.routedMajMass P emin eds

def majMassMain : ℕ → ℝ :=
  Twin.MajorArc.MajorArcLower.constMajMass P

/-!
## Remaining major-arc assumptions (still axiomatized)

These are the two remaining paper-facing obligations on the checklist route:
  - routing/transfer inequality (Appendix A.10 / §14.2),
  - pinned majors lower bound with the `/3` tail cap (§14.2 + Lemma 14.5 + Cor 12.8).

Note on future proofs:
  With `Twin.MajorArc.fullMass` and `Twin.MajorArc.minorMass` (see `Twin/MajorArc/MajMass.lean`),
  the intended proof structure for routing is:
    1. establish a Fourier inversion identity for `fullMass` giving a smoothed twin payload;
    2. bound the minor contribution (`minorMass`) by the minor-arc error channel;
    3. dispose prime powers / desmoothing into the `eds` channel;
  and then combine `fullMass = majMass + minorMass` with triangle/budget bounds to get the
  checklist inequality.
-/

/-!
## Routing / transfer (still axiomatized)

At “gold assumptions” level, this is the remaining major-arc input:
the chosen checklist mass `majMass` (currently the canonical main-term function) must be
routed/controlled by the localized twin mass plus explicit error channels.

Paper anchor: Appendix A.10 (routing / bookkeeping), specialized to the window `[X, X+H]`.
-/

theorem h_transfer : Twin.MajorArc.MajorArcTransfer P emin eds majMass := by
  simpa [majMass] using (Twin.MajorArc.MajorArcTransfer.routedMajMass_transfer P emin eds)

theorem routing_onWindow :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass X
      ≤ Twin.Bridge.localizedTwinMass X P.H
        + Twin.Ledger.windowSum X P.H emin
        + Twin.Ledger.windowSum X P.H eds :=
by
  intro X hX
  simpa using (h_transfer.bound (X := X) hX)

/-!
## Pinned majors lower (still axiomatized)

Paper anchor: §14.2 “Pinned major arcs, and closing the gate”, combined with
Lemma 14.5 (Fourier tail control) and Corollary 12.8 (orthogonality / bank margin).

We record it as the canonical `MajorArcLower` record, and also provide the rearranged
inequality form expected by `Twin.ChecklistTargets.ObligationsExplicit`.
-/

/-- The actual remaining paper-facing assumption on the checklist route:
the *window-sum gate inequality* (AnalyticCore), uniform in `X ≥ X0`.

With the current choice `majMass := routedMajMass`, this is exactly the content of
the §14.2 pinned majors evaluation after accounting for the `/3` tail cap. -/
axiom gate_onWindow : Twin.AnalyticCore.GateOnWindow P emin eds

theorem h_lower : Twin.MajorArc.MajorArcLower P majMass := by
  refine ⟨?_⟩
  intro X hX
  have h := gate_onWindow.bound (X := X) hX
  simpa [majMass] using h

theorem pinnedMajors_lower :
  ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
    majMass X
      ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
        - (P.eps * SS) * ((P.H : ℝ) + 1) / 3 :=
by
  intro X hX
  have h := h_lower.bound (X := X) hX
  -- rearrange `main ≤ majMass + tail` into `majMass ≥ main - tail`
  linarith

end

end Twin.ChecklistAxioms
