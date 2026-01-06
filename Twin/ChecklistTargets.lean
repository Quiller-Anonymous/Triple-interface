import Twin.ChecklistAssumptions

namespace Twin.ChecklistTargets

noncomputable section

open Twin

abbrev P : Twin.GoalAPI.Params := Twin.ChecklistAssumptions.P
abbrev SS : ℝ := Twin.ChecklistAssumptions.SS

abbrev A : ℝ := Twin.ChecklistAssumptions.A
abbrev B : ℝ := Twin.ChecklistAssumptions.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistAssumptions.Lambda
abbrev Wwin : ℝ → ℝ := Twin.ChecklistAssumptions.Wwin
abbrev What : ℝ → ℝ := Twin.ChecklistAssumptions.What

/--
Checklist-route obligations for the frozen model (`A,B,Lambda,Wwin,What`).

This is the exact “to-do list” you need to discharge to obtain the final theorem
via `Twin.ChecklistAssumptions.windows_largeX_all_windows`.
-/
structure Obligations where
  /-- Smoothed major-arc estimate (paper §11.2-style). -/
  sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What
  /-- Global error channels (functions of `n` only). -/
  emin : ℕ → ℝ
  eds : ℕ → ℝ
  /-- Checklist major-arc mass (window-start indexed). -/
  majMass : ℕ → ℝ
  /-- Minor-arc L² window bound at the `/9` constant. -/
  h_l2 : Twin.CLSL2.Bound P emin
  /-- Desmoothing / prime-power window L¹ budget at the `/3` constant. -/
  h_desmooth : Twin.AnalyticCore.DesmoothBound P eds
  /-- Pinned majors lower bound in the exact `MajorArcLower` format. -/
  h_lower : Twin.MajorArc.MajorArcLower P majMass
  /-- Window-sum routing: majors ≤ localizedTwinMass + budgets. -/
  h_transfer : Twin.MajorArc.MajorArcTransfer P emin eds majMass
  /-- Positivity of the truncated singular series for `P.S`. -/
  ss_pos : 0 < SS := Twin.PaperParams.ss_pos

/-- Final theorem obtained once you discharge the checklist obligations. -/
theorem windows_largeX_all_windows (O : Obligations) :
    ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
  Twin.ChecklistAssumptions.windows_largeX_all_windows
    (sme := O.sme)
    (emin := O.emin)
    (eds := O.eds)
    (majMass := O.majMass)
    (h_l2 := O.h_l2)
    (h_desmooth := O.h_desmooth)
    (h_lower := O.h_lower)
    (h_transfer := O.h_transfer)
    (ss_pos := O.ss_pos)

/-!
## A more solver-friendly obligation bundle

Many of the checklist fields are records whose content is a single window-inequality.
For “gold status” (axiomatize conventional analysis, then derive), it is often cleaner
to postulate those inequalities directly and let Lean build the records.
-/

/--
Explicit checklist obligations: same data as `Obligations`, but with the analytic inputs
stated as their *raw window-inequalities* (the shapes that appear in the paper).

This is intended as the “easiest interface” to hand to an external solver.
-/
structure ObligationsExplicit where
  /-- Smoothed major-arc estimate (paper §11.2-style). -/
  sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What
  /-- Global error channels (functions of `n` only). -/
  emin : ℕ → ℝ
  eds : ℕ → ℝ
  /-- Checklist major-arc mass (window-start indexed). -/
  majMass : ℕ → ℝ
  /-- Minor-arc L² window inequality at the canonical `/9` constant. -/
  l2_minor_onWindow :
    ∀ X, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H (fun n => (emin n)^2)
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9
  /-- Desmoothing / prime-power L¹ window inequality at the canonical `/3` constant. -/
  desmooth_onWindow :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      Twin.Ledger.windowSum X P.H eds
        ≤ P.eps * SS * (P.H + 1) / 3
  /-- Window-sum routing: analytic majors ≤ localized twin mass + explicit budgets. -/
  routing_onWindow :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      majMass X
        ≤ Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds
  /-- Pinned majors lower bound aligned to `SS := truncSingularSeries(P.S)` with a `/3` tail cap. -/
  pinnedMajors_lower :
    ∀ ⦃X : ℕ⦄, P.X0 ≤ X →
      majMass X
        ≥ (1 - P.eps) * SS * ((P.H : ℝ) + 1)
          - (P.eps * SS) * ((P.H : ℝ) + 1) / 3
  /-- Positivity of the truncated singular series for `P.S`. -/
  ss_pos : 0 < SS := Twin.PaperParams.ss_pos

namespace ObligationsExplicit

/-- Convert explicit inequalities into the record-shaped checklist obligations. -/
def toObligations (O : ObligationsExplicit) : Obligations :=
{ sme := O.sme
, emin := O.emin
, eds := O.eds
, majMass := O.majMass
, h_l2 := ⟨by intro X hX; simpa [SS] using (O.l2_minor_onWindow X hX)⟩
, h_desmooth := ⟨by intro X hX; simpa [SS, mul_assoc, mul_comm, mul_left_comm] using (O.desmooth_onWindow (X := X) hX)⟩
, h_lower := by
    refine ⟨?_⟩
    intro X hX
    have h := O.pinnedMajors_lower (X := X) hX
    linarith
, h_transfer := ⟨by intro X hX; simpa using (O.routing_onWindow (X := X) hX)⟩
, ss_pos := O.ss_pos
}

end ObligationsExplicit

/-- Final theorem obtained once you discharge the *explicit* checklist obligations. -/
theorem windows_largeX_all_windows_explicit (O : ObligationsExplicit) :
    ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
  windows_largeX_all_windows (O := O.toObligations)

end

end Twin.ChecklistTargets
