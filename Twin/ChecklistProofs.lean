import Twin.ChecklistTargets

namespace Twin.ChecklistProofs

noncomputable section

open Twin

abbrev P : Twin.GoalAPI.Params := Twin.ChecklistTargets.P
abbrev SS : ℝ := Twin.ChecklistTargets.SS

abbrev A : ℝ := Twin.ChecklistTargets.A
abbrev B : ℝ := Twin.ChecklistTargets.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistTargets.Lambda
abbrev Wwin : ℝ → ℝ := Twin.ChecklistTargets.Wwin
abbrev What : ℝ → ℝ := Twin.ChecklistTargets.What

/-- Constructor helper: bundle the checklist obligations. -/
def mkObligations
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
  (emin eds : ℕ → ℝ)
  (majMass : ℕ → ℝ)
  (h_l2 : Twin.CLSL2.Bound P emin)
  (h_desmooth : Twin.AnalyticCore.DesmoothBound P eds)
  (h_lower : Twin.MajorArc.MajorArcLower P majMass)
  (h_transfer : Twin.MajorArc.MajorArcTransfer P emin eds majMass)
  (ss_pos : 0 < SS := Twin.PaperParams.ss_pos) :
  Twin.ChecklistTargets.Obligations :=
{ sme := sme
, emin := emin
, eds := eds
, majMass := majMass
, h_l2 := h_l2
, h_desmooth := h_desmooth
, h_lower := h_lower
, h_transfer := h_transfer
, ss_pos := ss_pos
}

/--
The “one-line” final theorem: once you supply the eight analytic inputs (plus `ss_pos`),
you get twins in every sufficiently large window for the frozen model.
-/
theorem windows_largeX_all_windows_of
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
  (emin eds : ℕ → ℝ)
  (majMass : ℕ → ℝ)
  (h_l2 : Twin.CLSL2.Bound P emin)
  (h_desmooth : Twin.AnalyticCore.DesmoothBound P eds)
  (h_lower : Twin.MajorArc.MajorArcLower P majMass)
  (h_transfer : Twin.MajorArc.MajorArcTransfer P emin eds majMass)
  (ss_pos : 0 < SS := Twin.PaperParams.ss_pos) :
  ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
  Twin.ChecklistTargets.windows_largeX_all_windows
    (O := mkObligations sme emin eds majMass h_l2 h_desmooth h_lower h_transfer ss_pos)

end

end Twin.ChecklistProofs

