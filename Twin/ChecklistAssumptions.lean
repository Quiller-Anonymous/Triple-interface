import Twin.ChecklistAnalyticGlue
import Twin.ChecklistModel
import Twin.GateSpec

namespace Twin.ChecklistAssumptions

noncomputable section

open Twin

abbrev P : Twin.GoalAPI.Params := Twin.Main.P
abbrev SS : ℝ := Twin.fullTruncSingularSeries P.S

abbrev A : ℝ := Twin.ChecklistModel.A
abbrev B : ℝ := Twin.ChecklistModel.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistModel.Λ
abbrev Wwin : ℝ → ℝ := Twin.ChecklistModel.W
abbrev What : ℝ → ℝ := Twin.ChecklistModel.W_hat

/--
Checklist route assumptions, specialized to the frozen analytic model in `Twin/ChecklistModel.lean`.

Supply these as *arguments* (not global axioms) to keep dependencies explicit.
-/
theorem windows_largeX_all_windows
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)
  (emin eds : ℕ → ℝ)
  (majMass : ℕ → ℝ)
  (h_l2 : Twin.CLSL2.Bound P emin)
  (h_desmooth : Twin.AnalyticCore.DesmoothBound P eds)
  (h_lower : Twin.MajorArc.MajorArcLower P majMass)
  (h_transfer : Twin.MajorArc.MajorArcTransfer P emin eds majMass)
  (ss_pos : 0 < SS := Twin.PaperParams.ss_full_pos) :
  ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
  Twin.ChecklistAnalyticGlue.windows_largeX_all_windows
    (sme := sme)
    (spec := Twin.GateSpec.spec)
    (emin := emin)
    (eds := eds)
    (majMass := majMass)
    (h_l2 := h_l2)
    (h_desmooth := h_desmooth)
    (h_lower := h_lower)
    (h_transfer := h_transfer)
    (ss_pos := ss_pos)

end

end Twin.ChecklistAssumptions
