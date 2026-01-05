import Twin.TwinMain

namespace Twin.ChecklistAnalyticGlue

noncomputable section
open scoped BigOperators

open Twin

/-!
Compile-shaped glue for the **checklist** route (paper-facing, window-sum routing).

This file is intentionally “interface-only”: it introduces no new analytic definitions.
If you provide inhabitants of the hypotheses below, you can call
`Twin.Main.windows_largeX_of_checklist`.
-/

abbrev P : Twin.GoalAPI.Params := Twin.Main.P
/-- Main theorem (checklist route): every sufficiently large window contains a twin. -/
theorem windows_largeX_all_windows
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (emin eds : ℕ → ℝ)
  (majMass : ℕ → ℝ)
  (h_l2 : Twin.CLSL2.Bound P emin)
  (h_desmooth : Twin.AnalyticCore.DesmoothBound P eds)
  (h_lower : Twin.MajorArc.MajorArcLower P majMass)
  (h_transfer : Twin.MajorArc.MajorArcTransfer P emin eds majMass)
  (ss_pos : 0 < Twin.truncSingularSeries P.S := Twin.PaperParams.ss_pos) :
  ∀ {X : ℕ}, P.X0 ≤ X → Twin.ExistsTwinInWindow X P.H :=
by
  classical
  intro X hX
  let E' : Twin.AnalyticFromPaper.ErrorData :=
    { emin := emin, eds := eds, l2_minor := h_l2, desmooth := h_desmooth }
  have C' :
      Twin.MajorArc.PaperMajorArcChecklist
        (P := P) (emin := E'.emin) (eds := E'.eds) (sme := sme) (spec := spec) :=
    { majMass := majMass
    , lower := h_lower
    , transfer := by simpa [E'] using h_transfer
    }
  exact
    Twin.Main.windows_largeX_of_checklist
      (E := E') (sme := sme) (spec := spec) (C := C') (ss_pos := ss_pos) (X := X) hX

end

end Twin.ChecklistAnalyticGlue
