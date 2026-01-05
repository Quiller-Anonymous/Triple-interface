/-
  Twin/TwinMain.lean
  Thin wrapper: expose a ready-to-use “large X ⇒ twin in window” theorem
  from the assembled pipeline.
-/
import Mathlib
import Twin.GoalAPI
import Twin.PaperParams
import Twin.PaperBricks
import Twin.TwinFinalize
import Twin.WiringFromPaper
import Twin.MajorArc.PaperChecklist
import Twin.MajorArc.AppendixAAdapter

noncomputable section

namespace Twin.Main

open Twin
open Twin.GoalAPI

/-- Shorthand for the concrete parameters. -/
def P  : GoalAPI.Params := Twin.PaperParams.P

/--
If the truncated singular series is positive and `0 < eps < 1/2`,
then every sufficiently large window (starting at `X ≥ P.X0`) contains a twin pair.
-/
theorem windows_largeX
  (b : Twin.PaperBricks.Bricks P)
  (ss_pos      : 0 < truncSingularSeries P.S)
  (eps_pos     : 0 < P.eps := by norm_num)
  (eps_lt_half : P.eps < (1 : ℝ) / 2 := by norm_num)
  : ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H := by
  intro X hX
  -- Call the finalizer's theorem directly with the current X.
  exact Twin.TwinFinalize.windows_largeX (P := P) b ss_pos eps_pos eps_lt_half (X := X) hX

/--
Paper-facing entrypoint (§§11/14): given the supplied `ErrorData` (minor arcs + desmoothing)
and a `SmoothMajorArcEstimate`, conclude that every large window contains a twin.
-/
theorem windows_largeX_of_errorData
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : Twin.AnalyticFromPaper.ErrorData)
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  Twin.WiringFromPaper.windows_largeX_of_errorData (E := E) sme spec pkg ss_pos

/-- Same entry point, but taking `SiegelWalfisz` as the major-arc input (paper §11.2). -/
theorem windows_largeX_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : Twin.AnalyticFromPaper.ErrorData)
  (spec : Twin.MajorArc.GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (Twin.MajorArc.SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  Twin.WiringFromPaper.windows_largeX_of_errorData_ofSW (E := E) (spec := spec) (pkg := pkg) ss_pos

/-- Same paper-facing route, but accepting the §14/A.10 checklist record instead of the raw package. -/
theorem windows_largeX_of_checklist
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : Twin.AnalyticFromPaper.ErrorData)
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (C : Twin.MajorArc.PaperMajorArcChecklist (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  Twin.WiringFromPaper.windows_largeX_of_checklist (E := E) sme spec C ss_pos

/-- Checklist version, but taking `SiegelWalfisz` as the major-arc input (paper §11.2). -/
theorem windows_largeX_of_checklist_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : Twin.AnalyticFromPaper.ErrorData)
  (spec : Twin.MajorArc.GateSpec P)
  (C : Twin.MajorArc.PaperMajorArcChecklist (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (Twin.MajorArc.SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  Twin.WiringFromPaper.windows_largeX_of_checklist_ofSW (E := E) (spec := spec) (C := C) ss_pos

/-- Appendix-A version: supply `Wmaj` + pinned majors + routing, and get twins in every large window. -/
theorem windows_largeX_of_appendixA
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : Twin.AnalyticFromPaper.ErrorData)
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (I : Twin.MajorArc.AppendixAInputs (P := P) (emin := E.emin) (eds := E.eds) (sme := sme) (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  Twin.WiringFromPaper.windows_largeX_of_appendixA (E := E) sme spec I ss_pos

/-- Appendix-A version, but taking `SiegelWalfisz` as the major-arc input (paper §11.2). -/
theorem windows_largeX_of_appendixA_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : Twin.AnalyticFromPaper.ErrorData)
  (spec : Twin.MajorArc.GateSpec P)
  (I : Twin.MajorArc.AppendixAInputs (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (Twin.MajorArc.SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  Twin.WiringFromPaper.windows_largeX_of_appendixA_ofSW (E := E) (spec := spec) (I := I) ss_pos

/-- (Optional convenience) produce the assembled witness object directly from the paper-facing inputs. -/
noncomputable def witness_of_errorData
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : Twin.AnalyticFromPaper.ErrorData)
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  Twin.WiringFromPaper.witness_of_errorData (E := E) sme spec pkg ss_pos

/-- Same witness constructor, but taking `SiegelWalfisz` as the major-arc input. -/
noncomputable def witness_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : Twin.AnalyticFromPaper.ErrorData)
  (spec : Twin.MajorArc.GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (Twin.MajorArc.SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  Twin.WiringFromPaper.witness_of_errorData_ofSW (E := E) (spec := spec) (pkg := pkg) ss_pos

/-- Checklist version of `witness_of_errorData`. -/
noncomputable def witness_of_checklist
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : Twin.AnalyticFromPaper.ErrorData)
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (C : Twin.MajorArc.PaperMajorArcChecklist (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  witness_of_errorData (E := E) (sme := sme) (spec := spec) (pkg := C.toMajorArcPackage) ss_pos

/-- Checklist version of `witness_ofSW`. -/
noncomputable def witness_of_checklist_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : Twin.AnalyticFromPaper.ErrorData)
  (spec : Twin.MajorArc.GateSpec P)
  (C : Twin.MajorArc.PaperMajorArcChecklist (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (Twin.MajorArc.SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  witness_ofSW (E := E) (spec := spec) (pkg := C.toMajorArcPackage) ss_pos

/-- Appendix-A witness constructor. -/
noncomputable def witness_of_appendixA
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : Twin.AnalyticFromPaper.ErrorData)
  (sme  : Twin.MajorArc.SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : Twin.MajorArc.GateSpec P)
  (I : Twin.MajorArc.AppendixAInputs (P := P) (emin := E.emin) (eds := E.eds) (sme := sme) (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  witness_of_errorData (E := E) (sme := sme) (spec := spec) (pkg := I.toMajorArcPackage) ss_pos

/-- Appendix-A witness constructor, but taking `SiegelWalfisz` as the major-arc input (paper §11.2). -/
noncomputable def witness_of_appendixA_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : Twin.AnalyticFromPaper.ErrorData)
  (spec : Twin.MajorArc.GateSpec P)
  (I : Twin.MajorArc.AppendixAInputs (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (Twin.MajorArc.SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < truncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  witness_ofSW (E := E) (spec := spec) (pkg := I.toMajorArcPackage) ss_pos

/-- (Optional convenience) produce the assembled witness object directly. -/
noncomputable def witness
  (b : Twin.PaperBricks.Bricks P)
  (ss_pos      : 0 < truncSingularSeries P.S)
  (eps_pos     : 0 < P.eps := by norm_num)
  (eps_lt_half : P.eps < (1 : ℝ) / 2 := by norm_num)
  : Analytic.TwinWitness :=
  Twin.TwinFinalize.witness_from_bricks (P := P) b ss_pos eps_pos eps_lt_half

end Twin.Main
