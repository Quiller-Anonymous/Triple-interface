/-
  Twin/WiringFromPaper.lean

  “Wiring layer” (paper §§11/14):
  take the three analytic inputs that the paper isolates
    • minor-arc CLS (via L²),
    • desmoothing / prime-power disposal,
    • Siegel–Walfisz major-arc window estimate,
  and feed them into the gate interface `Twin.MajorArc.gate_onWindow_of_SME`,
  producing `PaperBricks.Bricks` and hence the final “twin in every large window” theorem.
-/
import Mathlib
import Twin.AnalyticFromPaper
import Twin.PaperBricks_Instance
import Twin.MajorArc.SWUniform
import Twin.MajorArc.Pin
import Twin.MajorArc.PaperChecklist
import Twin.MajorArc.AppendixAAdapter
import Twin.TwinFinalize

noncomputable section

namespace Twin.WiringFromPaper

open Twin
open Twin.GoalAPI
open Twin.AnalyticFromPaper
open Twin.PaperBricks
open Twin.MajorArc

/-- Concrete parameters used throughout the Twin paper. -/
abbrev P : Params := Twin.PaperParams.P

/-- Build `Bricks P` from the paper’s three analytic inputs:
CLS (minor arcs), desmoothing (prime powers), and an SW major-arc window estimate. -/
def bricks_of_errorData
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : ErrorData)
  (sme  : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec)) :
  Bricks P :=
by
  classical
  refine
    Twin.PaperBricks_Instance.bricks_of (P := P)
      (emin := E.emin) (eds := E.eds)
      (cls := cls_bound (E := E))
      (desm := desmooth_bound (E := E))
      (gate := gate_onWindow_of_SME (E := E) sme spec pkg)

/-- Same wiring, but taking a `SiegelWalfisz` instance and rewrapping it as a
`SmoothMajorArcEstimate` automatically (paper §11.2). -/
def bricks_of_errorData_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : ErrorData)
  (spec : GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec)) :
  Bricks P :=
  bricks_of_errorData (E := E)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    spec pkg

/-- (Optional) Produce the assembled `TwinWitness` directly from the paper-facing inputs. -/
noncomputable def witness_of_errorData
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : ErrorData)
  (sme  : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  Twin.TwinFinalize.witness_from_bricks (P := P)
    (b := bricks_of_errorData (E := E) sme spec pkg)
    ss_pos
    (_eps_pos := P.eps_pos)
    (eps_lt_half := P.eps_lt_half)

/-- Same witness constructor, but taking `SiegelWalfisz` as the major-arc input. -/
noncomputable def witness_of_errorData_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : ErrorData)
  (spec : GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  Twin.Analytic.TwinWitness :=
  witness_of_errorData (E := E)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec) (pkg := pkg) ss_pos

/-- Final theorem, expressed directly in terms of the paper-level wiring inputs. -/
theorem windows_largeX_of_errorData
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : ErrorData)
  (sme  : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
by
  intro X hX
  -- assemble `Bricks P` from the three analytic inputs, then use the existing finalizer
  exact
    Twin.TwinFinalize.windows_largeX (P := P)
      (b := bricks_of_errorData (E := E) sme spec pkg)
      ss_pos
      (_eps_pos := P.eps_pos)
      (eps_lt_half := P.eps_lt_half)
      (X := X) hX

/-- Same final theorem, but taking `SiegelWalfisz` as the major-arc input (paper §11.2). -/
theorem windows_largeX_of_errorData_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : ErrorData)
  (spec : GateSpec P)
  (pkg : Twin.MajorArc.MajorArcPackage (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  windows_largeX_of_errorData (E := E)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec) (pkg := pkg) ss_pos

/-- Paper-facing route, expressed using the §14/A.10 checklist record rather than the raw package. -/
theorem windows_largeX_of_checklist
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : ErrorData)
  (sme  : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P)
  (C : Twin.MajorArc.PaperMajorArcChecklist (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  windows_largeX_of_errorData (E := E) (sme := sme) (spec := spec)
    (pkg := C.toMajorArcPackage) ss_pos

/-- Checklist version, but taking `SiegelWalfisz` as the major-arc input (paper §11.2). -/
theorem windows_largeX_of_checklist_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : ErrorData)
  (spec : GateSpec P)
  (C : Twin.MajorArc.PaperMajorArcChecklist (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  windows_largeX_of_checklist (E := E)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec) (C := C) ss_pos

/-- Paper-facing route, using Appendix-A-style inputs (`Wmaj` + pinned majors + routing). -/
theorem windows_largeX_of_appendixA
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (E : ErrorData)
  (sme  : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P)
  (I : Twin.MajorArc.AppendixAInputs (P := P) (emin := E.emin) (eds := E.eds)
    (sme := sme) (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  windows_largeX_of_checklist (E := E) (sme := sme) (spec := spec)
    (C := I.toPaperMajorArcChecklist) ss_pos

/-- Appendix-A version, but taking `SiegelWalfisz` as the major-arc input (paper §11.2). -/
theorem windows_largeX_of_appendixA_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (E : ErrorData)
  (spec : GateSpec P)
  (I : Twin.MajorArc.AppendixAInputs (P := P) (emin := E.emin) (eds := E.eds)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec))
  (ss_pos : 0 < fullTruncSingularSeries P.S) :
  ∀ {X : ℕ}, P.X0 ≤ X → ExistsTwinInWindow X P.H :=
  windows_largeX_of_appendixA (E := E)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec) (I := I) ss_pos

end Twin.WiringFromPaper
