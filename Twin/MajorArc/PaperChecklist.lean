import Mathlib
import Twin.GoalAPI
import Twin.AnalyticCore
import Twin.Bridge
import Twin.Ledger
import Twin.SingularSeries
import Twin.MajorArc.SWUniform
import Twin.MajorArc.GateBookkeeping
import Twin.MajorArc.Pin

noncomputable section

namespace Twin.MajorArc

open Twin
open Twin.GoalAPI

/-
Paper-facing checklist for building `MajorArcPackage`
====================================================

In the PDF (`Twin_primes macho.pdf`), the §14 “Gate, pin, and pinned majors” story and
Appendix A (“Pinned majors, leakage, and the gate”) isolate a simple logical spine:

1. Define an auxiliary “major-arc mass” on each window.
2. Prove a **pinned majors lower bound** for that auxiliary mass (A.13, after accounting for
   whatever fixed tail/normalization losses are being budgeted).
3. Prove a **routing / transfer inequality** expressing that auxiliary mass is dominated by the
   localized twin mass plus explicit error channels (A.12 and the surrounding routing summary).

Items (2) and (3) are exactly what our `MajorArcLower` and `MajorArcTransfer` record.

This file packages those two paper-level obligations into a single record and gives a
constructor `toMajorArcPackage` producing the Lean `MajorArcPackage` expected by the
paper-facing entry points in `Twin/TwinMain.lean`.
-/

/-- Paper §14 + Appendix A.10 checklist:

Given a chosen model (captured by `sme`) and a gate parameter record (`spec`), provide:
* an auxiliary windowed major-arc quantity `majMass X`,
* a pinned-majors lower bound (`lower`),
* a routing/transfer inequality into localized twin mass + error channels (`transfer`).

Supplying this record is the precise “major arcs” obligation needed by the paper-facing route. -/
structure PaperMajorArcChecklist
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (P : Params)
  (emin eds : ℕ → ℝ)
  (sme  : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P) where
  /-- Auxiliary major-arc quantity on the window starting at `X`. -/
  majMass : ℕ → ℝ
  /-- Pinned majors lower bound (paper: “pinned majors contribute SS(2)…”). -/
  lower : MajorArcLower P majMass
  /-- Routing: the auxiliary major-arc mass is controlled by the localized twin mass plus
  explicit error channels (`emin`, `eds`). -/
  transfer : MajorArcTransfer P emin eds majMass

/-- Turn the paper checklist into the `MajorArcPackage` used by the Lean wiring layer. -/
def PaperMajorArcChecklist.toMajorArcPackage
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  {P : Params} {emin eds : ℕ → ℝ}
  {sme : SmoothMajorArcEstimate A B Λ W W_hat}
  {spec : GateSpec P}
  (C : PaperMajorArcChecklist (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec)) :
  MajorArcPackage (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec) :=
{ majMass := C.majMass
, lower := C.lower
, transfer := C.transfer }

end Twin.MajorArc

