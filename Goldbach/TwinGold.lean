import Goldbach.TI.TwinInstance
import Twin.TwinMain
import Twin.AnalyticFromPaper
import Twin.MajorArc.Pin
import Twin.ChecklistSme

/-!
Goldbach/TwinGold.lean
======================

An end-to-end “large window contains a twin” theorem obtained by feeding a
`Twin.HasTwinTI` instance (provided by `Goldbach.TI.TwinInstance`) into the Twin
pipeline.

This is the *cycle-safe* way to “hook Twin axioms into Goldbach”: `Goldbach` can import
`Twin.*` and provide the TI instance, while `Twin` itself does not import `Goldbach`.
-/

noncomputable section

namespace Goldbach.TwinGold

open Twin

/-!
We use the trivial `MajorArcPackage.of_gate` constructor: a `GateOnWindow` inequality
(from the TI instance) is repackaged into the major-arc interface required by
`Twin.Main.windows_largeX_of_errorData`.

Note: the `sme` parameter is still threaded through the API for paper-traceability;
the `of_gate` package does not inspect it.
-/

theorem twins_in_all_large_windows
  (sme : Twin.MajorArc.SmoothMajorArcEstimate
    Twin.ChecklistSme.A Twin.ChecklistSme.B
    Twin.ChecklistSme.Lambda Twin.ChecklistSme.Wwin Twin.ChecklistSme.What)
  [Twin.ChecklistSme.InstSWBound]
  [Twin.ChecklistAxioms.DsFourierAtSumBudget] [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget]
  [Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := Goldbach.TI.TwinInstance.ti_sme)]
  [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := Goldbach.TI.TwinInstance.ti_sme)]
  [Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := Goldbach.TI.TwinInstance.ti_sme)] :
    ∀ {X : ℕ}, Twin.Main.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.Main.P.H :=
by
  classical
  -- Pull TI outputs for the paper parameters.
  letI : Twin.HasTwinTI Twin.Main.P := by
    -- The instance is provided by `Goldbach.TI.TwinInstance`.
    infer_instance

  -- Build `ErrorData` from the TI minor/desmooth budgets.
  let E : Twin.AnalyticFromPaper.ErrorData :=
  { emin := (Twin.HasTwinTI.emin (P := Twin.Main.P))
  , eds := (Twin.HasTwinTI.eds (P := Twin.Main.P))
  , l2_minor := ⟨by
      intro X hX
      simpa using (Twin.HasTwinTI.l2_minor (P := Twin.Main.P) (X := X) hX)⟩
  , desmooth := ⟨by
      intro X hX
      simpa using (Twin.HasTwinTI.desmooth (P := Twin.Main.P) (X := X) hX)⟩
  }

  -- Gate spec: choose `cStar := SS` (positive for our concrete paper params).
  let spec : Twin.MajorArc.GateSpec Twin.Main.P :=
    Twin.MajorArc.gateCert Twin.Main.P (Twin.fullTruncSingularSeries Twin.Main.P.S)
      Twin.PaperParams.ss_full_pos

  -- Gate inequality from TI.
  have gate : Twin.AnalyticCore.GateOnWindow Twin.Main.P E.emin E.eds := by
    refine ⟨?_⟩
    intro X hX
    simpa [E] using (Twin.HasTwinTI.pinned (P := Twin.Main.P) (X := X) hX)

  -- Repackage the gate as a major-arc package.
  let pkg :
      Twin.MajorArc.MajorArcPackage (P := Twin.Main.P) (emin := E.emin) (eds := E.eds)
      (sme := sme) (spec := spec) :=
    Twin.MajorArc.MajorArcPackage.of_gate (P := Twin.Main.P) (emin := E.emin) (eds := E.eds)
      (sme := sme) (spec := spec) gate

  -- Final call.
  intro X hX
  exact
    Twin.Main.windows_largeX_of_errorData (E := E) (sme := sme) (spec := spec) (pkg := pkg)
      Twin.PaperParams.ss_full_pos (X := X) hX

theorem twins_in_all_large_windows_default
    [Twin.ChecklistSme.InstSWBound]
    [Twin.ChecklistAxioms.DsFourierAtSumBudget] [Twin.ChecklistAxioms.DsPrimePowerAtSumBudget]
    [Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := Goldbach.TI.TwinInstance.ti_sme)]
    [Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := Goldbach.TI.TwinInstance.ti_sme)]
    [Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := Goldbach.TI.TwinInstance.ti_sme)] :
    ∀ {X : ℕ}, Twin.Main.P.X0 ≤ X → Twin.ExistsTwinInWindow X Twin.Main.P.H :=
  twins_in_all_large_windows (sme := Twin.ChecklistSme.sme)

end Goldbach.TwinGold
