import AltZeta.Barrier
import Goldbach.ETIExport
import Goldbach.Census.Data
import Twin.PaperParams

noncomputable section
open scoped BigOperators

namespace AltZeta
namespace Instances

open Real

/-!
AltZeta/GoldbachTwinHook.lean
=============================

This module is the intended “prime-detector toolkit” bridge point:

* Goldbach contributes ETI(E1–E3) data via `Goldbach.ETIExport.canonicalETI`.
* Goldbach contributes the census-style numeric certificates (`CGamma`, `S_cert`).
* Twin contributes the canonical parameter pack `Twin.PaperParams.P` so AltZeta and Twin
  share a single source of truth for the window length/basepoint.

The goal is to let AltZeta run its barrier/explicit-formula interface against the same
numerical schedule used by the Twin and Goldbach analytic layers, without introducing
import cycles (AltZeta may import Goldbach and Twin; Twin must not import Goldbach).
-/

/-- Canonical ETI(E1–E3) exported from the Goldbach side. -/
def goldbachCanonicalETI : ETI :=
  Goldbach.ETIExport.canonicalETI

/-- Completion bound certificate, sourced from the Goldbach census placeholders. -/
def goldbachCanonicalCompletion : CompletionBound :=
{ CGamma := Goldbach.Census.CGamma
, hCGamma := Goldbach.Census.CGamma_nonneg }

/-- Spectral envelope certificate, sourced from the Goldbach census placeholders. -/
def goldbachCanonicalEnvelope : EnvelopeCert :=
{ S_cert := Goldbach.Census.S_cert
, hS := Goldbach.Census.S_cert_nonneg }

/-- Baseline ledger constants (placeholder; may be replaced by certified AO-derived values). -/
def goldbachCanonicalLedger : Ledger :=
{ C1 := 1
, C2 := (1 : ℝ) / 2
, C3 := (1 : ℝ) / 4
, hC1 := by norm_num
, hC2 := by norm_num
, hC3 := by norm_num }

/-- Canonical AltZeta inputs derived from Goldbach’s ETI export. -/
def goldbachCanonicalInputs : Inputs :=
{ E := goldbachCanonicalETI
, L := goldbachCanonicalLedger
, G := goldbachCanonicalCompletion
, Env := goldbachCanonicalEnvelope
, W := goldbachCanonicalETI.W
, hW := rfl }

/-- Convenience witness point `x = X` for the canonical window. -/
def goldbachCanonicalX : ℝ :=
  goldbachCanonicalInputs.E.W.X

/-- The witness point `x = X` satisfies `ValidX`. -/
lemma goldbachCanonical_validX :
    ValidX goldbachCanonicalInputs.E.W goldbachCanonicalX := by
  refine ⟨?_, ?_, ?_⟩
  · simp [goldbachCanonicalX]
  · -- `X ≤ 2X` since `X > 0`.
    have hpos : 0 < goldbachCanonicalInputs.E.W.X := goldbachCanonicalInputs.E.W.hX
    have : goldbachCanonicalInputs.E.W.X ≤ 2 * goldbachCanonicalInputs.E.W.X := by
      linarith
    simpa [goldbachCanonicalX] using this
  · simpa [goldbachCanonicalX] using goldbachCanonicalInputs.E.W.hX

/-!
Twin alignment
--------------

AltZeta is intended to share a single “window basepoint + length” story with Twin.
We record the Twin paper parameters here so downstream code can reference them.
-/

/-- The canonical Twin parameters used by the Twin pipeline. -/
def twinPaperParams : Twin.GoalAPI.Params :=
  Twin.PaperParams.P

lemma goldbachCanonicalSchedule_H_eq_twinH :
    goldbachCanonicalInputs.E.Sch.H = (twinPaperParams.H : ℝ) := by
  -- both sides are `10_000` after unfolding the canonical schedule and Twin parameters
  simp [goldbachCanonicalInputs, goldbachCanonicalETI, Goldbach.ETIExport.canonicalETI,
    Goldbach.ETIExport.produceETI, Goldbach.ETIExport.canonicalSchedule, twinPaperParams,
    Twin.PaperParams.P, Twin.PaperParams.H]
  norm_num

lemma goldbachCanonicalWindow_X0_le_twinX0 :
    (twinPaperParams.X0 : ℝ) ≤ goldbachCanonicalInputs.E.W.X := by
  -- `twinPaperParams.X0 = 10_000` while the canonical Goldbach ETI window uses `X = 10^6`.
  have : (10_000 : ℝ) ≤ (10^6 : ℝ) := by norm_num
  simpa [goldbachCanonicalInputs, goldbachCanonicalETI, Goldbach.ETIExport.canonicalETI,
    Goldbach.ETIExport.produceETI, Goldbach.ETIExport.canonicalWindow, twinPaperParams,
    Twin.PaperParams.P, Twin.PaperParams.X0] using this

/-!
Preferred defaults
------------------

For robustness, prefer the Goldbach-exported canonical window (`X = 10^6`) over the toy
`censusInputs` window used in `AltZeta/Instances.lean`.
-/

/-- Preferred `AltZeta.Inputs` for downstream use (robust canonical window). -/
abbrev defaultInputs : Inputs :=
  goldbachCanonicalInputs

/-- Preferred witness point `x = X` for `defaultInputs`. -/
abbrev defaultX : ℝ :=
  goldbachCanonicalX

/-- `defaultX` satisfies `ValidX` for `defaultInputs`. -/
abbrev default_validX :
    ValidX defaultInputs.E.W defaultX :=
  goldbachCanonical_validX

end Instances
end AltZeta
