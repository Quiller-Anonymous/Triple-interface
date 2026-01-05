-- Twin/MajorArc/Pin.lean
-- Future home for the *derived* gate lemma, phrased in terms of the
-- SW-style smooth major-arc estimate plus CLS/desmoothing.  For now this
-- file declares the (currently axiomatized) interface so that the eventual
-- analytic proof has a stable target signature.

import Twin.GoalAPI
import Twin.AnalyticCore
import Twin.MajorArc.SWUniform
import Twin.MajorArc.GateBookkeeping

noncomputable section

namespace Twin.MajorArc

structure GateSpec (P : GoalAPI.Params) where
  mass       : ℝ
  mass_pos   : 0 < mass
  c_star     : ℝ
  c_star_pos : 0 < c_star

@[inline] def gateCert (P : GoalAPI.Params) (cStar : ℝ) (hcStar : 0 < cStar) : GateSpec P :=
by
  let N : ℝ := (↑P.H : ℝ) + 1
  have hN : 0 < N := by
    have : (0 : ℝ) ≤ (↑P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
    exact add_pos_of_nonneg_of_pos this (by norm_num)
  exact { mass := N/3, mass_pos := by exact div_pos hN (by norm_num)
        , c_star := cStar, c_star_pos := hcStar }

/-- Placeholder interface: once the deep major-arc analysis is in place, this
theorem should prove the pinned gate inequality from three analytic inputs:

* a CLS bound on the minor arcs,
* a desmoothing / prime-power budget, and
* a smooth major-arc estimate coming from Siegel–Walfisz.

This is currently an *interface only*: downstream code assumes a
`MajorArcPackage` is supplied.  The eventual goal is to prove this package from
the major-arc analysis in the paper (notably §§11/14). -/
structure MajorArcPackage
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (P : GoalAPI.Params)
  (emin eds : ℕ → ℝ)
  (sme : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P) where
  majMass : ℕ → ℝ
  lower : MajorArcLower P majMass
  transfer : MajorArcTransfer P emin eds majMass

/-- Trivial constructor: any already-proved `GateOnWindow` inequality can be repackaged
as a `MajorArcPackage`. This is useful when the gate inequality comes from a TI witness
rather than the SW-based major-arc analysis. -/
def MajorArcPackage.of_gate
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (P : GoalAPI.Params)
  (emin eds : ℕ → ℝ)
  (sme : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P)
  (hgate : AnalyticCore.GateOnWindow P emin eds) :
  MajorArcPackage (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec) :=
by
  classical
  refine
    { majMass := fun X =>
        Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds
    , lower := ?_
    , transfer := ?_ }
  · refine ⟨?_⟩
    intro X hX
    simpa [add_assoc, add_comm, add_left_comm] using (hgate.bound (X := X) hX)
  · refine ⟨?_⟩
    intro X hX
    simp

/-- Convenience: if you have a `SiegelWalfisz` instance (paper §11.2), rewrap it as a
`SmoothMajorArcEstimate` and obtain the same major-arc package. -/
theorem majorArcPackage_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (P : GoalAPI.Params)
  (emin eds : ℕ → ℝ)
  (spec : GateSpec P)
  (pkg : MajorArcPackage (P := P) (emin := emin) (eds := eds)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec)) :
  ∃ majMass : ℕ → ℝ, MajorArcLower P majMass ∧ MajorArcTransfer P emin eds majMass :=
by
  exact ⟨pkg.majMass, pkg.lower, pkg.transfer⟩

/-- §14 bookkeeping: combine the two major-arc facts into the gate-on-window inequality.

Note: the CLS/desmoothing *budgets* are accounted for separately (they appear as
`windowSum emin` and `windowSum eds` in the conclusion and are later bounded by
`cls_budget` / `desmooth_budget`). -/
theorem gate_onWindow_of_SME
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (P : GoalAPI.Params)
  (emin eds : ℕ → ℝ)
  (sme   : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec  : GateSpec P)
  (pkg : MajorArcPackage (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec)) :
  AnalyticCore.GateOnWindow P emin eds :=
by
  classical
  exact gate_onWindow_of_majorArc (P := P) (emin := emin) (eds := eds) (majMass := pkg.majMass) pkg.lower pkg.transfer

/-- Same gate conclusion, but taking `SiegelWalfisz` as the major-arc input. -/
theorem gate_onWindow_ofSW
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  [hSW : Twin.MajorArc.SiegelWalfisz A B Λ W W_hat]
  (P : GoalAPI.Params)
  (emin eds : ℕ → ℝ)
  (spec  : GateSpec P)
  (pkg : MajorArcPackage (P := P) (emin := emin) (eds := eds)
    (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
    (spec := spec)) :
  AnalyticCore.GateOnWindow P emin eds :=
by
  classical
  -- route through the windowed SME form so we do not duplicate bookkeeping
  simpa using
    gate_onWindow_of_SME (P := P) (emin := emin) (eds := eds)
      (sme := (SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Λ) (W := W) (W_hat := W_hat)))
      (spec := spec) (pkg := pkg)
