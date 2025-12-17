-- Twin/MajorArc/Pin.lean
-- Future home for the *derived* gate lemma, phrased in terms of the
-- SW-style smooth major-arc estimate plus CLS/desmoothing.  For now this
-- file only provides a wrapper around the pinned axiom in `MajorArcPin` so
-- that the eventual analytic proof has a stable target signature.

import Twin.GoalAPI
import Twin.AnalyticCore
import Twin.MajorArc.SWUniform
import Twin.MajorArcPin
import Twin.LedgerExtra
import Twin.Compat
import Twin.SW.Defs

namespace Twin.MajorArc

structure GateSpec (P : GoalAPI.Params) where
  mass       : ℝ
  mass_pos   : 0 < mass
  c_star     : ℝ
  c_star_pos : 0 < c_star

@[inline] def gateCert (P : GoalAPI.Params) (c⋆ : ℝ) (hc⋆ : 0 < c⋆) : GateSpec P :=
by
  let N : ℝ := (↑P.H : ℝ) + 1
  have hN : 0 < N := by
    have : (0 : ℝ) ≤ (↑P.H : ℝ) := by exact_mod_cast Nat.zero_le P.H
    exact add_pos_of_nonneg_of_pos this (by norm_num)
  exact { mass := N/3, mass_pos := by exact div_pos hN (by norm_num)
        , c_star := c⋆, c_star_pos := hc⋆ }

/-- Placeholder interface: once the deep major-arc analysis is in place, this
theorem should prove the pinned gate inequality from three analytic inputs:

* a CLS bound on the minor arcs,
* a desmoothing / prime-power budget, and
* a smooth major-arc estimate coming from Siegel–Walfisz.

Currently this is just a thin wrapper around the pinned axiom
`Twin.MajorArcPin.gate_pointwise`; the analytic hypotheses are not yet used.
This keeps the project honest (no new axioms) while giving a stable target
signature for the eventual proof. -/
theorem gate_pointwise_of_SME_CLS
  {A B : ℝ} {Λ : ℕ → ℝ} {W Ŵ : ℝ → ℝ}
  (P : GoalAPI.Params)
  (emin eds : ℕ → ℝ)
  (hCLS  : AnalyticCore.CLSBound P emin)
  (hDesm : AnalyticCore.DesmoothBound P eds)
  (sme   : SmoothMajorArcEstimate A B Λ W Ŵ)
  (spec  : GateSpec P) :
  AnalyticCore.GatePointwise P emin eds :=
by
  -- TODO: replace this with the real major-arc argument.
  -- For now we faithfully delegate to the single pinned axiom.
  exact Twin.MajorArcPin.gate_pointwise P emin eds
