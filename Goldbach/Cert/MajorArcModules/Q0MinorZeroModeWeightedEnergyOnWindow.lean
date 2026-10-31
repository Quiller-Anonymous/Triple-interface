import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeWeightedEnergy
import Goldbach.Cert.MajorArcModules.Q0MinorRouteAMeanVarianceTargets

/-!
# Canonical-window weighted energy transfer

The existing geometric and singular-series lower bounds make every denominator in the weighted
transfer nonzero on `EvenIn X H` for `X ≥ X0`. This module discharges those hypotheses without
importing the generated singular-series truncation certificates.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeWeightedEnergyOnWindow

open Goldbach Goldbach.BankParams Goldbach.Windows
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorRouteAMeanVarianceTargets
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeWeightedEnergy

noncomputable section

/-- The exact singular-series geometric baseline has positive real part on the working window. -/
theorem zeroModeSigmaBaseline_re_pos_onWindow
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    0 < (zeroModeSigmaBaseline X N).re := by
  have hlogX_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hXN : X ≤ N :=
    Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds.X_le_of_mem_EvenIn hN
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le (le_trans hX hXN)
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hkernel_pos : 0 < Goldbach.BG_Identity.K_full (0 : ℤ) :=
    Goldbach.BG_Identity.K_full_pos_at_zero
  have hprofile_pos : 0 < routeAPSBZeroModeGeometricWindowScalarLowerProfile X := by
    unfold routeAPSBZeroModeGeometricWindowScalarLowerProfile
      routeAPSBExactGeometricScalarLowerProfile
    positivity
  have hwindow_pos : 0 < (routeAPSBZeroModeGeometricWindowScalar X).re :=
    lt_of_lt_of_le hprofile_pos
      (routeAPSBZeroModeGeometricWindowScalarReLowerBound_explicit.bound hX)
  have hsigma_pos : 0 < (sigmaNormalizedSeries N).re :=
    lt_of_lt_of_le (by norm_num) (one_le_sigmaNormalizedSeries_re_of_mem_even_window hX hN)
  rw [zeroModeSigmaBaseline_re_eq_sigma_mul_geometricBaseline_re,
    zeroModeGeometricBaseline_re_eq_q0NormFactor_sq_mul_windowScalar_re_of_mem_even_window hX hN]
  positivity

/-- Baseline nonvanishing is automatic on the canonical working window. -/
theorem zeroModeSigmaBaseline_ne_zero_onWindow
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    zeroModeSigmaBaseline X N ≠ 0 := by
  intro hzero
  have hpos := zeroModeSigmaBaseline_re_pos_onWindow hX hN
  simp [hzero] at hpos

/-- Exact weighted energy transfer on every canonical working window, with no denominator
hypotheses left for the caller. -/
theorem zeroModeEnvelopeErrorWindowEnergy_eq_floorSq_mul_weightedNormalizedShapeEnergy_onWindow
    (κ : ℝ) {X : ℕ} (hX : X0 ≤ X) :
    zeroModeEnvelopeErrorWindowEnergy κ X
      = routeVisibleWindowNormFloorSq X
          * weightedNormalizedZeroModeShapeErrorWindowEnergy κ X := by
  have hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0 := by
    exact_mod_cast (routeVisibleWindowNormFloor_pos_of_X0_le hX).ne'
  exact zeroModeEnvelopeErrorWindowEnergy_eq_floorSq_mul_weightedNormalizedShapeEnergy
    κ X (zeroModeSigmaBaseline_ne_zero_onWindow hX) hfloor

/-- The native and weighted normalized targets have identical constants on the canonical route. -/
theorem zeroModeEnvelopeShapeTarget_iff_weightedNormalizedShapeTarget_onWindow
    {κ C2 C3 : ℝ} :
    ZeroModeEnvelopeShapeTarget κ C2 C3 ↔
      WeightedNormalizedZeroModeShapeTarget κ C2 C3 :=
  zeroModeEnvelopeShapeTarget_iff_weightedNormalizedShapeTarget
    zeroModeSigmaBaseline_ne_zero_onWindow

theorem zeroModeEnvelopeShapeTarget_of_weightedNormalizedShapeTarget
    {κ C2 C3 : ℝ} (h : WeightedNormalizedZeroModeShapeTarget κ C2 C3) :
    ZeroModeEnvelopeShapeTarget κ C2 C3 :=
  zeroModeEnvelopeShapeTarget_iff_weightedNormalizedShapeTarget_onWindow.mpr h

theorem weightedNormalizedZeroModeShapeTarget_of_envelope
    {κ C2 C3 : ℝ} (h : ZeroModeEnvelopeShapeTarget κ C2 C3) :
    WeightedNormalizedZeroModeShapeTarget κ C2 C3 :=
  zeroModeEnvelopeShapeTarget_iff_weightedNormalizedShapeTarget_onWindow.mp h

end

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeWeightedEnergyOnWindow
