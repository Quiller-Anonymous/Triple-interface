import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

/-!
# Exact weighted transfer for the zero-mode envelope error

The squared baseline weight is part of the exact normalization identity. Retaining it gives a
target equivalent to the native envelope energy bound, without an unweighted constant-shape
assumption. Baseline nonvanishing remains explicit; the route floor is positive for `X ≥ X0`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeWeightedEnergy

open scoped BigOperators
open Goldbach Goldbach.BankParams Goldbach.Windows
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

/-- The normalized shape error with the exact squared baseline weight retained. -/
noncomputable def weightedNormalizedZeroModeShapeErrorWindowEnergy
    (κ : ℝ) (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ‖zeroModeSigmaBaseline X N‖ ^ 2 * ‖normalizedZeroModeShapeError κ X N‖ ^ 2

/-- Exact pointwise energy transfer. Nonzero denominators are required because the
normalized observable uses division in `ℂ`, where division by zero is totalized. -/
theorem zeroModeEnvelopeError_norm_sq_eq_floorSq_mul_weightedShapeError
    (κ : ℝ) (X N : ℕ)
    (hsigma : zeroModeSigmaBaseline X N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    ‖zeroModeEnvelopeError κ X N‖ ^ 2
      = routeVisibleWindowNormFloorSq X
          * (‖zeroModeSigmaBaseline X N‖ ^ 2
              * ‖normalizedZeroModeShapeError κ X N‖ ^ 2) := by
  have hfloor_sq :
      ‖(routeVisibleWindowNormFloor X : ℂ)‖ ^ 2
        = routeVisibleWindowNormFloorSq X := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]
    simpa only [pow_two] using routeVisibleWindowNormFloor_sq X
  rw [zeroModeEnvelopeError_eq_sigma_floor_mul_normalizedShapeError
    κ X N hsigma hfloor]
  simp only [norm_mul, mul_pow]
  rw [hfloor_sq]
  ring

/-- Exact window-energy identity; no estimate of the baseline weight is used. -/
theorem zeroModeEnvelopeErrorWindowEnergy_eq_floorSq_mul_weightedNormalizedShapeEnergy
    (κ : ℝ) (X : ℕ)
    (hsigma : ∀ {N : ℕ}, N ∈ EvenIn X H → zeroModeSigmaBaseline X N ≠ 0)
    (hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0) :
    zeroModeEnvelopeErrorWindowEnergy κ X
      = routeVisibleWindowNormFloorSq X
          * weightedNormalizedZeroModeShapeErrorWindowEnergy κ X := by
  unfold zeroModeEnvelopeErrorWindowEnergy weightedNormalizedZeroModeShapeErrorWindowEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact zeroModeEnvelopeError_norm_sq_eq_floorSq_mul_weightedShapeError
    κ X N (hsigma hN) hfloor

/-- The canonical route floor is positive on every working window. -/
theorem routeVisibleWindowNormFloor_pos_of_X0_le
    {X : ℕ} (hX : X0 ≤ X) : 0 < routeVisibleWindowNormFloor X := by
  have hlog_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le
      (le_trans hX (Nat.le_add_right X H))
  have hlog_pos : 0 < Real.log ((X + H : ℕ) : ℝ) := by linarith
  unfold routeVisibleWindowNormFloor
  positivity

/-- The weighted normalized target retains exactly the energy consumed by the
route-facing envelope target. It makes no claim that the unweighted shape is
close to a constant. -/
structure WeightedNormalizedZeroModeShapeTarget (κ C2 C3 : ℝ) : Prop where
  C2_nonneg : 0 ≤ C2
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      weightedNormalizedZeroModeShapeErrorWindowEnergy κ X
        ≤ C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/-- With nonvanishing baselines, the weighted normalized target and the native
envelope target are equivalent with identical constants. Positivity of the route
floor follows from `X ≥ X0`; baseline nonvanishing remains an explicit input. -/
theorem zeroModeEnvelopeShapeTarget_iff_weightedNormalizedShapeTarget
    {κ C2 C3 : ℝ}
    (hsigma : ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      zeroModeSigmaBaseline X N ≠ 0) :
    ZeroModeEnvelopeShapeTarget κ C2 C3 ↔
      WeightedNormalizedZeroModeShapeTarget κ C2 C3 := by
  constructor
  · intro h
    refine ⟨h.C2_nonneg, h.C3_nonneg, ?_⟩
    intro X hX
    have hfloor_pos := routeVisibleWindowNormFloor_pos_of_X0_le hX
    have hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0 := by
      exact_mod_cast hfloor_pos.ne'
    have hfloor_sq_pos : 0 < routeVisibleWindowNormFloorSq X := by
      rw [← routeVisibleWindowNormFloor_sq]
      exact sq_pos_of_ne_zero hfloor_pos.ne'
    have hbound := h.bound hX
    rw [zeroModeEnvelopeErrorWindowEnergy_eq_floorSq_mul_weightedNormalizedShapeEnergy
      κ X (hsigma hX) hfloor] at hbound
    exact (mul_le_mul_iff_right₀ hfloor_sq_pos).mp hbound
  · intro h
    refine ⟨h.C2_nonneg, h.C3_nonneg, ?_⟩
    intro X hX
    have hfloor_pos := routeVisibleWindowNormFloor_pos_of_X0_le hX
    have hfloor : (routeVisibleWindowNormFloor X : ℂ) ≠ 0 := by
      exact_mod_cast hfloor_pos.ne'
    rw [zeroModeEnvelopeErrorWindowEnergy_eq_floorSq_mul_weightedNormalizedShapeEnergy
      κ X (hsigma hX) hfloor]
    exact mul_le_mul_of_nonneg_left (h.bound hX)
      (routeVisibleWindowNormFloorSq_nonneg X)

end

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeWeightedEnergy
