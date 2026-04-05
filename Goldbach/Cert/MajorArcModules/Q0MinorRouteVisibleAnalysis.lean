import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeAnalysis
import Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelCerts

/-!
`Q0MinorRouteVisibleAnalysis` isolates the actual route-visible minor object after the weighted
channel cleanup.

The key correction is that the current route does not see the old `coeffArith` family directly.
It sees only

`zeroMode + meanChannel`.

This file packages that object explicitly, in the exact finite-dimensional form that the new
diagnostic program needs:

* the route-visible slice as a family on the `t`-index set;
* the support enlarged by `t = 0`;
* the exact decomposition into a zero spike plus an ambient constant nonzero channel.

No new estimates are proved here. This is a theorem-facing interface layer for the conservative
route-visible diagnostic program.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleAnalysis

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeAnalysis
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

set_option maxRecDepth 4096

/-- The finite support on which the route-visible family lives: ambient nonzero support plus `0`. -/
noncomputable def routeVisibleSupport (X : ℕ) : Finset ℤ :=
  insert 0 (canonicalMinorAmbientSupport X)

/-- The exact route-visible family slice on the `t`-index set. -/
noncomputable def routeVisibleSlice (X N : ℕ) : ℤ → ℂ :=
  fun t => zeroModeSlice X N t + meanChannelSlice X N t

/-- Basis spike at the zero mode. -/
noncomputable def routeVisibleZeroBasis : ℤ → ℂ :=
  fun t => if t = 0 then 1 else 0

/-- Basis indicator of the ambient nonzero support. -/
noncomputable def routeVisibleMeanBasis (X : ℕ) : ℤ → ℂ :=
  fun t => if t ∈ canonicalMinorAmbientSupport X then 1 else 0

/-- The scalar coefficient of the zero-basis component. -/
noncomputable def routeVisibleZeroCoeff (X N : ℕ) : ℂ :=
  weightedMinorCoeff X N 0

/-- The scalar coefficient of the ambient-constant mean-channel component. -/
noncomputable def routeVisibleMeanCoeff (X N : ℕ) : ℂ :=
  coeffMeanOn (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N)

/-- The route-visible scalar seen by the current slice-sum operator. -/
noncomputable def routeVisibleValue (X N : ℕ) : ℂ :=
  routeVisibleZeroCoeff X N
    + familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N

theorem routeVisibleSupport_contains_zero (X : ℕ) : (0 : ℤ) ∈ routeVisibleSupport X := by
  simp [routeVisibleSupport]

theorem zero_not_mem_canonicalMinorAmbientSupport (X : ℕ) :
    (0 : ℤ) ∉ canonicalMinorAmbientSupport X := by
  simp [canonicalMinorAmbientSupport]

theorem routeVisibleSlice_eq_zero_add_mean
    (X N : ℕ) (t : ℤ) :
    routeVisibleSlice X N t = zeroModeSlice X N t + meanChannelSlice X N t := by
  rfl

theorem zeroModeSlice_eq_routeVisibleZeroCoeff_mul_zeroBasis
    (X N : ℕ) :
    zeroModeSlice X N = fun t => routeVisibleZeroCoeff X N * routeVisibleZeroBasis t := by
  funext t
  by_cases ht : t = 0
  · subst t
    simp [routeVisibleZeroCoeff, routeVisibleZeroBasis, zeroModeSlice_apply_zero]
  · simp [routeVisibleZeroBasis, zeroModeSlice_apply_ne_zero ht, ht, routeVisibleZeroCoeff]

theorem meanChannelSlice_eq_routeVisibleMeanCoeff_mul_meanBasis
    (X N : ℕ) :
    meanChannelSlice X N = fun t => routeVisibleMeanCoeff X N * routeVisibleMeanBasis X t := by
  funext t
  by_cases ht : t ∈ canonicalMinorAmbientSupport X
  · simp [routeVisibleMeanCoeff, routeVisibleMeanBasis, ht, meanChannelSlice, meanChannelOn]
  · simp [routeVisibleMeanCoeff, routeVisibleMeanBasis, ht, meanChannelSlice, meanChannelOn]

theorem routeVisibleSlice_eq_rankTwo_basis
    (X N : ℕ) :
    routeVisibleSlice X N
      =
    fun t =>
      routeVisibleZeroCoeff X N * routeVisibleZeroBasis t
        + routeVisibleMeanCoeff X N * routeVisibleMeanBasis X t := by
  funext t
  rw [routeVisibleSlice_eq_zero_add_mean]
  rw [zeroModeSlice_eq_routeVisibleZeroCoeff_mul_zeroBasis]
  rw [meanChannelSlice_eq_routeVisibleMeanCoeff_mul_meanBasis]

theorem routeVisibleValue_eq_minorResidual
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ minorWindow X) :
    routeVisibleValue X N = minorResidual X N Δ_canon := by
  unfold routeVisibleValue routeVisibleZeroCoeff
  symm
  rw [minorResidual_eq_routeZeroMode_add_meanChannel hX hN]
  rw [canonicalExpansion_typeIPart_eq_weighted_zeroMode]

theorem routeVisibleSliceSum_eq_routeVisibleValue
    (X N : ℕ) :
    (∑ t ∈ routeVisibleSupport X, routeVisibleSlice X N t) = routeVisibleValue X N := by
  unfold routeVisibleSupport routeVisibleSlice routeVisibleValue routeVisibleZeroCoeff
  rw [Finset.sum_insert]
  · have hzero :
        zeroModeSlice X N 0 + meanChannelSlice X N 0 = weightedMinorCoeff X N 0 := by
          have hmean0 : meanChannelSlice X N 0 = 0 := by
            simp [meanChannelSlice, meanChannelOn, zero_not_mem_canonicalMinorAmbientSupport]
          rw [zeroModeSlice_apply_zero, hmean0]
          ring
    rw [hzero]
    unfold familySliceSumOn
    refine congrArg (fun z => weightedMinorCoeff X N 0 + z) ?_
    refine Finset.sum_congr rfl ?_
    intro t ht
    have hzeroSlice : zeroModeSlice X N t = 0 := by
      exact zeroModeSlice_apply_ne_zero (by exact Finset.mem_erase.mp ht |>.1)
    simp [hzeroSlice]
  · exact zero_not_mem_canonicalMinorAmbientSupport X

end

end Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleAnalysis
