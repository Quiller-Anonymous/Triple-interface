import Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIDeterministic

/-!
`Q0MinorZeroModeAnalysis` is a theorem-facing layer for the route-visible zero mode.

After the weighted-channel cleanup, the current route sees

`minorResidual = zeroMode + meanChannel`.

This file isolates the first term of that split in a form that is useful for the next stage of
mathematical analysis:

* it identifies the weighted `t = 0` channel with the old canonical Type-I part;
* it exposes the exact finite `(n,m)` formula for that zero mode;
* it records the deterministic diagonal-mass bounds already available for it.

No new estimates are proved here. This is an interface layer for the live obstruction.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeAnalysis

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIDeterministic
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

set_option maxRecDepth 4096

/-- The route-visible zero mode is exactly the `t = 0` weighted minor coefficient. -/
theorem routeZeroMode_eq_weightedMinorCoeff_zero
    (X N : ℕ) :
    canonicalExpansion.typeIPart X N = weightedMinorCoeff X N 0 :=
  canonicalExpansion_typeIPart_eq_weighted_zeroMode X N

/-- The zero-mode slice evaluated at `t = 0` is the route-visible zero mode. -/
theorem routeZeroMode_eq_zeroModeSlice_zero
    (X N : ℕ) :
    canonicalExpansion.typeIPart X N = zeroModeSlice X N 0 :=
  canonicalExpansion_typeIPart_eq_zeroModeSlice X N

/--
Exact finite arithmetic formula for the route-visible zero mode.

This is the precise `t = 0` coefficient of the canonical minor frequency expansion.
-/
theorem weightedMinorCoeff_zero_eq_q0NormFactor_mul_sum_nmSupport0
    (X N : ℕ) :
    weightedMinorCoeff X N 0
      =
    q0NormFactor N
      * ∑ nm ∈ nmSupportOfT N 0,
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.1
            * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.2
            * minorArcWeightFourier X Δ_canon 0
            * KHatH (kFn nm) := by
  calc
    weightedMinorCoeff X N 0 = canonicalExpansion.typeIPart X N := by
      symm
      exact canonicalExpansion_typeIPart_eq_weighted_zeroMode X N
    _ =
      q0NormFactor N
        * ∑ nm ∈ nmSupportOfT N 0,
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.1
              * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.2
              * minorArcWeightFourier X Δ_canon 0
              * KHatH (kFn nm) := by
        simpa using typeIPart_eq_q0NormFactor_mul_sum_nmSupport0 (X := X) (N := N)

/-- The same exact formula written through the explicit `zeroModeSlice`. -/
theorem zeroModeSlice_zero_eq_q0NormFactor_mul_sum_nmSupport0
    (X N : ℕ) :
    zeroModeSlice X N 0
      =
    q0NormFactor N
      * ∑ nm ∈ nmSupportOfT N 0,
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.1
            * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.2
            * minorArcWeightFourier X Δ_canon 0
            * KHatH (kFn nm) := by
  calc
    zeroModeSlice X N 0 = weightedMinorCoeff X N 0 := zeroModeSlice_apply_zero X N
    _ =
      q0NormFactor N
        * ∑ nm ∈ nmSupportOfT N 0,
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.1
              * Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X nm.2
              * minorArcWeightFourier X Δ_canon 0
              * KHatH (kFn nm) := weightedMinorCoeff_zero_eq_q0NormFactor_mul_sum_nmSupport0 X N

/--
Deterministic diagonal-mass control for the route-visible zero mode.

This is the direct weighted-zero-mode version of the old Type-I pointwise estimate.
-/
theorem weightedMinorCoeff_zero_norm_sq_le_weight0_sq_mul_diagMass
    (X N : ℕ) :
    ‖weightedMinorCoeff X N 0‖ ^ 2
      ≤
    ‖q0NormFactor N‖ ^ 2
      * (‖minorArcWeightFourier X Δ_canon 0‖ ^ 2 * diagMass X N) := by
  rw [← canonicalExpansion_typeIPart_eq_weighted_zeroMode]
  simpa using typeIPart_norm_sq_le_weight0_sq_mul_diagMass (X := X) (N := N)

/--
Complementary deterministic control phrased with the major-arc weight complement at `t = 0`.
-/
theorem weightedMinorCoeff_zero_norm_sq_le_complement_weight_sq_mul_diagMass
    (X N : ℕ) :
    ‖weightedMinorCoeff X N 0‖ ^ 2
      ≤
    ‖q0NormFactor N‖ ^ 2
      * (‖1 - Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier
            X Δ_canon 0‖ ^ 2 * diagMass X N) := by
  rw [← canonicalExpansion_typeIPart_eq_weighted_zeroMode]
  simpa using typeIPart_norm_sq_le_complement_weight_sq_mul_diagMass (X := X) (N := N)

/--
Route-facing form of the corrected weighted decomposition, restated for zero-mode analysis.
-/
theorem minorResidual_eq_routeZeroMode_add_meanChannel
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ minorWindow X) :
    Q0MinorNormalizedEnergy.minorResidual X N Δ_canon
      =
    canonicalExpansion.typeIPart X N
      + familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N := by
  rw [canonicalExpansion_typeIPart_eq_weighted_zeroMode]
  exact minorResidual_eq_zeroMode_add_meanChannel hX hN

end

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeAnalysis
