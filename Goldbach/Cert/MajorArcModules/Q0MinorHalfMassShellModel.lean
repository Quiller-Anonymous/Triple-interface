import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise

/-!
Deterministic shell-model comparison layer for the arithmetic half-mass endpoint.

This file keeps the live shell frontier small:

* a pointwise `O(1)` target for `halfMassArithmeticModel` on the canonical even window;
* a deterministic comparison from the shell residual energy to the unscaled half-mass error energy.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellModel

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

/--
Pointwise canonical-window `O(1)` control of the half-mass arithmetic model.

This is the remaining multiplicative input needed by the shell route once denominator control for
`unscaledGeometricZeroSliceMass` has been established.
-/
structure HalfMassArithmeticModelWindowNormTarget (Cmodel : ℝ) : Prop where
  Cmodel_nonneg : 0 ≤ Cmodel
  bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H → ‖halfMassArithmeticModel X N‖ ≤ Cmodel

/--
Deterministic shell-energy comparison from a pointwise model bound and the canonical-window
nonvanishing target for the unscaled geometric zero slice.
-/
theorem halfMassShellResidualWindowEnergy_le_model_sq_mul_halfMassErrorWindowEnergy
    {c0 c1 Cmodel : ℝ}
    (hMass : UnscaledGeometricZeroSliceMassWindowNormTarget c0 c1)
    (hModel : HalfMassArithmeticModelWindowNormTarget Cmodel)
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassShellResidualWindowEnergy X
      ≤
    4 * Cmodel ^ 2 * unscaledGeometricZeroSliceHalfMassErrorWindowEnergy X := by
  have hNZ : ∀ N ∈ EvenIn X H, unscaledGeometricZeroSliceMass X N ≠ 0 := by
    intro N hN
    exact hMass.nonzero hX hN
  rw [halfMassShellResidualWindowEnergy_eq_weighted_halfMassError X hNZ]
  unfold unscaledGeometricZeroSliceHalfMassErrorWindowEnergy
  have hsum :
      ∑ N ∈ EvenIn X H, 4 * ‖halfMassArithmeticModel X N‖ ^ 2
          * ‖unscaledGeometricZeroSliceHalfMassError X N‖ ^ 2
        ≤
      ∑ N ∈ EvenIn X H, 4 * Cmodel ^ 2
          * ‖unscaledGeometricZeroSliceHalfMassError X N‖ ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro N hN
    have hmodelN : ‖halfMassArithmeticModel X N‖ ≤ Cmodel := hModel.bound hX hN
    have hmodel_sq : ‖halfMassArithmeticModel X N‖ ^ 2 ≤ Cmodel ^ 2 := by
      nlinarith [hmodelN, norm_nonneg (halfMassArithmeticModel X N), hModel.Cmodel_nonneg]
    have herr_nonneg : 0 ≤ ‖unscaledGeometricZeroSliceHalfMassError X N‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmodel_sq (by norm_num : 0 ≤ (4 : ℝ)))
      herr_nonneg
  have hEq :
      ∑ N ∈ EvenIn X H, 4 * Cmodel ^ 2 * ‖unscaledGeometricZeroSliceHalfMassError X N‖ ^ 2
        =
      4 * Cmodel ^ 2 * ∑ N ∈ EvenIn X H, ‖unscaledGeometricZeroSliceHalfMassError X N‖ ^ 2 := by
    rw [Finset.mul_sum]
  exact le_trans hsum (le_of_eq hEq)

/--
Route-sized raw shell-energy bound obtained from a pointwise model bound and the existing unscaled
half-mass window-energy target.
-/
theorem halfMassShellResidualWindowEnergy_le_route_of_model_and_halfMassTarget
    {c0 c1 Cmodel C2 C3 : ℝ}
    (hMass : UnscaledGeometricZeroSliceMassWindowNormTarget c0 c1)
    (hModel : HalfMassArithmeticModelWindowNormTarget Cmodel)
    (hHalfMass : UnscaledGeometricZeroSliceHalfMassTarget C2 C3)
    {X : ℕ} (hX : X0 ≤ X) :
    halfMassShellResidualWindowEnergy X
      ≤
    4 * Cmodel ^ 2
      * (C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
  refine le_trans
    (halfMassShellResidualWindowEnergy_le_model_sq_mul_halfMassErrorWindowEnergy hMass hModel hX)
    ?_
  have hbound := hHalfMass.bound hX
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end
