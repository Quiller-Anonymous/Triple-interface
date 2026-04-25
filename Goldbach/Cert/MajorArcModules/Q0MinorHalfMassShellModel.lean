import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks

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
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks

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

private lemma halfMassShellResidualWindowAverage_norm_sq_le_windowEnergy
    {X : ℕ} :
    ‖halfMassShellResidualWindowAverage X‖ ^ 2
      ≤
    halfMassShellResidualWindowEnergy X := by
  have hcard_nat : (EvenIn X H).card ≠ 0 := by
    refine Finset.card_ne_zero.mpr ?_
    by_cases hEven : Goldbach.Windows.IsEven X
    · exact ⟨X, Goldbach.Windows.mem_EvenIn_self (N := X) (H := H) hEven⟩
    · have h1 : 1 ∈ Finset.range (H + 1) := by
        norm_num [H]
      have hEvenSucc : Goldbach.Windows.IsEven (X + 1) := by
        dsimp [Goldbach.Windows.IsEven] at hEven ⊢
        omega
      unfold Goldbach.Windows.EvenIn Goldbach.Windows.IccShift
      refine ⟨X + 1, Finset.mem_filter.mpr ?_⟩
      refine ⟨Finset.mem_image.mpr ?_, hEvenSucc⟩
      exact ⟨1, h1, by simp⟩
  have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hcard_pos : 0 < ((EvenIn X H).card : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hcard_nat
  have hcard_ge_one : 1 ≤ ((EvenIn X H).card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hcard_nat)
  have hsum :
      ‖∑ N ∈ EvenIn X H, halfMassShellResidual X N‖ ^ 2
        ≤
      ((EvenIn X H).card : ℝ) * ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2 :=
    norm_sum_sq_le_card_mul_sum_norm_sq (s := EvenIn X H) (z := fun N => halfMassShellResidual X N)
  unfold halfMassShellResidualWindowAverage halfMassShellResidualWindowEnergy halfMassShellResidualWindowRawSum
  have havg :
      ‖((↑(EvenIn X H).card : ℂ)⁻¹ * ∑ N ∈ EvenIn X H, halfMassShellResidual X N)‖ ^ 2
        =
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2 * ‖∑ N ∈ EvenIn X H, halfMassShellResidual X N‖ ^ 2 := by
    rw [norm_mul]
    have hnorm_inv : ‖((↑(EvenIn X H).card : ℂ)⁻¹)‖ = (((EvenIn X H).card : ℝ)⁻¹) := by
      rw [norm_inv]
      rw [Complex.norm_natCast]
    rw [hnorm_inv]
    ring
  rw [havg]
  have hmain :
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2 * ‖∑ N ∈ EvenIn X H, halfMassShellResidual X N‖ ^ 2
        ≤
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2
        * (((EvenIn X H).card : ℝ) * ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
  refine le_trans hmain ?_
  have hcard_inv_sq_mul :
      (((EvenIn X H).card : ℝ)⁻¹) ^ 2
        * (((EvenIn X H).card : ℝ) * ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2)
        ≤
      ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2 := by
    have hsum_nonneg : 0 ≤ ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2 := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hfactor_le : (((EvenIn X H).card : ℝ)⁻¹) ^ 2 * ((EvenIn X H).card : ℝ) ≤ 1 := by
      have hcard_nonzero : ((EvenIn X H).card : ℝ) ≠ 0 := ne_of_gt hcard_pos
      have hcard_inv_le_one : ((EvenIn X H).card : ℝ)⁻¹ ≤ 1 := by
        exact (inv_le_one₀ hcard_pos).2 hcard_ge_one
      have hcard_inv_nonneg : 0 ≤ ((EvenIn X H).card : ℝ)⁻¹ := by
        exact inv_nonneg.mpr (le_of_lt hcard_pos)
      have hsq_le : (((EvenIn X H).card : ℝ)⁻¹) ^ 2 ≤ ((EvenIn X H).card : ℝ)⁻¹ := by
        nlinarith [hcard_inv_nonneg, hcard_inv_le_one]
      have hmul_le :
          (((EvenIn X H).card : ℝ)⁻¹) ^ 2 * ((EvenIn X H).card : ℝ)
            ≤
          ((EvenIn X H).card : ℝ)⁻¹ * ((EvenIn X H).card : ℝ) := by
        exact mul_le_mul_of_nonneg_right hsq_le (le_of_lt hcard_pos)
      have hcancel : ((EvenIn X H).card : ℝ)⁻¹ * ((EvenIn X H).card : ℝ) = 1 := by
        field_simp [hcard_nonzero]
      exact le_trans hmul_le (by rw [hcancel])
    nlinarith [hfactor_le, hsum_nonneg]
  calc
    (((EvenIn X H).card : ℝ)⁻¹) ^ 2
        * (((EvenIn X H).card : ℝ) * ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2)
      ≤
    ∑ N ∈ EvenIn X H, ‖halfMassShellResidual X N‖ ^ 2 := hcard_inv_sq_mul

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

/--
Route-sized bound for the shell-residual window average.

This packages the shell branch in the exact scalar form needed to test whether the normalized Route
A main term can treat the shell contribution as lower-order.
-/
theorem halfMassShellResidualWindowAverage_norm_sq_le_route_of_model_and_halfMassTarget
    {c0 c1 Cmodel C2 C3 : ℝ}
    (hMass : UnscaledGeometricZeroSliceMassWindowNormTarget c0 c1)
    (hModel : HalfMassArithmeticModelWindowNormTarget Cmodel)
    (hHalfMass : UnscaledGeometricZeroSliceHalfMassTarget C2 C3)
    {X : ℕ} (hX : X0 ≤ X) :
    ‖halfMassShellResidualWindowAverage X‖ ^ 2
      ≤
    4 * Cmodel ^ 2
      * (C2 * ((H : ℝ) / (X : ℝ))
          + C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
  refine le_trans halfMassShellResidualWindowAverage_norm_sq_le_windowEnergy ?_
  exact halfMassShellResidualWindowEnergy_le_route_of_model_and_halfMassTarget hMass hModel hHalfMass hX

end
