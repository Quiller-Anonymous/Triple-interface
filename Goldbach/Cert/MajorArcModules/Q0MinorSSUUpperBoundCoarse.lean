import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
import Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
import Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundSpec
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundPrep
import Goldbach.PPBoundCore
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Coarse certified upper bound for the ε₁ SSU / nonzero-mode piece.

This file closes the remaining SSU seam with a deliberately slack argument:

* `q0NormFactor` varies across the window by at most a factor `2`;
* `aTerm2Mass = 0` on the pinned range `X ≥ X0`;
* `coeffMass` and `diagMass` are bounded by the same tiny top-window coefficient cap;
* `kernelMassNZEven` is controlled by the trivial constant-mode bound
  `‖Ŵ(t)‖ ≤ 60000 / X`.

The resulting constant still fits comfortably under the advertised SSU cap `A2 = 80`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundCoarse

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
open Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundSpec
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundPrep
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

set_option maxRecDepth 4096

private abbrev UC' : Type :=
  Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private noncomputable def window (X : ℕ) : Finset ℕ :=
  Finset.Icc (X / 2 - H) (X / 2 + H)

private lemma H_le_X_div2 {X : ℕ} (hX : X0 ≤ X) : H ≤ X / 2 := by
  have hhalf : (2 : ℕ) * H ≤ X := by
    have hbase : (2 : ℕ) * H ≤ X0 := by norm_num [H, X0]
    exact le_trans hbase hX
  exact Nat.le_div_iff_mul_le (by decide : 0 < 2) |>.2 hhalf

private lemma card_evenIn_le_H_add_one (X : ℕ) :
    (EvenIn X H).card ≤ H + 1 := by
  classical
  unfold EvenIn IccShift
  have hsub :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)
        ⊆
      (Finset.range (H + 1)).image (fun k : ℕ => X + k) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcard_le :
      (((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)).card
        ≤
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card :=
    Finset.card_le_card hsub
  have hcard_eq :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card = H + 1 := by
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro a b hab
    exact Nat.add_left_cancel hab
  exact le_trans hcard_le (le_of_eq hcard_eq)

private lemma q0NormFactor_sq_le_two_normFactorSq
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖q0NormFactor N‖ ^ 2 ≤ (2 : ℝ) * normFactorSq X := by
  have hXleN : X ≤ N := X_le_of_mem_EvenIn (X := X) (N := N) hN
  have hX0leN : X0 ≤ N := le_trans hX hXleN
  have hX0leXH : X0 ≤ X + H := le_trans hX (Nat.le_add_right X H)
  have hlogN_ge13 : (13 : ℝ) ≤ Real.log (N : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leN
  have hlogXH_ge13 : (13 : ℝ) ≤ Real.log ((X + H : ℕ) : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX0leXH
  have hlogN_pos : 0 < Real.log (N : ℝ) := by linarith
  have hlogXH_pos : 0 < Real.log ((X + H : ℕ) : ℝ) := by linarith
  have hXH_le_twoX : X + H ≤ 2 * X := by
    have hHX : H ≤ X := le_trans (by decide : H ≤ X0) hX
    omega
  have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos_nat
  have hXHpos : (0 : ℝ) < (((X + H : ℕ) : ℝ)) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX0leXH)
  have hlogXH_le :
      Real.log ((X + H : ℕ) : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    exact Real.log_le_log hXHpos (by exact_mod_cast hXH_le_twoX)
  have hlog_two_mul :
      Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 : ℝ) + Real.log (X : ℝ) := by
    have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hXpos_nat)
    simpa [Nat.cast_mul] using Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXne
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have hlogX_leN : Real.log (X : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log hXpos (by exact_mod_cast hXleN)
  have hlogXH_le14 :
      Real.log ((X + H : ℕ) : ℝ) ≤ ((14 : ℝ) / 13) * Real.log (N : ℝ) := by
    have hone :
        1 ≤ ((1 : ℝ) / 13) * Real.log (N : ℝ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left hlogN_ge13 (show 0 ≤ (1 : ℝ) / 13 by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      Real.log ((X + H : ℕ) : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := hlogXH_le
      _ = Real.log (2 : ℝ) + Real.log (X : ℝ) := hlog_two_mul
      _ ≤ 1 + Real.log (N : ℝ) := by linarith
      _ ≤ ((1 : ℝ) / 13) * Real.log (N : ℝ) + Real.log (N : ℝ) := by
            exact add_le_add_right hone _
      _ = ((14 : ℝ) / 13) * Real.log (N : ℝ) := by ring
  have hratio :
      Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ) ≤ (14 : ℝ) / 13 := by
    have hmul :
        Real.log ((X + H : ℕ) : ℝ) * (Real.log (N : ℝ))⁻¹
          ≤
        (((14 : ℝ) / 13) * Real.log (N : ℝ)) * (Real.log (N : ℝ))⁻¹ := by
      exact mul_le_mul_of_nonneg_right hlogXH_le14 (inv_nonneg.mpr (le_of_lt hlogN_pos))
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 := hlogN_pos.ne'
    calc
      Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ)
          = Real.log ((X + H : ℕ) : ℝ) * (Real.log (N : ℝ))⁻¹ := by
              rw [div_eq_mul_inv]
      _ ≤ (((14 : ℝ) / 13) * Real.log (N : ℝ)) * (Real.log (N : ℝ))⁻¹ := hmul
      _ = (14 : ℝ) / 13 := by
            field_simp [hlogN_ne]
  have hratio_nonneg :
      0 ≤ Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg (le_of_lt hlogXH_pos) (le_of_lt hlogN_pos)
  have hratio4 :
      (Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ)) ^ 4 ≤ ((14 : ℝ) / 13) ^ 4 := by
    exact pow_le_pow_left₀ hratio_nonneg hratio 4
  have hrew :
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 =
        (Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ)) ^ 4 * normFactorSq X := by
    rw [Q0MinorNormalizedEnergy.norm_q0NormFactor, normFactorSq]
    field_simp [hlogN_pos.ne', hlogXH_pos.ne']
  calc
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
        =
      (Real.log ((X + H : ℕ) : ℝ) / Real.log (N : ℝ)) ^ 4 * normFactorSq X := hrew
    _ ≤ ((14 : ℝ) / 13) ^ 4 * normFactorSq X := by
          exact mul_le_mul_of_nonneg_right hratio4 (normFactorSq_nonneg X)
    _ ≤ (2 : ℝ) * normFactorSq X := by
          exact mul_le_mul_of_nonneg_right (by norm_num : ((14 : ℝ) / 13) ^ 4 ≤ 2)
            (normFactorSq_nonneg X)

private lemma norm_majorArcWeightC_eq_majorArcWeight (X : ℕ) (Δ : ℝ) (α : ℝ) :
    ‖majorArcWeightC X Δ α‖ = majorArcWeight X Δ α := by
  by_cases hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ
  · simp [majorArcWeightC, majorArcWeight, hα]
  · simp [majorArcWeightC, majorArcWeight, hα]

private lemma norm_majorArcWeightFourier_le_constMode (X : ℕ) (Δ : ℝ) (t : ℤ) :
    ‖majorArcWeightFourier X Δ t‖ ≤ majorArcConstMode X Δ := by
  have hab01 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  unfold majorArcWeightFourier
  have hnorm :
      ‖∫ α in (0 : ℝ)..(1 : ℝ),
          majorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖
        ≤
      ∫ α in (0 : ℝ)..(1 : ℝ),
        ‖majorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖ := by
    exact
      (intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun α : ℝ =>
          majorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC') : ℂ)) hab01)
  have hrew :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          ‖majorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖)
        =
      majorArcConstMode X Δ := by
    unfold majorArcConstMode
    refine intervalIntegral.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro α
    intro _hα
    have hchar : ‖(fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖ = 1 := by
      simpa [fourier_apply] using
        (Circle.norm_coe (AddCircle.toCircle (t • (α : UC'))))
    calc
      ‖majorArcWeightC X Δ α * (fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖
          =
          ‖majorArcWeightC X Δ α‖ * ‖(fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖ := by
            simpa [norm_mul]
      _ = majorArcWeight X Δ α := by
            have hW :
                ‖majorArcWeightC X Δ α‖ = majorArcWeight X Δ α :=
              norm_majorArcWeightC_eq_majorArcWeight (X := X) (Δ := Δ) (α := α)
            calc
              ‖majorArcWeightC X Δ α‖ * ‖(fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖
                  = majorArcWeight X Δ α * ‖(fourier (T := (1 : ℝ)) t (α : UC') : ℂ)‖ := by
                      simpa [hW]
              _ = majorArcWeight X Δ α * 1 := by
                      simpa using (congrArg (fun z => majorArcWeight X Δ α * z) hchar)
              _ = majorArcWeight X Δ α := by simp
  exact le_trans hnorm (le_of_eq hrew)

private lemma majorArcConstMode_le_60000_div_X {X : ℕ} (hX : X0 ≤ X) :
    majorArcConstMode X (1 : ℝ) ≤ (60000 : ℝ) / (X : ℝ) := by
  have hXpos : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hΔ : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have hraw :
      majorArcConstMode X (1 : ℝ) ≤ (2 * (30000 : ℝ)) / (X : ℝ) := by
    simpa [Goldbach.AO_OffDiag.TailBlock.Q0, mul_assoc, mul_left_comm, mul_comm] using
      (majorArcConstMode_le (X := X) (Δ := (1 : ℝ)) hΔ hXpos)
  have hnum : (2 : ℝ) * (30000 : ℝ) = (60000 : ℝ) := by norm_num
  simpa [hnum] using hraw

private lemma kernelMassNZEven_le_base
    {X N : ℕ} (hX : X0 ≤ X) :
    kernelMassNZEven X Δ_canon N
      ≤
    ((2 * N + 1 : ℕ) : ℝ) * ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
  classical
  have hconst_nonneg : 0 ≤ (60000 : ℝ) / (X : ℝ) := by
    have hXpos : 0 < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    exact div_nonneg (by norm_num) (le_of_lt hXpos)
  have hterm :
      ∀ t ∈ ((Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0).filter Even,
        ‖majorArcWeightFourier X Δ_canon t‖ ^ 2 ≤ ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
    intro t _ht
    have h0 : ‖majorArcWeightFourier X Δ_canon t‖ ≤ majorArcConstMode X Δ_canon :=
      norm_majorArcWeightFourier_le_constMode (X := X) (Δ := Δ_canon) (t := t)
    have h1 : majorArcConstMode X Δ_canon ≤ (60000 : ℝ) / (X : ℝ) := by
      have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
      have hraw :
          majorArcConstMode X (1 : ℝ) ≤ (2 * (30000 : ℝ)) / (X : ℝ) := by
        simpa [Goldbach.AO_OffDiag.TailBlock.Q0, mul_assoc, mul_left_comm, mul_comm] using
          (majorArcConstMode_le (X := X) (Δ := (1 : ℝ)) (by norm_num) hXpos_nat)
      norm_num [Δ_canon] at hraw ⊢
      exact hraw
    have hle : ‖majorArcWeightFourier X Δ_canon t‖ ≤ (60000 : ℝ) / (X : ℝ) := le_trans h0 h1
    have hright : 0 ≤ (60000 : ℝ) / (X : ℝ) := hconst_nonneg
    have hleft : 0 ≤ ‖majorArcWeightFourier X Δ_canon t‖ := norm_nonneg _
    have hmul :
        ‖majorArcWeightFourier X Δ_canon t‖ * ‖majorArcWeightFourier X Δ_canon t‖
          ≤ ((60000 : ℝ) / (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) :=
      mul_le_mul hle hle hleft hright
    simpa [pow_two] using hmul
  have hsum_le :
      kernelMassNZEven X Δ_canon N
        ≤
      (((((Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0).filter Even).card : ℕ) : ℝ)
          * ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
    unfold kernelMassNZEven
    have :=
      (Finset.sum_le_sum (fun t ht => hterm t ht) :
        (∑ t ∈ ((Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0).filter Even,
            ‖majorArcWeightFourier X Δ_canon t‖ ^ 2)
          ≤
        ∑ _t ∈ ((Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0).filter Even,
          ((60000 : ℝ) / (X : ℝ)) ^ 2)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hcard_le :
      ((((Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0).filter Even).card : ℕ)
        ≤
      (Q0MajorTailTTStarToeplitzScaffold.tSupport N).card := by
    have hsub :
        (((Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0).filter Even)
          ⊆
        Q0MajorTailTTStarToeplitzScaffold.tSupport N := by
      intro t ht
      have ht' : t ∈ (Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0 :=
        (Finset.mem_filter.mp ht).1
      exact (Finset.mem_erase.mp ht').2
    exact Finset.card_le_card hsub
  have hcard_exact : (Q0MajorTailTTStarToeplitzScaffold.tSupport N).card = 2 * N + 1 := by
    simpa [Q0MajorTailTTStarToeplitzScaffold.tSupport] using
      (Goldbach.PPBoundCore.card_Icc_neg_to_pos (H := N))
  have hcard_le' :
      (((((Q0MajorTailTTStarToeplitzScaffold.tSupport N).erase 0).filter Even).card : ℕ) : ℝ)
        ≤
      ((2 * N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_trans hcard_le (le_of_eq hcard_exact))
  exact le_trans hsum_le (by
    have h0 : 0 ≤ ((60000 : ℝ) / (X : ℝ)) ^ 2 := sq_nonneg _
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hcard_le' h0))

private lemma kernelMassNZEven_le_coarse
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    kernelMassNZEven X Δ_canon N
      ≤
    (3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)) := by
  have hbase := kernelMassNZEven_le_base (X := X) (N := N) hX
  have h2H1 : 2 * H + 1 ≤ X := by
    have hbase' : 2 * H + 1 ≤ X0 := by norm_num [H, X0]
    exact le_trans hbase' hX
  have hNcard : ((2 * N + 1 : ℕ) : ℝ) ≤ (3 : ℝ) * (X : ℝ) := by
    have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
    have hnat : 2 * N + 1 ≤ 3 * X := by
      omega
    exact_mod_cast hnat
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  have hmul :
      ((2 * N + 1 : ℕ) : ℝ) * ((60000 : ℝ) / (X : ℝ)) ^ 2
        ≤
      ((3 : ℝ) * (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
    exact mul_le_mul_of_nonneg_right hNcard (sq_nonneg _)
  have hrew :
      ((3 : ℝ) * (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) ^ 2
        =
      (3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)) := by
    field_simp [hXne]
  exact le_trans hbase (le_trans hmul (by simpa [hrew]))

private lemma aTerm2Mass_eq_zero_of_large {X : ℕ} (hX : X0 ≤ X) :
    aTerm2Mass X = 0 := by
  have hHX : H ≤ X / 2 := H_le_X_div2 (X := X) hX
  have hX2 : 2 < X / 2 - H := by
    have : 490000 ≤ X / 2 - H := by
      have hX0 : X0 / 2 - H = 490000 := by decide
      have hmono : X0 / 2 ≤ X / 2 := Nat.div_le_div_right hX
      have : X0 / 2 - H ≤ X / 2 - H := Nat.sub_le_sub_right hmono H
      simpa [hX0] using this
    exact lt_of_lt_of_le (by decide : 2 < 490000) this
  have hnot : 2 ∉ window X := by
    intro hmem
    have hge : X / 2 - H ≤ 2 := (Finset.mem_Icc.mp hmem).1
    exact not_lt_of_ge hge hX2
  have hnot' : 2 ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by
    simpa [window] using hnot
  have hwX0 : Goldbach.BG_Bank.wX X 2 = 0 := by
    simp [Goldbach.BG_Bank.wX, hnot']
  unfold aTerm2Mass Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm
  simp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm, hwX0]

private lemma coeffMass_sq_le_inv40000_sq {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (coeffMass X N) ^ 2 ≤ ((1 : ℝ) / 40000) ^ 2 := by
  have hmono : coeffMass X N ≤ coeffMass X (X + H) := by
    exact coeffMass_mono_N (le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN)
  have htop : coeffMass X (X + H) ≤ (10001 : ℝ) / (20001 : ℝ) ^ 2 :=
    coeffMass_le_10001_div_20001_sq hX
  have hcoeff_nonneg : 0 ≤ coeffMass X N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcap_nonneg : 0 ≤ (10001 : ℝ) / (20001 : ℝ) ^ 2 := by positivity
  have hsq :
      (coeffMass X N) ^ 2
        ≤
      ((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2 := by
    nlinarith [hmono, htop, hcoeff_nonneg, hcap_nonneg]
  exact le_trans hsq (by norm_num)

private lemma weight0_sq_le_60000_div_X
    {X : ℕ} (hX : X0 ≤ X) :
    ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 ≤ (60000 : ℝ) / (X : ℝ) := by
  have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos_nat
  have hsq :
      ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 ≤ ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
    have h0 :
        ‖majorArcWeightFourier X Δ_canon 0‖ ≤ (60000 : ℝ) / (X : ℝ) := by
      have hraw :=
        norm_majorArcWeightFourier_zero_le
          (X := X) (Δ := (1 : ℝ)) (by norm_num) hXpos_nat
      norm_num [Δ_canon, Goldbach.AO_OffDiag.TailBlock.Q0] at hraw ⊢
      exact hraw
    have hright : 0 ≤ (60000 : ℝ) / (X : ℝ) := by
      exact div_nonneg (by norm_num) (le_of_lt hXpos)
    have hleft : 0 ≤ ‖majorArcWeightFourier X Δ_canon 0‖ := norm_nonneg _
    have hmul :
        ‖majorArcWeightFourier X Δ_canon 0‖ * ‖majorArcWeightFourier X Δ_canon 0‖
          ≤ ((60000 : ℝ) / (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) :=
      mul_le_mul h0 h0 hleft hright
    simpa [pow_two] using hmul
  have hsmall : (60000 : ℝ) / (X : ℝ) ≤ 1 := by
    have hXr : (1000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    rw [div_le_iff₀ hXpos]
    nlinarith
  have hnonneg : 0 ≤ (60000 : ℝ) / (X : ℝ) := by
    exact div_nonneg (by norm_num) (le_of_lt hXpos)
  have hsq_le : ((60000 : ℝ) / (X : ℝ)) ^ 2 ≤ (60000 : ℝ) / (X : ℝ) := by
    nlinarith
  exact le_trans hsq hsq_le

private noncomputable def coarseBracketCoeff : ℝ :=
  (2 : ℝ) * (((1 : ℝ) / 40000) ^ 2) * (21600180000 : ℝ)

private noncomputable def coarsePointwiseCoeff : ℝ :=
  (4 : ℝ) * (((1 : ℝ) / 40000) ^ 2) * (21600180000 : ℝ)

private lemma pointwiseUpper_le_coarse
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    pointwiseUpper X N
      ≤
    coarsePointwiseCoeff * (1 / (X : ℝ)) * normFactorSq X := by
  have hq0 := q0NormFactor_sq_le_two_normFactorSq hX hN
  have hker := kernelMassNZEven_le_coarse hX hN
  have hcoeff := coeffMass_sq_le_inv40000_sq hX hN
  have hdiag : diagMass X N ≤ ((1 : ℝ) / 40000) ^ 2 := by
    exact le_trans (diagMass_le_coeffMass_sq X N) hcoeff
  have hweight := weight0_sq_le_60000_div_X hX
  have hodd0 :
      (4 * kernelMassNZOdd X Δ_canon N) * aTerm2Mass X * coeffMass X N = 0 := by
    simp [aTerm2Mass_eq_zero_of_large hX]
  have hterm1 :
      (2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
        ≤
      (2 * ((3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)))) * (((1 : ℝ) / 40000) ^ 2) := by
    have hker2 :
        2 * kernelMassNZEven X Δ_canon N
          ≤
        2 * ((3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ))) :=
      mul_le_mul_of_nonneg_left hker (by norm_num)
    exact mul_le_mul hker2 hcoeff (by positivity) (by positivity)
  have hterm3 :
      (3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * diagMass X N
        ≤
      (3 * ((60000 : ℝ) / (X : ℝ))) * (((1 : ℝ) / 40000) ^ 2) := by
    have hweight3 :
        3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2
          ≤
        3 * ((60000 : ℝ) / (X : ℝ)) :=
      mul_le_mul_of_nonneg_left hweight (by norm_num)
    have hdiag_nonneg : 0 ≤ diagMass X N := by
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hrhs_nonneg : 0 ≤ 3 * ((60000 : ℝ) / (X : ℝ)) := by
      positivity
    exact mul_le_mul hweight3 hdiag hdiag_nonneg hrhs_nonneg
  have hker_nonneg : 0 ≤ kernelMassNZEven X Δ_canon N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoeff_nonneg : 0 ≤ coeffMass X N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hdiag_nonneg : 0 ≤ diagMass X N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hinside0 :
      0 ≤
        2 *
          ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
            +
          (4 * kernelMassNZOdd X Δ_canon N) * aTerm2Mass X * coeffMass X N
            +
          (3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * diagMass X N) := by
    rw [hodd0]
    have hweight_nonneg : 0 ≤ ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2 := sq_nonneg _
    nlinarith
  have hinside :
      2 *
          ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
            +
          (4 * kernelMassNZOdd X Δ_canon N) * aTerm2Mass X * coeffMass X N
            +
          (3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * diagMass X N)
        ≤
      coarseBracketCoeff * (1 / (X : ℝ)) := by
    rw [hodd0]
    have hsum :
        2 *
            (((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2)
              + 0
              + ((3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * diagMass X N))
          ≤
        2 *
            (((2 * ((3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)))) * (((1 : ℝ) / 40000) ^ 2))
              + 0
              + ((3 * ((60000 : ℝ) / (X : ℝ))) * (((1 : ℝ) / 40000) ^ 2))) := by
      nlinarith [hterm1, hterm3]
    have hrew :
        2 *
            (((2 * ((3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)))) * (((1 : ℝ) / 40000) ^ 2))
              + 0
              + ((3 * ((60000 : ℝ) / (X : ℝ))) * (((1 : ℝ) / 40000) ^ 2)))
          =
        coarseBracketCoeff * (1 / (X : ℝ)) := by
      unfold coarseBracketCoeff
      ring
    exact hsum.trans_eq hrew
  calc
    pointwiseUpper X N
        =
      ‖q0NormFactor N‖ ^ 2
        *
          (2 *
            ((2 * kernelMassNZEven X Δ_canon N) * (coeffMass X N) ^ 2
              +
            (4 * kernelMassNZOdd X Δ_canon N) * aTerm2Mass X * coeffMass X N
              +
            (3 * ‖majorArcWeightFourier X Δ_canon 0‖ ^ 2) * diagMass X N)) := by
              rfl
    _ ≤ ((2 : ℝ) * normFactorSq X) * (coarseBracketCoeff * (1 / (X : ℝ))) := by
          have hnorm_nonneg : 0 ≤ (2 : ℝ) * normFactorSq X := by
            exact mul_nonneg (by norm_num) (normFactorSq_nonneg X)
          have hinside_nonneg : 0 ≤ coarseBracketCoeff * (1 / (X : ℝ)) := by
            have hXpos : (0 : ℝ) < (X : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
            have hcoeff_nonneg : 0 ≤ coarseBracketCoeff := by
              unfold coarseBracketCoeff
              positivity
            exact mul_nonneg hcoeff_nonneg (one_div_nonneg.mpr (le_of_lt hXpos))
          exact mul_le_mul hq0 hinside hinside0 hnorm_nonneg
    _ = coarsePointwiseCoeff * (1 / (X : ℝ)) * normFactorSq X := by
          unfold coarsePointwiseCoeff coarseBracketCoeff
          ring

theorem windowUpper_le_target (X : ℕ) (hX : X0 ≤ X) :
    windowUpper X ≤ normFactorSq X * ((80 : ℝ) * ((H : ℝ) / (X : ℝ))) := by
  have hsum :
      windowUpper X
        ≤
      (((EvenIn X H).card : ℝ) * coarsePointwiseCoeff) * (1 / (X : ℝ)) * normFactorSq X := by
    unfold windowUpper
    calc
      ∑ N ∈ EvenIn X H, pointwiseUpper X N
          ≤
        ∑ _N ∈ EvenIn X H, coarsePointwiseCoeff * (1 / (X : ℝ)) * normFactorSq X := by
              refine Finset.sum_le_sum ?_
              intro N hN
              exact pointwiseUpper_le_coarse hX hN
      _ = (((EvenIn X H).card : ℝ) * coarsePointwiseCoeff) * (1 / (X : ℝ)) * normFactorSq X := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
  have hcard : (((EvenIn X H).card : ℝ)) ≤ ((H + 1 : ℕ) : ℝ) := by
    exact_mod_cast card_evenIn_le_H_add_one X
  have hcp_nonneg : 0 ≤ coarsePointwiseCoeff := by
    unfold coarsePointwiseCoeff
    positivity
  have hcoeff :
      (((EvenIn X H).card : ℝ) * coarsePointwiseCoeff)
        ≤
      ((H + 1 : ℕ) : ℝ) * coarsePointwiseCoeff := by
    exact mul_le_mul_of_nonneg_right hcard hcp_nonneg
  have hnum :
      ((H + 1 : ℕ) : ℝ) * coarsePointwiseCoeff ≤ (80 : ℝ) * (H : ℝ) := by
    unfold coarsePointwiseCoeff
    norm_num [H]
  have hfactor :
      0 ≤ (1 / (X : ℝ)) * normFactorSq X := by
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    exact mul_nonneg (one_div_nonneg.mpr (le_of_lt hXpos)) (normFactorSq_nonneg X)
  calc
    windowUpper X
        ≤
      ((((EvenIn X H).card : ℝ) * coarsePointwiseCoeff) * (1 / (X : ℝ)) * normFactorSq X) := hsum
    _ ≤ (((H + 1 : ℕ) : ℝ) * coarsePointwiseCoeff) * (1 / (X : ℝ)) * normFactorSq X := by
          have hstep :
              (((EvenIn X H).card : ℝ) * coarsePointwiseCoeff) * (1 / (X : ℝ))
                ≤
              (((H + 1 : ℕ) : ℝ) * coarsePointwiseCoeff) * (1 / (X : ℝ)) := by
            have hXpos : (0 : ℝ) < (X : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
            exact mul_le_mul_of_nonneg_right hcoeff (one_div_nonneg.mpr (le_of_lt hXpos))
          exact mul_le_mul_of_nonneg_right hstep (normFactorSq_nonneg X)
    _ ≤ ((80 : ℝ) * (H : ℝ)) * (1 / (X : ℝ)) * normFactorSq X := by
          have hstep :
              (((H + 1 : ℕ) : ℝ) * coarsePointwiseCoeff) * (1 / (X : ℝ))
                ≤
              ((80 : ℝ) * (H : ℝ)) * (1 / (X : ℝ)) := by
            have hXpos : (0 : ℝ) < (X : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
            exact mul_le_mul_of_nonneg_right hnum (one_div_nonneg.mpr (le_of_lt hXpos))
          exact mul_le_mul_of_nonneg_right hstep (normFactorSq_nonneg X)
    _ = normFactorSq X * ((80 : ℝ) * ((H : ℝ) / (X : ℝ))) := by
          ring

theorem nonzeroModeEnergyBound_80 :
    Q0MinorTTStarFrequencyExpansion.canonicalExpansion.NonzeroModeEnergyBound (80 : ℝ) := by
  refine nonzeroModeEnergyBound_of_windowUpper (U := (80 : ℝ)) (by norm_num) ?_
  intro X hX
  exact windowUpper_le_target X hX

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundCoarse
