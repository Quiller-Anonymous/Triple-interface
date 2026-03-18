import Goldbach.PPBoundCore
import Goldbach.BG_Bank
import Goldbach.Cert.MajorArcModules.Q0MajorTailConstModeBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Stage 2 (ε₂-large TT*/Toeplitz): eliminate the remaining project-pinned `U` axiom.

This module provides a deterministic uniform bound

`toeplitzExprTopTight X Δ_canon ≤ U_target` for all `X ≥ X0`,

using only:
* the deterministic TT*/Toeplitz reduction (`sum_kSupport_sq_le_toeplitzExprTopTight`), and
* crude uniform estimates coming from the **windowed + scaled** bank weight `wX`.

No project-pinned axioms remain here.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0
open Goldbach.Cert.MajorArcModules.Q0MajorTailMeanZero
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ABC
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundSpec

noncomputable section

noncomputable abbrev U_target : ℝ :=
  Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromCert.U

private abbrev UC' : Type :=
  Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

lemma U_target_nonneg : 0 ≤ U_target := by
  dsimp [U_target, Q0MajorTailTTStarUpperBoundFromCert.U, Q0MajorTailTTStarCertData.data]
  norm_num

private lemma H_le_X {X : ℕ} (hX : X0 ≤ X) : H ≤ X := by
  -- `H = 10000 ≤ X0 = 1000000`.
  have hHX0 : H ≤ X0 := by decide
  exact le_trans hHX0 hX

private lemma H_le_X_div2 {X : ℕ} (hX : X0 ≤ X) : H ≤ X / 2 := by
  -- `2*H = 20000 ≤ X0 = 1000000`.
  have h2H : 2 * H ≤ X0 := by decide
  have h2H' : 2 * H ≤ X := le_trans h2H hX
  have hmul : H * 2 ≤ X := by simpa [Nat.mul_comm] using h2H'
  exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : ℕ))).2 hmul

private noncomputable def window (X : ℕ) : Finset ℕ :=
  Finset.Icc (X / 2 - H) (X / 2 + H)

private lemma window_card_eq (X : ℕ) (hX : X0 ≤ X) : (window X).card = 2 * H + 1 := by
  classical
  have hHX : H ≤ X / 2 := H_le_X_div2 (X := X) hX
  -- Let `a := X/2 - H`, so the upper endpoint is `a + 2H`.
  set a : ℕ := X / 2 - H
  have ha : a + H = X / 2 := by
    simpa [a] using (Nat.sub_add_cancel hHX)
  have hb : X / 2 + H = a + 2 * H := by
    calc
      X / 2 + H = (a + H) + H := by simpa [ha, Nat.add_assoc]
      _ = a + (H + H) := by simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = a + 2 * H := by simp [two_mul, Nat.add_assoc]
  have hcard :
      (window X).card = (X / 2 + H) + 1 - (X / 2 - H) := by
    simpa [window] using (Finset.card_Icc (a := (X / 2 - H)) (b := (X / 2 + H)))
  -- Rewrite the card in terms of `a`.
  calc
    (window X).card
        = (a + 2 * H) + 1 - a := by simpa [hcard, a, hb]
    _ = (a + (2 * H + 1)) - a := by
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = 2 * H + 1 := by
          simpa using (Nat.add_sub_cancel_left a (2 * H + 1))

private lemma majorArcConstMode_nonneg (X : ℕ) (Δ : ℝ) :
    0 ≤ majorArcConstMode X Δ := by
  classical
  unfold majorArcConstMode majorArcWeight
  have hW : ∀ α : ℝ, 0 ≤
      (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
        (fun _ : ℝ => (1 : ℝ)) α := by
    intro α
    by_cases hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ
    · simp [hα]
    · simp [hα]
  simpa using
    (intervalIntegral.integral_nonneg_of_forall (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
      (by nlinarith) hW)

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
      -- `fourier` lands on the complex unit circle.
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
  -- Use the deterministic arc-length bound and simplify `Q0 = 30000`.
  have hraw :
      majorArcConstMode X (1 : ℝ) ≤ (2 * (30000 : ℝ)) / (X : ℝ) := by
    simpa [Goldbach.AO_OffDiag.TailBlock.Q0, mul_assoc, mul_left_comm, mul_comm] using
      (majorArcConstMode_le (X := X) (Δ := (1 : ℝ)) hΔ hXpos)
  have hnum : (2 : ℝ) * (30000 : ℝ) = (60000 : ℝ) := by norm_num
  simpa [hnum] using hraw

private lemma kernelMassNZEven_le_bound {X N : ℕ} (hX : X0 ≤ X) :
    kernelMassNZEven X (1 : ℝ) N
      ≤
    ((2 * N + 1 : ℕ) : ℝ) * ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
  classical
  -- Each summand is bounded by `((60000/X)^2)`, and the index set has at most `2N+1` elements.
  have hconst_nonneg : 0 ≤ (60000 : ℝ) / (X : ℝ) := by
    have hXpos : 0 < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    exact div_nonneg (by norm_num) (le_of_lt hXpos)
  have hterm :
      ∀ t ∈ ((tSupport N).erase 0).filter Even,
        ‖majorArcWeightFourier X (1 : ℝ) t‖ ^ 2 ≤ ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
    intro t _ht
    have h0 : ‖majorArcWeightFourier X (1 : ℝ) t‖ ≤ majorArcConstMode X (1 : ℝ) :=
      norm_majorArcWeightFourier_le_constMode (X := X) (Δ := (1 : ℝ)) (t := t)
    have h1 : majorArcConstMode X (1 : ℝ) ≤ (60000 : ℝ) / (X : ℝ) :=
      majorArcConstMode_le_60000_div_X (X := X) hX
    have hle : ‖majorArcWeightFourier X (1 : ℝ) t‖ ≤ (60000 : ℝ) / (X : ℝ) := le_trans h0 h1
    have hright : 0 ≤ (60000 : ℝ) / (X : ℝ) := hconst_nonneg
    have hleft : 0 ≤ ‖majorArcWeightFourier X (1 : ℝ) t‖ := norm_nonneg _
    have hmul : ‖majorArcWeightFourier X (1 : ℝ) t‖ * ‖majorArcWeightFourier X (1 : ℝ) t‖
        ≤ ((60000 : ℝ) / (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) :=
      mul_le_mul hle hle hleft hright
    simpa [pow_two] using hmul
  have hsum_le :
      kernelMassNZEven X (1 : ℝ) N
        ≤
      (((((tSupport N).erase 0).filter Even).card : ℕ) : ℝ) * ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
    unfold kernelMassNZEven
    have :=
      (Finset.sum_le_sum (fun t ht => hterm t ht) :
        (∑ t ∈ ((tSupport N).erase 0).filter Even, ‖majorArcWeightFourier X (1 : ℝ) t‖ ^ 2)
          ≤
        ∑ _t ∈ ((tSupport N).erase 0).filter Even, ((60000 : ℝ) / (X : ℝ)) ^ 2)
    -- Evaluate the constant sum as `card * const`.
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  -- Bound the filtered-card by the full band size `2N+1`.
  have hcard_le :
      ((((tSupport N).erase 0).filter Even).card : ℕ) ≤ (tSupport N).card := by
    have hsub : (((tSupport N).erase 0).filter Even) ⊆ tSupport N := by
      intro t ht
      have ht' : t ∈ (tSupport N).erase 0 := (Finset.mem_filter.mp ht).1
      exact (Finset.mem_erase.mp ht').2
    exact Finset.card_le_card hsub
  have hcard_exact : (tSupport N).card = 2 * N + 1 := by
    simpa [tSupport] using (Goldbach.PPBoundCore.card_Icc_neg_to_pos (H := N))
  have hcard_le' :
      (((((tSupport N).erase 0).filter Even).card : ℕ) : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_trans hcard_le (le_of_eq hcard_exact))
  -- Finish by monotonicity in the prefactor.
  exact le_trans hsum_le (by
    have h0 : 0 ≤ ((60000 : ℝ) / (X : ℝ)) ^ 2 := sq_nonneg _
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hcard_le' h0))

private lemma aTerm2Mass_eq_zero_of_large {X : ℕ} (hX : X0 ≤ X) :
    aTerm2Mass X = 0 := by
  -- `2` is far from the window around `X/2` once `X ≥ X0`.
  have hHX : H ≤ X / 2 := H_le_X_div2 (X := X) hX
  have hlow : X / 2 - H ≤ X / 2 := Nat.sub_le _ _
  have hX2 : 2 < X / 2 - H := by
    -- since `X/2 - H ≥ X0/2 - H = 490000`
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
  -- Unfold and simplify.
  have hnot' : 2 ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by
    simpa [window] using hnot
  have hwX0 : Goldbach.BG_Bank.wX X 2 = 0 := by
    simp [Goldbach.BG_Bank.wX, hnot']
  unfold aTerm2Mass Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm
  simp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm, hwX0]

private lemma coeffMass_le_one_div_20001 {X : ℕ} (hX : X0 ≤ X) :
    coeffMass X (X + H) ≤ (1 : ℝ) / (20001 : ℝ) := by
  classical
  -- Basic window facts.
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    have h2 : (2 : ℕ) ≤ X := le_trans (by decide : (2 : ℕ) ≤ X0) hX
    have hx : (1 : ℝ) < (X : ℝ) := by
      have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
    exact Real.log_pos hx
  have hHX : H ≤ X / 2 := H_le_X_div2 (X := X) hX
  have hupperX : X / 2 + H ≤ X := by
    have h1 : X / 2 + H ≤ X / 2 + X / 2 := Nat.add_le_add_left hHX (X / 2)
    have h2 : X / 2 + X / 2 ≤ X := by
      -- `2*(X/2) ≤ X`
      have hmul : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using hmul
    exact le_trans h1 h2
  -- Cardinality of the support window.
  have hcardWin : (window X).card = 20001 := by
    have : (window X).card = 2 * H + 1 := window_card_eq (X := X) hX
    simpa [show (2 * H + 1) = 20001 by decide] using this
  -- Pointwise: on the window, `‖aTerm‖ ≤ 1/20001`.
  have hterm :
      ∀ n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    intro n hn
    have hnwin : n ∈ window X := (Finset.mem_filter.mp hn).2
    have hnX : n ≤ X := le_trans (Finset.mem_Icc.mp hnwin).2 hupperX
    -- bound `|Λ n| ≤ log X`
    have hΛ : |Goldbach.BG_Bank.Λ n| ≤ Real.log (X : ℝ) := by
      by_cases hp : Nat.Prime n
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.Prime.pos hp)
        have hn_le : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hnX
        have hlog_le : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
          Real.log_le_log hnpos hn_le
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
          have : (1 : ℕ) ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) (Nat.Prime.two_le hp)
          exact_mod_cast this
        have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
        simpa [Goldbach.BG_Bank.Λ, hp, abs_of_nonneg hlog_nonneg] using hlog_le
      · have hlog_nonneg : 0 ≤ Real.log (X : ℝ) := le_of_lt hlogXpos
        simpa [Goldbach.BG_Bank.Λ, hp, abs_of_nonneg hlog_nonneg]
    -- `wX = wScale` on the window.
    have hw : Goldbach.BG_Bank.wX X n = Goldbach.BG_Bank.wScale X := by
      have hnwin' : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by
        simpa [window] using hnwin
      simp [Goldbach.BG_Bank.wX, hnwin', window]
    have hwScale_nonneg : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    have habs :
        |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
          ≤ Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) := by
      -- `|wX*Λ| = |wX|*|Λ| ≤ wScale * log X`.
      have hmul :
          |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
            = |Goldbach.BG_Bank.wX X n| * |Goldbach.BG_Bank.Λ n| := by
        simp [abs_mul]
      have hwabs : |Goldbach.BG_Bank.wX X n| = Goldbach.BG_Bank.wScale X := by
        simpa [hw, abs_of_nonneg hwScale_nonneg]
      have h0 : 0 ≤ |Goldbach.BG_Bank.Λ n| := abs_nonneg _
      have := mul_le_mul_of_nonneg_left hΛ (by
        simpa [hwabs] using hwScale_nonneg)
      -- rewrite and finish
      simpa [hmul, hwabs, mul_assoc] using this
    have hscale :
        Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) = (1 : ℝ) / (20001 : ℝ) := by
      have hlogne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogXpos
      have h20001r : (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1 = (20001 : ℝ) := by
        norm_num [Goldbach.BG_Bank.H, Goldbach.BankParams.H]
      -- `wScale = 1 / (log X * (2H+1))`, so multiplying by `log X` cancels.
      unfold Goldbach.BG_Bank.wScale
      set d : ℝ := (2 : ℝ) * (Goldbach.BG_Bank.H : ℝ) + 1
      have hd20001 : d = (20001 : ℝ) := by simpa [d] using h20001r
      calc
        (1 : ℝ) / (Real.log (X : ℝ) * (2 * Goldbach.BG_Bank.H + 1)) * Real.log (X : ℝ)
            = (1 : ℝ) / (Real.log (X : ℝ) * d) * Real.log (X : ℝ) := by
              simp [d, Nat.cast_add, Nat.cast_mul]
        _ = Real.log (X : ℝ) / (Real.log (X : ℝ) * d) := by
              simpa using
                (one_div_mul_eq_div (a := Real.log (X : ℝ) * d) (b := Real.log (X : ℝ)))
        _ = (Real.log (X : ℝ) * (1 : ℝ)) / (Real.log (X : ℝ) * d) := by
              simp [mul_assoc]
        _ = (1 : ℝ) / d := by
              simpa [mul_assoc] using
                (mul_div_mul_left (c := Real.log (X : ℝ)) (a := (1 : ℝ)) (b := d) hlogne)
        _ = (1 : ℝ) / (20001 : ℝ) := by
              simp [hd20001]
    have haTerm :
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖
          ≤ (1 : ℝ) / (20001 : ℝ) := by
      have hnorm :
          ‖((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n : ℝ) : ℂ)‖
            =
          |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := by
        simp [RCLike.norm_ofReal]
      have : |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| ≤ (1 : ℝ) / (20001 : ℝ) := by
        simpa [hscale] using habs
      simpa [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm, hnorm] using this
    have h0 : 0 ≤ (1 : ℝ) / (20001 : ℝ) := by norm_num
    have hmul : ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖
        * ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖
        ≤ ((1 : ℝ) / (20001 : ℝ)) * ((1 : ℝ) / (20001 : ℝ)) :=
      mul_le_mul haTerm haTerm (norm_nonneg _) h0
    simpa [pow_two] using hmul
  -- Rewrite `coeffMass` as a sum over the window-filter.
  have hrewrite :
      coeffMass X (X + H)
        =
      ∑ n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2 := by
    classical
    unfold coeffMass
    have hsum_if :
        (∑ n ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H),
            ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2)
          =
        ∑ n ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H),
          if n ∈ window X then ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro n _hn
      by_cases hnwin : n ∈ window X
      · simp [hnwin]
      · have : Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n = 0 := by
          have hnwin' : n ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by
            simpa [window] using hnwin
          have hwX0 : Goldbach.BG_Bank.wX X n = 0 := by
            simp [Goldbach.BG_Bank.wX, hnwin']
          simp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm, hwX0]
        simp [hnwin, this]
    have hfilter :
        (∑ n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
            ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2)
          =
        ∑ n ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H),
          if n ∈ window X then ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2 else 0 := by
      simpa using
        (Finset.sum_filter (s := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H))
          (p := fun n : ℕ => n ∈ window X)
          (f := fun n : ℕ => ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2))
    exact hsum_if.trans hfilter.symm
  -- Bound the filtered sum by `card * (1/20001)^2`, then use `card ≤ window.card = 20001`.
  have hsum_le :
      (∑ n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
          ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2)
        ≤
      (((((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) : ℝ)
        * ((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
    have :=
      (Finset.sum_le_sum (fun n hn => hterm n hn) :
        (∑ n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
          ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n‖ ^ 2)
          ≤
        ∑ _n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
          ((1 : ℝ) / (20001 : ℝ)) ^ 2)
    -- Evaluate the constant sum as `card * const`.
    have hconstEq :
        (∑ _n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
            ((1 : ℝ) / (20001 : ℝ)) ^ 2)
          =
        (((((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) : ℝ)
          * ((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
      -- Avoid `simp` recursion: use `Finset.sum_const` then rewrite `•` via `nsmul_eq_mul`.
      calc
        (∑ _n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
            ((1 : ℝ) / (20001 : ℝ)) ^ 2)
            =
          ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card
            • ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
          exact
            (Finset.sum_const
              (s := (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X))
              (b := ((1 : ℝ) / (20001 : ℝ)) ^ 2))
        _ =
          (((((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) : ℝ)
            * ((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
          exact
            (nsmul_eq_mul
              (((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card)
              (((1 : ℝ) / (20001 : ℝ)) ^ 2))
    have hconstLe :
        (∑ _n ∈ (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X),
            ((1 : ℝ) / (20001 : ℝ)) ^ 2)
          ≤
        (((((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) : ℝ)
          * ((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
      exact le_of_eq hconstEq
    exact le_trans this hconstLe
  have hcard_le :
      (((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) ≤ 20001 := by
    have hsub :
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)
          ⊆ window X := by
      intro n hn
      exact (Finset.mem_filter.mp hn).2
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hcardWin)
  have hcard_le' :
      (((((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) : ℝ))
        ≤ (20001 : ℝ) := by
    exact_mod_cast hcard_le
  have h0 : 0 ≤ ((1 : ℝ) / (20001 : ℝ)) ^ 2 := sq_nonneg _
  have hsum_le' :
      (((((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) : ℝ)
          * ((1 : ℝ) / (20001 : ℝ)) ^ 2)
        ≤ (20001 : ℝ) * ((1 : ℝ) / (20001 : ℝ)) ^ 2 := by
    exact mul_le_mul_of_nonneg_right hcard_le' h0
  have hfinal :
      (20001 : ℝ) * ((1 : ℝ) / (20001 : ℝ)) ^ 2 = (1 : ℝ) / (20001 : ℝ) := by
    have hne : (20001 : ℝ) ≠ 0 := by norm_num
    field_simp [hne]
  have hsum_le_coeff :
      coeffMass X (X + H)
        ≤
      (((((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s (X + H)).filter (fun n : ℕ => n ∈ window X)).card : ℕ) : ℝ)
        * ((1 : ℝ) / (20001 : ℝ)) ^ 2) := by
    rw [hrewrite]
    exact hsum_le
  exact le_trans hsum_le_coeff (le_trans hsum_le' (le_of_eq hfinal))

private lemma toeplitzExprTopTight_le_36742000 {X : ℕ} (hX : X0 ≤ X) :
    toeplitzExprTopTight X (1 : ℝ) ≤ (36742000 : ℝ) := by
  classical
  have hNcard :
      ((2 * (X + H) + 1 : ℕ) : ℝ) ≤ (3 : ℝ) * (X : ℝ) := by
    have h2H1 : (2 * H + 1 : ℕ) ≤ X := by
      have : (2 * H + 1 : ℕ) ≤ X0 := by decide
      exact le_trans this hX
    have hnat : 2 * (X + H) + 1 ≤ 3 * X := by
      -- `2*(X+H)+1 = 2*X + (2*H+1) ≤ 2*X + X = 3*X`.
      calc
        2 * (X + H) + 1 = 2 * X + (2 * H + 1) := by
          simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul]
        _ ≤ 2 * X + X := by
          exact Nat.add_le_add_left h2H1 (2 * X)
        _ = 3 * X := by
          -- `2*X + X = (2*X) + (1*X) = (2+1)*X = 3*X`.
          calc
            2 * X + X = 2 * X + 1 * X := by simp
            _ = (2 + 1) * X := (Nat.add_mul 2 1 X).symm
            _ = 3 * X := by simp
    exact_mod_cast hnat
  have hker :
      kernelMassNZEven X (1 : ℝ) (X + H)
        ≤
      (3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)) := by
    have h0 :=
      kernelMassNZEven_le_bound (X := X) (N := X + H) hX
    -- Use `((2N+1)*(60000/X)^2) ≤ (3X)*(60000^2/X^2) = 3*60000^2*(1/X)`.
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    have hmul :
        ((2 * (X + H) + 1 : ℕ) : ℝ) * ((60000 : ℝ) / (X : ℝ)) ^ 2
          ≤
        ((3 : ℝ) * (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hNcard (sq_nonneg _)
    have hrew :
        ((3 : ℝ) * (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) ^ 2
          =
        (3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)) := by
      -- expand `(60000/X)^2` and cancel one `X`
      field_simp [hXne]
    exact le_trans h0 (le_trans hmul (by simpa [hrew]))
  have hcoeff : coeffMass X (X + H) ≤ (1 : ℝ) / (20001 : ℝ) :=
    coeffMass_le_one_div_20001 (X := X) hX
  have hcoeffsq : (coeffMass X (X + H)) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ coeffMass X (X + H) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h1 : coeffMass X (X + H) ≤ 1 := by
      have : (1 : ℝ) / (20001 : ℝ) ≤ 1 := by norm_num
      exact le_trans hcoeff this
    have hmul : coeffMass X (X + H) * coeffMass X (X + H) ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul h1 h1 h0 (by norm_num)
    simpa [pow_two] using hmul
  have hodd : (2 * (1 + 1 / δ_split) *
        kernelMassNZOdd X (1 : ℝ) (X + H)) *
      aTerm2Mass X *
      coeffMass X (X + H) = 0 := by
    have h2 : aTerm2Mass X = 0 := aTerm2Mass_eq_zero_of_large (X := X) hX
    simp [h2]
  have hlog2 :
      (Real.log ((X + H : ℕ) : ℝ)) ^ 2 ≤ (4 : ℝ) * (X : ℝ) ^ 2 := by
    have hXnatpos : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
    have hNnatpos : 0 < X + H := Nat.add_pos_left hXnatpos H
    have hNpos : 0 < ((X + H : ℕ) : ℝ) := by exact_mod_cast hNnatpos
    have hNge1 : (1 : ℝ) ≤ ((X + H : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ X + H := Nat.succ_le_iff.mpr hNnatpos
      exact_mod_cast this
    have hlog_nonneg : 0 ≤ Real.log ((X + H : ℕ) : ℝ) := Real.log_nonneg hNge1
    have hlog_le_N : Real.log ((X + H : ℕ) : ℝ) ≤ ((X + H : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos hNpos
      linarith
    have hsq1 :
        (Real.log ((X + H : ℕ) : ℝ)) ^ 2 ≤ (((X + H : ℕ) : ℝ)) ^ 2 := by
      have hmul :
          Real.log ((X + H : ℕ) : ℝ) * Real.log ((X + H : ℕ) : ℝ)
            ≤
          ((X + H : ℕ) : ℝ) * ((X + H : ℕ) : ℝ) :=
        mul_le_mul hlog_le_N hlog_le_N hlog_nonneg (by positivity)
      simpa [pow_two] using hmul
    have hNle2X : (X + H : ℕ) ≤ 2 * X := by
      have hH : H ≤ X := H_le_X (X := X) hX
      calc
        X + H ≤ X + X := Nat.add_le_add_left hH X
        _ = 2 * X := by simp [two_mul, Nat.add_assoc]
    have hsq2 :
        (((X + H : ℕ) : ℝ)) ^ 2 ≤ (4 : ℝ) * (X : ℝ) ^ 2 := by
      have hle : ((X + H : ℕ) : ℝ) ≤ (2 : ℝ) * (X : ℝ) := by exact_mod_cast hNle2X
      have hmul :
          ((X + H : ℕ) : ℝ) * ((X + H : ℕ) : ℝ) ≤ ((2 : ℝ) * (X : ℝ)) * ((2 : ℝ) * (X : ℝ)) :=
        mul_le_mul hle hle (by positivity) (by positivity)
      -- `(2X)^2 = 4*X^2`.
      have hrew : ((2 : ℝ) * (X : ℝ)) * ((2 : ℝ) * (X : ℝ)) = (4 : ℝ) * (X : ℝ) ^ 2 := by
        ring
      simpa [pow_two, hrew] using hmul
    exact le_trans hsq1 hsq2
  have hnorm0 :
      ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2 ≤ ((60000 : ℝ) / (X : ℝ)) ^ 2 := by
    have h0 : ‖majorArcWeightFourier X (1 : ℝ) 0‖ ≤ majorArcConstMode X (1 : ℝ) :=
      norm_majorArcWeightFourier_le_constMode (X := X) (Δ := (1 : ℝ)) (t := 0)
    have h1 : majorArcConstMode X (1 : ℝ) ≤ (60000 : ℝ) / (X : ℝ) :=
      majorArcConstMode_le_60000_div_X (X := X) hX
    have hle : ‖majorArcWeightFourier X (1 : ℝ) 0‖ ≤ (60000 : ℝ) / (X : ℝ) := le_trans h0 h1
    have hright : 0 ≤ (60000 : ℝ) / (X : ℝ) := by
      have hXpos : (0 : ℝ) < (X : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
      exact div_nonneg (by norm_num) (le_of_lt hXpos)
    have hleft : 0 ≤ ‖majorArcWeightFourier X (1 : ℝ) 0‖ := norm_nonneg _
    have hmul :
        ‖majorArcWeightFourier X (1 : ℝ) 0‖ * ‖majorArcWeightFourier X (1 : ℝ) 0‖
          ≤ ((60000 : ℝ) / (X : ℝ)) * ((60000 : ℝ) / (X : ℝ)) :=
      mul_le_mul hle hle hleft hright
    simpa [pow_two] using hmul
  have hdiag :
      ((1 + δ_split) * ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2) * diagBoundTight X (X + H)
        ≤ (36720000 : ℝ) := by
    -- `diagBoundTight = log^2 * coeffMass`.
    unfold diagBoundTight
    have hcoeff' : coeffMass X (X + H) ≤ (1 : ℝ) / (20001 : ℝ) := hcoeff
    have hδ : (1 + δ_split) = (51 : ℝ) := by norm_num [δ_split]
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    -- combine bounds
    have hmain :
        ((1 + δ_split) * ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2) * ((Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H))
          ≤
        (51 : ℝ) * (((60000 : ℝ) / (X : ℝ)) ^ 2) * ((4 : ℝ) * (X : ℝ) ^ 2) * ((1 : ℝ) / (20001 : ℝ)) := by
      have hδ0 : 0 ≤ (1 + δ_split) := by
        have : 0 ≤ δ_split := by norm_num [δ_split]
        nlinarith
      have h1 :
          (1 + δ_split) * ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2
            ≤
          (51 : ℝ) * (((60000 : ℝ) / (X : ℝ)) ^ 2) := by
        -- use `hδ` and `hnorm0`
        simpa [hδ] using (mul_le_mul_of_nonneg_left hnorm0 hδ0)
      have h2 :
          (Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H)
            ≤
          (4 : ℝ) * (X : ℝ) ^ 2 * ((1 : ℝ) / (20001 : ℝ)) := by
        have hlog0 : 0 ≤ (Real.log ((X + H : ℕ) : ℝ)) ^ 2 := sq_nonneg _
        have hX2 : 0 ≤ (4 : ℝ) * (X : ℝ) ^ 2 := by positivity
        have hlogle : (Real.log ((X + H : ℕ) : ℝ)) ^ 2 ≤ (4 : ℝ) * (X : ℝ) ^ 2 := hlog2
        have : (Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H)
              ≤ (4 : ℝ) * (X : ℝ) ^ 2 * ((1 : ℝ) / (20001 : ℝ)) :=
          mul_le_mul hlogle hcoeff' (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hX2
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      have h1nn : 0 ≤ (51 : ℝ) * (((60000 : ℝ) / (X : ℝ)) ^ 2) := by positivity
      have : ( (1 + δ_split) * ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2)
              * ((Real.log ((X + H : ℕ) : ℝ)) ^ 2 * coeffMass X (X + H))
            ≤
            ( (51 : ℝ) * (((60000 : ℝ) / (X : ℝ)) ^ 2))
              * ((4 : ℝ) * (X : ℝ) ^ 2 * ((1 : ℝ) / (20001 : ℝ))) :=
        mul_le_mul h1 h2
          (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) h1nn
      -- reorder
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    -- cancel `X` from `((60000/X)^2) * (4*X^2)` and close numerically.
    have hbound :
        (51 : ℝ) * (((60000 : ℝ) / (X : ℝ)) ^ 2) * ((4 : ℝ) * (X : ℝ) ^ 2) * ((1 : ℝ) / (20001 : ℝ))
          =
        (204 : ℝ) * (60000 : ℝ) ^ 2 * ((1 : ℝ) / (20001 : ℝ)) := by
      field_simp [hXne]
      ring
    have hnum : (204 : ℝ) * (60000 : ℝ) ^ 2 * ((1 : ℝ) / (20001 : ℝ)) ≤ (36720000 : ℝ) := by
      norm_num
    have hnum' :
        (51 : ℝ) * (((60000 : ℝ) / (X : ℝ)) ^ 2) * ((4 : ℝ) * (X : ℝ) ^ 2) * ((1 : ℝ) / (20001 : ℝ))
          ≤ (36720000 : ℝ) := by
      -- rewrite by `hbound` and close with `hnum`
      calc
        (51 : ℝ) * (((60000 : ℝ) / (X : ℝ)) ^ 2) * ((4 : ℝ) * (X : ℝ) ^ 2) * ((1 : ℝ) / (20001 : ℝ))
            = (204 : ℝ) * (60000 : ℝ) ^ 2 * ((1 : ℝ) / (20001 : ℝ)) := hbound
        _ ≤ (36720000 : ℝ) := hnum
    exact le_trans hmain hnum'
  have heven :
      ((1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)) * (coeffMass X (X + H)) ^ 2
        ≤ (21600 : ℝ) := by
    have hδ : (1 + 1 / δ_split) ≤ (2 : ℝ) := by
      -- `1 + 1/50 ≤ 2`
      norm_num [δ_split]
    have hker' : kernelMassNZEven X (1 : ℝ) (X + H) ≤ (3 : ℝ) * (60000 : ℝ) ^ 2 * (1 / (X : ℝ)) := hker
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < X0) hX)
    have h1X : (1 : ℝ) / (X : ℝ) ≤ (1 : ℝ) / (1000000 : ℝ) := by
      have : (1000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1000000 : ℝ)) this
    have hker'' :
        kernelMassNZEven X (1 : ℝ) (X + H) ≤ (10800 : ℝ) := by
      have hmul :
          ((3 : ℝ) * (60000 : ℝ) ^ 2) * ((1 : ℝ) / (X : ℝ))
            ≤
          ((3 : ℝ) * (60000 : ℝ) ^ 2) * ((1 : ℝ) / (1000000 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left h1X (by positivity : 0 ≤ (3 : ℝ) * (60000 : ℝ) ^ 2)
        simpa [mul_assoc] using this
      have hnumInv : (3 : ℝ) * (60000 : ℝ) ^ 2 * ((1000000 : ℝ)⁻¹) = (10800 : ℝ) := by
        norm_num
      -- rewrite `hker'` into the `((3*60000^2) * (1/X))` form to use `hmul`.
      have hker1 :
          kernelMassNZEven X (1 : ℝ) (X + H) ≤ ((3 : ℝ) * (60000 : ℝ) ^ 2) * ((1 : ℝ) / (X : ℝ)) := by
        simpa [mul_assoc] using hker'
      have hker2 :
          kernelMassNZEven X (1 : ℝ) (X + H) ≤ ((3 : ℝ) * (60000 : ℝ) ^ 2) * ((1 : ℝ) / (1000000 : ℝ)) :=
        le_trans hker1 hmul
      -- normalize `1 / 1000000` to `1000000⁻¹` for rewriting
      have : ((3 : ℝ) * (60000 : ℝ) ^ 2) * ((1 : ℝ) / (1000000 : ℝ))
          = (3 : ℝ) * (60000 : ℝ) ^ 2 * ((1000000 : ℝ)⁻¹) := by
        simp [one_div, mul_assoc, mul_left_comm, mul_comm]
      -- rewrite the RHS of `hker2` and close
      have hker2' : kernelMassNZEven X (1 : ℝ) (X + H) ≤ (3 : ℝ) * (60000 : ℝ) ^ 2 * ((1000000 : ℝ)⁻¹) := by
        simpa [this] using hker2
      simpa [hnumInv] using hker2'
    have hcoeffsq' : (coeffMass X (X + H)) ^ 2 ≤ 1 := hcoeffsq
    have h0 : 0 ≤ (1 + 1 / δ_split) := by
      have : 0 ≤ (1 / δ_split) := le_of_lt (one_div_pos.mpr δ_split_pos)
      nlinarith
    have hmain :
        ((1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)) * (coeffMass X (X + H)) ^ 2
          ≤
        ((2 : ℝ) * (10800 : ℝ)) * (1 : ℝ) := by
      have h1 :
          (1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)
            ≤
          (2 : ℝ) * (10800 : ℝ) := by
        have hk0 : 0 ≤ kernelMassNZEven X (1 : ℝ) (X + H) :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have hstep1 :
            (1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)
              ≤ (2 : ℝ) * kernelMassNZEven X (1 : ℝ) (X + H) :=
          mul_le_mul_of_nonneg_right hδ hk0
        have hstep2 :
            (2 : ℝ) * kernelMassNZEven X (1 : ℝ) (X + H) ≤ (2 : ℝ) * (10800 : ℝ) :=
          mul_le_mul_of_nonneg_left hker'' (by norm_num)
        exact le_trans hstep1 hstep2
      have h2 : (coeffMass X (X + H)) ^ 2 ≤ 1 := hcoeffsq'
      have h1nn : 0 ≤ (2 : ℝ) * (10800 : ℝ) := by norm_num
      have := mul_le_mul h1 h2 (by positivity) h1nn
      simpa [mul_assoc] using this
    -- numeric
    have : ((2 : ℝ) * (10800 : ℝ)) * (1 : ℝ) ≤ (21600 : ℝ) := by norm_num
    exact le_trans hmain this
  -- Finish: even term + odd term + diagonal term.
  unfold toeplitzExprTopTight
  have hsumTight :
      ((1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)) * (coeffMass X (X + H)) ^ 2
        +
      (2 * (1 + 1 / δ_split) * kernelMassNZOdd X (1 : ℝ) (X + H)) * aTerm2Mass X * coeffMass X (X + H)
        +
      ((1 + δ_split) * ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2) * diagBoundTight X (X + H)
        ≤ (36742000 : ℝ) := by
    -- Odd term is `0`, so it suffices to bound `even + diag`.
    have hsumAC :
        ((1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)) * (coeffMass X (X + H)) ^ 2
          +
        ((1 + δ_split) * ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2) * diagBoundTight X (X + H)
          ≤ (36742000 : ℝ) := by
      nlinarith [heven, hdiag]
    -- Rewrite the full sum by `rw [hodd]` (no `mul_eq_zero` case-splitting).
    have :
        ((1 + 1 / δ_split) * kernelMassNZEven X (1 : ℝ) (X + H)) * (coeffMass X (X + H)) ^ 2
          +
        (2 * (1 + 1 / δ_split) * kernelMassNZOdd X (1 : ℝ) (X + H)) * aTerm2Mass X * coeffMass X (X + H)
          +
        ((1 + δ_split) * ‖majorArcWeightFourier X (1 : ℝ) 0‖ ^ 2) * diagBoundTight X (X + H)
          ≤ (36742000 : ℝ) := by
      -- after rewriting, this becomes exactly `hsumAC`
      rw [hodd]
      simpa [add_assoc, add_left_comm, add_comm] using hsumAC
    exact this
  simpa [add_assoc] using hsumTight

private lemma toeplitzExprTopTight_le_U_target {X : ℕ} (hX : X0 ≤ X) :
    toeplitzExprTopTight X Δ_canon ≤ U_target := by
  have hTight : toeplitzExprTopTight X (1 : ℝ) ≤ (36742000 : ℝ) :=
    toeplitzExprTopTight_le_36742000 (X := X) hX
  have hU : (36742000 : ℝ) ≤ U_target := by
    dsimp [U_target, Q0MajorTailTTStarUpperBoundFromCert.U, Q0MajorTailTTStarCertData.data]
    norm_num
  simpa [Δ_canon] using le_trans hTight hU

theorem innerMajorQ0_full_ttstar_kSupport_upperBound :
    Q0InnerMajorFullTTStarKSupportUpperBound Δ_canon U_target := by
  refine ⟨U_target_nonneg, ?_⟩
  intro X N hX hN
  have hToe :
      (∑ k ∈ Q0MajorTailTTStarFiniteSupport.kSupport N,
          ‖fourierCoeffOn Goldbach.Cert.MajorArcModules.BetaInterval.hab
              (fun β : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerMajorQ0 X N Δ_canon β) k‖ ^ 2)
        ≤ toeplitzExprTopTight X Δ_canon :=
    sum_kSupport_sq_le_toeplitzExprTopTight (Δ := Δ_canon) (X := X) (N := N) hX hN
  exact le_trans hToe (toeplitzExprTopTight_le_U_target (X := X) hX)

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarUpperBoundFromToeplitz
