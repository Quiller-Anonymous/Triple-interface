import Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcModules.NumericFacts
import Goldbach.AO_OffDiag.TailBlock
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Deterministic (axiom-free) ε₂-small upper bound for the turnkey `Q0` route.

This file is intentionally coarse: with the current **windowed + scaled** bank weight `wX`,
the shifted exponential sums are uniformly bounded (on canonical windows `X ≥ X0`) by a small
log-ratio, which is enough to bound the small-β deviation by the current certificate `U = 2`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.NumericFacts
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundFromCert
open Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundSpec

open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit

open Goldbach.AO_OffDiag.TailBlock

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private noncomputable def window (X : ℕ) : Finset ℕ :=
  Finset.Icc (X / 2 - H) (X / 2 + H)

private lemma window_card_le (X : ℕ) : (window X).card ≤ 2 * H + 1 := by
  classical
  by_cases hHX : H ≤ X / 2
  · -- Full-width regime.
    set a : ℕ := X / 2 - H
    have ha : a + H = X / 2 := by simpa [a] using (Nat.sub_add_cancel hHX)
    have hb : X / 2 + H = a + 2 * H := by
      calc
        X / 2 + H = (a + H) + H := by simpa [ha, Nat.add_assoc]
        _ = a + (H + H) := by simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = a + 2 * H := by simp [two_mul, Nat.add_assoc]
    have hcard :
        (window X).card = (X / 2 + H) + 1 - (X / 2 - H) := by
      simpa [window] using (Finset.card_Icc (a := (X / 2 - H)) (b := (X / 2 + H)))
    have : (window X).card = 2 * H + 1 := by
      calc
        (window X).card
            = (a + 2 * H) + 1 - a := by simpa [hcard, a, hb]
        _ = (a + (2 * H + 1)) - a := by
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = 2 * H + 1 := by
              simpa using (Nat.add_sub_cancel_left a (2 * H + 1))
    simpa [this]
  · -- Truncated regime: card is even smaller.
    have hXH : X / 2 ≤ H := le_of_lt (Nat.lt_of_not_ge hHX)
    have hleft : X / 2 - H = 0 := Nat.sub_eq_zero_of_le hXH
    have hcard :
        (window X).card = (X / 2 + H) + 1 - (X / 2 - H) := by
      simpa [window] using (Finset.card_Icc (a := (X / 2 - H)) (b := (X / 2 + H)))
    calc
      (window X).card
          = (X / 2 + H) + 1 := by simp [hcard, hleft]
      _ ≤ (H + H) + 1 := by
            gcongr
      _ = 2 * H + 1 := by simp [two_mul, Nat.add_assoc]

private lemma card_filter_window_le (X N : ℕ) :
    ((MajorArcStep10RLSmoothIntegral.s N).filter (fun n => n ∈ window X)).card ≤ 2 * H + 1 := by
  classical
  have hsubset :
      (MajorArcStep10RLSmoothIntegral.s N).filter (fun n => n ∈ window X) ⊆ window X := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  exact le_trans (Finset.card_le_card hsubset) (window_card_le X)

private lemma Lambda_le_log_of_le {n N : ℕ} (hn : n ≤ N) (hN2 : 2 ≤ N) :
    Goldbach.BG_Bank.Λ n ≤ Real.log (N : ℝ) := by
  by_cases hp : Nat.Prime n
  · have hn0 : 0 < (n : ℝ) := by
      have : 0 < n := Nat.pos_of_ne_zero (Nat.Prime.ne_zero hp)
      exact_mod_cast this
    have hN0 : 0 < (N : ℝ) := by
      have : 0 < N := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hN2
      exact_mod_cast this
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    have : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hn0 hnN
    simpa [Goldbach.BG_Bank.Λ, hp] using this
  · have hlog : 0 ≤ Real.log (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by
        have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ 2) hN2
        exact_mod_cast this
      exact Real.log_nonneg this
    simpa [Goldbach.BG_Bank.Λ, hp] using hlog

private lemma N_ge_two_of_mem_EvenIn {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) : 2 ≤ N := by
  have hIn : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hIn with ⟨k, _hk, rfl⟩
  have h2X0 : 2 ≤ X0 := by decide
  exact le_trans (le_trans h2X0 hX) (Nat.le_add_right _ _)

private lemma logRatio_le_14_13 {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (Real.log (N : ℝ)) / (Real.log (X : ℝ)) ≤ (14 : ℝ) / 13 := by
  have hIn : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hIn with ⟨k, hk, rfl⟩
  have hk_le : k ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hk)

  have hHX0 : H ≤ X0 := by decide
  have hHX : H ≤ X := le_trans hHX0 hX
  have hXposNat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX

  have hN_le_2X : X + k ≤ 2 * X := by
    have hkH : X + k ≤ X + H := Nat.add_le_add_left hk_le X
    have hXH : X + H ≤ 2 * X := by
      have : X + H ≤ X + X := Nat.add_le_add_left hHX X
      simpa [two_mul] using this
    exact le_trans hkH hXH

  have hNpos : (0 : ℝ) < ((X + k : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_pos_left hXposNat k)
  have hN_le : ((X + k : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
    exact_mod_cast hN_le_2X
  have hlog_le : Real.log ((X + k : ℕ) : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) :=
    Real.log_le_log hNpos hN_le

  have hlogX_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) :=
    thirteen_le_log_of_X0_le hX
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 13) hlogX_ge13

  have hlog2X : Real.log (2 * (X : ℝ)) = Real.log (2 : ℝ) + Real.log (X : ℝ) := by
    have h2ne : (2 : ℝ) ≠ 0 := by norm_num
    have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hXposNat)
    simpa [mul_assoc] using (Real.log_mul h2ne hXne)

  have hlog2_le1 : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_two_lt_d9.le]

  have hlogN_le : Real.log ((X + k : ℕ) : ℝ) ≤ Real.log (X : ℝ) + 1 := by
    have h1 : Real.log ((X + k : ℕ) : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := hlog_le
    have h2 : Real.log ((2 * X : ℕ) : ℝ) ≤ Real.log (X : ℝ) + 1 := by
      have := add_le_add_right hlog2_le1 (Real.log (X : ℝ))
      -- `log(2*X) = log 2 + log X ≤ 1 + log X = log X + 1`.
      have hcast : Real.log ((2 * X : ℕ) : ℝ) = Real.log (2 * (X : ℝ)) := by
        simpa [Nat.cast_mul, two_mul, mul_assoc, mul_comm, mul_left_comm]
      have : Real.log ((2 * X : ℕ) : ℝ) ≤ 1 + Real.log (X : ℝ) := by
        -- keep RHS in the `1 + log X` shape to match `this`
        simpa [hcast, hlog2X, mul_assoc] using this
      -- swap the RHS order
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact le_trans h1 h2

  have hinv : (Real.log (X : ℝ))⁻¹ ≤ (13 : ℝ)⁻¹ := by
    -- `log X ≥ 13 > 0`, so `1/log X ≤ 1/13`.
    have : (1 : ℝ) / Real.log (X : ℝ) ≤ (1 : ℝ) / 13 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 13) hlogX_ge13
    simpa [one_div] using this

  calc
    Real.log ((X + k : ℕ) : ℝ) / Real.log (X : ℝ)
        ≤ (Real.log (X : ℝ) + 1) / Real.log (X : ℝ) := by
              exact div_le_div_of_nonneg_right hlogN_le (le_of_lt hlogXpos)
    _ = 1 + (Real.log (X : ℝ))⁻¹ := by
          field_simp [hlogXpos.ne']
    _ ≤ 1 + (13 : ℝ)⁻¹ := by
          exact add_le_add_left hinv 1
    _ = (14 : ℝ) / 13 := by norm_num

private lemma logRatio_sq_le_two {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 ≤ (2 : ℝ) := by
  have hratio : (Real.log (N : ℝ)) / (Real.log (X : ℝ)) ≤ (14 : ℝ) / 13 :=
    logRatio_le_14_13 (X := X) (N := N) hX hN
  have hlogX_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) := thirteen_le_log_of_X0_le hX
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 13) hlogX_ge13
  have h0 : 0 ≤ (Real.log (N : ℝ)) / (Real.log (X : ℝ)) := by
    have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
      -- `N ≥ X0 ≥ 1`, so `log N ≥ 0`.
      have hIn : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
      rcases Finset.mem_image.mp hIn with ⟨k, _hk, rfl⟩
      have hXposNat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
      have h1 : (1 : ℝ) ≤ ((X + k : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (Nat.add_pos_left hXposNat k))
      exact Real.log_nonneg h1
    exact div_nonneg hlogN0 (le_of_lt hlogXpos)
  have hsq :
      ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 ≤ ((14 : ℝ) / 13) ^ 2 := by
    -- square is monotone on `ℝ≥0`
    have hmul :
        ((Real.log (N : ℝ)) / (Real.log (X : ℝ)))
            * ((Real.log (N : ℝ)) / (Real.log (X : ℝ)))
          ≤ ((14 : ℝ) / 13) * ((14 : ℝ) / 13) :=
      mul_le_mul hratio hratio h0 (by norm_num)
    simpa [pow_two] using hmul
  have hnum : ((14 : ℝ) / 13) ^ 2 ≤ (2 : ℝ) := by norm_num
  exact le_trans hsq hnum

private lemma kernelCap_le_three : kernelCap ≤ (3 : ℝ) := by
  dsimp [Q0MajorBoundSplit.kernelCap, Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap]
  norm_num [Goldbach.BankParams.H, Goldbach.BG_Identity.Ucut]

private lemma norm_expSum_le_logRatio (X N : ℕ) (γ : UC) (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖expSum X N γ‖ ≤ (Real.log (N : ℝ)) / (Real.log (X : ℝ)) := by
  classical
  have hN2 : 2 ≤ N := N_ge_two_of_mem_EvenIn (X := X) (N := N) hX hN

  -- Triangle inequality.
  have hsum :
      ‖expSum X N γ‖
        ≤
      ∑ n ∈ MajorArcStep10RLSmoothIntegral.s N,
        ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := by
    simpa [MajorArcStep12ShiftedExpSums.expSum] using
      (norm_sum_le
        (s := MajorArcStep10RLSmoothIntegral.s N)
        (f := fun n => aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)))

  have hfour : ∀ n : ℕ, ‖(fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ = 1 := by
    intro n
    simp [fourier_apply]

  -- Replace `‖aTerm * fourier‖` by `‖aTerm‖`.
  have hsum_norm :
      (∑ n ∈ MajorArcStep10RLSmoothIntegral.s N,
          ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
        =
      (∑ n ∈ MajorArcStep10RLSmoothIntegral.s N, ‖aTerm X n‖) := by
    classical
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [norm_mul, hfour n]

  -- Drop terms outside the window (they are zero).
  have hdrop :
      (∑ n ∈ MajorArcStep10RLSmoothIntegral.s N, ‖aTerm X n‖)
        =
      ∑ n ∈ (MajorArcStep10RLSmoothIntegral.s N).filter (fun n => n ∈ window X),
        ‖aTerm X n‖ := by
    classical
    have hite :
        (∑ n ∈ MajorArcStep10RLSmoothIntegral.s N, ‖aTerm X n‖)
          =
        ∑ n ∈ MajorArcStep10RLSmoothIntegral.s N, (if n ∈ window X then ‖aTerm X n‖ else 0) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      by_cases hnwin : n ∈ window X
      · simp [hnwin]
      · have hwX0 : Goldbach.BG_Bank.wX X n = 0 := by
          have hnIcc : n ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by
            simpa [window] using hnwin
          simp [Goldbach.BG_Bank.wX, hnIcc]
        have ha0 : aTerm X n = 0 := by
          simp [MajorArcStep10RLSmoothIntegral.aTerm, hwX0]
        simp [hnwin, ha0]
    -- Convert the RHS via `Finset.sum_filter`.
    -- (`sum_filter` is `∑ x in s.filter p, f x = ∑ x in s, if p x then f x else 0`.)
    have hfilter :
        (∑ n ∈ (MajorArcStep10RLSmoothIntegral.s N).filter (fun n => n ∈ window X), ‖aTerm X n‖)
          =
        ∑ n ∈ MajorArcStep10RLSmoothIntegral.s N, (if n ∈ window X then ‖aTerm X n‖ else 0) := by
      simpa using
        (Finset.sum_filter (s := MajorArcStep10RLSmoothIntegral.s N)
          (p := fun n => n ∈ window X) (f := fun n => ‖aTerm X n‖))
    -- Rearrange (avoid simp rewriting `filter (· ∈ window X)` into `∩ window X`).
    exact Eq.trans hite (Eq.symm hfilter)

  -- Pointwise bound on surviving terms.
  have hterm :
      ∀ n ∈ (MajorArcStep10RLSmoothIntegral.s N).filter (fun n => n ∈ window X),
        ‖aTerm X n‖ ≤ (Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ) := by
    intro n hn
    have hn_s : n ∈ MajorArcStep10RLSmoothIntegral.s N := (Finset.mem_filter.mp hn).1
    have hn_win : n ∈ window X := (Finset.mem_filter.mp hn).2
    have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn_s).2 (Nat.sub_le N 2)
    have hΛ : Goldbach.BG_Bank.Λ n ≤ Real.log (N : ℝ) :=
      Lambda_le_log_of_le (n := n) (N := N) hn_le hN2
    have hwX : Goldbach.BG_Bank.wX X n = Goldbach.BG_Bank.wScale X := by
      have hnIcc : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by
        simpa [window] using hn_win
      simp [Goldbach.BG_Bank.wX, hnIcc]
    have hwScale0 : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    have hΛ0 : 0 ≤ Goldbach.BG_Bank.Λ n := by
      by_cases hp : Nat.Prime n
      · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
        simpa [Goldbach.BG_Bank.Λ, hp] using (le_of_lt (Real.log_pos hn1))
      · simp [Goldbach.BG_Bank.Λ, hp]
    have hnorm :
        ‖aTerm X n‖ = |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := by
      simp [MajorArcStep10RLSmoothIntegral.aTerm, RCLike.norm_ofReal]
    calc
      ‖aTerm X n‖ = |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := hnorm
      _ = (Goldbach.BG_Bank.wScale X) * (Goldbach.BG_Bank.Λ n) := by
            have hprod0 : 0 ≤ Goldbach.BG_Bank.wScale X * Goldbach.BG_Bank.Λ n :=
              mul_nonneg hwScale0 hΛ0
            calc
              |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
                  = |Goldbach.BG_Bank.wScale X * Goldbach.BG_Bank.Λ n| := by
                        simp [hwX]
              _ = Goldbach.BG_Bank.wScale X * Goldbach.BG_Bank.Λ n := abs_of_nonneg hprod0
      _ ≤ (Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ) := by
            exact mul_le_mul_of_nonneg_left hΛ hwScale0

  -- Sum bound: `≤ card * const ≤ (2H+1) * const`.
  set S : Finset ℕ := (MajorArcStep10RLSmoothIntegral.s N).filter (fun n => n ∈ window X)
  have hcard : S.card ≤ 2 * H + 1 := by
    simpa [S] using (card_filter_window_le (X := X) (N := N))
  have hsum_le :
      (∑ n ∈ S, ‖aTerm X n‖) ≤ ((2 * H + 1 : ℕ) : ℝ) * ((Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ)) := by
    have hsum_le' : (∑ n ∈ S, ‖aTerm X n‖) ≤ ∑ _n ∈ S, (Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      exact hterm n (by simpa [S] using hn)
    have hconst :
        (∑ _n ∈ S, (Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ))
          = (S.card : ℝ) * ((Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ)) := by
      simp [mul_assoc]
    have hcard' : (S.card : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    have hnonneg : 0 ≤ (Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ) := by
      have hlogN0 : 0 ≤ Real.log (N : ℝ) := by
        have hIn : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
        rcases Finset.mem_image.mp hIn with ⟨k, _hk, rfl⟩
        have hXposNat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
        have h1 : (1 : ℝ) ≤ ((X + k : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.add_pos_left hXposNat k))
        exact Real.log_nonneg h1
      exact mul_nonneg (Goldbach.BG_Bank.wScale_nonneg X) hlogN0
    calc
      (∑ n ∈ S, ‖aTerm X n‖)
          ≤ ∑ _n ∈ S, (Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ) := hsum_le'
      _ = (S.card : ℝ) * ((Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ)) := hconst
      _ ≤ ((2 * H + 1 : ℕ) : ℝ) * ((Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hcard' hnonneg

  -- Normalize `(2H+1) * wScale X = 1 / log X`.
  have hlogX_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) := thirteen_le_log_of_X0_le hX
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 13) hlogX_ge13
  have hwScale :
      ((2 * H + 1 : ℕ) : ℝ) * (Goldbach.BG_Bank.wScale X) = (Real.log (X : ℝ))⁻¹ := by
    have hlogX0 : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogXpos
    have hHpos : (0 : ℝ) < (2 * (H : ℝ) + 1) := by positivity
    have hH0 : (2 * (H : ℝ) + 1) ≠ 0 := ne_of_gt hHpos
    have hcastH : ((2 * H + 1 : ℕ) : ℝ) = (2 * (H : ℝ) + 1) := by
      -- `↑(2H+1) = 2↑H + 1`
      simp [Nat.cast_add, Nat.cast_mul, two_mul, add_assoc, add_left_comm, add_comm, mul_assoc]
    -- unfold and cancel `(2H+1)` against its inverse
    -- goal becomes: `a * (1 / (logX * a)) = (logX)⁻¹`
    have : (2 * (H : ℝ) + 1) * Goldbach.BG_Bank.wScale X = (Real.log (X : ℝ))⁻¹ := by
      unfold Goldbach.BG_Bank.wScale
      field_simp [hlogX0, hH0]
    simpa [hcastH] using this

  -- Assemble.
  calc
    ‖expSum X N γ‖
        ≤ ∑ n ∈ MajorArcStep10RLSmoothIntegral.s N,
            ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := hsum
    _ = ∑ n ∈ MajorArcStep10RLSmoothIntegral.s N, ‖aTerm X n‖ := by
          simpa [hsum_norm]
    _ = ∑ n ∈ S, ‖aTerm X n‖ := by
          simpa [S] using hdrop
    _ ≤ ((2 * H + 1 : ℕ) : ℝ) * ((Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ)) := hsum_le
    _ = (Real.log (N : ℝ)) / (Real.log (X : ℝ)) := by
          -- commute and use `hwScale`.
          calc
            ((2 * H + 1 : ℕ) : ℝ) * (Goldbach.BG_Bank.wScale X * Real.log (N : ℝ))
                = (((2 * H + 1 : ℕ) : ℝ) * Goldbach.BG_Bank.wScale X) * Real.log (N : ℝ) := by
                    ring_nf
            _ = (Real.log (X : ℝ))⁻¹ * Real.log (N : ℝ) := by
                  have := congrArg (fun t => t * Real.log (N : ℝ)) hwScale
                  simpa [mul_assoc] using this
            _ = (Real.log (N : ℝ)) / (Real.log (X : ℝ)) := by
                  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

private lemma norm_innerIntegrand_le (X N : ℕ) (β α : ℝ) (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖innerIntegrand X N β α‖ ≤ ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by
  have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 := by
    simp [fourier_apply]
  have hsub :
      ‖expSum X N ((α : UC) - (β : UC))‖ ≤ (Real.log (N : ℝ)) / (Real.log (X : ℝ)) :=
    norm_expSum_le_logRatio (X := X) (N := N) (γ := (α : UC) - (β : UC)) hX hN
  have hadd :
      ‖expSum X N ((α : UC) + (β : UC))‖ ≤ (Real.log (N : ℝ)) / (Real.log (X : ℝ)) :=
    norm_expSum_le_logRatio (X := X) (N := N) (γ := (α : UC) + (β : UC)) hX hN
  calc
    ‖innerIntegrand X N β α‖
        = ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
            * expSum X N ((α : UC) - (β : UC))
            * expSum X N ((α : UC) + (β : UC))‖ := by
              simp [MajorArcStep17MajorMinorSplit.innerIntegrand, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
          * ‖expSum X N ((α : UC) - (β : UC))‖
          * ‖expSum X N ((α : UC) + (β : UC))‖ := by
          -- `‖x*y*z‖ ≤ ‖x‖*‖y‖*‖z‖` (associate as `(x*y)*z`).
          set x : ℂ := (fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
          set y : ℂ := expSum X N ((α : UC) - (β : UC))
          set z : ℂ := expSum X N ((α : UC) + (β : UC))
          have hxy : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le _ _
          have hxyz : ‖(x * y) * z‖ ≤ ‖x * y‖ * ‖z‖ := norm_mul_le _ _
          have : ‖(x * y) * z‖ ≤ (‖x‖ * ‖y‖) * ‖z‖ :=
            le_trans hxyz (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
          simpa [x, y, z, mul_assoc] using this
    _ ≤ 1 * ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) * ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) := by
          have hfour_le :
              ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ ≤ (1 : ℝ) := by
            simpa [hfour]
          gcongr
    _ = ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by
          simp [pow_two, mul_assoc, hfour]

private lemma norm_innerMajorQ0_le (X N : ℕ) (Δ : ℝ) (β : ℝ) (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖innerMajorQ0 X N Δ β‖ ≤ ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by
  have hconst :
      ∀ α ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖(Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
            (fun α => innerIntegrand X N β α) α‖
          ≤ ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by
    intro α _hα
    by_cases hαM : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ
    · simpa [Set.indicator_of_mem hαM] using
        (norm_innerIntegrand_le (X := X) (N := N) (β := β) (α := α) hX hN)
    · have : (0 : ℝ) ≤ ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by nlinarith
      simpa [Set.indicator_of_notMem hαM] using this
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (C := ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2)
      (f := fun α : ℝ =>
        (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ).indicator
          (fun α => innerIntegrand X N β α) α)
      hconst
  have habs : |((1 : ℝ) - (0 : ℝ))| = (1 : ℝ) := by norm_num
  simpa [Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.innerMajorQ0, habs] using h

private lemma betaSmallSet_subset_Ioc : betaSmallSet ⊆ Set.Ioc aβ bβ := by
  intro β hβ
  have hβ' : -betaSmallRadius ≤ β ∧ β ≤ betaSmallRadius := by
    simpa [betaSmallSet, Set.mem_Icc] using hβ
  have hrad_lt_half : betaSmallRadius < ((2 : ℝ)⁻¹) := by
    -- `betaSmallRadius = 1/(4π) < 1/2`.
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hlt : (2 : ℝ) < (4 * Real.pi : ℝ) := by
      -- `π > 3` gives `4π > 12`.
      nlinarith [Real.pi_gt_three]
    have : (1 : ℝ) / (4 * Real.pi) < (1 : ℝ) / (2 : ℝ) :=
      one_div_lt_one_div_of_lt h2 hlt
    simpa [betaSmallRadius, one_div] using this
  have hleft : aβ < β := by
    have : (-( (2 : ℝ)⁻¹) : ℝ) < -betaSmallRadius := by
      have := neg_lt_neg hrad_lt_half
      simpa [aβ] using this
    exact lt_of_lt_of_le (lt_of_lt_of_le this hβ'.1) le_rfl
  have hright : β ≤ bβ := by
    have : betaSmallRadius ≤ ((2 : ℝ)⁻¹) := le_of_lt hrad_lt_half
    exact le_trans hβ'.2 (by simpa [bβ] using this)
  exact ⟨hleft, hright⟩

private lemma volume_betaSmallSet_toReal_le_one_div_six :
    (volume betaSmallSet).toReal ≤ (1 : ℝ) / 6 := by
  have htoReal : (volume betaSmallSet).toReal = (1 : ℝ) / (2 * Real.pi) := by
    have hvol : volume betaSmallSet = ENNReal.ofReal (2 * betaSmallRadius) := by
      simp [betaSmallSet, Real.volume_Icc, betaSmallRadius, sub_eq_add_neg, two_mul,
        add_assoc, add_left_comm, add_comm, mul_assoc]
    have hnonneg : 0 ≤ (2 * betaSmallRadius : ℝ) := by
      nlinarith [le_of_lt betaSmallRadius_pos]
    calc
      (volume betaSmallSet).toReal
          = (ENNReal.ofReal (2 * betaSmallRadius)).toReal := by simpa [hvol]
      _ = 2 * betaSmallRadius := by
            simpa using (ENNReal.toReal_ofReal hnonneg)
      _ = (1 : ℝ) / (2 * Real.pi) := by
            have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
            -- `betaSmallRadius = 1/(4π)`, so `2*betaSmallRadius = 1/(2π)`.
            unfold betaSmallRadius
            field_simp [hpi0]
            ring
  have h2pi : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hden_le : (1 : ℝ) / (2 * Real.pi) ≤ (1 : ℝ) / 6 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (6 : ℝ)) h2pi
  simpa [htoReal] using hden_le

private lemma norm_corr_integral_major_Q0_small_le_one
    {X N : ℕ} {Δ : ℝ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖corr_integral_major_Q0_small X N Δ‖ ≤ (1 : ℝ) := by
  -- Apply `‖∫ f‖ ≤ |∫ g|` with `g = betaSmallSet.indicator (fun _ => C)`.
  set C : ℝ := kernelCap * ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2
  have hnorm_le :
      ∀ᵐ β ∂(volume : Measure ℝ).restrict (Ι aβ bβ),
        ‖betaSmallSet.indicator (betaIntegrand X N Δ) β‖
          ≤ betaSmallSet.indicator (fun _ : ℝ => C) β := by
    refine Filter.Eventually.of_forall ?_
    intro β
    by_cases hβ : β ∈ betaSmallSet
    · have hK : ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelCap :=
        norm_kernelPolyC_le_kernelCap (x := (β : UC))
      have hI : ‖innerMajorQ0 X N Δ β‖ ≤ ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 :=
        norm_innerMajorQ0_le (X := X) (N := N) (Δ := Δ) (β := β) hX hN
      have hprod : ‖betaIntegrand X N Δ β‖ ≤ C := by
        -- `betaIntegrand = kernelPolyC * innerMajorQ0`.
        have : ‖betaIntegrand X N Δ β‖ ≤ kernelCap * ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by
          calc
            ‖betaIntegrand X N Δ β‖
                = ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
                      * innerMajorQ0 X N Δ β‖ := by rfl
            _ = ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
                  * ‖innerMajorQ0 X N Δ β‖ := by simp [norm_mul]
            _ ≤ kernelCap * ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by
                  exact mul_le_mul hK hI (norm_nonneg _) kernelCap_nonneg
        simpa [C] using this
      simpa [Set.indicator_of_mem hβ] using hprod
    · simp [Set.indicator_of_notMem hβ]
  have hInt : IntervalIntegrable (fun _β : ℝ => betaSmallSet.indicator (fun _ : ℝ => C) _β)
      (volume : Measure ℝ) aβ bβ := by
    -- constant functions are integrable; use the helper from `BetaLocalization`.
    have hconst : IntervalIntegrable (fun _β : ℝ => (C : ℝ)) (volume : Measure ℝ) aβ bβ := by
      simpa using (intervalIntegrable_const : IntervalIntegrable (fun _β : ℝ => (C : ℝ))
        (volume : Measure ℝ) aβ bβ)
    exact intervalIntegrable_indicator_of_intervalIntegrable (a := aβ) (b := bβ)
      (s := betaSmallSet) measurableSet_betaSmallSet hconst
  have hmain :
      ‖corr_integral_major_Q0_small X N Δ‖ ≤ |∫ β in aβ..bβ, betaSmallSet.indicator (fun _ : ℝ => C) β| := by
    -- `corr_integral_major_Q0_small` is an interval integral of `betaSmallSet.indicator`.
    simpa [corr_integral_major_Q0_small, aβ, bβ] using
      (intervalIntegral.norm_integral_le_abs_of_norm_le (μ := (volume : Measure ℝ)) (a := aβ) (b := bβ)
        (f := fun β : ℝ => betaSmallSet.indicator (betaIntegrand X N Δ) β)
        (g := fun β : ℝ => betaSmallSet.indicator (fun _ : ℝ => C) β)
        hnorm_le hInt)
  -- Evaluate `∫ betaSmallSet.indicator (const C)` as `C * volume(betaSmallSet)`.
  have hsubset : betaSmallSet ⊆ Set.Ioc aβ bβ := betaSmallSet_subset_Ioc
  have hab : aβ ≤ bβ := BetaInterval.hle
  have hcalc :
      (∫ β in aβ..bβ, betaSmallSet.indicator (fun _ : ℝ => C) β)
        =
      (volume betaSmallSet).toReal * C := by
    -- Convert to an integral with restricted measure on `Ioc`, then apply `integral_indicator_const`.
    rw [intervalIntegral.integral_of_le hab]
    -- Integral of indicator-constant over the restricted measure.
    have hI :
        (∫ β : ℝ,
            betaSmallSet.indicator (fun _ : ℝ => C) β
              ∂(volume : Measure ℝ).restrict (Set.Ioc aβ bβ))
          =
        ((volume : Measure ℝ).restrict (Set.Ioc aβ bβ)).real betaSmallSet * C := by
      simpa [smul_eq_mul] using
        (MeasureTheory.integral_indicator_const (μ := (volume : Measure ℝ).restrict (Set.Ioc aβ bβ))
          (e := (C : ℝ)) (s := betaSmallSet) measurableSet_betaSmallSet)
    -- Rewrite the restricted measure of `betaSmallSet` using the subset relation.
    have hμ :
        ((volume : Measure ℝ).restrict (Set.Ioc aβ bβ)) betaSmallSet = volume betaSmallSet := by
      have hmeas : MeasurableSet (Set.Ioc aβ bβ) := measurableSet_Ioc
      have hmeasβ : MeasurableSet betaSmallSet := measurableSet_betaSmallSet
      -- `betaSmallSet ∩ Ioc = betaSmallSet`.
      have hinter : betaSmallSet ∩ Set.Ioc aβ bβ = betaSmallSet := by
        ext β
        constructor
        · intro h; exact h.1
        · intro h; exact ⟨h, hsubset h⟩
      simpa [Measure.restrict_apply, hmeasβ, hinter, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using
        (Measure.restrict_apply (volume : Measure ℝ) (Set.Ioc aβ bβ) betaSmallSet)
    -- Assemble.
    have : ((volume : Measure ℝ).restrict (Set.Ioc aβ bβ)).real betaSmallSet = (volume betaSmallSet).toReal := by
      simp [Measure.real, hμ]
    simpa [hI, this, mul_assoc, mul_left_comm, mul_comm]
  -- Use crude bounds: `C ≤ 6` and `volume(betaSmallSet) ≤ 1/6`.
  have hC_le6 : C ≤ (6 : ℝ) := by
    have hk : kernelCap ≤ (3 : ℝ) := kernelCap_le_three
    have hs : ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 ≤ (2 : ℝ) :=
      logRatio_sq_le_two (X := X) (N := N) hX hN
    have hk0 : 0 ≤ kernelCap := kernelCap_nonneg
    nlinarith [hk, hs, hk0]
  have hvol : (volume betaSmallSet).toReal ≤ (1 : ℝ) / 6 :=
    volume_betaSmallSet_toReal_le_one_div_six
  have hbound_int :
      |∫ β in aβ..bβ, betaSmallSet.indicator (fun _ : ℝ => C) β|
        ≤ (1 : ℝ) := by
    have hC0 : 0 ≤ C := by
      have hk0 : 0 ≤ kernelCap := kernelCap_nonneg
      have hs0 : 0 ≤ ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 := by nlinarith
      exact mul_nonneg hk0 hs0
    -- `∫ = (volume betaSmallSet).toReal * C`, and both factors are nonnegative.
    have habs : |(volume betaSmallSet).toReal * C| = (volume betaSmallSet).toReal * C := by
      exact abs_of_nonneg (mul_nonneg (by
        have : 0 ≤ (volume betaSmallSet).toReal := by exact ENNReal.toReal_nonneg
        exact this) hC0)
    calc
      |∫ β in aβ..bβ, betaSmallSet.indicator (fun _ : ℝ => C) β|
          = |(volume betaSmallSet).toReal * C| := by simpa [hcalc]
      _ = (volume betaSmallSet).toReal * C := habs
      _ ≤ ((1 : ℝ) / 6) * (6 : ℝ) := by nlinarith [hvol, hC_le6]
      _ = (1 : ℝ) := by norm_num
  exact le_trans hmain hbound_int

private lemma abs_sigma_trunc_Q0_le_Q0 (N : ℕ) :
    |sigma_trunc_Q0 N| ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
  classical
  -- Triangle inequality and a termwise `≤ 1` bound.
  unfold sigma_trunc_Q0
  have hsum :
      |∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * ramanujanR q N|
        ≤
      ∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          |muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * ramanujanR q N| :=
    Finset.abs_sum_le_sum_abs
      (f := fun q =>
        muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * ramanujanR q N)
      (s := Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0)
  refine le_trans hsum ?_
  have hterm :
      ∀ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
        |muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * ramanujanR q N| ≤ (1 : ℝ) := by
    intro q hq
    by_cases hsq : Squarefree q
    · have hq0 : q ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 1) (Finset.mem_Icc.mp hq).1)
      -- Rewrite the term using the closed form from `TailBlock.term_bound_after_split`.
      set d : ℕ := Nat.gcd q N
      set r : ℕ := q / d
      have hEq :
          |muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * ramanujanR q N|
            =
          1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
        simpa [d, r] using (term_bound_after_split (q := q) (N := N) hsq hq0)
      -- Denominator is ≥ 1, hence the fraction is ≤ 1.
      have hdpos : 0 < d := Nat.gcd_pos_of_pos_left N (Nat.pos_of_ne_zero hq0)
      have hd0 : d ≠ 0 := Nat.ne_of_gt hdpos
      have hd_le_q : d ≤ q := by
        simpa [d] using (Nat.gcd_le_left (m := q) (n := N) (Nat.pos_of_ne_zero hq0))
      have hr0 : r ≠ 0 := by
        have : q / d ≠ 0 := by
          intro hdiv
          have h' : d = 0 ∨ q < d := (Nat.div_eq_zero_iff).1 hdiv
          cases h' with
          | inl hd0' => exact hd0 hd0'
          | inr hlt => exact (Nat.not_lt_of_ge hd_le_q) hlt
        simpa [r, d] using this
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      have hd1 : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
        have : (1 : ℕ) ≤ Nat.totient d := Nat.succ_le_of_lt (Nat.totient_pos.mpr hdpos)
        exact_mod_cast this
      have hr1 : (1 : ℝ) ≤ (Nat.totient r : ℝ) := by
        have : (1 : ℕ) ≤ Nat.totient r := Nat.succ_le_of_lt (Nat.totient_pos.mpr hrpos)
        exact_mod_cast this
      have hr_sq1 : (1 : ℝ) ≤ (Nat.totient r : ℝ) ^ 2 := by
        have hr0' : (0 : ℝ) ≤ (Nat.totient r : ℝ) := le_trans (by norm_num) hr1
        have hmul :
            (1 : ℝ) * (1 : ℝ) ≤ (Nat.totient r : ℝ) * (Nat.totient r : ℝ) :=
          mul_le_mul hr1 hr1 (by norm_num : (0 : ℝ) ≤ 1) hr0'
        simpa [pow_two] using hmul
      have hden1 : (1 : ℝ) ≤ (Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2 := by
        have hd0' : (0 : ℝ) ≤ (Nat.totient d : ℝ) := le_trans (by norm_num) hd1
        have hmul :
            (1 : ℝ) * (1 : ℝ) ≤ (Nat.totient d : ℝ) * ((Nat.totient r : ℝ) ^ 2) :=
          mul_le_mul hd1 hr_sq1 (by norm_num : (0 : ℝ) ≤ 1) hd0'
        simpa [one_mul] using hmul
      have hfrac :
          (1 : ℝ) / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) ≤ (1 : ℝ) := by
        have h :=
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden1
        simpa using h
      -- Finish: rewrite the goal using the closed form.
      rw [hEq]
      exact hfrac
    · simp [muSq, hsq]
  have hsum_le :
      (∑ q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0,
          |muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * ramanujanR q N|)
        ≤
      ∑ _q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0, (1 : ℝ) := by
    exact Finset.sum_le_sum (fun q hq => hterm q hq)
  have hcard :
      (∑ _q ∈ Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0, (1 : ℝ))
        =
      (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
    have h1 : (1 : ℕ) ≤ Goldbach.AO_OffDiag.TailBlock.Q0 := by decide
    have hcard' :
        (Finset.Icc (1 : ℕ) Goldbach.AO_OffDiag.TailBlock.Q0).card
          =
        Goldbach.AO_OffDiag.TailBlock.Q0 := by
      simpa using (Finset.card_Icc (a := (1 : ℕ)) (b := Goldbach.AO_OffDiag.TailBlock.Q0) h1)
    simp [hcard']
  exact le_trans hsum_le (by simpa [hcard])

private lemma mass_even_abs_le_two : |Goldbach.AO_SigmaModel.Canon.mass_even| ≤ (2 : ℝ) := by
  -- `mass_even = A - B` with `A,B ≥ 0` and both `A ≤ 1`, `B ≤ 1` for the fixed parameters.
  set m : ℕ := Goldbach.AO_SigmaModel.Canon.m
  set Ucut : ℕ := Goldbach.AO_SigmaModel.Canon.Ucut
  set A : ℝ := ((2 * m + 1 : ℕ) : ℝ) / (Ucut : ℝ)
  set B : ℝ := ((2 * m * (m + 1) : ℕ) : ℝ) / ((Ucut : ℝ) ^ 2)
  have hUpos : 0 < (Ucut : ℝ) := by
    have : 0 < Ucut := by decide
    exact_mod_cast this
  have hUpos2 : 0 < (Ucut : ℝ) ^ 2 := sq_pos_of_pos hUpos
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact div_nonneg this (le_of_lt hUpos)
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ((2 * m * (m + 1) : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact div_nonneg this (le_of_lt hUpos2)
  have hA1 : A ≤ (1 : ℝ) := by
    have hnat : 2 * m + 1 ≤ Ucut := by decide
    have hreal : ((2 * m + 1 : ℕ) : ℝ) ≤ (Ucut : ℝ) := by exact_mod_cast hnat
    exact (div_le_iff₀ hUpos).2 (by simpa using hreal)
  have hB1 : B ≤ (1 : ℝ) := by
    have hnat : 2 * m * (m + 1) ≤ Ucut ^ 2 := by decide
    have hreal : ((2 * m * (m + 1) : ℕ) : ℝ) ≤ (Ucut : ℝ) ^ 2 := by exact_mod_cast hnat
    exact (div_le_iff₀ hUpos2).2 (by simpa using hreal)
  have habs : |A - B| ≤ A + B := by
    -- `|A - B| = |A + (-B)| ≤ |A| + |B| = A + B`.
    have := abs_add_le A (-B)
    simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg hA0, abs_of_nonneg hB0, add_comm, add_left_comm,
      add_assoc] using this
  have hsum : A + B ≤ (2 : ℝ) := by nlinarith [hA1, hB1]
  -- Unfold `mass_even` and rewrite.
  have hmass :
      Goldbach.AO_SigmaModel.Canon.mass_even = A - B := by
    simp [Goldbach.AO_SigmaModel.Canon.mass_even, A, B, m, Ucut, sub_eq_add_neg]
  simpa [hmass] using le_trans habs hsum

private lemma norm_corrModel_le_one
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖corrModel X N‖ ≤ (1 : ℝ) := by
  have hs : |sigma_trunc_Q0 N| ≤ (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) :=
    abs_sigma_trunc_Q0_le_Q0 (N := N)
  have hm : |Goldbach.AO_SigmaModel.Canon.mass_even| ≤ (2 : ℝ) :=
    mass_even_abs_le_two
  have hratio : ((Real.log (N : ℝ)) / (Real.log (X : ℝ))) ^ 2 ≤ (2 : ℝ) :=
    logRatio_sq_le_two (X := X) (N := N) hX hN
  have hlogX_ge13 : (13 : ℝ) ≤ Real.log (X : ℝ) := thirteen_le_log_of_X0_le hX
  have hlogXpos : 0 < Real.log (X : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 13) hlogX_ge13
  have hlogX0 : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogXpos

  -- Rewrite `‖corrModel‖` as an absolute value of a real product.
  have hnorm :
      ‖corrModel X N‖
        =
      |(Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaModel.sigma N *
          Goldbach.AO_WeightMass.weight_mass X| := by
    -- Avoid rewriting the casted real expression into a product of complex factors; just use `‖(r:ℂ)‖ = |r|`.
    set r : ℝ :=
      (Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaModel.sigma N *
        Goldbach.AO_WeightMass.weight_mass X
    have hr : corrModel X N = (r : ℂ) := by
      simp [CorrModel.corrModel, r]
    calc
      ‖corrModel X N‖ = ‖(r : ℂ)‖ := by simpa [hr]
      _ = |r| := by
        simpa using (RCLike.norm_ofReal (K := ℂ) r)
      _ = |(Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaModel.sigma N *
            Goldbach.AO_WeightMass.weight_mass X| := by
        simp [r]

  -- Bound the sigma factor: `|(800)*sigma| = |mass_even|*|sigma_trunc| ≤ 2*Q0`.
  have hsigma :
      |(800 : ℝ) * Goldbach.AO_SigmaModel.sigma N|
        =
      |Goldbach.AO_SigmaModel.Canon.mass_even| * |sigma_trunc_Q0 N| := by
    simp [Goldbach.AO_SigmaModel.sigma, abs_mul, mul_assoc, mul_left_comm, mul_comm]
  have hsigma_le :
      |(800 : ℝ) * Goldbach.AO_SigmaModel.sigma N|
        ≤ (2 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
    have : |Goldbach.AO_SigmaModel.Canon.mass_even| * |sigma_trunc_Q0 N|
        ≤ (2 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) := by
      -- `|mass_even|*|sigma_trunc| ≤ 2*Q0` from the separate bounds.
      exact
        mul_le_mul hm hs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    simpa [hsigma] using this

  -- Bound the log+weight factor:
  -- `(log N)^2 * weight_mass X = (log N / log X)^2 / (2H+1)^2 ≤ 2 / (2H+1)^2`.
  have hwmass :
      Goldbach.AO_WeightMass.weight_mass X
        =
      (Real.log (X : ℝ))⁻¹ ^ 2 * ((2 * H + 1 : ℝ)⁻¹ ^ 2) := by
    simp [Goldbach.AO_WeightMass.weight_mass, Goldbach.BG_Bank.wScale, one_div, hlogX0,
      pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hlogmass :
      (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_WeightMass.weight_mass X
        ≤ (2 : ℝ) / ((2 * H + 1 : ℝ) ^ 2) := by
    have hden : ((2 * H + 1 : ℝ)⁻¹ ^ 2) = 1 / ((2 * H + 1 : ℝ) ^ 2) := by
      simp [pow_two, one_div]
    -- Convert the ratio square bound into a bound on `log^2 * (1/logX)^2`.
    have hlogpart :
        (Real.log (N : ℝ)) ^ 2 * ((Real.log (X : ℝ))⁻¹ ^ 2) ≤ (2 : ℝ) := by
      -- `(log N / log X)^2 = (log N)^2 * (1/log X)^2`.
      simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio
    calc
      (Real.log (N : ℝ)) ^ 2 * Goldbach.AO_WeightMass.weight_mass X
          = ((Real.log (N : ℝ)) ^ 2 * ((Real.log (X : ℝ))⁻¹ ^ 2)) * ((2 * H + 1 : ℝ)⁻¹ ^ 2) := by
              rw [hwmass]
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (2 : ℝ) * ((2 * H + 1 : ℝ)⁻¹ ^ 2) := by
              gcongr
      _ = (2 : ℝ) / ((2 * H + 1 : ℝ) ^ 2) := by
              -- Rewrite the square of the inverse as a division, then fold `*` into `/`.
              simp [hden, div_eq_mul_inv, mul_assoc]

  -- Put everything together: `‖corrModel‖ ≤ 4 * Q0 / (2H+1)^2`.
  have hbound :
      ‖corrModel X N‖
        ≤ (4 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 * H + 1 : ℝ) ^ 2) := by
    rw [hnorm]
    have hlogabs : |(Real.log (N : ℝ)) ^ 2| = (Real.log (N : ℝ)) ^ 2 := abs_of_nonneg (sq_nonneg _)
    have hwmass_abs : |Goldbach.AO_WeightMass.weight_mass X| = Goldbach.AO_WeightMass.weight_mass X := by
      have : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
        have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
        -- `weight_mass X = (wScale X)^2`.
        simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
      simpa [abs_of_nonneg this]
    calc
      |(Real.log (N : ℝ)) ^ 2 * (800 : ℝ) * Goldbach.AO_SigmaModel.sigma N *
            Goldbach.AO_WeightMass.weight_mass X|
          =
        (Real.log (N : ℝ)) ^ 2 * |(800 : ℝ) * Goldbach.AO_SigmaModel.sigma N|
          * Goldbach.AO_WeightMass.weight_mass X := by
            simp [hlogabs, hwmass_abs, abs_mul, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ ((Real.log (N : ℝ)) ^ 2 * Goldbach.AO_WeightMass.weight_mass X)
            * ((2 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)) := by
            have hlog_nonneg : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
            have hmass_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
              have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
              simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
            have h1 :
                (Real.log (N : ℝ)) ^ 2 * |(800 : ℝ) * Goldbach.AO_SigmaModel.sigma N|
                  ≤ (Real.log (N : ℝ)) ^ 2 * ((2 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hsigma_le hlog_nonneg
            have h2 :
                ((Real.log (N : ℝ)) ^ 2 * |(800 : ℝ) * Goldbach.AO_SigmaModel.sigma N|)
                    * Goldbach.AO_WeightMass.weight_mass X
                  ≤ ((Real.log (N : ℝ)) ^ 2 * ((2 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)))
                    * Goldbach.AO_WeightMass.weight_mass X := by
              exact mul_le_mul_of_nonneg_right h1 hmass_nonneg
            simpa [mul_assoc, mul_left_comm, mul_comm] using h2
      _ ≤ (2 : ℝ) / ((2 * H + 1 : ℝ) ^ 2) * ((2 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)) := by
            gcongr
      _ = (4 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 * H + 1 : ℝ) ^ 2) := by
            ring_nf

  have hnum : (4 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ) / ((2 * H + 1 : ℝ) ^ 2) ≤ (1 : ℝ) := by
    norm_num [Goldbach.BankParams.H, Goldbach.AO_OffDiag.TailBlock.Q0]

  exact le_trans hbound hnum

/-- Deterministic small-β upper bound in the certificate-facing interface. -/
theorem major_arc_small_beta_upperBound :
    Q0MajorSmallUpperBound Δ_canon U := by
  refine ⟨?_, ?_⟩
  · -- `U = 2` in the current generated artifact.
    have hQ : (0 : ℚ) ≤ Q0MajorSmallCertData.data.U := by
      dsimp [Q0MajorSmallCertData.data]
      norm_num
    exact_mod_cast hQ
  · intro X N hX hN
    have hcorr : ‖corr_integral_major_Q0_small X N Δ_canon‖ ≤ (1 : ℝ) :=
      norm_corr_integral_major_Q0_small_le_one (X := X) (N := N) (Δ := Δ_canon) hX hN
    have hmodel : ‖corrModel X N‖ ≤ (1 : ℝ) :=
      norm_corrModel_le_one (X := X) (N := N) hX hN
    have htri :
        ‖corr_integral_major_Q0_small X N Δ_canon - corrModel X N‖
          ≤ ‖corr_integral_major_Q0_small X N Δ_canon‖ + ‖corrModel X N‖ := by
      simpa using (norm_sub_le (corr_integral_major_Q0_small X N Δ_canon) (corrModel X N))
    have h2 : ‖corr_integral_major_Q0_small X N Δ_canon - corrModel X N‖ ≤ (2 : ℝ) := by
      have : ‖corr_integral_major_Q0_small X N Δ_canon - corrModel X N‖ ≤ (1 : ℝ) + (1 : ℝ) :=
        le_trans htri (add_le_add hcorr hmodel)
      have h11 : (1 : ℝ) + (1 : ℝ) = (2 : ℝ) := by norm_num
      simpa [h11] using this
    have hU : U = (2 : ℝ) := by
      dsimp [U, Q0MajorSmallCertData.data]
      norm_num
    simpa [hU] using h2

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallUpperBoundDeterministic
