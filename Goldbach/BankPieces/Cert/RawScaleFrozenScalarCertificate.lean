import Goldbach.BankPieces.Cert.RawScaleFrozenCertificates
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarLower
import Goldbach.ProofTools

namespace Goldbach.BankPieces.Cert.RawScaleFrozenScalarCertificate

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.ProofTools.Windows
open Goldbach.BankPieces.Cert.RawScaleFrozenClosure
open Goldbach.BankPieces.Cert.RawScaleFrozenCertificates
open Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge
open Goldbach.BankPieces.Cert.RawScaleWeightedKernel
open Goldbach.BankPieces.Cert.IntegralScaleClosureGate
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarBounds
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarLower

noncomputable section

lemma mass_even_nonneg : 0 ≤ Goldbach.AO_SigmaModel.Canon.mass_even := by
  norm_num [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
    Goldbach.AO_SigmaModel.Canon.Ucut, Goldbach.BankParams.H]

lemma mass_even_le_one : Goldbach.AO_SigmaModel.Canon.mass_even ≤ (1 : ℝ) := by
  norm_num
    [Goldbach.AO_SigmaModel.Canon.mass_even, Goldbach.AO_SigmaModel.Canon.m,
      Goldbach.AO_SigmaModel.Canon.Ucut, Goldbach.BankParams.H]

lemma log_sq_le_X_div_fifty {X : ℕ} (hX : BankParams.X0 ≤ X) :
    (Real.log (X : ℝ)) ^ 2 ≤ (X : ℝ) / 50 := by
  have hXreal : (BankParams.X0 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hX
  have hXreal' : (1000000 : ℝ) ≤ (X : ℝ) := by
    simpa [BankParams.X0] using hXreal
  have hXreal' : (1000000 : ℝ) ≤ (X : ℝ) := by
    simpa [BankParams.X0] using hXreal
  have hXreal' : (1000000 : ℝ) ≤ (X : ℝ) := by
    simpa [BankParams.X0] using hXreal
  have hXreal' : (1000000 : ℝ) ≤ (X : ℝ) := by
    simpa [BankParams.X0] using hXreal
  have hXnonneg : 0 ≤ (X : ℝ) := by positivity
  have hXpos : 0 < (X : ℝ) := by
    exact lt_of_lt_of_le (by norm_num [BankParams.X0]) hXreal
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hlog :
      Real.log (X : ℝ) ≤ ((X : ℝ) ^ (1 / 4 : ℝ)) / (1 / 4 : ℝ) :=
    Real.log_le_rpow_div hXnonneg hquarter
  have hlog_nonneg : 0 ≤ Real.log (X : ℝ) := by
    have hXge1 : (1 : ℝ) ≤ (X : ℝ) := by
      have hX0one : (1 : ℕ) ≤ BankParams.X0 := by norm_num [BankParams.X0]
      exact_mod_cast (le_trans hX0one hX)
    exact Real.log_nonneg hXge1
  have hpow_nonneg : 0 ≤ ((X : ℝ) ^ (1 / 4 : ℝ)) / (1 / 4 : ℝ) := by
    positivity
  have hsq :
      (Real.log (X : ℝ)) ^ 2 ≤ ((((X : ℝ) ^ (1 / 4 : ℝ)) / (1 / 4 : ℝ)) ^ 2) := by
    nlinarith
  have hsquare :
      ((((X : ℝ) ^ (1 / 4 : ℝ)) / (1 / 4 : ℝ)) ^ 2) = 16 * Real.sqrt (X : ℝ) := by
    have hpow :
        (((X : ℝ) ^ (1 / 4 : ℝ)) ^ 2) = Real.sqrt (X : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXnonneg]
      norm_num
      rw [Real.sqrt_eq_rpow]
    calc
      ((((X : ℝ) ^ (1 / 4 : ℝ)) / (1 / 4 : ℝ)) ^ 2)
          = 16 * (((X : ℝ) ^ (1 / 4 : ℝ)) ^ 2) := by
              ring_nf
      _ = 16 * Real.sqrt (X : ℝ) := by rw [hpow]
  have hsqrt_le : Real.sqrt (X : ℝ) ≤ (X : ℝ) / 1000 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)).2
    have hsq : (Real.sqrt (X : ℝ)) ^ 2 = (X : ℝ) := by
      rw [Real.sq_sqrt hXnonneg]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
    have h1000sq : ((1000 : ℝ) ^ 2) ≤ (X : ℝ) := by
      nlinarith [hXreal']
    have h1000_le : (1000 : ℝ) ≤ Real.sqrt (X : ℝ) := by
      nlinarith
    nlinarith
  calc
    (Real.log (X : ℝ)) ^ 2 ≤ ((((X : ℝ) ^ (1 / 4 : ℝ)) / (1 / 4 : ℝ)) ^ 2) := hsq
    _ = 16 * Real.sqrt (X : ℝ) := hsquare
    _ ≤ 16 * ((X : ℝ) / 1000) := by gcongr
    _ = ((2 : ℝ) / 125) * (X : ℝ) := by ring
    _ ≤ (X : ℝ) / 50 := by
      have hcoef : (2 : ℝ) / 125 ≤ (1 : ℝ) / 50 := by norm_num
      nlinarith

lemma scalar_explicit_lower_ge_X_div_fifty
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    (X : ℝ) / 50
      ≤
    (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
      - 2 * Goldbach.BG_Identity.C_tail_closed * (N - 5 : ℝ) := by
  have hXreal : (BankParams.X0 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hX
  have hXreal' : (1000000 : ℝ) ≤ (X : ℝ) := by
    simpa [BankParams.X0] using hXreal
  have hNge : (X : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_left_of_mem_EvenIn hN
  have hNle : (N : ℝ) ≤ (X + BankParams.H : ℕ) := by
    exact_mod_cast le_right_of_mem_EvenIn hN
  have hN5 : 5 ≤ N := by
    exact le_trans (le_trans (by decide : 5 ≤ BankParams.X0) hX) (le_left_of_mem_EvenIn hN)
  have hvol :
      (MeasureTheory.volume (tinyBetaSet X)).toReal = 1 / (3 * ((X + BankParams.H : ℕ) : ℝ)) := by
    rw [volume_tinyBetaSet_toReal, tinyBetaRadius]
    ring_nf
  have hsub :
      (((N - 5 : ℕ) : ℝ)) = (N : ℝ) - 5 := by
    rw [Nat.cast_sub hN5]
    norm_num
  have hsubsq :
      ((((N - 5 : ℕ) : ℝ) ^ 2) / 8) = (((N : ℝ) - 5) ^ 2 / 8) := by
    rw [hsub]
  have htail :
      Goldbach.BG_Identity.C_tail_closed = (99 : ℝ) / 1020100 := by
    norm_num [Goldbach.BG_Identity.C_tail_closed, Goldbach.BG_Identity.Ucut, Goldbach.BankParams.H]
  have htail_nonneg : 0 ≤ Goldbach.BG_Identity.C_tail_closed := by
    rw [htail]
    positivity
  have hposterm :
      ((X : ℝ) - 5) ^ 2 / (24 * ((X + BankParams.H : ℕ) : ℝ))
        ≤
      (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8) := by
    rw [hvol, hsubsq]
    have hXminus_le_Nminus : (X : ℝ) - 5 ≤ (N : ℝ) - 5 := by linarith
    have hXminus_nonneg : 0 ≤ (X : ℝ) - 5 := by
      have : (5 : ℝ) ≤ (X : ℝ) := by
        exact_mod_cast (le_trans (by decide : 5 ≤ BankParams.X0) hX)
      linarith
    have hsquare_le : ((X : ℝ) - 5) ^ 2 ≤ ((N : ℝ) - 5) ^ 2 := by
      nlinarith
    have hXHnat : 0 < X + BankParams.H := by
      have hH : 0 < BankParams.H := by norm_num [BankParams.H]
      exact lt_of_lt_of_le hH (Nat.le_add_left BankParams.H X)
    have hXHpos : 0 < ((X + BankParams.H : ℕ) : ℝ) := by exact_mod_cast hXHnat
    have hden : 0 < (24 : ℝ) * ((X + BankParams.H : ℕ) : ℝ) := by positivity
    have hXH_ne : ((X + BankParams.H : ℕ) : ℝ) ≠ 0 := by linarith
    have hrhs :
        (1 / (3 * ((X + BankParams.H : ℕ) : ℝ))) * (((N : ℝ) - 5) ^ 2 / 8)
          = ((N : ℝ) - 5) ^ 2 / (24 * ((X + BankParams.H : ℕ) : ℝ)) := by
      field_simp [hXH_ne]
      ring
    rw [hrhs]
    exact div_le_div_of_nonneg_right hsquare_le hden.le
  have htailterm :
      -(2 * Goldbach.BG_Identity.C_tail_closed * (((X + BankParams.H : ℕ) : ℝ) - 5))
        ≤
      -(2 * Goldbach.BG_Identity.C_tail_closed * ((N : ℝ) - 5)) := by
    nlinarith
  have hmain :
      (X : ℝ) / 50
        ≤
      ((X : ℝ) - 5) ^ 2 / (24 * ((X + BankParams.H : ℕ) : ℝ))
        - 2 * Goldbach.BG_Identity.C_tail_closed * (((X + BankParams.H : ℕ) : ℝ) - 5) := by
    rw [htail]
    have hXHnat : 0 < X + BankParams.H := by
      have hH : 0 < BankParams.H := by norm_num [BankParams.H]
      exact lt_of_lt_of_le hH (Nat.le_add_left BankParams.H X)
    have hXHpos : 0 < ((X + BankParams.H : ℕ) : ℝ) := by exact_mod_cast hXHnat
    have hXH_ne : ((X + BankParams.H : ℕ) : ℝ) ≠ 0 := by linarith
    have hXreal'' : (1000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXreal'
    norm_num [BankParams.H] at ⊢
    field_simp [hXH_ne]
    ring_nf at *
    nlinarith [hXreal'']
  calc
    (X : ℝ) / 50
      ≤ ((X : ℝ) - 5) ^ 2 / (24 * ((X + BankParams.H : ℕ) : ℝ))
          - 2 * Goldbach.BG_Identity.C_tail_closed * (((X + BankParams.H : ℕ) : ℝ) - 5) := hmain
    _ ≤ (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
          - 2 * Goldbach.BG_Identity.C_tail_closed * (((X + BankParams.H : ℕ) : ℝ) - 5) := by
            linarith [hposterm]
    _ ≤ (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
          - 2 * Goldbach.BG_Identity.C_tail_closed * ((N : ℝ) - 5) := by
            linarith [htailterm]
    _ = (MeasureTheory.volume (tinyBetaSet X)).toReal * ((((N - 5 : ℕ) : ℝ) ^ 2) / 8)
          - 2 * Goldbach.BG_Identity.C_tail_closed * (N - 5 : ℝ) := by
            rw [hsub]

theorem frozenScalarXCenteredTargetOne_zero_nonneg
    {X : ℕ} (_hX : BankParams.X0 ≤ X) :
    0 ≤ frozenScalarXCenteredTargetOne (fun _ => 0) X := by
  dsimp [frozenScalarXCenteredTargetOne, frozenScalarXCenteredTarget]
  have hlog_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ 2 := sq_nonneg _
  simpa using mul_nonneg hlog_nonneg mass_even_nonneg

theorem frozenScalarXCenteredTargetOne_zero_le_re_two_mul_frozenBetaScalarC
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    frozenScalarXCenteredTargetOne (fun _ => 0) X
      ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N) := by
  have htarget_le_X :
      frozenScalarXCenteredTargetOne (fun _ => 0) X ≤ (X : ℝ) / 50 := by
    dsimp [frozenScalarXCenteredTargetOne, frozenScalarXCenteredTarget]
    have hlog : (Real.log (X : ℝ)) ^ 2 ≤ (X : ℝ) / 50 := log_sq_le_X_div_fifty hX
    have hmass_nonneg : 0 ≤ Goldbach.AO_SigmaModel.Canon.mass_even := mass_even_nonneg
    have hmass_le : Goldbach.AO_SigmaModel.Canon.mass_even ≤ 1 := mass_even_le_one
    nlinarith
  have hlower :
      (X : ℝ) / 50 ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N) := by
    exact le_trans (scalar_explicit_lower_ge_X_div_fifty hX hN)
      (re_two_mul_frozenBetaScalarC_lower_bound_explicit hX hN)
  exact le_trans htarget_le_X hlower

theorem frozenWeightedMainTermKappaC_re_lower_of_XCenteredScalarCertOneZero_seriesTail
    (hκconst_nonneg : 0 ≤ kappaSeriesR 1 - (90 : ℝ) / Goldbach.AO_OffDiag.TailBlock.Q0) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      (frozenScalarXCenteredTargetOne (fun _ => 0) X
          * (kappaSeriesR 1 - (90 : ℝ) / Goldbach.AO_OffDiag.TailBlock.Q0)) / (X : ℝ)
        ≤ Complex.re (frozenWeightedMainTermKappaC X N) := by
  intro X N hX hN
  exact
    frozenWeightedMainTermKappaC_re_lower_of_XCenteredScalarCertOne_seriesTail
      (ηscalar := fun _ => 0) hκconst_nonneg
      (fun {_} hX => frozenScalarXCenteredTargetOne_zero_nonneg hX)
      (fun hX hN => frozenScalarXCenteredTargetOne_zero_le_re_two_mul_frozenBetaScalarC hX hN)
      hX hN

theorem R_bank_pos_of_frozenRoute_XCenteredScalarCertOneZero_fullGap_seriesTail
    (ηminor ηlarge ηsmall εb : ℕ → ℝ)
    (hκconst_nonneg : 0 ≤ kappaSeriesR 1 - (90 : ℝ) / Goldbach.AO_OffDiag.TailBlock.Q0)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X →
        (ηminor X + ηlarge X + ηsmall X) + εb X
          < (frozenScalarXCenteredTargetOne (fun _ => 0) X
              * (kappaSeriesR 1 - (90 : ℝ) / Goldbach.AO_OffDiag.TailBlock.Q0)) / (X : ℝ))
    (hMinor :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0 X N (1 : ℝ)‖
          ≤ ηminor X)
    (hLarge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_large X N (1 : ℝ)‖
          ≤ ηlarge X)
    (hSmall :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
            - frozenWeightedMainTermKappaC X N‖ ≤ ηsmall X)
    (hInt :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        IntervalIntegrable
          (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.βIntegrand X N (1 : ℝ))
          MeasureTheory.volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  exact
    R_bank_pos_of_frozenRoute_XCenteredScalarCertOne_fullGap_seriesTail
      (ηscalar := fun _ => 0) (ηminor := ηminor) (ηlarge := ηlarge) (ηsmall := ηsmall) (εb := εb)
      hκconst_nonneg hεb_nonneg
      (fun {_} hX => frozenScalarXCenteredTargetOne_zero_nonneg hX)
      (fun hX hN => frozenScalarXCenteredTargetOne_zero_le_re_two_mul_frozenBetaScalarC hX hN)
      hsum_lt hMinor hLarge hSmall hInt hBridge hX hN

end

end Goldbach.BankPieces.Cert.RawScaleFrozenScalarCertificate
