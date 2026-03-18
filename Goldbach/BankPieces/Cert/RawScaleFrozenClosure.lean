import Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge
import Goldbach.BankPieces.Cert.IntegralScaleClosureGate

namespace Goldbach.BankPieces.Cert.RawScaleFrozenClosure

open Complex
open Goldbach
open Goldbach.Windows
open Goldbach.BankPieces.Cert.RawScaleFrozenKernelBridge
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.BankPieces.Cert.RawScaleWeightedKernel
open Goldbach.BankPieces.Cert.IntegralScaleClosureGate

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-- The full corr-integral gap follows from a rest term plus the frozen small-`β` gap. -/
theorem norm_corr_integral_sub_frozenWeightedMainTermKappaC_le_of_rest_small
    {X N : ℕ} {ηrest ηsmall : ℝ}
    (hrest :
      ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
          - Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N
              (1 : ℝ)‖ ≤ ηrest)
    (hsmall :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
          - frozenWeightedMainTermKappaC X N‖ ≤ ηsmall) :
    ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
        - frozenWeightedMainTermKappaC X N‖ ≤ ηrest + ηsmall := by
  calc
    ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
        - frozenWeightedMainTermKappaC X N‖
      =
        ‖(Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
              - Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N
                  (1 : ℝ))
            + (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N
                (1 : ℝ)
              - frozenWeightedMainTermKappaC X N)‖ := by
          ring_nf
    _ ≤
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N
                (1 : ℝ)‖
          +
        ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
            - frozenWeightedMainTermKappaC X N‖ := by
          exact norm_add_le _ _
    _ ≤ ηrest + ηsmall := add_le_add hrest hsmall

/-- Uniform `κ≤Q0` lower bound coming from the infinite `κ` series and the explicit tail bound. -/
theorem kappaLeQ0R_ge_kappaSeriesR_one_sub_ninety_div
    (N : ℕ) (hN0 : N ≠ 0) :
    kappaSeriesR 1 - (90 : ℝ) / Q0 ≤ kappaLeQ0R N := by
  have htail :
      ‖kappaSeriesR N - kappaLeQ0R N‖ ≤ (90 : ℝ) / Q0 :=
    norm_kappaSeriesR_sub_kappaLeQ0R_le_ninety_div N hN0
  have htail' :
      |kappaSeriesR N - kappaLeQ0R N| ≤ (90 : ℝ) / Q0 := by
    simpa [Real.norm_eq_abs] using htail
  have hleft : kappaSeriesR N - (90 : ℝ) / Q0 ≤ kappaLeQ0R N := by
    have hleft' := (abs_le.mp htail').2
    linarith
  have hmono : kappaSeriesR 1 ≤ kappaSeriesR N := kappaSeriesR_one_le N hN0
  linarith

/-- Real-part lower bound for the frozen `κ`-model from scalar and kernel lower bounds. -/
theorem frozenWeightedMainTermKappaC_re_lower_of_beta_kappa_lower
    {X N : ℕ} {β0 κ0 : ℝ}
    (hX : 1 ≤ X)
    (hβ0 : 0 ≤ β0)
    (hκ0 : 0 ≤ κ0)
    (hβ : β0 ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N))
    (hκ : κ0 ≤ kappaLeQ0R N) :
    (β0 * κ0) / (X : ℝ) ≤ Complex.re (frozenWeightedMainTermKappaC X N) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hre :=
    congrArg Complex.re
      (X_mul_frozenWeightedMainTermKappaC_eq_two_mul_frozenBetaScalarC_mul_kappa
        (X := X) (N := N) hX)
  have hre' :
      (X : ℝ) * Complex.re (frozenWeightedMainTermKappaC X N)
        = Complex.re ((2 : ℂ) * frozenBetaScalarC N) * kappaLeQ0R N := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hre
  have hβre_nonneg : 0 ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N) := le_trans hβ0 hβ
  have hprod :
      β0 * κ0 ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N) * kappaLeQ0R N := by
    exact mul_le_mul hβ hκ hκ0 hβre_nonneg
  have hscaled :
      β0 * κ0 ≤ (X : ℝ) * Complex.re (frozenWeightedMainTermKappaC X N) := by
    simpa [hre'] using hprod
  exact (div_le_iff₀' hXpos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)

/-- Final positivity wrapper for the frozen `κ`-model, parameterized by a scalar lower bound. -/
theorem R_bank_pos_of_frozenWeightedMainTermKappaC
    (cβ η εb : ℕ → ℝ) (κ0 : ℝ)
    (hκ0 : 0 ≤ κ0)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X ->
        η X + εb X < (cβ X * κ0) / (X : ℝ))
    (hβ_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X -> 0 ≤ cβ X)
    (hβ :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        cβ X ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N))
    (hκ :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H ->
        κ0 ≤ kappaLeQ0R N)
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - frozenWeightedMainTermKappaC X N‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ BankParams.X0) hX
  let c0 : ℕ → ℝ := fun X => (cβ X * κ0) / (X : ℝ)
  have hMain :
      c0 X ≤ Complex.re (frozenWeightedMainTermKappaC X N) := by
    exact frozenWeightedMainTermKappaC_re_lower_of_beta_kappa_lower
      (X := X) (N := N) hX1 (hβ_nonneg hX) hκ0 (hβ hX hN) (hκ hX hN)
  exact
    IntegralScaleClosureGate.R_bank_pos_of_weighted_main_gap_re
      (mainC := frozenWeightedMainTermKappaC)
      (c0 := c0) (η := η) (εb := εb)
      (hεb_nonneg := hεb_nonneg)
      (hsum_lt := hsum_lt)
      (hMain := by
        intro X N hX hN
        have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ BankParams.X0) hX
        exact frozenWeightedMainTermKappaC_re_lower_of_beta_kappa_lower
          (X := X) (N := N) hX1 (hβ_nonneg hX) hκ0 (hβ hX hN) (hκ hX hN))
      (hCorr := hCorr)
      (hBridge := hBridge)
      hX hN

/-- Specialization of the frozen closure wrapper using the built `κ` series lower-plus-tail bound. -/
theorem R_bank_pos_of_frozenWeightedMainTermKappaC_seriesTail
    (cβ η εb : ℕ → ℝ)
    (hκconst_nonneg : 0 ≤ kappaSeriesR 1 - (90 : ℝ) / Q0)
    (hεb_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X → 0 ≤ εb X)
    (hsum_lt :
      ∀ {X : ℕ}, BankParams.X0 ≤ X ->
        η X + εb X < (cβ X * (kappaSeriesR 1 - (90 : ℝ) / Q0)) / (X : ℝ))
    (hβ_nonneg : ∀ {X : ℕ}, BankParams.X0 ≤ X -> 0 ≤ cβ X)
    (hβ :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        cβ X ≤ Complex.re ((2 : ℂ) * frozenBetaScalarC N))
    (hCorr :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        ‖Goldbach.Cert.MajorArcModules.IntegralPipeline.corr_integral X N
            - frozenWeightedMainTermKappaC X N‖ ≤ η X)
    (hBridge :
      ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
        |Goldbach.BG_Identity.R_bank X N - Goldbach.BG_Identity.conv_ref X N|
          ≤ convScaleLower X * εb X) :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      0 < Goldbach.BG_Identity.R_bank X N := by
  intro X N hX hN
  have hN0 : N ≠ 0 := by
    have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H := (Finset.mem_filter.mp hN).1
    have hXN : X ≤ N := by
      rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
      exact Nat.le_add_right X k
    have hX0 : 0 < X := lt_of_lt_of_le (by decide : 0 < BankParams.X0) hX
    exact Nat.ne_of_gt (lt_of_lt_of_le hX0 hXN)
  exact
    R_bank_pos_of_frozenWeightedMainTermKappaC
      (cβ := cβ) (η := η) (εb := εb)
      (κ0 := kappaSeriesR 1 - (90 : ℝ) / Q0)
      hκconst_nonneg hεb_nonneg hsum_lt hβ_nonneg hβ
      (fun {X' N'} hX' hN' =>
        by
          have hN0' : N' ≠ 0 := by
            have hI : N' ∈ Goldbach.Windows.IccShift X' BankParams.H := (Finset.mem_filter.mp hN').1
            have hX'N' : X' ≤ N' := by
              rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
              exact Nat.le_add_right X' k
            have hX'0 : 0 < X' := lt_of_lt_of_le (by decide : 0 < BankParams.X0) hX'
            exact Nat.ne_of_gt (lt_of_lt_of_le hX'0 hX'N')
          exact kappaLeQ0R_ge_kappaSeriesR_one_sub_ninety_div N' hN0')
      hCorr hBridge hX hN

end

end Goldbach.BankPieces.Cert.RawScaleFrozenClosure
