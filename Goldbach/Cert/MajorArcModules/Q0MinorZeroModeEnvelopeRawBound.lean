import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
import Goldbach.Cert.MajorArcModules.EvenWindowReindex
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
import Goldbach.Cert.MajorArcModules.Q0MinorSigmaNormalizedLogBound
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode

/-!
A direct weighted bound for the actual zero-mode envelope residual.

The proof retains every route normalization, bounds the bank payload by
`1 / (2 * H + 1)`, and uses an elementary logarithmic bound for the normalized
singular series.  The same estimate works for every scalar of absolute value at
most one.  It is therefore an absolute residual estimate, not evidence that the
frozen scalar predicts the main term accurately.
-/
namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelopeRawBound

open scoped BigOperators
open Complex
open Goldbach Goldbach.BankParams Goldbach.Windows
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

private abbrev aTerm := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm

private lemma card_evenIn_le_5001 {X : ℕ} (hX : X0 ≤ X) :
    (EvenIn X H).card ≤ 5001 := by
  have hXone : 1 ≤ X := le_trans (by decide : 1 ≤ X0) hX
  simpa [H] using (EvenWindowReindex.evenIn_card_le (H := H) hXone)

private lemma complement_weight_sq_le_53_50_sq {X : ℕ} (hX : X0 ≤ X) :
    ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
      ≤ ((53 : ℝ) / 50) ^ 2 := by
  have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos_nat
  have hmaj :
      ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖
        ≤ (60000 : ℝ) / (X : ℝ) := by
    have h0 :
        ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖
          ≤ (2 * (1 : ℝ) * (Goldbach.AO_OffDiag.TailBlock.Q0 : ℝ)) / (X : ℝ) :=
      norm_majorArcWeightFourier_zero_le
        (X := X) (Δ := (1 : ℝ)) (by norm_num) hXpos_nat
    norm_num [Goldbach.AO_OffDiag.TailBlock.Q0] at h0 ⊢
    exact h0
  have hsmall : (60000 : ℝ) / (X : ℝ) ≤ (3 : ℝ) / 50 := by
    have hXr : (1000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    rw [div_le_iff₀ hXpos]
    have hbase : (60000 : ℝ) * 50 ≤ 3 * (X : ℝ) := by
      nlinarith
    nlinarith
  have htri :
      ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖
        ≤ 1 + ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ := by
    simpa using norm_sub_le (1 : ℂ) (Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0)
  have hbound :
      ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ≤ (53 : ℝ) / 50 := by
    have htmp : ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ≤ 1 + (3 : ℝ) / 50 := by
      exact le_trans htri (add_le_add_left (le_trans hmaj hsmall) 1)
    have h53 : 1 + (3 : ℝ) / 50 = (53 : ℝ) / 50 := by norm_num
    simpa [h53] using htmp
  have hnonneg :
      0 ≤ ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ := norm_nonneg _
  nlinarith


private lemma norm_minor_zero_le {X : ℕ} (hX : X0 ≤ X) :
    ‖minorArcWeightFourier X Δ_canon 0‖ ≤ (53 : ℝ) / 50 := by
  have h := complement_weight_sq_le_53_50_sq hX
  rw [minorArcWeightFourier_zero]
  nlinarith [norm_nonneg
    (1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0)]

private lemma norm_aTerm_le_cap {X n : ℕ} (hX : X0 ≤ X)
    (hn : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H)) :
    ‖aTerm X n‖ ≤ (1 : ℝ) / 20001 := by
  have hlogX : (13 : ℝ) ≤ Real.log (X : ℝ) :=
    Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX
  have hlogXpos : 0 < Real.log (X : ℝ) := by linarith
  have hHX : H ≤ X / 2 := by
    norm_num [H, X0] at hX ⊢
    omega
  have hnX : n ≤ X := by
    have := (Finset.mem_Icc.mp hn).2
    omega
  by_cases hp : Nat.Prime n
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    have hn_one : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_trans (by decide : 1 ≤ 2) hp.two_le)
    have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_one
    have hlogle : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hnpos (by exact_mod_cast hnX)
    have hscale :
        Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) = (1 : ℝ) / 20001 := by
      unfold Goldbach.BG_Bank.wScale
      norm_num [Goldbach.BG_Bank.H, H]
      field_simp [hlogXpos.ne']
    calc
      ‖aTerm X n‖ = Goldbach.BG_Bank.wScale X * Real.log (n : ℝ) := by
        change ‖((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n : ℝ) : ℂ)‖ = _
        rw [Complex.norm_real, Real.norm_eq_abs]
        simp only [Goldbach.BG_Bank.wX, if_pos hn, Goldbach.BG_Bank.Λ, if_pos hp]
        exact abs_of_nonneg (mul_nonneg (Goldbach.BG_Bank.wScale_nonneg X) hlogn)
      _ ≤ Goldbach.BG_Bank.wScale X * Real.log (X : ℝ) :=
        mul_le_mul_of_nonneg_left hlogle (Goldbach.BG_Bank.wScale_nonneg X)
      _ = (1 : ℝ) / 20001 := hscale
  · simp [aTerm, Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm,
      Goldbach.BG_Bank.Λ, hp]

private lemma geometric_term_norm_eq_re (X : ℕ) (nm : ℕ × ℕ) :
    ‖uniformWindowSupportIndicator X nm.1
        * uniformWindowSupportIndicator X nm.2 * KHatH (kFn nm)‖
      =
    (uniformWindowSupportIndicator X nm.1
        * uniformWindowSupportIndicator X nm.2 * KHatH (kFn nm)).re := by
  unfold uniformWindowSupportIndicator KHatH
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.coeffC
  simp only [Goldbach.Cert.MajorArcStep9CorrelationIntegral.coeff_eq]
  split_ifs <;> simp_all [abs_of_nonneg (Goldbach.BG_Identity.K_full_nonneg _)]

/-- The bounded bank payload preserves the geometric kernel mass. -/
theorem rawExactZeroModeMass_norm_le_geometric_cap
    {X N : ℕ} (hX : X0 ≤ X) :
    ‖rawExactZeroModeMass X N‖
      ≤ ((1 : ℝ) / 20001) ^ 2 * ‖unscaledGeometricZeroSliceMass X N‖ := by
  have hterm : ∀ nm : ℕ × ℕ,
      ‖aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm)‖
        ≤ ((1 : ℝ) / 20001) ^ 2 *
          ‖uniformWindowSupportIndicator X nm.1
            * uniformWindowSupportIndicator X nm.2 * KHatH (kFn nm)‖ := by
    intro nm
    by_cases h1 : nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
    · by_cases h2 : nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
      · have ha := norm_aTerm_le_cap hX h1
        have hb := norm_aTerm_le_cap hX h2
        have hab : ‖aTerm X nm.1‖ * ‖aTerm X nm.2‖ ≤ ((1 : ℝ) / 20001) ^ 2 := by
          simpa only [pow_two] using mul_le_mul ha hb (norm_nonneg _)
            (by norm_num : (0 : ℝ) ≤ 1 / 20001)
        simpa [uniformWindowSupportIndicator, h1, h2, norm_mul, mul_assoc]
          using mul_le_mul_of_nonneg_right hab (norm_nonneg (KHatH (kFn nm)))
      · simp [aTerm, Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm,
          Goldbach.BG_Bank.wX, h2, uniformWindowSupportIndicator]
    · simp [aTerm, Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm,
        Goldbach.BG_Bank.wX, h1, uniformWindowSupportIndicator]
  have hsum :
      (∑ nm ∈ nmSupportOfT N 0,
        ‖uniformWindowSupportIndicator X nm.1
          * uniformWindowSupportIndicator X nm.2 * KHatH (kFn nm)‖)
        = (unscaledGeometricZeroSliceMass X N).re := by
    simp only [unscaledGeometricZeroSliceMass, Complex.re_sum]
    exact Finset.sum_congr rfl (fun nm _ => geometric_term_norm_eq_re X nm)
  calc
    ‖rawExactZeroModeMass X N‖
        ≤ ∑ nm ∈ nmSupportOfT N 0,
            ‖aTerm X nm.1 * aTerm X nm.2 * KHatH (kFn nm)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ nm ∈ nmSupportOfT N 0, ((1 : ℝ) / 20001) ^ 2 *
        ‖uniformWindowSupportIndicator X nm.1
          * uniformWindowSupportIndicator X nm.2 * KHatH (kFn nm)‖ :=
      Finset.sum_le_sum (fun nm _ => hterm nm)
    _ = ((1 : ℝ) / 20001) ^ 2 * (unscaledGeometricZeroSliceMass X N).re := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ ((1 : ℝ) / 20001) ^ 2 * ‖unscaledGeometricZeroSliceMass X N‖ :=
      mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) (sq_nonneg _)

theorem rawExactZeroModeMass_norm_le_cap
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖rawExactZeroModeMass X N‖ ≤ (2 : ℝ) / 20001 ^ 2 := by
  have hG := unscaledGeometricZeroSliceMassWindowNormTarget_explicit.upper hX hN
  have hP := rawExactZeroModeMass_norm_le_geometric_cap (N := N) hX
  calc
    ‖rawExactZeroModeMass X N‖
      ≤ ((1 : ℝ) / 20001) ^ 2 * ‖unscaledGeometricZeroSliceMass X N‖ := hP
    _ ≤ ((1 : ℝ) / 20001) ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hG (sq_nonneg _)
    _ = (2 : ℝ) / 20001 ^ 2 := by norm_num

/-- Pointwise raw bound, with the geometric normalization retained. -/
theorem zeroModeScalar_norm_sq_le_cap
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖zeroModeScalar X N‖ ^ 2 ≤
      (((14 : ℝ) / 13) ^ 4 * ((53 : ℝ) / 50) ^ 2
        * ((2 : ℝ) / 20001 ^ 2) ^ 2) * routeVisibleWindowNormFloorSq X := by
  have hq := q0NormFactor_sq_le_routeVisibleWindowNormFloorSq hX hN
  have hw := complement_weight_sq_le_53_50_sq hX
  have hP := rawExactZeroModeMass_norm_le_cap hX hN
  have hP2 : ‖rawExactZeroModeMass X N‖ ^ 2 ≤ ((2 : ℝ) / 20001 ^ 2) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hP hP (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 2 / 20001 ^ 2)
  rw [← minorArcWeightFourier_zero X Δ_canon] at hw
  have hwP := mul_le_mul hw hP2
    (sq_nonneg ‖rawExactZeroModeMass X N‖) (by positivity)
  have hprod := mul_le_mul hq hwP
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (by positivity) (routeVisibleWindowNormFloorSq_nonneg X))
  simpa [zeroModeScalar_eq_q0_weight0_mul_rawExactZeroModeMass,
    norm_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hprod


private lemma sigma_norm_le_two_log {N : ℕ} (hN : X0 ≤ N) :
    ‖sigmaNormalizedSeries N‖ ≤ 2 * Real.log (N : ℝ) := by
  unfold sigmaNormalizedSeries
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Q0MinorSigmaNormalizedLogBound.abs_normalized_sigma_le_two_mul_log
    Goldbach.Analytic.C2_numeric hN

private lemma q0_sq_mul_sigma_norm_le {N : ℕ} (hN : X0 ≤ N) :
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 * ‖sigmaNormalizedSeries N‖
      ≤ (1 : ℝ) / 800 := by
  have hlog13 := Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hN
  have hlog1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by linarith
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hl3 : (1 : ℝ) ≤ Real.log (N : ℝ) ^ 3 := one_le_pow₀ hlog1
  have hl4 : Real.log (N : ℝ) ≤ Real.log (N : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hl3 hlogpos.le]
  have hpoly : 2 * Real.log (N : ℝ) ≤ 800 * Real.log (N : ℝ) ^ 4 := by
    nlinarith
  calc
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 * ‖sigmaNormalizedSeries N‖
      ≤ ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 *
          (2 * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (sigma_norm_le_two_log hN) (sq_nonneg _)
    _ = (2 * Real.log (N : ℝ)) / (640000 * Real.log (N : ℝ) ^ 4) := by
      rw [norm_q0NormFactor]
      field_simp [hlogpos.ne']
      ring
    _ ≤ (1 : ℝ) / 800 := by
      rw [div_le_iff₀ (show 0 < (640000 : ℝ) * Real.log (N : ℝ) ^ 4 by positivity)]
      nlinarith

private lemma geometricNormalization_norm_le {X : ℕ} (hX : X0 ≤ X) :
    ‖geometricZeroSliceNormalization X‖ ≤ (1 : ℝ) / 20001 ^ 2 := by
  have hlog13 := Goldbach.Cert.MajorArcNumericFacts.thirteen_le_log_of_X0_le hX
  have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by linarith
  have hlogpos : 0 < Real.log (X : ℝ) := by linarith
  have hden : (20001 : ℝ) ≤ Real.log (X : ℝ) * 20001 := by nlinarith
  have hdiv : (1 : ℝ) / (Real.log (X : ℝ) * 20001) ≤ (1 : ℝ) / 20001 :=
    one_div_le_one_div_of_le (by norm_num) hden
  have hdiv0 : 0 ≤ (1 : ℝ) / (Real.log (X : ℝ) * 20001) := by positivity
  have heq :
      ‖geometricZeroSliceNormalization X‖
        = ((1 : ℝ) / (Real.log (X : ℝ) * 20001)) ^ 2 := by
    unfold geometricZeroSliceNormalization uniformWindowNormalization
    rw [norm_pow, norm_inv, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num only [H, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    norm_num
    rw [abs_of_nonneg hlogpos.le]
  rw [heq]
  have hmul := mul_le_mul hdiv hdiv hdiv0 (by norm_num : (0 : ℝ) ≤ 1 / 20001)
  norm_num [pow_two] at hmul ⊢
  exact hmul

/-- A deliberately loose bound suffices for the frozen singular-series baseline. -/
theorem zeroModeSigmaBaseline_norm_le
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖zeroModeSigmaBaseline X N‖ ≤ (4 : ℝ) / (800 * 20001 ^ 2) := by
  have hXN : X ≤ N := X_le_of_mem_EvenIn hN
  have hqσ := q0_sq_mul_sigma_norm_le (le_trans hX hXN)
  have hw : ‖minorArcWeightFourier X Δ_canon 0‖ ≤ 2 := by
    have := norm_minor_zero_le hX
    linarith
  have hg := geometricNormalization_norm_le hX
  have hG := unscaledGeometricZeroSliceMassWindowNormTarget_explicit.upper hX hN
  have hprod1 := mul_le_mul hqσ hw (norm_nonneg _) (by positivity)
  have hprod2 := mul_le_mul hprod1 hg (norm_nonneg _) (by positivity)
  have hprod3 := mul_le_mul hprod2 hG (norm_nonneg _) (by positivity)
  calc
    ‖zeroModeSigmaBaseline X N‖ =
      ((‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 * ‖sigmaNormalizedSeries N‖)
        * ‖minorArcWeightFourier X Δ_canon 0‖)
        * ‖geometricZeroSliceNormalization X‖ * ‖unscaledGeometricZeroSliceMass X N‖ := by
      rw [zeroModeSigmaBaseline, zeroModeGeometricBaseline,
        geometricWeightedMinorCoeff_zero_eq_q0_weight0_mul_rawGeometricZeroSliceMass,
        rawGeometricZeroSliceMass_eq_geometricZeroSliceNormalization_mul_unscaled]
      simp only [norm_mul]
      ring
    _ ≤ (((1 : ℝ) / 800) * 2) * ((1 : ℝ) / 20001 ^ 2) * 2 := hprod3
    _ = (4 : ℝ) / (800 * 20001 ^ 2) := by norm_num

private lemma candidate_abs_le_one : |zeroModeBookkeepingScalarCandidate| ≤ (1 : ℝ) := by
  norm_num [zeroModeBookkeepingScalarCandidate, sigmaEnvelopeKappa]

/-- A direct residual target; the large quotient observable is never estimated. -/
theorem zeroModeEnvelopeShapeTarget_four {κ : ℝ} (hκ : |κ| ≤ 1) :
    ZeroModeEnvelopeShapeTarget κ 0 4 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro X hX
  let A : ℝ := ((14 : ℝ) / 13) ^ 4 * ((53 : ℝ) / 50) ^ 2
    * ((2 : ℝ) / 20001 ^ 2) ^ 2
  let B : ℝ := (4 : ℝ) / (800 * 20001 ^ 2)
  have hc : 0 ≤ routeVisibleWindowNormFloorSq X :=
    routeVisibleWindowNormFloorSq_nonneg X
  have hpoint : ∀ N ∈ EvenIn X H,
      ‖zeroModeEnvelopeError κ X N‖ ^ 2
        ≤ (2 * A + 2 * B ^ 2) * routeVisibleWindowNormFloorSq X := by
    intro N hN
    have hz := zeroModeScalar_norm_sq_le_cap hX hN
    have hb := zeroModeSigmaBaseline_norm_le hX hN
    have hb2 : ‖zeroModeSigmaBaseline X N‖ ^ 2 ≤ B ^ 2 := by
      simpa only [pow_two, B] using mul_le_mul hb hb (norm_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 4 / (800 * 20001 ^ 2))
    have hk2 : |κ| ^ 2 ≤ (1 : ℝ) := by
      simpa only [pow_two, one_mul] using mul_le_mul
        hκ hκ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hmodel :
        ‖zeroModeSigmaBaseline X N *
          (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)‖ ^ 2
          ≤ B ^ 2 * routeVisibleWindowNormFloorSq X := by
      have hbk := mul_le_mul hb2 hk2 (sq_nonneg _) (sq_nonneg B)
      have hbk' := mul_le_mul_of_nonneg_right hbk hc
      simpa [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        sq_abs, routeVisibleWindowNormFloor_sq, mul_assoc] using hbk'
    have ht := norm_sq_add_le_two_mul_sum_norm_sq (zeroModeScalar X N)
      (-(zeroModeSigmaBaseline X N *
        (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)))
    simp only [norm_neg] at ht
    change ‖zeroModeScalar X N -
      zeroModeSigmaBaseline X N *
        (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)‖ ^ 2 ≤ _
    rw [sub_eq_add_neg]
    calc
      _ ≤ 2 * (‖zeroModeScalar X N‖ ^ 2 +
          ‖zeroModeSigmaBaseline X N * (((κ * routeVisibleWindowNormFloor X : ℝ)) : ℂ)‖ ^ 2) := ht
      _ ≤ 2 * (A * routeVisibleWindowNormFloorSq X + B ^ 2 * routeVisibleWindowNormFloorSq X) :=
        mul_le_mul_of_nonneg_left (add_le_add hz hmodel) (by norm_num)
      _ = _ := by ring
  have hsum :
      zeroModeEnvelopeErrorWindowEnergy κ X
        ≤ ((EvenIn X H).card : ℝ) * (2 * A + 2 * B ^ 2)
            * routeVisibleWindowNormFloorSq X := by
    calc
      zeroModeEnvelopeErrorWindowEnergy κ X
        ≤ ∑ _N ∈ EvenIn X H, (2 * A + 2 * B ^ 2) * routeVisibleWindowNormFloorSq X :=
          Finset.sum_le_sum (fun N hN => hpoint N hN)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : ((EvenIn X H).card : ℝ) ≤ 5001 := by
    exact_mod_cast card_evenIn_le_5001 hX
  have hbudget :
      ((EvenIn X H).card : ℝ) * (2 * A + 2 * B ^ 2)
        ≤ (4 : ℝ) / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
    calc
      ((EvenIn X H).card : ℝ) * (2 * A + 2 * B ^ 2)
        ≤ 5001 * (2 * A + 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_right hcard (by dsimp [A]; positivity)
      _ ≤ _ := by norm_num [A, B, H, Goldbach.AO_OffDiag.TailBlock.Q0]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    le_trans hsum (mul_le_mul_of_nonneg_right hbudget hc)


/-- The frozen scalar is one instance of the direct bound. -/
theorem zeroModeEnvelopeShapeTarget_candidate_four :
    ZeroModeEnvelopeShapeTarget zeroModeBookkeepingScalarCandidate 0 4 :=
  zeroModeEnvelopeShapeTarget_four candidate_abs_le_one

/-- The zero-scalar instance gives a direct Type-I upper bound. -/
theorem zeroModeEnergyBound_four :
    canonicalExpansion.ZeroModeEnergyBound (4 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  intro X hX
  have hraw := (zeroModeEnvelopeShapeTarget_four (κ := 0) (by norm_num)).bound hX
  simpa [zeroModeEnvelopeErrorWindowEnergy, zeroModeEnvelopeError, zeroModeScalar,
    Q0MinorRouteVisibleAnalysis.routeVisibleZeroCoeff,
    Q0MinorZeroModeAnalysis.routeZeroMode_eq_weightedMinorCoeff_zero,
    routeVisibleWindowNormFloorSq, Q0MinorSplitCert.normFactorSq,
    Q0MinorFrequencySplit.Q0] using hraw

end
end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelopeRawBound
