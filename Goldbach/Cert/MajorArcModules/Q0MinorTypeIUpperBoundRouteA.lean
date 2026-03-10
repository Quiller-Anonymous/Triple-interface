import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundPrep
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundSpec

/-!
Route-A coarse upper bound for the ε₁ Type-I / zero-mode piece.

This closes the zero-mode side with a deliberately coarse argument:

* `diagMass ≤ coeffMass^2`;
* the bank coefficient mass on the top window is supported on odd entries only;
* the hard-minor constant mode is bounded by `1 + 60000/X ≤ 53/50`;
* the normalization factor varies across the window by at most `(14/13)^4`.

The resulting uniform constant still fits the advertised `A3 = 72,000,000`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundRouteA

open scoped BigOperators Interval

open Complex

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarConstMode
open Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundPrep
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundSpec
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

set_option maxRecDepth 4096

private lemma card_even_range_H :
    ((Finset.range (H + 1)).filter (fun k : ℕ => Even k)).card ≤ 5001 := by
  native_decide

private lemma card_odd_range_H :
    ((Finset.range (H + 1)).filter (fun k : ℕ => Odd k)).card ≤ 5001 := by
  native_decide

private lemma card_evenIn_le_5001 (X : ℕ) :
    (EvenIn X H).card ≤ 5001 := by
  classical
  unfold EvenIn IccShift
  by_cases hXeven : Even X
  · have hEq :
        ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
            (fun n : ℕ => Goldbach.Windows.IsEven n)
          =
        (((Finset.range (H + 1)).filter (fun k : ℕ => Even k)).image (fun k : ℕ => X + k)) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_filter.mp hn with ⟨himg, hne⟩
        rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
        have hEvenXk : Even (X + k) := even_of_isEven (by simpa [Goldbach.Windows.IsEven] using hne)
        simpa [Nat.even_add, hXeven] using hEvenXk
      · intro hn
        rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
        refine Finset.mem_filter.mpr ?_
        constructor
        · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
        · exact Goldbach.Windows.isEven_of_even (by
            have hEvenK : Even k := (Finset.mem_filter.mp hk).2
            simpa [Nat.even_add, hXeven] using hEvenK)
    rw [hEq, Finset.card_image_of_injective]
    · exact card_even_range_H
    · intro a b hab
      exact Nat.add_left_cancel hab
  · have hEq :
        ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
            (fun n : ℕ => Goldbach.Windows.IsEven n)
          =
        (((Finset.range (H + 1)).filter (fun k : ℕ => Odd k)).image (fun k : ℕ => X + k)) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_filter.mp hn with ⟨himg, hne⟩
        rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
        have hEven : Even (X + k) := even_of_isEven (by simpa [Goldbach.Windows.IsEven] using hne)
        have hOddX : Odd X := Nat.not_even_iff_odd.mp hXeven
        simpa [Nat.even_add', hOddX] using hEven
      · intro hn
        rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
        refine Finset.mem_filter.mpr ?_
        constructor
        · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
        have hOddX : Odd X := Nat.not_even_iff_odd.mp hXeven
        have hOddK : Odd k := (Finset.mem_filter.mp hk).2
        exact Goldbach.Windows.isEven_of_even (by
          simpa [Nat.even_add', hOddX] using hOddK)
    rw [hEq, Finset.card_image_of_injective]
    · exact card_odd_range_H
    · intro a b hab
      exact Nat.add_left_cancel hab

private lemma q0NormFactor_sq_le_windowRatio
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
      ≤ ((14 : ℝ) / 13) ^ 4 * normFactorSq X := by
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
  rw [hrew]
  exact mul_le_mul_of_nonneg_right hratio4 (normFactorSq_nonneg X)

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

private lemma coeffMass_sq_le_10001_div_20001_sq_sq {X N : ℕ}
    (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (Q0MajorTailTTStarToeplitzScaffold.coeffMass X N) ^ 2
      ≤ ((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2 := by
  have hmono :
      Q0MajorTailTTStarToeplitzScaffold.coeffMass X N
        ≤ Q0MajorTailTTStarToeplitzScaffold.coeffMass X (X + H) := by
    exact Q0MajorTailTTStarToeplitzScaffold.coeffMass_mono_N
      (le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN)
  have htop :
      Q0MajorTailTTStarToeplitzScaffold.coeffMass X (X + H)
        ≤ (10001 : ℝ) / (20001 : ℝ) ^ 2 :=
    coeffMass_le_10001_div_20001_sq hX
  have hcoeff_nonneg : 0 ≤ Q0MajorTailTTStarToeplitzScaffold.coeffMass X N := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcap_nonneg : 0 ≤ (10001 : ℝ) / (20001 : ℝ) ^ 2 := by positivity
  nlinarith [hmono, htop, hcoeff_nonneg, hcap_nonneg]

private lemma pointwiseUpper_le_routeA {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    pointwiseUpper X N
      ≤
    (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2)))
      * normFactorSq X := by
  have hq0 := q0NormFactor_sq_le_windowRatio hX hN
  have hweight := complement_weight_sq_le_53_50_sq hX
  have hdiag := diagMass_le_coeffMass_sq X N
  have hcoeff := coeffMass_sq_le_10001_div_20001_sq_sq hX hN
  have hmain :
      ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
          * Q0MajorTailTTStarToeplitzScaffold.diagMass X N
        ≤
      ((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2) := by
    have hstep :
        ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
            * Q0MajorTailTTStarToeplitzScaffold.diagMass X N
          ≤
        ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
            * (Q0MajorTailTTStarToeplitzScaffold.coeffMass X N) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hdiag (sq_nonneg _)
    have hstep' :
        ‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
            * (Q0MajorTailTTStarToeplitzScaffold.coeffMass X N) ^ 2
          ≤
        ((53 : ℝ) / 50) ^ 2 * (Q0MajorTailTTStarToeplitzScaffold.coeffMass X N) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    have hstep'' :
        ((53 : ℝ) / 50) ^ 2 * (Q0MajorTailTTStarToeplitzScaffold.coeffMass X N) ^ 2
          ≤
        ((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcoeff (sq_nonneg _)
    exact le_trans hstep (le_trans hstep' hstep'')
  calc
    pointwiseUpper X N
        =
      ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
        *
          (‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon 0‖ ^ 2
            * Q0MajorTailTTStarToeplitzScaffold.diagMass X N) := by
              rfl
    _ ≤ ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
          * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ ≤ (((14 : ℝ) / 13) ^ 4 * normFactorSq X)
          * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2)) := by
            exact mul_le_mul_of_nonneg_right hq0 (by positivity)
    _ = (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2)))
          * normFactorSq X := by ring

theorem windowUpper_le_target (X : ℕ) (hX : X0 ≤ X) :
    windowUpper X
      ≤
    normFactorSq X * ((72000000 : ℝ) / ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2))) := by
  have hsum :
      windowUpper X
        ≤
      (((EvenIn X H).card : ℝ)
        * (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2))))
        * normFactorSq X := by
    unfold windowUpper
    calc
      ∑ N ∈ EvenIn X H, pointwiseUpper X N
          ≤
        ∑ _N ∈ EvenIn X H,
          ((((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2)))
            * normFactorSq X) := by
              refine Finset.sum_le_sum ?_
              intro N hN
              exact pointwiseUpper_le_routeA hX hN
      _ = (((EvenIn X H).card : ℝ)
            * (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2))))
            * normFactorSq X := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
  have hcard : (((EvenIn X H).card : ℝ)) ≤ 5001 := by
    exact_mod_cast card_evenIn_le_5001 X
  have hnum :
      (((EvenIn X H).card : ℝ)
        * (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2))))
        ≤
      (72000000 : ℝ) / ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)) := by
    have hcoeff :
        (((EvenIn X H).card : ℝ)
          * (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2))))
          ≤
        (5001 : ℝ)
          * (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2))) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    refine le_trans hcoeff ?_
    norm_num [H, Q0MinorSplitCert.Q0]
  have hfactor : 0 ≤ normFactorSq X := normFactorSq_nonneg X
  calc
    windowUpper X
        ≤
      ((((EvenIn X H).card : ℝ)
        * (((14 : ℝ) / 13) ^ 4 * (((53 : ℝ) / 50) ^ 2 * (((10001 : ℝ) / (20001 : ℝ) ^ 2) ^ 2))))
        * normFactorSq X) := hsum
    _ ≤
      ((72000000 : ℝ) / ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2))) * normFactorSq X := by
        exact mul_le_mul_of_nonneg_right hnum hfactor
    _ = normFactorSq X * ((72000000 : ℝ) / ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2))) := by
        ring

theorem zeroModeEnergyBound_72000000 :
    canonicalExpansion.ZeroModeEnergyBound (72000000 : ℝ) := by
  refine zeroModeEnergyBound_of_windowUpper (U := (72000000 : ℝ)) (by norm_num) ?_
  intro X hX
  exact windowUpper_le_target X hX

end

end Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundRouteA
