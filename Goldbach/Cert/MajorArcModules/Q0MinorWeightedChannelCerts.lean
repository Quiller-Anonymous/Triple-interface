import Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge
import Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert

namespace Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelCerts

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorRawEnergyLedgerRoute
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

private lemma norm_add_sq_le_two_mul_sum_sq (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [htri, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  have hquad : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact le_trans hsq hquad

/-- Route-facing energy certificate for the mean-channel slice-sum. -/
structure MeanChannelRouteBound (A2 : ℝ) : Prop where
  A2_nonneg : 0 ≤ A2
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H,
          ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2)
        ≤ normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))

/-- Route-facing energy certificate for the explicit zero mode. -/
structure ZeroModeRouteBound (A3 : ℝ) : Prop where
  A3_nonneg : 0 ≤ A3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖weightedMinorCoeff X N 0‖ ^ 2)
        ≤ normFactorSq X * (A3 / ((H : ℝ) * (Q0MinorSplitCert.Q0 : ℝ) ^ 2))

theorem meanChannelEnergyBound_of_canonicalSSU
    {A2 : ℝ} (h : canonicalExpansion.NonzeroModeEnergyBound A2) :
    MeanChannelRouteBound A2 := by
  refine ⟨h.A2_nonneg, ?_⟩
  intro X hX
  have hEq :
      (∑ N ∈ EvenIn X H,
          ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2)
        =
      ∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [← canonicalExpansion_ssuPart_eq_meanChannelSliceSum (X := X) (N := N) hN]
  rw [hEq]
  exact h.bound (X := X) hX

theorem zeroModeEnergyBound_of_canonicalTypeI
    {A3 : ℝ} (h : canonicalExpansion.ZeroModeEnergyBound A3) :
    ZeroModeRouteBound A3 := by
  refine ⟨h.A3_nonneg, ?_⟩
  intro X hX
  have hEq :
      (∑ N ∈ EvenIn X H, ‖weightedMinorCoeff X N 0‖ ^ 2)
        =
      ∑ N ∈ EvenIn X H, ‖canonicalExpansion.typeIPart X N‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [← canonicalExpansion_typeIPart_eq_weighted_zeroMode]
  rw [hEq]
  exact h.bound (X := X) hX

theorem meanChannelEnergyBound : MeanChannelRouteBound Q0MinorSSUFromCert.A2 :=
  meanChannelEnergyBound_of_canonicalSSU
    (Q0MinorSSUFromCert.nonzeroModeEnergyBound_of_upperBound
      Q0MinorSSUFromCert.nonzeroModeEnergyBound)

theorem zeroModeEnergyBound : ZeroModeRouteBound Q0MinorTypeIFromCert.A3 :=
  zeroModeEnergyBound_of_canonicalTypeI
    (Q0MinorTypeIFromCert.zeroModeEnergyBound_of_upperBound
      Q0MinorTypeIFromCert.zeroModeEnergyBound)

theorem normalizedEnergy_of_weightedChannelBounds
    {A2 A3 : ℝ}
    (hMean : MeanChannelRouteBound A2)
    (hZero : ZeroModeRouteBound A3) :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2)
        ≤
      normFactorSq X
        * ((2 * A2) * ((H : ℝ) / (X : ℝ))
            + (2 * A3) / ((H : ℝ) * ((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)) := by
  intro X hX
  have hSplitTerm :
      ∀ N ∈ EvenIn X H,
        ‖minorResidual X N Δ_canon‖ ^ 2
          ≤
        2 * ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2
          + 2 * ‖weightedMinorCoeff X N 0‖ ^ 2 := by
    intro N hN
    rw [minorResidual_eq_zeroMode_add_meanChannel (X := X) (N := N) hX hN]
    simpa [add_comm, add_left_comm, add_assoc] using
      (norm_add_sq_le_two_mul_sum_sq
        (weightedMinorCoeff X N 0)
        (familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N))
  have hsum :
      (∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2)
        ≤
      ∑ N ∈ EvenIn X H,
        (2 * ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2
          + 2 * ‖weightedMinorCoeff X N 0‖ ^ 2) := by
    exact Finset.sum_le_sum hSplitTerm
  have hMeanX :=
    hMean.bound (X := X) hX
  have hZeroX :=
    hZero.bound (X := X) hX
  have h2Mean :
      2 *
        (∑ N ∈ EvenIn X H,
          ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2)
        ≤
      2 * (normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))) := by
    exact mul_le_mul_of_nonneg_left hMeanX (by norm_num)
  have h2Zero :
      2 * (∑ N ∈ EvenIn X H, ‖weightedMinorCoeff X N 0‖ ^ 2)
        ≤
      2 * (normFactorSq X * (A3 / ((H : ℝ) * (Q0MinorSplitCert.Q0 : ℝ) ^ 2))) := by
    exact mul_le_mul_of_nonneg_left hZeroX (by norm_num)
  have hsumSplit :
      (∑ N ∈ EvenIn X H,
        (2 * ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2
          + 2 * ‖weightedMinorCoeff X N 0‖ ^ 2))
        =
      2 *
        (∑ N ∈ EvenIn X H,
          ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2)
        + 2 * (∑ N ∈ EvenIn X H, ‖weightedMinorCoeff X N 0‖ ^ 2) := by
    rw [Finset.sum_add_distrib]
    simp [Finset.mul_sum]
  have hmain :
      (∑ N ∈ EvenIn X H,
        (2 * ‖familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N‖ ^ 2
          + 2 * ‖weightedMinorCoeff X N 0‖ ^ 2))
        ≤
      2 * (normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))))
        + 2 * (normFactorSq X * (A3 / ((H : ℝ) * (Q0MinorSplitCert.Q0 : ℝ) ^ 2))) := by
    rw [hsumSplit]
    exact add_le_add h2Mean h2Zero
  have hrew :
      2 * (normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))))
        + 2 * (normFactorSq X * (A3 / ((H : ℝ) * (Q0MinorSplitCert.Q0 : ℝ) ^ 2)))
      =
      normFactorSq X
        * ((2 * A2) * ((H : ℝ) / (X : ℝ))
            + (2 * A3) / ((H : ℝ) * ((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)) := by
    ring
  exact le_trans hsum (hrew ▸ hmain)

theorem normalizedEnergy_of_currentWeightedChannelCerts :
    ∀ {X : ℕ}, X0 ≤ X →
      (∑ N ∈ EvenIn X H, ‖minorResidual X N Δ_canon‖ ^ 2)
        ≤
      normFactorSq X
        * ((2 * Q0MinorSSUFromCert.A2) * ((H : ℝ) / (X : ℝ))
            + (2 * Q0MinorTypeIFromCert.A3) / ((H : ℝ) * ((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)) := by
  exact normalizedEnergy_of_weightedChannelBounds meanChannelEnergyBound zeroModeEnergyBound

theorem rawLedger_of_weightedChannelBounds
    {A2 A3 : ℝ}
    (hMean : MeanChannelRouteBound A2)
    (hZero : ZeroModeRouteBound A3)
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon).indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon)ᶜ.indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorRawEnergyLedger Δ_canon (2 * A2) (2 * A3) := by
  refine
    rawMinorPacketEnergy_canon_of_normalized_energy
      (C2 := 2 * A2) (C3 := 2 * A3)
      (hC2 := mul_nonneg (by norm_num) hMean.A2_nonneg)
      (hC3 := mul_nonneg (by norm_num) hZero.A3_nonneg)
      (hInner := hInner) (hOuterMaj := hOuterMaj) (hOuterMin := hOuterMin) ?_
  intro X hX
  simpa [normFactorSq] using normalizedEnergy_of_weightedChannelBounds hMean hZero hX

theorem rawLedger_of_currentWeightedChannelCerts
    (hInner :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        ∀ β : ℝ,
          IntervalIntegrable
            (fun α : ℝ => Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α)
            volume (0 : ℝ) (1 : ℝ))
    (hOuterMaj :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon).indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ))
    (hOuterMin :
      ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
                (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) *
              (∫ α in (0 : ℝ)..(1 : ℝ),
                (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ_canon)ᶜ.indicator
                  (fun α =>
                    Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand X N β α) α))
          volume (0 : ℝ) (1 : ℝ)) :
    Q0MinorRawEnergyLedger Δ_canon (2 * Q0MinorSSUFromCert.A2) (2 * Q0MinorTypeIFromCert.A3) := by
  exact rawLedger_of_weightedChannelBounds
    meanChannelEnergyBound
    zeroModeEnergyBound
    hInner
    hOuterMaj
    hOuterMin

end

end Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelCerts
