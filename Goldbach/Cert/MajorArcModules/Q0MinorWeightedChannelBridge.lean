import Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
import Goldbach.Cert.MajorArcModules.Q0MinorSingularityRouteBridge
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert

namespace Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityRouteBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition

noncomputable section

set_option maxRecDepth 4096

theorem canonicalExpansion_typeIPart_eq_weighted_zeroMode
    (X N : ℕ) :
    canonicalExpansion.typeIPart X N = weightedMinorCoeff X N 0 := by
  simp [FrequencyExpansion.typeIPart, canonicalExpansion, weightedMinorCoeff]

theorem canonicalExpansion_typeIPart_eq_zeroModeSlice
    (X N : ℕ) :
    canonicalExpansion.typeIPart X N = zeroModeSlice X N 0 := by
  simp [FrequencyExpansion.typeIPart, canonicalExpansion, weightedMinorCoeff, zeroModeSlice]

theorem canonicalExpansion_ssuPart_eq_weightedNonzeroSliceSum
    {X N : ℕ} (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    canonicalExpansion.ssuPart X N
      =
    familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => weightedNonzeroSlice X N t) N := by
  unfold FrequencyExpansion.ssuPart familySliceSumOn weightedNonzeroSlice
  simp [canonicalExpansion]
  change ∑ t ∈ (tSupport N).erase 0, weightedMinorCoeff X N t =
    ∑ t ∈ canonicalMinorAmbientSupport X, coeffZeroRemoved X N t
  rw [← exactNonzeroWeightedSlice_eq_sum_tSupport_erase (X := X) (N := N) hN]
  unfold exactNonzeroWeightedSlice weightedMinorCoeffFamilyShadowSlice canonicalAmbientSliceSum
    familySliceSumOn weightedMinorCoeffFamily
  refine Finset.sum_congr rfl ?_
  intro t ht
  have hmem : t ∈ (windowMinorCoeffSupport X).erase 0 := by
    simpa [canonicalMinorAmbientSupport] using ht
  unfold coeffZeroRemoved finiteModeProjector
  simp [hmem]

theorem canonicalExpansion_ssuPart_eq_meanChannelSliceSum
    {X N : ℕ} (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    canonicalExpansion.ssuPart X N
      =
    familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N := by
  rw [canonicalExpansion_ssuPart_eq_weightedNonzeroSliceSum hN]
  exact weightedNonzeroSlice_sliceSum_eq_meanChannelSlice_sliceSum X N

theorem minorResidual_eq_zeroMode_add_meanChannel
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    Q0MinorNormalizedEnergy.minorResidual X N TurnkeyRouteQ0.Δ_canon
      =
    weightedMinorCoeff X N 0
      + familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N := by
  calc
    Q0MinorNormalizedEnergy.minorResidual X N TurnkeyRouteQ0.Δ_canon
        = canonicalExpansion.ssuPart X N + canonicalExpansion.typeIPart X N := by
            exact canonicalExpansion.expand_eq_ssuPart_add_typeIPart hX (by simpa using hN)
    _ =
      familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N
        + weightedMinorCoeff X N 0 := by
          rw [canonicalExpansion_ssuPart_eq_meanChannelSliceSum hN,
            canonicalExpansion_typeIPart_eq_weighted_zeroMode]
    _ =
      weightedMinorCoeff X N 0
        + familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N := by
          ring

theorem minorResidual_eq_zeroMode_add_meanChannel_add_zero
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    Q0MinorNormalizedEnergy.minorResidual X N TurnkeyRouteQ0.Δ_canon
      =
    weightedMinorCoeff X N 0
      + familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N
      + familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => coeffArith X N t) N := by
  rw [minorResidual_eq_zeroMode_add_meanChannel hX hN, coeffArith_sliceSum_eq_zero]
  ring
end

end Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge
