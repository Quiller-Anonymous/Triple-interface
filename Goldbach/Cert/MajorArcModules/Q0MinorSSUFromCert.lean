import Goldbach.Cert.MajorArcModules.Q0MinorSSUCertData
import Goldbach.Cert.MajorArcModules.Q0MinorSSUUpperBoundCoarse
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion

/-!
Glue from the generated ε₁ SSU certificate payload to the split-certificate interface.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorSSUCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUCertData
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion

noncomputable section

noncomputable abbrev A2 : ℝ := (data.A2 : ℝ)
noncomputable abbrev U : ℝ := (data.U : ℝ)

private lemma A2_nonneg : 0 ≤ A2 := by
  exact_mod_cast Data.a2_nonneg (d := data) data_valid

private lemma U_le_A2 : U ≤ A2 := by
  simpa [U, A2] using Data.ule_a2_cast_real (d := data) data_valid

theorem nonzeroModeEnergyBound_of_upperBound
    (hU : canonicalExpansion.NonzeroModeEnergyBound U) :
    canonicalExpansion.NonzeroModeEnergyBound A2 := by
  refine ⟨A2_nonneg, ?_⟩
  intro X hX
  have hbase := hU.bound (X := X) hX
  have hHX_nonneg : 0 ≤ ((H : ℝ) / (X : ℝ)) := by
    positivity
  have hscale :
      normFactorSq X * (U * ((H : ℝ) / (X : ℝ)))
        ≤
      normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right U_le_A2 hHX_nonneg)
      (normFactorSq_nonneg X)
  exact le_trans hbase hscale

theorem ssuCert_of_upperBound
    (hU : canonicalExpansion.NonzeroModeEnergyBound U) :
    SSUCert canonicalExpansion.residualSplit A2 :=
  FrequencyExpansion.ssuCert_of_nonzeroModeEnergyBound
    (E := canonicalExpansion) (A2 := A2)
    (nonzeroModeEnergyBound_of_upperBound hU)

theorem nonzeroModeEnergyBound : canonicalExpansion.NonzeroModeEnergyBound U := by
  simpa [U, A2] using
    Q0MinorSSUUpperBoundCoarse.nonzeroModeEnergyBound_80

theorem ssuCert : SSUCert canonicalExpansion.residualSplit A2 :=
  ssuCert_of_upperBound nonzeroModeEnergyBound

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
