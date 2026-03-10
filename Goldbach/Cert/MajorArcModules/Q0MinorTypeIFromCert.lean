import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
import Goldbach.Cert.MajorArcModules.Q0MinorTypeICertData
import Goldbach.Cert.MajorArcModules.Q0MinorTypeIUpperBoundRouteA

/-!
Glue from the generated ε₁ Type-I certificate payload to the split-certificate interface.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorTypeICert
open Goldbach.Cert.MajorArcModules.Q0MinorTypeICertData

noncomputable section

noncomputable abbrev A3 : ℝ := (data.A3 : ℝ)
noncomputable abbrev U : ℝ := (data.U : ℝ)

private lemma A3_nonneg : 0 ≤ A3 := by
  exact_mod_cast Data.a3_nonneg (d := data) data_valid

private lemma U_le_A3 : U ≤ A3 := by
  simpa [U, A3] using Data.ule_a3_cast_real (d := data) data_valid

theorem zeroModeEnergyBound_of_upperBound
    (hU : canonicalExpansion.ZeroModeEnergyBound U) :
    canonicalExpansion.ZeroModeEnergyBound A3 := by
  refine ⟨A3_nonneg, ?_⟩
  intro X hX
  have hbase := hU.bound (X := X) hX
  have hden_nonneg : 0 ≤ ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)) := by positivity
  have hfrac_nonneg :
      0 ≤ 1 / ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)) := by
    simpa using one_div_nonneg.mpr hden_nonneg
  have hInv_nonneg :
      0 ≤ (((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2))⁻¹) := by
    simpa [one_div] using hfrac_nonneg
  have hscale :
      normFactorSq X * (U / ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2)))
        ≤
      normFactorSq X * (A3 / ((H : ℝ) * (((Q0MinorSplitCert.Q0 : ℕ) : ℝ) ^ 2))) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right U_le_A3 hInv_nonneg)
        (normFactorSq_nonneg X)
  exact le_trans hbase hscale

theorem typeICert_of_upperBound
    (hU : canonicalExpansion.ZeroModeEnergyBound U) :
    TypeICert canonicalExpansion.residualSplit A3 :=
  FrequencyExpansion.typeICert_of_zeroModeEnergyBound
    (E := canonicalExpansion) (A3 := A3)
    (zeroModeEnergyBound_of_upperBound hU)

theorem zeroModeEnergyBound : canonicalExpansion.ZeroModeEnergyBound U := by
  simpa [U, A3] using
    Q0MinorTypeIUpperBoundRouteA.zeroModeEnergyBound_72000000

theorem typeICert : TypeICert canonicalExpansion.residualSplit A3 :=
  typeICert_of_upperBound zeroModeEnergyBound

end

end Goldbach.Cert.MajorArcModules.Q0MinorTypeIFromCert
