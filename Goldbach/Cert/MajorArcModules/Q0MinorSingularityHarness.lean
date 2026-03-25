import Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularityHarness

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge

noncomputable section

/-- Thin report bundle for top-`K` feasibility checks on a family object. -/
structure TopKHarnessReport where
  fullFamilyEnergy : ℝ
  capturedFamilyEnergy : ℝ
  residualFamilyEnergy : ℝ
  shadowResidualEnergy : ℝ

/-- The exact raw weighted family, viewed as a family on the canonical ambient support. -/
noncomputable def weightedMinorCoeffFamilyOnAmbient (X : ℕ) : ℕ → ℤ → ℂ :=
  fun N => finiteModeProjector (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N)

/-- Total canonical-ambient family energy of the exact raw weighted family. -/
noncomputable def weightedMinorCoeffFamilyAmbientEnergy (X : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X) (weightedMinorCoeffFamilyOnAmbient X)

/-- Family-level top-`K` projector on the exact raw weighted family restricted to the canonical ambient support. -/
noncomputable def weightedMinorCoeffFamilyProjectTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℕ → ℤ → ℂ :=
  familyProjectTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (weightedMinorCoeffFamilyOnAmbient X)

/-- Family-level residual after top-`K` projection on the exact raw weighted family. -/
noncomputable def weightedMinorCoeffFamilyResidualTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℕ → ℤ → ℂ :=
  familyResidualTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (weightedMinorCoeffFamilyOnAmbient X)

/-- Captured canonical-ambient family energy for the exact raw weighted family on a top-`K` mode set. -/
noncomputable def weightedMinorCoeffFamilyCapturedEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (weightedMinorCoeffFamilyProjectTopK X orderedModes K)

/-- Residual canonical-ambient family energy for the exact raw weighted family after a top-`K` projection. -/
noncomputable def weightedMinorCoeffFamilyResidualEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (weightedMinorCoeffFamilyResidualTopK X orderedModes K)

/-- Downstream shadow energy of the top-`K` complement for the exact raw weighted family. -/
noncomputable def weightedMinorCoeffFamilyShadowResidualEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  canonicalAmbientWindowSliceEnergy X (weightedMinorCoeffFamilyResidualTopK X orderedModes K)

/-- Downstream shadow energy of the top-`K` complement for the centered family. -/
noncomputable def coeffCenteredFamilyShadowResidualEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  canonicalAmbientWindowSliceEnergy X (coeffCenteredFamilyResidualTopK X orderedModes K)

/-- Downstream shadow energy of the top-`K` complement for the arithmetic family. -/
noncomputable def coeffArithFamilyShadowResidualEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  canonicalAmbientWindowSliceEnergy X (coeffArithFamilyResidualTopK X orderedModes K)

/-- One-stop top-`K` feasibility report for the exact raw weighted family. -/
noncomputable def weightedMinorCoeffFamilyTopKReport
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : TopKHarnessReport where
  fullFamilyEnergy := weightedMinorCoeffFamilyAmbientEnergy X
  capturedFamilyEnergy := weightedMinorCoeffFamilyCapturedEnergyTopK X orderedModes K
  residualFamilyEnergy := weightedMinorCoeffFamilyResidualEnergyTopK X orderedModes K
  shadowResidualEnergy := weightedMinorCoeffFamilyShadowResidualEnergyTopK X orderedModes K

/-- One-stop top-`K` feasibility report for the centered weighted family. -/
noncomputable def coeffCenteredFamilyTopKReport
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : TopKHarnessReport where
  fullFamilyEnergy := coeffCenteredFamilyEnergy X
  capturedFamilyEnergy := coeffCenteredFamilyCapturedEnergyTopK X orderedModes K
  residualFamilyEnergy := coeffCenteredFamilyResidualEnergyTopK X orderedModes K
  shadowResidualEnergy := coeffCenteredFamilyShadowResidualEnergyTopK X orderedModes K

/-- One-stop top-`K` feasibility report for the weight-regressed arithmetic family. -/
noncomputable def coeffArithFamilyTopKReport
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : TopKHarnessReport where
  fullFamilyEnergy := coeffArithFamilyEnergy X
  capturedFamilyEnergy := coeffArithFamilyCapturedEnergyTopK X orderedModes K
  residualFamilyEnergy := coeffArithFamilyResidualEnergyTopK X orderedModes K
  shadowResidualEnergy := coeffArithFamilyShadowResidualEnergyTopK X orderedModes K

/-- Family-energy capture ratio, defined as `0` if the full energy vanishes. -/
noncomputable def TopKHarnessReport.captureRatio (R : TopKHarnessReport) : ℝ :=
  if _h : R.fullFamilyEnergy = 0 then 0 else R.capturedFamilyEnergy / R.fullFamilyEnergy

/-- Family-energy residual ratio, defined as `0` if the full energy vanishes. -/
noncomputable def TopKHarnessReport.residualRatio (R : TopKHarnessReport) : ℝ :=
  if _h : R.fullFamilyEnergy = 0 then 0 else R.residualFamilyEnergy / R.fullFamilyEnergy

/-- Shadow-to-family ratio, defined as `0` if the full energy vanishes. -/
noncomputable def TopKHarnessReport.shadowResidualRatio (R : TopKHarnessReport) : ℝ :=
  if _h : R.fullFamilyEnergy = 0 then 0 else R.shadowResidualEnergy / R.fullFamilyEnergy

theorem weightedMinorCoeffFamilyProjectTopK_apply
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) (N : ℕ) (t : ℤ) :
    weightedMinorCoeffFamilyProjectTopK X orderedModes K N t
      =
    projectTopKFromList (canonicalMinorAmbientSupport X) orderedModes K
      (finiteModeProjector (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N)) t := by
  rfl

theorem weightedMinorCoeffFamilyResidualTopK_apply
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) (N : ℕ) (t : ℤ) :
    weightedMinorCoeffFamilyResidualTopK X orderedModes K N t
      =
    residualAfterTopKFromList (canonicalMinorAmbientSupport X) orderedModes K
      (finiteModeProjector (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N)) t := by
  rfl

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularityHarness
