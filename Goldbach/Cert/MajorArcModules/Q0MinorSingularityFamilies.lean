import Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors

noncomputable section

/-- The canonical `N`-window for family-level minor singularity studies. -/
noncomputable def minorWindow (X : ℕ) : Finset ℕ :=
  EvenIn X H

/-- The family of centered weighted minor coefficient objects over the canonical window. -/
noncomputable def coeffCenteredFamily (X : ℕ) : ℕ → ℤ → ℂ :=
  fun N => coeffCentered X N

/-- The family of weight-regressed arithmetic residual objects over the canonical window. -/
noncomputable def coeffArithFamily (X : ℕ) : ℕ → ℤ → ℂ :=
  fun N => coeffArith X N

/-- Generic family-level top-`K` projector using a common ordered mode list across the whole window. -/
noncomputable def familyProjectTopKFromList
    (support : Finset ℤ) (orderedModes : List ℤ) (K : ℕ)
    (F : ℕ → ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun N => projectTopKFromList support orderedModes K (F N)

/-- Generic family-level residual after projecting onto a common top-`K` mode set. -/
noncomputable def familyResidualTopKFromList
    (support : Finset ℤ) (orderedModes : List ℤ) (K : ℕ)
    (F : ℕ → ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun N => residualAfterTopKFromList support orderedModes K (F N)

/-- The common top-`K` mode set on the canonical ambient support. -/
noncomputable def familyTopKModes (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : Finset ℤ :=
  topKModesFromList (canonicalMinorAmbientSupport X) orderedModes K

/-- Family-level top-`K` projector on the centered weighted minor object. -/
noncomputable def coeffCenteredFamilyProjectTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℕ → ℤ → ℂ :=
  familyProjectTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffCenteredFamily X)

/-- Family-level residual after top-`K` projection on the centered weighted minor object. -/
noncomputable def coeffCenteredFamilyResidualTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℕ → ℤ → ℂ :=
  familyResidualTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffCenteredFamily X)

/-- Family-level top-`K` projector on the weight-regressed arithmetic residual object. -/
noncomputable def coeffArithFamilyProjectTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℕ → ℤ → ℂ :=
  familyProjectTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffArithFamily X)

/-- Family-level residual after top-`K` projection on the weight-regressed arithmetic residual object. -/
noncomputable def coeffArithFamilyResidualTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℕ → ℤ → ℂ :=
  familyResidualTopKFromList (canonicalMinorAmbientSupport X) orderedModes K (coeffArithFamily X)

/-- Sum of squared coefficient norms over a finite `N`-window. -/
noncomputable def familyCoeffEnergyOn
    (window : Finset ℕ) (support : Finset ℤ) (F : ℕ → ℤ → ℂ) : ℝ :=
  ∑ N ∈ window, coeffNormSqOn support (F N)

/-- Total family energy for the centered weighted minor object on the canonical window. -/
noncomputable def coeffCenteredFamilyEnergy (X : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X) (coeffCenteredFamily X)

/-- Total family energy for the weight-regressed arithmetic residual object on the canonical window. -/
noncomputable def coeffArithFamilyEnergy (X : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X) (coeffArithFamily X)

/-- Captured family energy of the centered weighted minor object on a common top-`K` mode set. -/
noncomputable def coeffCenteredFamilyCapturedEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (coeffCenteredFamilyProjectTopK X orderedModes K)

/-- Residual family energy of the centered weighted minor object after a common top-`K` projection. -/
noncomputable def coeffCenteredFamilyResidualEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (coeffCenteredFamilyResidualTopK X orderedModes K)

/-- Captured family energy of the weight-regressed arithmetic residual object on a common top-`K` mode set. -/
noncomputable def coeffArithFamilyCapturedEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (coeffArithFamilyProjectTopK X orderedModes K)

/-- Residual family energy of the weight-regressed arithmetic residual object after a common top-`K` projection. -/
noncomputable def coeffArithFamilyResidualEnergyTopK
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) : ℝ :=
  familyCoeffEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (coeffArithFamilyResidualTopK X orderedModes K)

theorem familyTopKModes_subset_ambient
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) :
    familyTopKModes X orderedModes K ⊆ canonicalMinorAmbientSupport X := by
  exact topKModesFromList_subset_support (canonicalMinorAmbientSupport X) orderedModes K

theorem coeffArithFamilyProjectTopK_apply
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) (N : ℕ) (t : ℤ) :
    coeffArithFamilyProjectTopK X orderedModes K N t
      =
    coeffArithProjectTopK X N orderedModes K t := by
  rfl

theorem coeffArithFamilyResidualTopK_apply
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) (N : ℕ) (t : ℤ) :
    coeffArithFamilyResidualTopK X orderedModes K N t
      =
    coeffArithResidualTopK X N orderedModes K t := by
  rfl

theorem coeffCenteredFamilyProjectTopK_apply
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) (N : ℕ) (t : ℤ) :
    coeffCenteredFamilyProjectTopK X orderedModes K N t
      =
    coeffCenteredProjectTopK X N orderedModes K t := by
  rfl

theorem coeffCenteredFamilyResidualTopK_apply
    (X : ℕ) (orderedModes : List ℤ) (K : ℕ) (N : ℕ) (t : ℤ) :
    coeffCenteredFamilyResidualTopK X orderedModes K N t
      =
    coeffCenteredResidualTopK X N orderedModes K t := by
  rfl

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
