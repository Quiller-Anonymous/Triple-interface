import Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularitySubspaces

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors

noncomputable section

/--
Entry of a family object on the canonical window and canonical ambient support.

This is the exact matrix-entry view needed by external low-rank experiments on the repo object.
-/
noncomputable def familyEntry
    (X : ℕ) (F : ℕ → ℤ → ℂ)
    (N : minorWindow X) (t : canonicalMinorAmbientSupport X) : ℂ :=
  F (N : ℕ) (t : ℤ)

/-- Exact matrix-entry view of the centered weighted minor family. -/
noncomputable def coeffCenteredFamilyEntry
    (X : ℕ) (N : minorWindow X) (t : canonicalMinorAmbientSupport X) : ℂ :=
  familyEntry X (coeffCenteredFamily X) N t

/-- Exact matrix-entry view of the weight-regressed arithmetic residual family. -/
noncomputable def coeffArithFamilyEntry
    (X : ℕ) (N : minorWindow X) (t : canonicalMinorAmbientSupport X) : ℂ :=
  familyEntry X (coeffArithFamily X) N t

/--
Finite-dimensional family subspace approximant on the `t`-index set.

`basisIdx` is a finite label set for basis vectors, `basis j` is the `j`-th basis vector on the
ambient `t`-support, and `coord N j` is the coefficient attached to slice `N`.
-/
noncomputable def familySubspaceApprox
    {ι : Type} [DecidableEq ι]
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℕ → ℤ → ℂ :=
  fun N t => ∑ j ∈ basisIdx, coord N j * basis j t

/-- Residual after subtracting a chosen finite-dimensional family subspace approximant. -/
noncomputable def familySubspaceResidual
    {ι : Type} [DecidableEq ι]
    (F : ℕ → ℤ → ℂ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℕ → ℤ → ℂ :=
  fun N t => F N t - familySubspaceApprox basisIdx basis coord N t

/-- Captured family energy of a chosen finite-dimensional approximant on a fixed window/support. -/
noncomputable def familySubspaceCapturedEnergyOn
    {ι : Type} [DecidableEq ι]
    (window : Finset ℕ) (support : Finset ℤ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℝ :=
  familyCoeffEnergyOn window support (familySubspaceApprox basisIdx basis coord)

/-- Residual family energy after subtracting a chosen finite-dimensional approximant. -/
noncomputable def familySubspaceResidualEnergyOn
    {ι : Type} [DecidableEq ι]
    (window : Finset ℕ) (support : Finset ℤ)
    (F : ℕ → ℤ → ℂ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℝ :=
  familyCoeffEnergyOn window support (familySubspaceResidual F basisIdx basis coord)

/-- Canonical-window captured energy for a subspace approximant to the centered weighted family. -/
noncomputable def coeffCenteredFamilyCapturedEnergySubspace
    {ι : Type} [DecidableEq ι]
    (X : ℕ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℝ :=
  familySubspaceCapturedEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X) basisIdx basis coord

/-- Canonical-window residual energy for a subspace approximant to the centered weighted family. -/
noncomputable def coeffCenteredFamilyResidualEnergySubspace
    {ι : Type} [DecidableEq ι]
    (X : ℕ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℝ :=
  familySubspaceResidualEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (coeffCenteredFamily X) basisIdx basis coord

/-- Canonical-window captured energy for a subspace approximant to the arithmetic residual family. -/
noncomputable def coeffArithFamilyCapturedEnergySubspace
    {ι : Type} [DecidableEq ι]
    (X : ℕ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℝ :=
  familySubspaceCapturedEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X) basisIdx basis coord

/-- Canonical-window residual energy for a subspace approximant to the arithmetic residual family. -/
noncomputable def coeffArithFamilyResidualEnergySubspace
    {ι : Type} [DecidableEq ι]
    (X : ℕ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ) : ℝ :=
  familySubspaceResidualEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (coeffArithFamily X) basisIdx basis coord

theorem familyEntry_apply
    (X : ℕ) (F : ℕ → ℤ → ℂ)
    (N : minorWindow X) (t : canonicalMinorAmbientSupport X) :
    familyEntry X F N t = F (N : ℕ) (t : ℤ) := by
  rfl

theorem familySubspaceResidual_eq_sub_approx
    {ι : Type} [DecidableEq ι]
    (F : ℕ → ℤ → ℂ)
    (basisIdx : Finset ι) (basis : ι → ℤ → ℂ) (coord : ℕ → ι → ℂ)
    (N : ℕ) (t : ℤ) :
    familySubspaceResidual F basisIdx basis coord N t
      =
    F N t - familySubspaceApprox basisIdx basis coord N t := by
  rfl

theorem coeffArithFamilyEntry_eq_coeffArith
    (X : ℕ) (N : minorWindow X) (t : canonicalMinorAmbientSupport X) :
    coeffArithFamilyEntry X N t = coeffArith X (N : ℕ) (t : ℤ) := by
  rfl

theorem coeffCenteredFamilyEntry_eq_coeffCentered
    (X : ℕ) (N : minorWindow X) (t : canonicalMinorAmbientSupport X) :
    coeffCenteredFamilyEntry X N t = coeffCentered X (N : ℕ) (t : ℤ) := by
  rfl

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularitySubspaces
