import Goldbach.Cert.MajorArcModules.Q0MinorSingularitySubspaces

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularitySubspaces

noncomputable section

/-- The exact raw weighted minor family on the canonical window. -/
noncomputable def weightedMinorCoeffFamily (X : ℕ) : ℕ → ℤ → ℂ :=
  fun N t => weightedMinorCoeff X N t

/-- Exact matrix-entry view of the raw weighted minor family. -/
noncomputable def weightedMinorCoeffFamilyEntry
    (X : ℕ) (N : minorWindow X) (t : canonicalMinorAmbientSupport X) : ℂ :=
  familyEntry X (weightedMinorCoeffFamily X) N t

/--
Finite-rank family approximant data on the canonical ambient `t`-support.

This is the minimal theorem-facing subspace object: a common basis on the `t`-index set and
slice-dependent coefficients over the window.
-/
structure FamilySubspaceData (X : ℕ) (F : ℕ → ℤ → ℂ) where
  rank : ℕ
  basis : Fin rank → ℤ → ℂ
  coord : ℕ → Fin rank → ℂ

/-- The canonical finite-rank approximant attached to `FamilySubspaceData`. -/
noncomputable def FamilySubspaceData.approx
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℕ → ℤ → ℂ :=
  familySubspaceApprox (Finset.univ : Finset (Fin S.rank)) S.basis S.coord

/-- The canonical residual attached to `FamilySubspaceData`. -/
noncomputable def FamilySubspaceData.residual
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℕ → ℤ → ℂ :=
  familySubspaceResidual F (Finset.univ : Finset (Fin S.rank)) S.basis S.coord

/-- Captured energy on the canonical window/support. -/
noncomputable def FamilySubspaceData.capturedEnergy
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℝ :=
  familySubspaceCapturedEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X)
    (Finset.univ : Finset (Fin S.rank)) S.basis S.coord

/-- Residual energy on the canonical window/support. -/
noncomputable def FamilySubspaceData.residualEnergy
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) : ℝ :=
  familySubspaceResidualEnergyOn (minorWindow X) (canonicalMinorAmbientSupport X) F
    (Finset.univ : Finset (Fin S.rank)) S.basis S.coord

/-- Pointwise slice energy of the residual on the canonical ambient support. -/
noncomputable def FamilySubspaceData.residualSliceEnergy
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F) (N : ℕ) : ℝ :=
  coeffNormSqOn (canonicalMinorAmbientSupport X) (S.residual N)

theorem FamilySubspaceData.residual_eq_sub_approx
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F)
    (N : ℕ) (t : ℤ) :
    S.residual N t = F N t - S.approx N t := by
  rfl

theorem FamilySubspaceData.family_eq_approx_add_residual
    {X : ℕ} {F : ℕ → ℤ → ℂ} (S : FamilySubspaceData X F)
    (N : ℕ) (t : ℤ) :
    F N t = S.approx N t + S.residual N t := by
  rw [FamilySubspaceData.residual_eq_sub_approx]
  ring

/--
Residual-control certificate for a finite-rank family approximant.

This is the nontrivial existence interface intended for the bridge question: a finite-rank family
subspace together with slice-wise residual controls on the exact repo object and a global window
sum bound.
-/
structure FamilySubspaceCertificate (X : ℕ) (F : ℕ → ℤ → ℂ)
    extends FamilySubspaceData X F where
  residualSliceUpper : ℕ → ℝ
  residualUpper : ℝ
  residualUpper_nonneg : 0 ≤ residualUpper
  slice_nonneg : ∀ N : ℕ, 0 ≤ residualSliceUpper N
  hSlice :
    ∀ {N : ℕ}, N ∈ minorWindow X →
      toFamilySubspaceData.residualSliceEnergy N ≤ residualSliceUpper N
  hWindow :
    ∑ N ∈ minorWindow X, residualSliceUpper N ≤ residualUpper

/-- The certified residual energy is bounded by the packaged global residual upper envelope. -/
theorem FamilySubspaceCertificate.residualEnergy_le
    {X : ℕ} {F : ℕ → ℤ → ℂ} (C : FamilySubspaceCertificate X F) :
    C.toFamilySubspaceData.residualEnergy ≤ C.residualUpper := by
  unfold FamilySubspaceData.residualEnergy familySubspaceResidualEnergyOn familyCoeffEnergyOn
  refine le_trans ?_ C.hWindow
  refine Finset.sum_le_sum ?_
  intro N hN
  exact C.hSlice (N := N) hN

/-- The residual slice upper bound is nonnegative on the canonical window. -/
theorem FamilySubspaceCertificate.slice_nonneg_of_mem
    {X : ℕ} {F : ℕ → ℤ → ℂ} (C : FamilySubspaceCertificate X F)
    {N : ℕ} (_hN : N ∈ minorWindow X) :
    0 ≤ C.residualSliceUpper N := by
  exact C.slice_nonneg N

/-- Certificate type for the raw weighted minor family on the canonical window. -/
abbrev WeightedMinorCoeffFamilyCertificate (X : ℕ) : Type :=
  FamilySubspaceCertificate X (weightedMinorCoeffFamily X)

/-- Certificate type for the centered weighted minor family on the canonical window. -/
abbrev CoeffCenteredFamilyCertificate (X : ℕ) : Type :=
  FamilySubspaceCertificate X (coeffCenteredFamily X)

/-- Certificate type for the weight-regressed arithmetic residual family on the canonical window. -/
abbrev CoeffArithFamilyCertificate (X : ℕ) : Type :=
  FamilySubspaceCertificate X (coeffArithFamily X)

theorem weightedMinorCoeffFamilyEntry_eq_weightedMinorCoeff
    (X : ℕ) (N : minorWindow X) (t : canonicalMinorAmbientSupport X) :
    weightedMinorCoeffFamilyEntry X N t = weightedMinorCoeff X (N : ℕ) (t : ℤ) := by
  rfl

theorem coeffCenteredFamilyCertificate_residualEnergy_le
    {X : ℕ} (C : CoeffCenteredFamilyCertificate X) :
    C.toFamilySubspaceData.residualEnergy ≤ C.residualUpper :=
  C.residualEnergy_le

theorem coeffArithFamilyCertificate_residualEnergy_le
    {X : ℕ} (C : CoeffArithFamilyCertificate X) :
    C.toFamilySubspaceData.residualEnergy ≤ C.residualUpper :=
  C.residualEnergy_le

/-- The ambient-support indicator on the canonical window-stable `t`-box. -/
noncomputable def canonicalAmbientIndicator (X : ℕ) : ℤ → ℂ :=
  fun t => if t ∈ canonicalMinorAmbientSupport X then 1 else 0

/--
Adjoin the centered weight-only direction to an arithmetic-residual subspace.

This is the exact triple-interface lift
`coeffCentered = coeffArith + α · weightCentered`
on the canonical ambient support.
-/
noncomputable def centeredFamilySubspaceDataOfArith
    {X : ℕ} (C : CoeffArithFamilyCertificate X) :
    FamilySubspaceData X (coeffCenteredFamily X) where
  rank := C.rank + 1
  basis := Fin.cases (weightCentered X) (fun i => C.basis i)
  coord := fun N => Fin.cases (weightRegressionAlpha X N) (fun i => C.coord N i)

theorem centeredFamilySubspaceDataOfArith_approx
    {X : ℕ} (C : CoeffArithFamilyCertificate X) (N : ℕ) (t : ℤ) :
    (centeredFamilySubspaceDataOfArith C).approx N t
      =
    weightRegressionAlpha X N * weightCentered X t
      + C.toFamilySubspaceData.approx N t := by
  unfold FamilySubspaceData.approx centeredFamilySubspaceDataOfArith familySubspaceApprox
  rw [Fin.sum_univ_succ]
  simp

theorem centeredFamilySubspaceDataOfArith_residual_eq_arith_on_support
    {X : ℕ} (C : CoeffArithFamilyCertificate X)
    {N : ℕ} {t : ℤ} (_ht : t ∈ canonicalMinorAmbientSupport X) :
    (centeredFamilySubspaceDataOfArith C).residual N t
      =
    C.toFamilySubspaceData.residual N t := by
  have hcoeff :
      coeffArith X N t
        =
      coeffCentered X N t - weightRegressionAlpha X N * weightCentered X t := by
    simpa using coeffArith_eq_coeffCentered_sub_alpha_mul_weightCentered X N t
  rw [FamilySubspaceData.residual_eq_sub_approx,
    FamilySubspaceData.residual_eq_sub_approx,
    centeredFamilySubspaceDataOfArith_approx]
  simp [coeffCenteredFamily, coeffArithFamily]
  rw [hcoeff]
  ring

/-- Exact certificate lift from the arithmetic residual family to the centered weighted family. -/
noncomputable def coeffCenteredFamilyCertificateOfCoeffArith
    {X : ℕ} (C : CoeffArithFamilyCertificate X) :
    CoeffCenteredFamilyCertificate X where
  rank := (centeredFamilySubspaceDataOfArith C).rank
  basis := (centeredFamilySubspaceDataOfArith C).basis
  coord := (centeredFamilySubspaceDataOfArith C).coord
  residualSliceUpper := C.residualSliceUpper
  residualUpper := C.residualUpper
  residualUpper_nonneg := C.residualUpper_nonneg
  slice_nonneg := C.slice_nonneg
  hSlice := by
    intro N hN
    unfold FamilySubspaceData.residualSliceEnergy coeffNormSqOn
    have hsum :
        (∑ t ∈ canonicalMinorAmbientSupport X,
            ‖(centeredFamilySubspaceDataOfArith C).residual N t‖ ^ 2)
          =
        (∑ t ∈ canonicalMinorAmbientSupport X,
            ‖C.toFamilySubspaceData.residual N t‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [centeredFamilySubspaceDataOfArith_residual_eq_arith_on_support C ht]
    rw [hsum]
    exact C.hSlice (N := N) hN
  hWindow := C.hWindow

/--
Adjoin the ambient-support mean direction to a centered-family subspace.

This is the exact triple-interface lift from the centered object to the raw weighted family on the
canonical ambient support.
-/
noncomputable def weightedFamilySubspaceDataOfCentered
    {X : ℕ} (C : CoeffCenteredFamilyCertificate X) :
    FamilySubspaceData X (weightedMinorCoeffFamily X) where
  rank := C.rank + 1
  basis := Fin.cases (canonicalAmbientIndicator X) (fun i => C.basis i)
  coord := fun N =>
    Fin.cases
      (coeffMeanOn (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N))
      (fun i => C.coord N i)

theorem weightedFamilySubspaceDataOfCentered_approx
    {X : ℕ} (C : CoeffCenteredFamilyCertificate X) (N : ℕ) (t : ℤ) :
    (weightedFamilySubspaceDataOfCentered C).approx N t
      =
    coeffMeanOn (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N)
        * canonicalAmbientIndicator X t
      + C.toFamilySubspaceData.approx N t := by
  unfold FamilySubspaceData.approx weightedFamilySubspaceDataOfCentered familySubspaceApprox
  rw [Fin.sum_univ_succ]
  simp [canonicalAmbientIndicator]

theorem weightedFamilySubspaceDataOfCentered_residual_eq_centered_on_support
    {X : ℕ} (C : CoeffCenteredFamilyCertificate X)
    {N : ℕ} {t : ℤ} (ht : t ∈ canonicalMinorAmbientSupport X) :
    (weightedFamilySubspaceDataOfCentered C).residual N t
      =
    C.toFamilySubspaceData.residual N t := by
  have hcentered :
      coeffCentered X N t
        =
      weightedMinorCoeff X N t
        - coeffMeanOn (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N) := by
    simpa [canonicalMinorAmbientSupport] using
      coeffCentered_eq_weightedMinorCoeff_sub_mean (X := X) (N := N) (t := t) ht
  rw [FamilySubspaceData.residual_eq_sub_approx,
    FamilySubspaceData.residual_eq_sub_approx,
    weightedFamilySubspaceDataOfCentered_approx]
  have hind :
      canonicalAmbientIndicator X t = 1 := by
    simp [canonicalAmbientIndicator, ht]
  rw [hind]
  simp [weightedMinorCoeffFamily, coeffCenteredFamily]
  rw [hcentered]
  ring

/-- Exact certificate lift from the centered weighted family to the raw weighted family. -/
noncomputable def weightedMinorCoeffFamilyCertificateOfCoeffCentered
    {X : ℕ} (C : CoeffCenteredFamilyCertificate X) :
    WeightedMinorCoeffFamilyCertificate X where
  rank := (weightedFamilySubspaceDataOfCentered C).rank
  basis := (weightedFamilySubspaceDataOfCentered C).basis
  coord := (weightedFamilySubspaceDataOfCentered C).coord
  residualSliceUpper := C.residualSliceUpper
  residualUpper := C.residualUpper
  residualUpper_nonneg := C.residualUpper_nonneg
  slice_nonneg := C.slice_nonneg
  hSlice := by
    intro N hN
    unfold FamilySubspaceData.residualSliceEnergy coeffNormSqOn
    have hsum :
        (∑ t ∈ canonicalMinorAmbientSupport X,
            ‖(weightedFamilySubspaceDataOfCentered C).residual N t‖ ^ 2)
          =
        (∑ t ∈ canonicalMinorAmbientSupport X,
            ‖C.toFamilySubspaceData.residual N t‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [weightedFamilySubspaceDataOfCentered_residual_eq_centered_on_support C ht]
    rw [hsum]
    exact C.hSlice (N := N) hN
  hWindow := C.hWindow

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates
