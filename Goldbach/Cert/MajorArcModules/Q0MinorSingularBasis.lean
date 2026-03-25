import Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularBasis

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularitySubspaces
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates

noncomputable section

/--
Alternating near-Nyquist carrier used in the deterministic minor singular-basis template.

This is the explicit replacement target for the empirical SVD family on the minor side.
-/
noncomputable def alternatingCarrier (t : ℤ) : ℂ :=
  if Even t then (1 : ℂ) else (-1 : ℂ)

/--
Untruncated cosine template underlying the deterministic minor singular-basis family.

The shape matches the current feasibility signal: an alternating carrier times a low-rank
cosine profile on the canonical minor scale.
-/
noncomputable def altDCTBasisCore (j : ℕ) (t : ℤ) : ℂ :=
  alternatingCarrier t
    * Complex.ofReal
        (Real.cos
          (Real.pi * (j : ℝ) * ((((t : ℝ) + 3 * (H : ℝ)) / (4 * (H : ℝ))))))

/-- Canonical-ambient version of the alternating-DCT basis template. -/
noncomputable def altDCTBasisOnAmbient (X : ℕ) (j : ℕ) : ℤ → ℂ :=
  finiteModeProjector (canonicalMinorAmbientSupport X) (altDCTBasisCore j)

/-- The finite index set for the first `r` alternating-DCT basis vectors. -/
noncomputable def altDCTBasisIdx (r : ℕ) : Finset (Fin r) :=
  Finset.univ

/--
Family approximant on the canonical ambient support using the first `r` alternating-DCT basis
vectors and a supplied coefficient rule.
-/
noncomputable def altDCTFamilyApprox
    (X r : ℕ) (coord : ℕ → Fin r → ℂ) : ℕ → ℤ → ℂ :=
  familySubspaceApprox (altDCTBasisIdx r) (fun j => altDCTBasisOnAmbient X j.1) coord

/-- Residual after subtracting the alternating-DCT family approximant from `coeffArithFamily`. -/
noncomputable def coeffArithAltDCTResidual
    (X r : ℕ) (coord : ℕ → Fin r → ℂ) : ℕ → ℤ → ℂ :=
  familySubspaceResidual (coeffArithFamily X) (altDCTBasisIdx r) (fun j => altDCTBasisOnAmbient X j.1) coord

/-- Captured canonical-window energy of an alternating-DCT approximant to `coeffArithFamily`. -/
noncomputable def coeffArithAltDCTCapturedEnergy
    (X r : ℕ) (coord : ℕ → Fin r → ℂ) : ℝ :=
  coeffArithFamilyCapturedEnergySubspace X (altDCTBasisIdx r) (fun j => altDCTBasisOnAmbient X j.1) coord

/-- Residual canonical-window energy of an alternating-DCT approximant to `coeffArithFamily`. -/
noncomputable def coeffArithAltDCTResidualEnergy
    (X r : ℕ) (coord : ℕ → Fin r → ℂ) : ℝ :=
  coeffArithFamilyResidualEnergySubspace X (altDCTBasisIdx r) (fun j => altDCTBasisOnAmbient X j.1) coord

/-- Canonical family-subspace data attached to the alternating-DCT basis template. -/
noncomputable def coeffArithAltDCTSubspaceData
    (X r : ℕ) (coord : ℕ → Fin r → ℂ) :
    Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates.FamilySubspaceData X (coeffArithFamily X) where
  rank := r
  basis := fun j => altDCTBasisOnAmbient X j.1
  coord := coord

theorem altDCTBasisOnAmbient_apply_outside
    {X j : ℕ} {t : ℤ} (ht : t ∉ canonicalMinorAmbientSupport X) :
    altDCTBasisOnAmbient X j t = 0 := by
  unfold altDCTBasisOnAmbient finiteModeProjector
  simp [ht]

theorem altDCTFamilyApprox_eq_sum
    (X r : ℕ) (coord : ℕ → Fin r → ℂ) (N : ℕ) (t : ℤ) :
    altDCTFamilyApprox X r coord N t
      =
    ∑ j : Fin r, coord N j * altDCTBasisOnAmbient X j.1 t := by
  unfold altDCTFamilyApprox familySubspaceApprox altDCTBasisIdx
  simp

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularBasis
