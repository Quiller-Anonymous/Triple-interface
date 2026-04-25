import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise

/-!
Deterministic reality and size bounds for the frozen geometric scalar `exactGeometricScalar`.

This isolates the purely geometric part of the normalization package needed by the half-mass
average theorem surface:

* `exactGeometricScalar X` is real;
* its real part is nonnegative;
* its real part is bounded above by a coarse explicit constant.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassGeometricScalarBounds

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

private lemma KHatH_eq_of_mem_S_BG {k : ℤ} (hk : k ∈ Goldbach.BG_Identity.S_BG) :
    KHatH k = (Goldbach.BG_Identity.K_full k : ℂ) := by
  have hkneg : -k ∈ Goldbach.BG_Identity.S_BG := by
    rw [Goldbach.BG_Identity.mem_S_BG_iff] at hk
    rw [Goldbach.BG_Identity.mem_S_BG_iff]
    omega
  unfold KHatH Goldbach.Cert.MajorArcStep10RLSmoothIntegral.coeffC
  rw [Goldbach.Cert.MajorArcStep9CorrelationIntegral.coeff_eq]
  simp [hkneg, Goldbach.BG_Identity.K_full_neg]

private lemma KHatH_eq_zero_of_not_mem_S_BG {k : ℤ} (hk : k ∉ Goldbach.BG_Identity.S_BG) :
    KHatH k = 0 := by
  have hkneg : -k ∉ Goldbach.BG_Identity.S_BG := by
    intro hkneg
    have : k ∈ Goldbach.BG_Identity.S_BG := by
      rw [Goldbach.BG_Identity.mem_S_BG_iff] at hkneg
      rw [Goldbach.BG_Identity.mem_S_BG_iff]
      omega
    exact hk this
  unfold KHatH Goldbach.Cert.MajorArcStep10RLSmoothIntegral.coeffC
  rw [Goldbach.Cert.MajorArcStep9CorrelationIntegral.coeff_eq]
  simp [hkneg]

private lemma KHatH_im_eq_zero (k : ℤ) : (KHatH k).im = 0 := by
  by_cases hk : k ∈ Goldbach.BG_Identity.S_BG
  · rw [KHatH_eq_of_mem_S_BG hk]
    simp
  · rw [KHatH_eq_zero_of_not_mem_S_BG hk]
    simp

private lemma unscaledGeometricZeroSliceMass_term_im_eq_zero
    (X : ℕ) (nm : ℕ × ℕ) :
    (uniformWindowSupportIndicator X nm.1
      * uniformWindowSupportIndicator X nm.2
      * KHatH (kFn nm)).im = 0 := by
  by_cases h1 : nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
  · by_cases h2 : nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
    · simp [uniformWindowSupportIndicator, h1, h2]
    · simp [uniformWindowSupportIndicator, h1, h2]
  · simp [uniformWindowSupportIndicator, h1]

/-- The unscaled geometric zero slice is real-valued. -/
theorem unscaledGeometricZeroSliceMass_im_eq_zero
    (X N : ℕ) :
    (unscaledGeometricZeroSliceMass X N).im = 0 := by
  unfold unscaledGeometricZeroSliceMass
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero ?_
  intro nm hnm
  exact unscaledGeometricZeroSliceMass_term_im_eq_zero X nm

/-- The frozen geometric scalar has zero imaginary part. -/
theorem exactGeometricScalar_im_eq_zero
    {X : ℕ} :
    (exactGeometricScalar X).im = 0 := by
  unfold exactGeometricScalar
  exact unscaledGeometricZeroSliceMass_im_eq_zero X (canonicalEvenWindowPoint X)

/-- The frozen geometric scalar is equal to its own real part. -/
theorem exactGeometricScalar_eq_realPart
    (X : ℕ) :
    exactGeometricScalar X = ((exactGeometricScalar X).re : ℂ) := by
  apply Complex.ext
  · simp
  · exact exactGeometricScalar_im_eq_zero

/-- The frozen geometric scalar has nonnegative real part. -/
theorem exactGeometricScalar_re_nonneg
    {X : ℕ} (hX : X0 ≤ X) :
    0 ≤ (exactGeometricScalar X).re := by
  let N := canonicalEvenWindowPoint X
  have hN : N ∈ EvenIn X H := canonicalEvenWindowPoint_mem_even_window
  have hnonneg := unscaledGeometricZeroSliceMass_re_nonneg_of_mem_even_window hX hN
  simpa [N, exactGeometricScalar] using hnonneg

/-- The diagonal term gives a uniform lower floor for the frozen geometric scalar. -/
theorem exactGeometricScalar_re_lower
    {X : ℕ} (hX : X0 ≤ X) :
    Goldbach.BG_Identity.K_full (0 : ℤ) ≤ (exactGeometricScalar X).re := by
  let N := canonicalEvenWindowPoint X
  have hN : N ∈ EvenIn X H := canonicalEvenWindowPoint_mem_even_window
  have hlower := unscaledGeometricZeroSliceMass_re_lower_of_mem_even_window hX hN
  simpa [N, exactGeometricScalar] using hlower

/-- Coarse explicit upper bound for the real part of the frozen geometric scalar. -/
theorem exactGeometricScalar_re_le_two
    {X : ℕ} (hX : X0 ≤ X) :
    (exactGeometricScalar X).re ≤ 2 := by
  let N := canonicalEvenWindowPoint X
  have hN : N ∈ EvenIn X H := canonicalEvenWindowPoint_mem_even_window
  let hT :=
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise.unscaledGeometricZeroSliceMassWindowNormTarget_explicit
  have hnorm : ‖exactGeometricScalar X‖ ≤ 2 := by
    simpa [N, exactGeometricScalar] using hT.upper hX hN
  have hnonneg : 0 ≤ (exactGeometricScalar X).re := exactGeometricScalar_re_nonneg hX
  have habs :
      |(exactGeometricScalar X).re| = (exactGeometricScalar X).re := by
    simp [abs_of_nonneg hnonneg]
  have hre_le_norm : (exactGeometricScalar X).re ≤ ‖exactGeometricScalar X‖ := by
    calc
      (exactGeometricScalar X).re = |(exactGeometricScalar X).re| := by symm; exact habs
      _ ≤ ‖exactGeometricScalar X‖ := by
        simpa using (Complex.abs_re_le_norm (exactGeometricScalar X))
  exact le_trans hre_le_norm hnorm

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassGeometricScalarBounds
