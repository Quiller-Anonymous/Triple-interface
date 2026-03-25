import Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
import Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
import Goldbach.ProofTools

namespace Goldbach.Cert.MajorArcModules.Q0MinorSingularityRouteBridge

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSplitCert
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

/-- The raw weighted family certificate induced from an arithmetic-residual family certificate. -/
noncomputable def weightedMinorCoeffFamilyCertificateOfCoeffArith
    {X : ℕ} (C : CoeffArithFamilyCertificate X) :
    WeightedMinorCoeffFamilyCertificate X :=
  weightedMinorCoeffFamilyCertificateOfCoeffCentered
    (coeffCenteredFamilyCertificateOfCoeffArith C)

/-- The exact nonzero-mode slice of the raw weighted minor family on the canonical ambient support. -/
noncomputable def exactNonzeroWeightedSlice (X : ℕ) : ℕ → ℂ :=
  weightedMinorCoeffFamilyShadowSlice X

/-- The singular nonzero-mode slice induced by a coefficient-family certificate. -/
noncomputable def singularNonzeroSlice
    {X : ℕ} (C : CoeffArithFamilyCertificate X) : ℕ → ℂ :=
  FamilySubspaceData.shadowApproxSlice
    (weightedMinorCoeffFamilyCertificateOfCoeffArith C).toFamilySubspaceData

/-- The residual nonzero-mode slice induced by a coefficient-family certificate. -/
noncomputable def residualNonzeroSlice
    {X : ℕ} (C : CoeffArithFamilyCertificate X) : ℕ → ℂ :=
  FamilySubspaceData.shadowResidualSlice
    (weightedMinorCoeffFamilyCertificateOfCoeffArith C).toFamilySubspaceData

private theorem nmSupportOfT_eq_empty_of_not_mem_tSupport
    {N : ℕ} {t : ℤ} (ht : t ∉ tSupport N) :
    nmSupportOfT N t = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro nm hnm
  rcases mem_nmSupportOfT_iff.mp hnm with ⟨hn, hm, htfn⟩
  have hmem : tFn N nm ∈ tSupport N := by
    have hn_le : nm.1 ≤ N := by
      have hn_le' : nm.1 ≤ N - 2 := (Finset.mem_Icc.mp hn).2
      exact le_trans hn_le' (Nat.sub_le N 2)
    have hm_le : nm.2 ≤ N := by
      have hm_le' : nm.2 ≤ N - 2 := (Finset.mem_Icc.mp hm).2
      exact le_trans hm_le' (Nat.sub_le N 2)
    have hn0 : (0 : ℤ) ≤ (nm.1 : ℤ) := by exact_mod_cast (Nat.zero_le nm.1)
    have hm0 : (0 : ℤ) ≤ (nm.2 : ℤ) := by exact_mod_cast (Nat.zero_le nm.2)
    have hn_leZ : (nm.1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn_le
    have hm_leZ : (nm.2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hm_le
    have hlower : (-(N : ℤ)) ≤ tFn N nm := by
      have hnm0 : (0 : ℤ) ≤ (nm.1 : ℤ) + (nm.2 : ℤ) := add_nonneg hn0 hm0
      have := sub_le_sub_right hnm0 (N : ℤ)
      simpa [tFn] using this
    have hupper : tFn N nm ≤ (N : ℤ) := by
      have hnm_le : (nm.1 : ℤ) + (nm.2 : ℤ) ≤ (N : ℤ) + (N : ℤ) := add_le_add hn_leZ hm_leZ
      have : (nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ) ≤ (N : ℤ) := by
        have := sub_le_iff_le_add'.2 (by
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnm_le)
        simpa using this
      simpa [tFn] using this
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  exact ht (htfn ▸ hmem)

private theorem weightedMinorCoeff_eq_zero_of_not_mem_tSupport
    (X N : ℕ) (t : ℤ) (ht : t ∉ tSupport N) :
    weightedMinorCoeff X N t = 0 := by
  unfold weightedMinorCoeff coeff
  rw [nmSupportOfT_eq_empty_of_not_mem_tSupport ht]
  simp

private theorem tSupport_subset_windowMinorCoeffSupport
    {X N : ℕ} (hN : N ∈ minorWindow X) :
    tSupport N ⊆ windowMinorCoeffSupport X := by
  intro t ht
  rcases Finset.mem_Icc.mp ht with ⟨hl, hu⟩
  have hNle : N ≤ X + H := Goldbach.ProofTools.Windows.le_right_of_mem_EvenIn hN
  have hNleZ : (N : ℤ) ≤ ((X + H : ℕ) : ℤ) := by exact_mod_cast hNle
  have hneg : -(((X + H : ℕ) : ℤ)) ≤ -(N : ℤ) := by
    simpa using neg_le_neg hNleZ
  exact Finset.mem_Icc.mpr ⟨le_trans hneg hl, le_trans hu hNleZ⟩

theorem exactNonzeroWeightedSlice_eq_sum_tSupport_erase
    {X N : ℕ} (hN : N ∈ minorWindow X) :
    exactNonzeroWeightedSlice X N
      =
    ∑ t ∈ (tSupport N).erase 0, weightedMinorCoeff X N t := by
  classical
  unfold exactNonzeroWeightedSlice weightedMinorCoeffFamilyShadowSlice canonicalAmbientSliceSum
    familySliceSumOn weightedMinorCoeffFamily canonicalMinorAmbientSupport
  have hdecomp :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (windowMinorCoeffSupport X).erase 0)
      (p := fun t => t ∈ tSupport N)
      (f := fun t => weightedMinorCoeff X N t)).symm
  have hfilter :
      ((windowMinorCoeffSupport X).erase 0).filter (fun t => t ∈ tSupport N)
        =
      (tSupport N).erase 0 := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨htwin, htsup⟩
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp htwin).1, htsup⟩
    · intro ht
      have htsup : t ∈ tSupport N := (Finset.mem_erase.mp ht).2
      have htwin : t ∈ windowMinorCoeffSupport X := tSupport_subset_windowMinorCoeffSupport hN htsup
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1, htwin⟩, htsup⟩
  have hzero :
      ∀ t ∈ ((windowMinorCoeffSupport X).erase 0).filter (fun t => t ∉ tSupport N),
        weightedMinorCoeff X N t = 0 := by
    intro t ht
    exact weightedMinorCoeff_eq_zero_of_not_mem_tSupport X N t (Finset.mem_filter.mp ht).2
  calc
    ∑ t ∈ (windowMinorCoeffSupport X).erase 0, weightedMinorCoeff X N t
        =
      (∑ t ∈ ((windowMinorCoeffSupport X).erase 0).filter (fun t => t ∈ tSupport N),
          weightedMinorCoeff X N t)
        +
      ∑ t ∈ ((windowMinorCoeffSupport X).erase 0).filter (fun t => t ∉ tSupport N),
          weightedMinorCoeff X N t := hdecomp
    _ =
      (∑ t ∈ (tSupport N).erase 0, weightedMinorCoeff X N t)
        +
      ∑ t ∈ ((windowMinorCoeffSupport X).erase 0).filter (fun t => t ∉ tSupport N),
          weightedMinorCoeff X N t := by
            rw [hfilter]
    _ = ∑ t ∈ (tSupport N).erase 0, weightedMinorCoeff X N t := by
      have hzsum :
          ∑ t ∈ ((windowMinorCoeffSupport X).erase 0).filter (fun t => t ∉ tSupport N),
              weightedMinorCoeff X N t = 0 := Finset.sum_eq_zero hzero
      simp [hzsum]

theorem exactWeightedMinorSlice_eq_zero_add_nonzero
    (X N : ℕ) :
    exactWeightedMinorSlice X N
      =
    weightedMinorCoeff X N 0 + ∑ t ∈ (tSupport N).erase 0, weightedMinorCoeff X N t := by
  unfold exactWeightedMinorSlice
  have h0 : (0 : ℤ) ∈ weightedMinorCoeffSupport N := by
    simp [weightedMinorCoeffSupport, tSupport]
  simpa [weightedMinorCoeffSupport, add_comm, add_left_comm, add_assoc] using
    (Finset.sum_erase_add (s := weightedMinorCoeffSupport N)
      (a := (0 : ℤ)) (f := fun t => weightedMinorCoeff X N t) h0).symm

theorem exactNonzeroWeightedSlice_eq_singular_add_residual
    {X : ℕ} (C : CoeffArithFamilyCertificate X) (N : ℕ) :
    exactNonzeroWeightedSlice X N
      =
    singularNonzeroSlice C N + residualNonzeroSlice C N := by
  exact
    (FamilySubspaceData.familySlice_eq_approx_add_residual
      (S := (weightedMinorCoeffFamilyCertificateOfCoeffArith C).toFamilySubspaceData)
      (support := canonicalMinorAmbientSupport X) (N := N))

theorem minorResidual_eq_zero_add_singular_add_residual
    {X N : ℕ} (C : CoeffArithFamilyCertificate X)
    (hX : X0 ≤ X) (hN : N ∈ minorWindow X) :
    minorResidual X N Δ_canon
      =
    weightedMinorCoeff X N 0 + singularNonzeroSlice C N + residualNonzeroSlice C N := by
  calc
    minorResidual X N Δ_canon
        = exactWeightedMinorSlice X N := by
            symm
            exact exactWeightedMinorSlice_eq_minorResidual (X := X) (N := N) hX hN
    _ =
      weightedMinorCoeff X N 0
        + ∑ t ∈ (tSupport N).erase 0, weightedMinorCoeff X N t := by
            exact exactWeightedMinorSlice_eq_zero_add_nonzero X N
    _ =
      weightedMinorCoeff X N 0 + exactNonzeroWeightedSlice X N := by
        rw [exactNonzeroWeightedSlice_eq_sum_tSupport_erase (X := X) (N := N) hN]
    _ =
      weightedMinorCoeff X N 0 + (singularNonzeroSlice C N + residualNonzeroSlice C N) := by
        rw [exactNonzeroWeightedSlice_eq_singular_add_residual (C := C) (N := N)]
    _ =
      weightedMinorCoeff X N 0 + singularNonzeroSlice C N + residualNonzeroSlice C N := by
        ring

theorem residualNonzeroWindowEnergy_le
    {X : ℕ} (C : CoeffArithFamilyCertificate X) :
    ∑ N ∈ minorWindow X, ‖residualNonzeroSlice C N‖ ^ 2
      ≤
    FamilySubspaceCertificate.shadowResidualUpper
      (weightedMinorCoeffFamilyCertificateOfCoeffArith C) := by
  let W : WeightedMinorCoeffFamilyCertificate X := weightedMinorCoeffFamilyCertificateOfCoeffArith C
  have hEq :
      (∑ N ∈ minorWindow X, ‖residualNonzeroSlice C N‖ ^ 2)
        =
      FamilySubspaceData.shadowResidualEnergy W.toFamilySubspaceData := by
    rfl
  rw [hEq]
  exact FamilySubspaceCertificate.shadowResidualEnergy_le (C := W)

theorem residualNonzeroWindowEnergy_le_of_bound
    {X : ℕ} (C : CoeffArithFamilyCertificate X) {B : ℝ}
    (hB :
      FamilySubspaceCertificate.shadowResidualUpper
        (weightedMinorCoeffFamilyCertificateOfCoeffArith C) ≤ B) :
    ∑ N ∈ minorWindow X, ‖residualNonzeroSlice C N‖ ^ 2 ≤ B := by
  exact le_trans (residualNonzeroWindowEnergy_le C) hB

theorem residualNonzeroWindowEnergy_le_normFactor
    {X : ℕ} (C : CoeffArithFamilyCertificate X) {A2 : ℝ}
    (hA2 :
      FamilySubspaceCertificate.shadowResidualUpper
        (weightedMinorCoeffFamilyCertificateOfCoeffArith C)
        ≤
      normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ)))) :
    ∑ N ∈ minorWindow X, ‖residualNonzeroSlice C N‖ ^ 2
      ≤
    normFactorSq X * (A2 * ((H : ℝ) / (X : ℝ))) := by
  exact residualNonzeroWindowEnergy_le_of_bound C hA2

end

end Goldbach.Cert.MajorArcModules.Q0MinorSingularityRouteBridge
