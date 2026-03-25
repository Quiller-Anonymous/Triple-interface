import Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge

namespace Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityCertificates
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion

noncomputable section

/-- The constant mean-channel attached to a finite `t`-support. -/
noncomputable def meanChannelOn (S : Finset ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun t => if t ∈ S then coeffMeanOn S f else 0

/-- The explicit `t = 0` channel of the weighted minor coefficient object. -/
noncomputable def zeroModeSlice (X N : ℕ) : ℤ → ℂ :=
  fun t => if t = 0 then weightedMinorCoeff X N 0 else 0

/-- The exact nonzero channel on the canonical ambient support. -/
noncomputable def weightedNonzeroSlice (X N : ℕ) : ℤ → ℂ :=
  coeffZeroRemoved X N

/-- The ambient mean channel of the weighted nonzero coefficients. -/
noncomputable def meanChannelSlice (X N : ℕ) : ℤ → ℂ :=
  meanChannelOn (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N)

/-- The weight-only channel removed from the centered nonzero family. -/
noncomputable def weightChannelSlice (X N : ℕ) : ℤ → ℂ :=
  fun t => weightRegressionAlpha X N * weightCentered X t

theorem meanChannelOn_apply_mem
    {S : Finset ℤ} {f : ℤ → ℂ} {t : ℤ} (ht : t ∈ S) :
    meanChannelOn S f t = coeffMeanOn S f := by
  unfold meanChannelOn
  simp [ht]

theorem meanChannelOn_apply_not_mem
    {S : Finset ℤ} {f : ℤ → ℂ} {t : ℤ} (ht : t ∉ S) :
    meanChannelOn S f t = 0 := by
  unfold meanChannelOn
  simp [ht]

theorem sum_meanChannelOn_eq_sum
    (S : Finset ℤ) (f : ℤ → ℂ) :
    ∑ t ∈ S, meanChannelOn S f t = ∑ t ∈ S, f t := by
  by_cases hS : S.card = 0
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hS
    simp [hEmpty, meanChannelOn]
  · have hcard : (((S.card : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero.mpr hS)
    calc
      ∑ t ∈ S, meanChannelOn S f t
          = ∑ t ∈ S, coeffMeanOn S f := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              simp [meanChannelOn, ht]
      _ = ((S.card : ℕ) : ℂ) * coeffMeanOn S f := by
            simp
      _ = ((S.card : ℕ) : ℂ) * ((((S.card : ℕ) : ℂ))⁻¹ * ∑ t ∈ S, f t) := by
            simp [coeffMeanOn]
      _ = ∑ t ∈ S, f t := by
            calc
              (((S.card : ℕ) : ℂ) * ((((S.card : ℕ) : ℂ))⁻¹ * ∑ t ∈ S, f t))
                  = ((((S.card : ℕ) : ℂ) * (((S.card : ℕ) : ℂ))⁻¹) * ∑ t ∈ S, f t) := by ring
              _ = ∑ t ∈ S, f t := by simp [hcard]

theorem sum_centeredCoeffOn_eq_zero
    (S : Finset ℤ) (f : ℤ → ℂ) :
    ∑ t ∈ S, centeredCoeffOn S f t = 0 := by
  calc
    ∑ t ∈ S, centeredCoeffOn S f t
        = ∑ t ∈ S, (f t - coeffMeanOn S f) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            simp [centeredCoeffOn, ht]
    _ = (∑ t ∈ S, f t) - ∑ t ∈ S, coeffMeanOn S f := by
          rw [Finset.sum_sub_distrib]
    _ = (∑ t ∈ S, f t) - ∑ t ∈ S, meanChannelOn S f t := by
          congr 1
          symm
          refine Finset.sum_congr rfl ?_
          intro t ht
          simp [meanChannelOn, ht]
    _ = 0 := by
          rw [sum_meanChannelOn_eq_sum]
          ring

theorem weightedMinorCoeff_eq_zero_of_not_mem_tSupport
    (X N : ℕ) (t : ℤ) (ht : t ∉ tSupport N) :
    weightedMinorCoeff X N t = 0 := by
  unfold weightedMinorCoeff coeff
  have hempty : nmSupportOfT N t = ∅ := by
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
        have hnm_le :
            (nm.1 : ℤ) + (nm.2 : ℤ) ≤ (N : ℤ) + (N : ℤ) := add_le_add hn_leZ hm_leZ
        have :
            (nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ) ≤ (N : ℤ) := by
          have := sub_le_iff_le_add'.2 (by
            simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnm_le)
          simpa using this
        simpa [tFn] using this
      exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
    exact ht (htfn ▸ hmem)
  simp [hempty]

theorem tSupport_subset_windowMinorCoeffSupport
    {X N : ℕ} (hN : N ∈ minorWindow X) :
    tSupport N ⊆ windowMinorCoeffSupport X := by
  intro t ht
  rcases Finset.mem_Icc.mp ht with ⟨hl, hu⟩
  have hNle : N ≤ X + H := Goldbach.ProofTools.Windows.le_right_of_mem_EvenIn hN
  have hNleZ : (N : ℤ) ≤ ((X + H : ℕ) : ℤ) := by exact_mod_cast hNle
  have hneg : -(((X + H : ℕ) : ℤ)) ≤ -(N : ℤ) := by
    simpa using neg_le_neg hNleZ
  exact Finset.mem_Icc.mpr ⟨le_trans hneg hl, le_trans hu hNleZ⟩

theorem zeroModeSlice_apply_zero
    (X N : ℕ) :
    zeroModeSlice X N 0 = weightedMinorCoeff X N 0 := by
  simp [zeroModeSlice]

theorem zeroModeSlice_apply_ne_zero
    {X N : ℕ} {t : ℤ} (ht : t ≠ 0) :
    zeroModeSlice X N t = 0 := by
  simp [zeroModeSlice, ht]

theorem weightedNonzeroSlice_eq_coeffCentered_add_meanChannel
    (X N : ℕ) (t : ℤ) :
    weightedNonzeroSlice X N t
      = coeffCentered X N t + meanChannelSlice X N t := by
  by_cases ht : t ∈ canonicalMinorAmbientSupport X
  · have hcoeff :
      coeffCentered X N t
        =
      weightedMinorCoeff X N t
        - coeffMeanOn (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N) := by
        simpa [canonicalMinorAmbientSupport] using
          coeffCentered_eq_weightedMinorCoeff_sub_mean (X := X) (N := N) (t := t) ht
    have hproj : weightedNonzeroSlice X N t = weightedMinorCoeff X N t := by
      simpa [weightedNonzeroSlice, canonicalMinorAmbientSupport] using
        coeffZeroRemoved_apply_mem (X := X) (N := N)
          (show t ∈ (windowMinorCoeffSupport X).erase 0 by simpa [canonicalMinorAmbientSupport] using ht)
    have hmean : meanChannelSlice X N t = coeffMeanOn (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N) := by
      exact meanChannelOn_apply_mem ht
    rw [hproj, hcoeff, hmean]
    ring
  · have hproj : weightedNonzeroSlice X N t = 0 := by
      simpa [weightedNonzeroSlice, canonicalMinorAmbientSupport] using
        coeffZeroRemoved_apply_not_mem (X := X) (N := N)
          (show t ∉ (windowMinorCoeffSupport X).erase 0 by simpa [canonicalMinorAmbientSupport] using ht)
    have hcenter : coeffCentered X N t = 0 := by
      exact centeredCoeffOn_apply_not_mem (S := canonicalMinorAmbientSupport X)
        (f := weightedMinorCoeff X N) ht
    have hmean : meanChannelSlice X N t = 0 := by
      exact meanChannelOn_apply_not_mem ht
    rw [hproj, hcenter, hmean]
    ring

theorem coeffCentered_eq_coeffArith_add_weightChannel
    (X N : ℕ) (t : ℤ) :
    coeffCentered X N t = coeffArith X N t + weightChannelSlice X N t := by
  unfold weightChannelSlice
  rw [coeffArith_eq_coeffCentered_sub_alpha_mul_weightCentered]
  ring

theorem weightedMinorCoeff_eq_zeroMode_add_weightedNonzero
    {X N : ℕ} (hN : N ∈ minorWindow X) (t : ℤ) :
    weightedMinorCoeff X N t
      = zeroModeSlice X N t + weightedNonzeroSlice X N t := by
  by_cases hzero : t = 0
  · subst t
    have hnonzero : weightedNonzeroSlice X N 0 = 0 := by
      simpa [weightedNonzeroSlice, canonicalMinorAmbientSupport] using
        coeffZeroRemoved_apply_not_mem (X := X) (N := N)
          (by simp)
    rw [zeroModeSlice_apply_zero, hnonzero]
    ring
  · have hzeroSlice : zeroModeSlice X N t = 0 := zeroModeSlice_apply_ne_zero hzero
    by_cases htAmbient : t ∈ canonicalMinorAmbientSupport X
    · have hproj : weightedNonzeroSlice X N t = weightedMinorCoeff X N t := by
        simpa [weightedNonzeroSlice] using
          coeffZeroRemoved_apply_mem (X := X) (N := N)
            (show t ∈ (windowMinorCoeffSupport X).erase 0 by
              simpa [canonicalMinorAmbientSupport] using htAmbient)
      rw [hzeroSlice, zero_add, hproj]
    · have hnotSupport : t ∉ tSupport N := by
        intro htSupport
        have hwin : t ∈ windowMinorCoeffSupport X := tSupport_subset_windowMinorCoeffSupport hN htSupport
        exact htAmbient (by simpa [canonicalMinorAmbientSupport, hzero] using Finset.mem_erase.mpr ⟨hzero, hwin⟩)
      have hcoeff : weightedMinorCoeff X N t = 0 := weightedMinorCoeff_eq_zero_of_not_mem_tSupport X N t hnotSupport
      have hproj : weightedNonzeroSlice X N t = 0 := by
        simpa [weightedNonzeroSlice, canonicalMinorAmbientSupport] using
          coeffZeroRemoved_apply_not_mem (X := X) (N := N)
            (show t ∉ (windowMinorCoeffSupport X).erase 0 by
              simpa [canonicalMinorAmbientSupport] using htAmbient)
      rw [hcoeff, hzeroSlice, zero_add, hproj]

theorem weightedMinorCoeff_eq_zero_add_mean_add_weight_add_arith
    {X N : ℕ} (hN : N ∈ minorWindow X) (t : ℤ) :
    weightedMinorCoeff X N t
      =
    zeroModeSlice X N t
      + meanChannelSlice X N t
      + weightChannelSlice X N t
      + coeffArith X N t := by
  rw [weightedMinorCoeff_eq_zeroMode_add_weightedNonzero hN t]
  rw [weightedNonzeroSlice_eq_coeffCentered_add_meanChannel]
  rw [coeffCentered_eq_coeffArith_add_weightChannel]
  ring

theorem coeffCentered_sliceSum_eq_zero
    (X N : ℕ) :
    familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => coeffCentered X N t) N = 0 := by
  unfold familySliceSumOn
  exact sum_centeredCoeffOn_eq_zero (canonicalMinorAmbientSupport X) (weightedMinorCoeff X N)

theorem weightCentered_sliceSum_eq_zero
    (X : ℕ) (N : ℕ) :
    familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => weightCentered X t) N = 0 := by
  unfold familySliceSumOn
  exact sum_centeredCoeffOn_eq_zero (canonicalMinorAmbientSupport X) (weightCoeff X)

theorem coeffArith_sliceSum_eq_zero
    (X N : ℕ) :
    familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => coeffArith X N t) N = 0 := by
  unfold familySliceSumOn coeffArith
  rw [Finset.sum_sub_distrib]
  have hcenter :
      ∑ x ∈ canonicalMinorAmbientSupport X, coeffCentered X N x = 0 := by
        simpa [familySliceSumOn] using coeffCentered_sliceSum_eq_zero X N
  have hweight :
      ∑ x ∈ canonicalMinorAmbientSupport X, weightRegressionAlpha X N * weightCentered X x = 0 := by
        rw [← Finset.mul_sum]
        have hwsum : ∑ i ∈ canonicalMinorAmbientSupport X, weightCentered X i = 0 := by
          simpa [familySliceSumOn] using weightCentered_sliceSum_eq_zero X N
        rw [hwsum]
        simp
  rw [hcenter, hweight]
  simp

theorem weightedNonzeroSlice_sliceSum_eq_meanChannelSlice_sliceSum
    (X N : ℕ) :
    familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => weightedNonzeroSlice X N t) N
      =
    familySliceSumOn (canonicalMinorAmbientSupport X) (fun _ t => meanChannelSlice X N t) N := by
  unfold familySliceSumOn
  calc
    ∑ t ∈ canonicalMinorAmbientSupport X, weightedNonzeroSlice X N t
        =
      ∑ t ∈ canonicalMinorAmbientSupport X,
        (coeffCentered X N t + meanChannelSlice X N t) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [weightedNonzeroSlice_eq_coeffCentered_add_meanChannel]
    _ =
      (∑ t ∈ canonicalMinorAmbientSupport X, coeffCentered X N t)
        + ∑ t ∈ canonicalMinorAmbientSupport X, meanChannelSlice X N t := by
          rw [Finset.sum_add_distrib]
    _ =
      ∑ t ∈ canonicalMinorAmbientSupport X, meanChannelSlice X N t := by
          have hzero : ∑ t ∈ canonicalMinorAmbientSupport X, coeffCentered X N t = 0 := by
            simpa [familySliceSumOn] using coeffCentered_sliceSum_eq_zero X N
          rw [hzero]
          simp

end

end Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
