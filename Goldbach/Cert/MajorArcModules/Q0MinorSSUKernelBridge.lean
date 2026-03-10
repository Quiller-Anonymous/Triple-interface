import Goldbach.BG_Identity
import Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic

/-!
Kernel-weighted deterministic bridge for the `Q0`-minor SSU piece.

`Q0MinorSSUDeterministic` rewrites the nonzero minor residual as a `k`-sum whose summands still
carry the kernel coefficient `KHatH(k)`. This file factors those coefficients out and applies a
finite Cauchy-Schwarz reduction:

* isolate the unweighted major nonzero `k`-slice;
* show the kernel square-mass on `kSupport N` is at most `1`;
* bound the SSU square by the corresponding unweighted slice-square sum.

No numerical TT*/Toeplitz estimate appears here yet. This is the deterministic seam from the
minor SSU object to the major-side nonzero slice energy.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSSUKernelBridge

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

/-- The nonzero major `k`-slice before inserting the outer kernel coefficient `KHatH(k)`. -/
noncomputable def majorCoreSliceNZ (X N : ℕ) (k : ℤ) : ℂ :=
  ∑ nm ∈ nmSupportOfKNZ N k,
    aTerm X nm.1 * aTerm X nm.2
      * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
          (tFn N nm)

private theorem norm_sum_mul_sq_le_sum_sq_mul_sum_sq
    {ι : Type} (s : Finset ι) (b w : ι → ℂ) :
    ‖∑ i ∈ s, b i * w i‖ ^ 2 ≤ (∑ i ∈ s, ‖b i‖ ^ 2) * ∑ i ∈ s, ‖w i‖ ^ 2 := by
  classical
  have htri : ‖∑ i ∈ s, b i * w i‖ ≤ ∑ i ∈ s, ‖b i * w i‖ := by
    simpa using (norm_sum_le (s := s) (f := fun i => b i * w i))
  have htri' : ‖∑ i ∈ s, b i * w i‖ ≤ ∑ i ∈ s, ‖b i‖ * ‖w i‖ := by
    simpa [norm_mul] using htri
  have hsq :
      ‖∑ i ∈ s, b i * w i‖ ^ 2 ≤ (∑ i ∈ s, ‖b i‖ * ‖w i‖) ^ 2 := by
    have h0a : 0 ≤ ‖∑ i ∈ s, b i * w i‖ := norm_nonneg _
    have h0b : 0 ≤ ∑ i ∈ s, ‖b i‖ * ‖w i‖ := by
      exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have :
        ‖∑ i ∈ s, b i * w i‖ * ‖∑ i ∈ s, b i * w i‖
          ≤
        (∑ i ∈ s, ‖b i‖ * ‖w i‖) * (∑ i ∈ s, ‖b i‖ * ‖w i‖) :=
      mul_le_mul htri' htri' h0a h0b
    simpa [pow_two] using this
  have hcs :
      (∑ i ∈ s, ‖b i‖ * ‖w i‖) ^ 2
        ≤
      (∑ i ∈ s, ‖b i‖ ^ 2) * ∑ i ∈ s, ‖w i‖ ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := s) (f := fun i => ‖b i‖) (g := fun i => ‖w i‖))
  exact le_trans hsq hcs

private lemma mem_S_BG_neg_iff (k : ℤ) :
    -k ∈ Goldbach.BG_Identity.S_BG ↔ k ∈ Goldbach.BG_Identity.S_BG := by
  rw [Goldbach.BG_Identity.mem_S_BG_iff, Goldbach.BG_Identity.mem_S_BG_iff]
  constructor
  · intro hk
    omega
  · intro hk
    omega

private lemma KHatH_eq_of_mem_S_BG {k : ℤ} (hk : k ∈ Goldbach.BG_Identity.S_BG) :
    KHatH k = (Goldbach.BG_Identity.K_full k : ℂ) := by
  have hkneg : -k ∈ Goldbach.BG_Identity.S_BG := (mem_S_BG_neg_iff k).2 hk
  unfold KHatH Goldbach.Cert.MajorArcStep10RLSmoothIntegral.coeffC
  rw [Goldbach.Cert.MajorArcStep9CorrelationIntegral.coeff_eq]
  simp [hkneg, Goldbach.BG_Identity.K_full_neg]

private lemma KHatH_eq_zero_of_not_mem_S_BG {k : ℤ} (hk : k ∉ Goldbach.BG_Identity.S_BG) :
    KHatH k = 0 := by
  have hkneg : -k ∉ Goldbach.BG_Identity.S_BG := by
    intro hkneg
    exact hk ((mem_S_BG_neg_iff k).1 hkneg)
  unfold KHatH Goldbach.Cert.MajorArcStep10RLSmoothIntegral.coeffC
  rw [Goldbach.Cert.MajorArcStep9CorrelationIntegral.coeff_eq]
  simp [hkneg]

private lemma norm_KHatH_le_one (k : ℤ) : ‖KHatH k‖ ≤ 1 := by
  by_cases hk : k ∈ Goldbach.BG_Identity.S_BG
  · rw [KHatH_eq_of_mem_S_BG hk]
    have hpeak :=
      Goldbach.BG_Identity.K_full_peak_le (U := Goldbach.BG_Identity.Ucut) (k := k)
    have hnonneg : 0 ≤ Goldbach.BG_Identity.K_full k := Goldbach.BG_Identity.K_full_nonneg k
    have hraw_nonneg : 0 ≤ Goldbach.BG_Identity.K_full_raw Goldbach.BG_Identity.Ucut k := by
      simpa [Goldbach.BG_Identity.K_full] using hnonneg
    have hU : ((Goldbach.BG_Identity.Ucut : ℝ)⁻¹) ≤ 1 := by
      have hUpos : (1 : ℝ) ≤ (Goldbach.BG_Identity.Ucut : ℝ) := by
        exact_mod_cast (show 1 ≤ Goldbach.BG_Identity.Ucut by
          have : 0 < Goldbach.BG_Identity.Ucut := by
            have hHpos : 0 < H := by simp [H]
            have hle : H ≤ Goldbach.BG_Identity.Ucut := by simp [Goldbach.BG_Identity.Ucut]
            exact lt_of_lt_of_le hHpos hle
          omega)
      exact (inv_le_one₀ (by positivity)).2 hUpos
    calc
      ‖(Goldbach.BG_Identity.K_full k : ℂ)‖ = Goldbach.BG_Identity.K_full k := by
        simp [hnonneg]
      _ ≤ (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
        have hpeak' :
            Goldbach.BG_Identity.K_full_raw Goldbach.BG_Identity.Ucut k
              ≤ (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
          rw [abs_of_nonneg hraw_nonneg] at hpeak
          exact hpeak
        simpa [Goldbach.BG_Identity.K_full] using hpeak'
      _ ≤ 1 := hU
  · rw [KHatH_eq_zero_of_not_mem_S_BG hk]
    simp

private lemma sum_norm_KHatH_le_one (N : ℕ) :
    (∑ k ∈ kSupport N, ‖KHatH k‖) ≤ 1 := by
  classical
  let s : Finset ℤ := (kSupport N).filter (fun k => k ∈ Goldbach.BG_Identity.S_BG)
  have hs :
      (∑ k ∈ kSupport N, ‖KHatH k‖) = ∑ k ∈ s, ‖KHatH k‖ := by
    have :
        (∑ k ∈ kSupport N, ‖KHatH k‖)
          =
        ∑ k ∈ kSupport N,
          if k ∈ Goldbach.BG_Identity.S_BG then ‖KHatH k‖ else 0 := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      by_cases hkS : k ∈ Goldbach.BG_Identity.S_BG
      · simp [hkS]
      · simp [hkS, KHatH_eq_zero_of_not_mem_S_BG]
    rw [this]
    simpa [s, Finset.sum_filter] using
      (Finset.sum_filter (s := kSupport N) (p := fun k => k ∈ Goldbach.BG_Identity.S_BG)
        (f := fun k => ‖KHatH k‖)).symm
  rw [hs]
  have hsub : s ⊆ Goldbach.BG_Identity.S_BG := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hnonneg : ∀ k : ℤ, 0 ≤ Goldbach.BG_Identity.K_full k := Goldbach.BG_Identity.K_full_nonneg
  have hle :
      (∑ k ∈ s, ‖KHatH k‖) ≤ ∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k := by
    calc
      (∑ k ∈ s, ‖KHatH k‖)
          = ∑ k ∈ s, Goldbach.BG_Identity.K_full k := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [KHatH_eq_of_mem_S_BG ((Finset.mem_filter.mp hk).2)]
            simp [Goldbach.BG_Identity.K_full_nonneg k]
      _ ≤ ∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hnonneg k)
  have hmass_le_one :
      (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k) ≤ 1 := by
    have hsplit := Goldbach.BG_Identity.sum_bandU_outer_inner (f := fun k => Goldbach.BG_Identity.K_full k)
    have houter_nonneg : 0 ≤ ∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k := by
      exact Finset.sum_nonneg (fun _ hk => Goldbach.BG_Identity.K_full_nonneg_outer hk)
    have hfull :
        (∑ k ∈ Goldbach.BG_Identity.bandU, Goldbach.BG_Identity.K_full k) = 1 := by
      simpa [Goldbach.BG_Identity.tentFullMass, Goldbach.BG_Identity.tentFullWeight] using
        Goldbach.BG_Identity.tentFullMass_eq_one
    have :
        (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k)
          ≤
        (∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k)
          + (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k) := by
      simpa using add_le_add_right houter_nonneg
    calc
      (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k)
          ≤
        (∑ k ∈ Goldbach.BG_Identity.outerBand, Goldbach.BG_Identity.K_full k)
          + (∑ k ∈ Goldbach.BG_Identity.S_BG, Goldbach.BG_Identity.K_full k) := this
      _ = 1 := by simpa [hsplit] using hfull
  exact le_trans hle hmass_le_one

private lemma sum_sq_norm_KHatH_le_one (N : ℕ) :
    (∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2) ≤ 1 := by
  calc
    (∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2)
        ≤ ∑ k ∈ kSupport N, ‖KHatH k‖ := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk0 : 0 ≤ ‖KHatH k‖ := norm_nonneg _
          have hk1 : ‖KHatH k‖ ≤ 1 := norm_KHatH_le_one k
          nlinarith
    _ ≤ 1 := sum_norm_KHatH_le_one N

theorem majorSliceNZ_eq_core_mul_KHatH (X N : ℕ) (k : ℤ) :
    majorSliceNZ X N k = majorCoreSliceNZ X N k * KHatH k := by
  unfold majorSliceNZ majorCoreSliceNZ majorAtom
  have hterm :
      ∀ nm ∈ nmSupportOfKNZ N k,
        aTerm X nm.1 * aTerm X nm.2
            * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
                (tFn N nm)
            * KHatH (kFn nm)
          =
        (aTerm X nm.1 * aTerm X nm.2
            * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
                (tFn N nm))
          * KHatH k := by
    intro nm hnm
    rcases mem_nmSupportOfKNZ_iff.mp hnm with ⟨_hn, _hm, hk, _ht0⟩
    simp [hk, mul_assoc]
  calc
    ∑ nm ∈ nmSupportOfKNZ N k,
        aTerm X nm.1 * aTerm X nm.2
          * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
              (tFn N nm)
          * KHatH (kFn nm)
      =
    ∑ nm ∈ nmSupportOfKNZ N k,
        (aTerm X nm.1 * aTerm X nm.2
          * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
              (tFn N nm))
        * KHatH k := by
          refine Finset.sum_congr rfl ?_
          intro nm hnm
          exact hterm nm hnm
    _ = majorCoreSliceNZ X N k * KHatH k := by
          have hmul :
              (∑ nm ∈ nmSupportOfKNZ N k,
                  (aTerm X nm.1 * aTerm X nm.2
                    * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
                        (tFn N nm))
                    * KHatH k)
                =
              (∑ nm ∈ nmSupportOfKNZ N k,
                  aTerm X nm.1 * aTerm X nm.2
                    * Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra.majorArcWeightFourier X Δ_canon
                        (tFn N nm))
                * KHatH k := by
            simpa [Finset.sum_mul]
          simpa [majorCoreSliceNZ] using hmul

theorem ssuPart_norm_sq_le_q0NormFactor_sq_mul_sum_sq_core (X N : ℕ) :
    ‖canonicalExpansion.ssuPart X N‖ ^ 2
      ≤
    ‖q0NormFactor N‖ ^ 2 * (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2) := by
  have hrepr :=
    ssuPart_eq_neg_q0NormFactor_mul_sum_kSlicesNZ (X := X) (N := N)
  rw [hrepr]
  have hcore :
      (∑ k ∈ kSupport N, majorSliceNZ X N k)
        =
      ∑ k ∈ kSupport N, majorCoreSliceNZ X N k * KHatH k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact majorSliceNZ_eq_core_mul_KHatH (X := X) (N := N) (k := k)
  rw [hcore]
  calc
    ‖-q0NormFactor N * ∑ k ∈ kSupport N, majorCoreSliceNZ X N k * KHatH k‖ ^ 2
        = ‖q0NormFactor N‖ ^ 2 * ‖∑ k ∈ kSupport N, majorCoreSliceNZ X N k * KHatH k‖ ^ 2 := by
            rw [norm_mul, norm_neg, pow_two, pow_two]
            ring
    _ ≤ ‖q0NormFactor N‖ ^ 2
          * ((∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2)
              * ∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2) := by
            have hcs :
                ‖∑ k ∈ kSupport N, majorCoreSliceNZ X N k * KHatH k‖ ^ 2
                  ≤
                (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2)
                  * ∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2 := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
                  (s := kSupport N) (b := fun k => majorCoreSliceNZ X N k) (w := fun k => KHatH k))
            exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ ≤ ‖q0NormFactor N‖ ^ 2 * ((∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2) * 1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (sum_sq_norm_KHatH_le_one N)
                (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
              (sq_nonneg _)
    _ = ‖q0NormFactor N‖ ^ 2 * (∑ k ∈ kSupport N, ‖majorCoreSliceNZ X N k‖ ^ 2) := by
            rw [mul_one]

end

end Goldbach.Cert.MajorArcModules.Q0MinorSSUKernelBridge
