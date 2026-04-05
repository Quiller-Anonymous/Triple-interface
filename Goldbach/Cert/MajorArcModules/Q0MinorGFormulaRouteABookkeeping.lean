import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
import Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
import Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
import Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA
import Goldbach.Cert.MajorArcModules.Q0TwoBoundsConventionalAxioms
import Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
import Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizedEnergy
import Goldbach.PPBoundCore

/-!
Route-A-native theorem surface for the frozen geometric witness `G_formula`.

The current repo's exact Route A resources speak naturally in terms of Route-A-shaped upper bounds,
not directly in terms of `MeanChannelApproxTarget`.  This file introduces that intermediate
geometric theorem surface and then derives the bridge-facing mean-channel approximation target as a
corollary.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorGFormulaRouteA

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorRouteVisibleDecomposition
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.Q0MinorSSUFromCert
open Goldbach.Cert.MajorArcModules.Q0MinorSSUDeterministic
open Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedDecomposition
open Goldbach.Cert.MajorArcModules.Q0MinorWeightedChannelBridge

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private lemma geometricMem_tSupport_of_mem_s {N n m : ℕ}
    (hn : n ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N)
    (hm : m ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N) :
    ((n : ℤ) + (m : ℤ) - (N : ℤ)) ∈ Q0MinorTTStarFrequencyExpansion.tSupport N := by
  have hn_le : n ≤ N := by
    have hn_le' : n ≤ N - 2 := (Finset.mem_Icc.mp hn).2
    exact le_trans hn_le' (Nat.sub_le N 2)
  have hm_le : m ≤ N := by
    have hm_le' : m ≤ N - 2 := (Finset.mem_Icc.mp hm).2
    exact le_trans hm_le' (Nat.sub_le N 2)
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Nat.zero_le m)
  have hn_leZ : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn_le
  have hm_leZ : (m : ℤ) ≤ (N : ℤ) := by exact_mod_cast hm_le
  have hlower : (-(N : ℤ)) ≤ (n : ℤ) + (m : ℤ) - (N : ℤ) := by
    have hnm0 : (0 : ℤ) ≤ (n : ℤ) + (m : ℤ) := add_nonneg hn0 hm0
    have := sub_le_sub_right hnm0 (N : ℤ)
    simpa using this
  have hupper : (n : ℤ) + (m : ℤ) - (N : ℤ) ≤ (N : ℤ) := by
    have hnm_le : (n : ℤ) + (m : ℤ) ≤ (N : ℤ) + (N : ℤ) := add_le_add hn_leZ hm_leZ
    have : (n : ℤ) + (m : ℤ) - (N : ℤ) ≤ (N : ℤ) := by
      have := sub_le_iff_le_add'.2 (by simpa [two_mul, add_assoc, add_left_comm, add_comm] using hnm_le)
      simpa using this
    exact this
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

private lemma geometricMem_tSupport_of_mem_nmSupport {N : ℕ} {nm : ℕ × ℕ}
    (hnm : nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N) :
    Q0MinorTTStarFrequencyExpansion.tFn N nm ∈ Q0MinorTTStarFrequencyExpansion.tSupport N := by
  have hmem : nm.1 ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N
      ∧ nm.2 ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N := by
    simpa [Q0MinorTTStarFrequencyExpansion.nmSupport] using hnm
  exact geometricMem_tSupport_of_mem_s hmem.1 hmem.2

private lemma mem_S_BG_neg_iff (k : ℤ) :
    -k ∈ Goldbach.BG_Identity.S_BG ↔ k ∈ Goldbach.BG_Identity.S_BG := by
  rw [Goldbach.BG_Identity.mem_S_BG_iff, Goldbach.BG_Identity.mem_S_BG_iff]
  constructor <;> intro hk <;> omega

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
    have hsplit :=
      Goldbach.BG_Identity.sum_bandU_outer_inner (f := fun k => Goldbach.BG_Identity.K_full k)
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

private lemma norm_minorArcWeightC_le_one (X : ℕ) (Δ : ℝ) (α : ℝ) :
    ‖Q0MinorTTStarAlgebra.minorArcWeightC X Δ α‖ ≤ 1 := by
  unfold Q0MinorTTStarAlgebra.minorArcWeightC
  by_cases hα : α ∈ (Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ)ᶜ
  · simp [hα]
  · simp [hα]

private lemma norm_minorArcWeightFourier_le_one (X : ℕ) (Δ : ℝ) (t : ℤ) :
    ‖Q0MinorTTStarAlgebra.minorArcWeightFourier X Δ t‖ ≤ 1 := by
  have hconst :
      ∀ α ∈ Set.uIoc (0 : ℝ) 1,
        ‖Q0MinorTTStarAlgebra.minorArcWeightC X Δ α
          * (fourier (T := (1 : ℝ)) t
              (α : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)‖ ≤ 1 := by
    intro α hα
    have hchar : ‖(fourier (T := (1 : ℝ)) t
        (α : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)‖ = 1 := by
      simpa [fourier_apply] using
        (Circle.norm_coe
          (AddCircle.toCircle (t • (α : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC))))
    calc
      ‖Q0MinorTTStarAlgebra.minorArcWeightC X Δ α
          * (fourier (T := (1 : ℝ)) t
              (α : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)‖
          =
        ‖Q0MinorTTStarAlgebra.minorArcWeightC X Δ α‖
          * ‖(fourier (T := (1 : ℝ)) t
              (α : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)‖ := by
            rw [norm_mul]
      _ = ‖Q0MinorTTStarAlgebra.minorArcWeightC X Δ α‖ := by rw [hchar, mul_one]
      _ ≤ 1 := norm_minorArcWeightC_le_one X Δ α
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := (1 : ℝ))
      (f := fun α : ℝ =>
        Q0MinorTTStarAlgebra.minorArcWeightC X Δ α
          * (fourier (T := (1 : ℝ)) t
              (α : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ))
      hconst
  simpa [Q0MinorTTStarAlgebra.minorArcWeightFourier] using h

/-- The surrogate TT* atom carried by the frozen geometric witness before the outer `q0` factor. -/
noncomputable def geometricAtom (X N : ℕ) (nm : ℕ × ℕ) : ℂ :=
  uniformWindowScalarWeight X nm.1
    * uniformWindowScalarWeight X nm.2
    * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon (Q0MinorTTStarFrequencyExpansion.tFn N nm)
    * KHatH (Q0MinorTTStarFrequencyExpansion.kFn nm)

/-- The nonzero `k`-slice of the frozen geometric surrogate before inserting `KHatH(k)`. -/
noncomputable def geometricCoreSliceNZ (X N : ℕ) (k : ℤ) : ℂ :=
  ∑ nm ∈ nmSupportOfKNZ N k,
    uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2
      * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon (Q0MinorTTStarFrequencyExpansion.tFn N nm)

/-- The kernel-weighted nonzero `k`-slice of the frozen geometric surrogate. -/
noncomputable def geometricSliceNZ (X N : ℕ) (k : ℤ) : ℂ :=
  ∑ nm ∈ nmSupportOfKNZ N k, geometricAtom X N nm

private lemma norm_uniformWindowSupportIndicator_le_one (X n : ℕ) :
    ‖uniformWindowSupportIndicator X n‖ ≤ 1 := by
  unfold uniformWindowSupportIndicator
  by_cases hn : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
  · simp [hn]
  · simp [hn]

private lemma norm_uniformWindowScalarWeight_le_normalization (X n : ℕ) :
    ‖uniformWindowScalarWeight X n‖ ≤ ‖uniformWindowNormalization X‖ := by
  rw [uniformWindowScalarWeight_eq_normalization_mul_indicator]
  rw [norm_mul]
  calc
    ‖uniformWindowNormalization X‖ * ‖uniformWindowSupportIndicator X n‖
        ≤ ‖uniformWindowNormalization X‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (norm_uniformWindowSupportIndicator_le_one X n) (norm_nonneg _)
    _ = ‖uniformWindowNormalization X‖ := by ring

private lemma geometricAtom_eq_zero_of_fst_not_mem_window
    (X N : ℕ) (nm : ℕ × ℕ)
    (hn : nm.1 ∉ Finset.Icc (X / 2 - H) (X / 2 + H)) :
    geometricAtom X N nm = 0 := by
  unfold geometricAtom uniformWindowScalarWeight
  simp [hn]

private lemma geometricAtom_eq_zero_of_snd_not_mem_window
    (X N : ℕ) (nm : ℕ × ℕ)
    (hm : nm.2 ∉ Finset.Icc (X / 2 - H) (X / 2 + H)) :
    geometricAtom X N nm = 0 := by
  unfold geometricAtom uniformWindowScalarWeight
  simp [hm]

private lemma norm_geometricAtom_le_uniformWindowNormalization_sq
    (X N : ℕ) (nm : ℕ × ℕ) :
    ‖geometricAtom X N nm‖ ≤ ‖uniformWindowNormalization X‖ ^ 2 := by
  unfold geometricAtom
  repeat rw [norm_mul]
  have hw1 := norm_uniformWindowScalarWeight_le_normalization X nm.1
  have hw2 := norm_uniformWindowScalarWeight_le_normalization X nm.2
  have hminor := norm_minorArcWeightFourier_le_one X TurnkeyRouteQ0.Δ_canon
    (Q0MinorTTStarFrequencyExpansion.tFn N nm)
  have hk := norm_KHatH_le_one (Q0MinorTTStarFrequencyExpansion.kFn nm)
  let A : ℝ := ‖uniformWindowScalarWeight X nm.1‖ * ‖uniformWindowScalarWeight X nm.2‖
  let B : ℝ :=
    ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon (Q0MinorTTStarFrequencyExpansion.tFn N nm)‖
      * ‖KHatH (Q0MinorTTStarFrequencyExpansion.kFn nm)‖
  let U : ℝ := ‖uniformWindowNormalization X‖
  have h12 :
      A ≤ U * U := by
    exact mul_le_mul hw1 hw2 (norm_nonneg _) (norm_nonneg _)
  have h34 :
      B ≤ 1 * 1 := by
    exact mul_le_mul hminor hk (norm_nonneg _) (by norm_num)
  have hprod :
      A * B ≤ (U * U) * (1 * 1) := by
    have hcd_nonneg :
        0 ≤ B := by
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hb_nonneg :
        0 ≤ U * U := by
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact mul_le_mul h12 h34 hcd_nonneg hb_nonneg
  have hfinal : A * B ≤ U ^ 2 := by
    simpa [pow_two] using hprod
  simpa [A, B, U, pow_two, mul_assoc, mul_left_comm, mul_comm] using hfinal

private lemma geometricWeightedMinorCoeff_eq_zero_of_not_mem_tSupport
    (X N : ℕ) (t : ℤ) (ht : t ∉ Q0MinorTTStarFrequencyExpansion.tSupport N) :
    geometricWeightedMinorCoeff X N t = 0 := by
  unfold geometricWeightedMinorCoeff
  have hempty : Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro nm hnm
    rcases Q0MinorTTStarFrequencyExpansion.mem_nmSupportOfT_iff.mp hnm with ⟨hn, hm, htfn⟩
    have hmem : Q0MinorTTStarFrequencyExpansion.tFn N nm ∈ Q0MinorTTStarFrequencyExpansion.tSupport N := by
      exact geometricMem_tSupport_of_mem_s hn hm
    exact ht (htfn ▸ hmem)
  simp [hempty]

/--
Exact nonzero-frequency TT* support seen by the frozen geometric surrogate.

This is the same finite nonzero `t` support used by the SSU deterministic reduction, but with the
hard arithmetic `aTerm` coefficients replaced by the uniform-window surrogate weights.
-/
noncomputable def geometricNmSupportNZ (N : ℕ) : Finset (ℕ × ℕ) :=
  (Q0MinorTTStarFrequencyExpansion.nmSupport N).filter
    (fun nm => Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0)

/-- The actual surrogate support: nonzero TT* pairs whose two coordinates lie in the frozen window. -/
noncomputable def geometricWindowNmSupportNZ (X N : ℕ) : Finset (ℕ × ℕ) :=
  (geometricNmSupportNZ N).filter
    (fun nm =>
      nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
        ∧ nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H))

lemma mem_geometricNmSupportNZ_iff {N : ℕ} {nm : ℕ × ℕ} :
    nm ∈ geometricNmSupportNZ N
      ↔
    nm.1 ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N
      ∧ nm.2 ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N
      ∧ Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0 := by
  simp [geometricNmSupportNZ, Q0MinorTTStarFrequencyExpansion.nmSupport, and_left_comm, and_assoc,
    and_comm]

lemma mem_geometricWindowNmSupportNZ_iff {X N : ℕ} {nm : ℕ × ℕ} :
    nm ∈ geometricWindowNmSupportNZ X N
      ↔
    nm ∈ geometricNmSupportNZ N
      ∧ nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
      ∧ nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by
  simp [geometricWindowNmSupportNZ, and_left_comm, and_assoc, and_comm]

theorem sum_geometricNmSupportNZ_eq_sum_geometricWindowNmSupportNZ
    (X N : ℕ) :
    (∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm)
      =
    ∑ nm ∈ geometricWindowNmSupportNZ X N, geometricAtom X N nm := by
  have hsplit :
      (∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm)
        =
      ∑ nm ∈ geometricNmSupportNZ N,
        if nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
            ∧ nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
          then geometricAtom X N nm else 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    by_cases hwin : nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
        ∧ nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
    · simp [hwin]
    · have hzero : geometricAtom X N nm = 0 := by
        rcases not_and_or.mp hwin with hleft | hright
        · exact geometricAtom_eq_zero_of_fst_not_mem_window X N nm hleft
        · exact geometricAtom_eq_zero_of_snd_not_mem_window X N nm hright
      simp [hwin, hzero]
  rw [hsplit]
  simpa [geometricWindowNmSupportNZ, Finset.sum_filter] using
    (Finset.sum_filter
      (s := geometricNmSupportNZ N)
      (p := fun nm =>
        nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
          ∧ nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H))
      (f := fun nm => geometricAtom X N nm)).symm

private theorem geometricSum_nmSupport_eq_sum_tSupport
    (X N : ℕ) :
    (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N, geometricAtom X N nm)
      =
    ∑ t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N,
      ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t, geometricAtom X N nm := by
  classical
  have hrewrite :
      (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N, geometricAtom X N nm)
        =
      ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
        ∑ t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    have htmem :
        Q0MinorTTStarFrequencyExpansion.tFn N nm ∈ Q0MinorTTStarFrequencyExpansion.tSupport N :=
      geometricMem_tSupport_of_mem_nmSupport hnm
    simpa using
      (Finset.sum_ite_eq_of_mem (s := Q0MinorTTStarFrequencyExpansion.tSupport N)
        (a := Q0MinorTTStarFrequencyExpansion.tFn N nm)
        (b := fun _ : ℤ => geometricAtom X N nm) htmem).symm
  have hswap :
      (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ∑ t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N,
            ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
        =
      ∑ t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N,
        ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm
        (s := Q0MinorTTStarFrequencyExpansion.nmSupport N)
        (t := Q0MinorTTStarFrequencyExpansion.tSupport N)
        (f := fun nm t =>
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0))
  have hfilter (t : ℤ) :
      (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
        =
      ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t, geometricAtom X N nm := by
    have :
        (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
            ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
          =
        ∑ nm ∈ (Q0MinorTTStarFrequencyExpansion.nmSupport N).filter
            (fun nm => Q0MinorTTStarFrequencyExpansion.tFn N nm = t), geometricAtom X N nm := by
      simpa [Finset.sum_filter] using
        (Finset.sum_filter
          (s := Q0MinorTTStarFrequencyExpansion.nmSupport N)
          (p := fun nm => Q0MinorTTStarFrequencyExpansion.tFn N nm = t)
          (f := fun nm => geometricAtom X N nm)).symm
    simpa [Q0MinorTTStarFrequencyExpansion.nmSupportOfT, Q0MinorTTStarFrequencyExpansion.tFn] using this
  calc
    (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N, geometricAtom X N nm)
        =
      ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
        ∑ t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0 := hrewrite
    _ =
      ∑ t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N,
        ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0 := hswap
    _ =
      ∑ t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N,
        ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t, geometricAtom X N nm := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      exact hfilter t

private theorem geometricSum_tSupport_erase_zero_eq_sum_nmSupportNZ
    (X N : ℕ) :
    (∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
        ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t, geometricAtom X N nm)
      =
    ∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm := by
  classical
  have hstep1 :
      (∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
          ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t, geometricAtom X N nm)
        =
      ∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
        ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0 := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    have :
        (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t, geometricAtom X N nm)
          =
        ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0 := by
      have :
          (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
              ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
            =
          ∑ nm ∈ (Q0MinorTTStarFrequencyExpansion.nmSupport N).filter
              (fun nm => Q0MinorTTStarFrequencyExpansion.tFn N nm = t), geometricAtom X N nm := by
        simpa [Finset.sum_filter] using
          (Finset.sum_filter
            (s := Q0MinorTTStarFrequencyExpansion.nmSupport N)
            (p := fun nm => Q0MinorTTStarFrequencyExpansion.tFn N nm = t)
            (f := fun nm => geometricAtom X N nm)).symm
      simpa [Q0MinorTTStarFrequencyExpansion.nmSupportOfT, Q0MinorTTStarFrequencyExpansion.tFn] using this.symm
    exact this
  rw [hstep1]
  have hswap :
      (∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
          ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
            ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
        =
      ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
        ∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm
        (s := (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0)
        (t := Q0MinorTTStarFrequencyExpansion.nmSupport N)
        (f := fun t nm =>
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0))
  rw [hswap]
  have hstep2 :
      (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
            ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
        =
      ∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm := by
    have :
        (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
            ∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
              ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
          =
        ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0)
            (∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
              ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
            0 := by
      refine Finset.sum_congr rfl ?_
      intro nm hnm
      by_cases ht0 : Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0
      · simp [ht0]
      · simp [ht0]
    rw [this]
    have hfilter :
        (∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupport N,
            ite (Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0)
              (∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
                ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)
              0)
          =
        ∑ nm ∈ geometricNmSupportNZ N,
          (∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
            ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0) := by
      simpa [geometricNmSupportNZ, Finset.sum_filter] using
        (Finset.sum_filter
          (s := Q0MinorTTStarFrequencyExpansion.nmSupport N)
          (p := fun nm => Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0)
          (f := fun nm =>
            ∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
              ite (Q0MinorTTStarFrequencyExpansion.tFn N nm = t) (geometricAtom X N nm) 0)).symm
    rw [hfilter]
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    have htmem :
        Q0MinorTTStarFrequencyExpansion.tFn N nm ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0 := by
      rcases mem_geometricNmSupportNZ_iff.mp hnm with ⟨hn, hm, ht0⟩
      refine Finset.mem_erase.mpr ⟨ht0, ?_⟩
      exact geometricMem_tSupport_of_mem_s hn hm
    simpa using
      (Finset.sum_ite_eq_of_mem
        (s := (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0)
        (a := Q0MinorTTStarFrequencyExpansion.tFn N nm)
        (b := fun _ : ℤ => geometricAtom X N nm) htmem)
  exact hstep2

/--
Exact nonzero-frequency TT* expansion of the frozen geometric mean-channel scalar.

This is the cert-native geometric analogue of the SSU deterministic expansion: it exposes the
frozen witness as one explicit finite nonzero `(n,m)` sum, with no approximation yet applied.
-/
theorem geometricMeanChannelScalar_eq_q0_mul_sum_geometricNmSupportNZ
    {X N : ℕ} (hN : N ∈ Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies.minorWindow X) :
    geometricMeanChannelScalar X N
      =
    Q0MinorNormalizationBridge.q0NormFactor N
      * ∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm := by
  have hsumMean :
      geometricMeanChannelScalar X N
        =
      ∑ t ∈ Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X,
        geometricWeightedMinorCoeff X N t := by
    unfold geometricMeanChannelScalar
    unfold Q0MinorSingularityShadowBridge.familySliceSumOn
    exact sum_meanChannelOn_eq_sum
      (Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
      (geometricWeightedMinorCoeff X N)
  have hsub :
      (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0
        ⊆
      Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X := by
    intro t ht
    have htSupport : t ∈ Q0MinorTTStarFrequencyExpansion.tSupport N := (Finset.mem_erase.mp ht).2
    have htNe : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have hwin : t ∈ windowMinorCoeffSupport X := by
      exact tSupport_subset_windowMinorCoeffSupport hN htSupport
    simpa [Q0MinorSingularityProjectors.canonicalMinorAmbientSupport] using
      Finset.mem_erase.mpr ⟨htNe, hwin⟩
  have hsumSupport :
      (∑ t ∈ Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X,
          geometricWeightedMinorCoeff X N t)
        =
      ∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
        geometricWeightedMinorCoeff X N t := by
    symm
    refine Finset.sum_subset hsub ?_
    intro t htAmbient htNot
    have htNe : t ≠ 0 := by
      intro ht0
      have : (0 : ℤ) ∈ Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X := ht0 ▸ htAmbient
      simpa [Q0MinorSingularityProjectors.canonicalMinorAmbientSupport] using this
    have htNotSupport : t ∉ Q0MinorTTStarFrequencyExpansion.tSupport N := by
      intro htSupport
      exact htNot (Finset.mem_erase.mpr ⟨htNe, htSupport⟩)
    exact geometricWeightedMinorCoeff_eq_zero_of_not_mem_tSupport X N t htNotSupport
  rw [hsumMean, hsumSupport]
  unfold geometricWeightedMinorCoeff
  rw [← Finset.mul_sum]
  have hraw :
      (∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
          ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t,
            uniformWindowScalarWeight X nm.1
              * uniformWindowScalarWeight X nm.2
              * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon t
              * KHatH (Q0MinorTTStarFrequencyExpansion.kFn nm))
        =
      ∑ t ∈ (Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0,
          ∑ nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfT N t, geometricAtom X N nm := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    rcases Q0MinorTTStarFrequencyExpansion.mem_nmSupportOfT_iff.mp hnm with ⟨_, _, htEq⟩
    simp [geometricAtom, htEq]
  rw [hraw]
  exact congrArg (fun z => Q0MinorNormalizationBridge.q0NormFactor N * z)
    (geometricSum_tSupport_erase_zero_eq_sum_nmSupportNZ X N)

theorem geometricMeanChannelScalar_eq_q0_mul_sum_geometricWindowNmSupportNZ
    {X N : ℕ} (hN : N ∈ Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies.minorWindow X) :
    geometricMeanChannelScalar X N
      =
    Q0MinorNormalizationBridge.q0NormFactor N
      * ∑ nm ∈ geometricWindowNmSupportNZ X N, geometricAtom X N nm := by
  rw [geometricMeanChannelScalar_eq_q0_mul_sum_geometricNmSupportNZ hN]
  exact congrArg (fun z => Q0MinorNormalizationBridge.q0NormFactor N * z)
    (sum_geometricNmSupportNZ_eq_sum_geometricWindowNmSupportNZ X N)

theorem geometricSliceNZ_eq_core_mul_KHatH (X N : ℕ) (k : ℤ) :
    geometricSliceNZ X N k = geometricCoreSliceNZ X N k * KHatH k := by
  unfold geometricSliceNZ geometricCoreSliceNZ geometricAtom
  have hterm :
      ∀ nm ∈ nmSupportOfKNZ N k,
        uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2
            * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
                (Q0MinorTTStarFrequencyExpansion.tFn N nm)
            * KHatH (Q0MinorTTStarFrequencyExpansion.kFn nm)
          =
        (uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2
            * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
                (Q0MinorTTStarFrequencyExpansion.tFn N nm))
          * KHatH k := by
    intro nm hnm
    rcases mem_nmSupportOfKNZ_iff.mp hnm with ⟨_hn, _hm, hk, _ht0⟩
    simp [hk, mul_assoc]
  calc
    ∑ nm ∈ nmSupportOfKNZ N k,
        uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2
          * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
              (Q0MinorTTStarFrequencyExpansion.tFn N nm)
          * KHatH (Q0MinorTTStarFrequencyExpansion.kFn nm)
      =
    ∑ nm ∈ nmSupportOfKNZ N k,
        (uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2
          * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
              (Q0MinorTTStarFrequencyExpansion.tFn N nm))
        * KHatH k := by
          refine Finset.sum_congr rfl ?_
          intro nm hnm
          exact hterm nm hnm
    _ = geometricCoreSliceNZ X N k * KHatH k := by
          have hmul :
              (∑ nm ∈ nmSupportOfKNZ N k,
                  (uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2
                    * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
                        (Q0MinorTTStarFrequencyExpansion.tFn N nm))
                    * KHatH k)
                =
              (∑ nm ∈ nmSupportOfKNZ N k,
                  uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2
                    * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
                        (Q0MinorTTStarFrequencyExpansion.tFn N nm))
                * KHatH k := by
            simpa [Finset.sum_mul]
          simpa [geometricCoreSliceNZ] using hmul

theorem sum_geometricNmSupportNZ_eq_sum_kSlicesNZ (X N : ℕ) :
    (∑ nm ∈ geometricNmSupportNZ N, geometricAtom X N nm)
      =
    ∑ k ∈ kSupport N, geometricSliceNZ X N k := by
  classical
  have hstep1 :
      (∑ k ∈ kSupport N, geometricSliceNZ X N k)
        =
      ∑ k ∈ kSupport N, ∑ nm ∈ geometricNmSupportNZ N,
        ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k) (geometricAtom X N nm) 0 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have :
        geometricSliceNZ X N k
          =
        ∑ nm ∈ geometricNmSupportNZ N,
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k) (geometricAtom X N nm) 0 := by
      have hEq :
          nmSupportOfKNZ N k = (geometricNmSupportNZ N).filter (fun nm => Q0MinorTTStarFrequencyExpansion.kFn nm = k) := by
        ext nm
        simp [nmSupportOfKNZ, geometricNmSupportNZ, Q0MinorTTStarFrequencyExpansion.nmSupportOfK,
          Q0MinorTTStarFrequencyExpansion.nmSupport, Q0MinorTTStarFrequencyExpansion.kFn,
          Q0MinorTTStarFrequencyExpansion.tFn, and_left_comm, and_assoc, and_comm]
      calc
        geometricSliceNZ X N k
            = ∑ nm ∈ (geometricNmSupportNZ N).filter (fun nm => Q0MinorTTStarFrequencyExpansion.kFn nm = k),
                geometricAtom X N nm := by
                  simp [geometricSliceNZ, hEq]
        _ =
          ∑ nm ∈ geometricNmSupportNZ N,
            ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k) (geometricAtom X N nm) 0 := by
              simpa [Finset.sum_filter] using
                (Finset.sum_filter
                  (s := geometricNmSupportNZ N)
                  (p := fun nm => Q0MinorTTStarFrequencyExpansion.kFn nm = k)
                  (f := fun nm => geometricAtom X N nm)).symm
    exact this
  symm
  rw [hstep1]
  have hswap :
      (∑ k ∈ kSupport N, ∑ nm ∈ geometricNmSupportNZ N,
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k) (geometricAtom X N nm) 0)
        =
      ∑ nm ∈ geometricNmSupportNZ N, ∑ k ∈ kSupport N,
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k) (geometricAtom X N nm) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm
        (s := kSupport N) (t := geometricNmSupportNZ N)
        (f := fun k nm =>
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k) (geometricAtom X N nm) 0))
  rw [hswap]
  refine Finset.sum_congr rfl ?_
  intro nm hnm
  have hk :
      Q0MinorTTStarFrequencyExpansion.kFn nm ∈ kSupport N := by
    rcases mem_geometricNmSupportNZ_iff.mp hnm with ⟨hn, hm, _ht0⟩
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
    have hlower : (-(N : ℤ)) ≤ (nm.2 : ℤ) - (nm.1 : ℤ) := by
      have := sub_le_sub hm0 hn_leZ
      simpa using this
    have hupper : (nm.2 : ℤ) - (nm.1 : ℤ) ≤ (N : ℤ) := by
      have := sub_le_sub hm_leZ hn0
      simpa using this
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  simpa using
    (Finset.sum_ite_eq_of_mem
      (s := kSupport N)
      (a := Q0MinorTTStarFrequencyExpansion.kFn nm)
      (b := fun _ : ℤ => geometricAtom X N nm) hk)

theorem geometricMeanChannelScalar_eq_q0_mul_sum_kSlicesNZ
    {X N : ℕ} (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    geometricMeanChannelScalar X N
      =
    Q0MinorNormalizationBridge.q0NormFactor N
      * ∑ k ∈ kSupport N, geometricSliceNZ X N k := by
  rw [geometricMeanChannelScalar_eq_q0_mul_sum_geometricNmSupportNZ hN]
  exact congrArg (fun z => Q0MinorNormalizationBridge.q0NormFactor N * z)
    (sum_geometricNmSupportNZ_eq_sum_kSlicesNZ X N)

theorem geometricMeanChannelScalar_norm_sq_le_q0NormFactor_sq_mul_sum_sq_core
    {X N : ℕ} (hN : N ∈ Q0MinorSingularityFamilies.minorWindow X) :
    ‖geometricMeanChannelScalar X N‖ ^ 2
      ≤
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
      * (∑ k ∈ kSupport N, ‖geometricCoreSliceNZ X N k‖ ^ 2) := by
  rw [geometricMeanChannelScalar_eq_q0_mul_sum_kSlicesNZ hN]
  have hcore :
      (∑ k ∈ kSupport N, geometricSliceNZ X N k)
        =
      ∑ k ∈ kSupport N, geometricCoreSliceNZ X N k * KHatH k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact geometricSliceNZ_eq_core_mul_KHatH (X := X) (N := N) (k := k)
  rw [hcore]
  calc
    ‖Q0MinorNormalizationBridge.q0NormFactor N
        * ∑ k ∈ kSupport N, geometricCoreSliceNZ X N k * KHatH k‖ ^ 2
        = ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
            * ‖∑ k ∈ kSupport N, geometricCoreSliceNZ X N k * KHatH k‖ ^ 2 := by
            rw [norm_mul, pow_two, pow_two]
            ring
    _ ≤ ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
          * ((∑ k ∈ kSupport N, ‖geometricCoreSliceNZ X N k‖ ^ 2)
              * ∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2) := by
            have hcs :
                ‖∑ k ∈ kSupport N, geometricCoreSliceNZ X N k * KHatH k‖ ^ 2
                  ≤
                (∑ k ∈ kSupport N, ‖geometricCoreSliceNZ X N k‖ ^ 2)
                  * ∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2 := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
                  (s := kSupport N) (b := fun k => geometricCoreSliceNZ X N k)
                  (w := fun k => KHatH k))
            exact mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ ≤ ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
          * ((∑ k ∈ kSupport N, ‖geometricCoreSliceNZ X N k‖ ^ 2) * 1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (sum_sq_norm_KHatH_le_one N)
                (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
              (sq_nonneg _)
    _ = ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2
          * (∑ k ∈ kSupport N, ‖geometricCoreSliceNZ X N k‖ ^ 2) := by
            rw [mul_one]

/--
Exact slice-level discrepancy between the true mean-channel family and the frozen geometric
witness family.
-/
noncomputable def meanChannelApproxSliceError (X N : ℕ) : ℤ → ℂ :=
  fun t =>
    meanChannelOn
        (Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
        (Goldbach.Cert.MajorArcModules.Q0MinorSingularityBridge.weightedMinorCoeff X N) t
      -
    Q0MinorNormalizationBridge.q0NormFactor N
      * meanChannelOn
          (Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
          (geometricWeightedMinorCoeff X N) t

/--
The mean-channel approximation error is exactly the ambient slice sum of the slice-level witness
`meanChannelApproxSliceError`.
-/
theorem meanChannelApproxError_eq_sliceSum
    (X N : ℕ) :
    meanChannelApproxError X N
      =
    Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge.familySliceSumOn
      (Goldbach.Cert.MajorArcModules.Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
      (fun _ t => meanChannelApproxSliceError X N t) N := by
  unfold meanChannelApproxError G_formula geometricMeanChannelScalar meanChannelScalar
    meanChannelApproxSliceError
  unfold Goldbach.Cert.MajorArcModules.Q0MinorSingularityShadowBridge.familySliceSumOn
  have hmul :
      Q0MinorNormalizationBridge.q0NormFactor N
          * ∑ t ∈ Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X,
              (fun x t =>
                  meanChannelOn
                    (Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
                    (geometricWeightedMinorCoeff X N) t) N t
        =
      ∑ t ∈ Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X,
        Q0MinorNormalizationBridge.q0NormFactor N
          * (fun x t =>
              meanChannelOn
                (Q0MinorSingularityProjectors.canonicalMinorAmbientSupport X)
                (geometricWeightedMinorCoeff X N) t) N t := by
    simp [Finset.mul_sum]
  rw [hmul, Finset.sum_sub_distrib]
  simp [meanChannelSlice]

/--
On the canonical minor window, the exact mean-channel scalar is exactly the SSU part of the
frequency expansion.
-/
theorem meanChannelScalar_eq_ssuPart
    {X N : ℕ} (hN : N ∈ Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies.minorWindow X) :
    meanChannelScalar X N = canonicalExpansion.ssuPart X N := by
  rw [canonicalExpansion_ssuPart_eq_meanChannelSliceSum hN]
  rfl

/--
The geometric approximation error is exactly the Route-A SSU object minus the frozen geometric
surrogate.
-/
theorem meanChannelApproxError_eq_ssuPart_sub_G_formula
    {X N : ℕ} (hN : N ∈ Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies.minorWindow X) :
    meanChannelApproxError X N = canonicalExpansion.ssuPart X N - G_formula X N := by
  rw [show meanChannelApproxError X N = meanChannelScalar X N - G_formula X N by rfl]
  rw [meanChannelScalar_eq_ssuPart hN]

/--
Window-energy form of the exact Route-A-native geometric discrepancy:
the bridge-facing mean-channel error is exactly the SSU part minus the frozen geometric witness.
-/
theorem meanChannelApproxErrorWindowEnergy_eq_ssuPart_sub_G_formula
    (X : ℕ) :
    meanChannelApproxErrorWindowEnergy X
      =
    ∑ N ∈ EvenIn X H, ‖canonicalExpansion.ssuPart X N - G_formula X N‖ ^ 2 := by
  unfold meanChannelApproxErrorWindowEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  rw [meanChannelApproxError_eq_ssuPart_sub_G_formula
    (hN := by simpa [Goldbach.Cert.MajorArcModules.Q0MinorSingularityFamilies.minorWindow] using hN)]

private lemma norm_sub_sq_le_two_mul_sum_sq (a b : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have htri : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := by
    simpa [sub_eq_add_neg] using norm_add_le a (-b)
  have hsq : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [htri, norm_nonneg (a - b), norm_nonneg a, norm_nonneg b]
  have hquad : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact le_trans hsq hquad

/--
Pointwise geometric surrogate energy on the canonical window.

This is the exact cert-native object whose window sum is `gFormulaWindowUpper`.
-/
noncomputable def gFormulaPointwiseEnergy (X N : ℕ) : ℝ :=
  ‖Q0MinorNormalizationBridge.q0NormFactor N * geometricMeanChannelScalar X N‖ ^ 2

theorem gFormulaPointwiseEnergy_eq_norm_sq
    (X N : ℕ) :
    gFormulaPointwiseEnergy X N = ‖G_formula X N‖ ^ 2 := by
  rfl

/--
Exact algebraic form of the pointwise geometric surrogate energy after separating the outer
`q0NormFactor` layer.
-/
theorem gFormulaPointwiseEnergy_eq_q0NormFactor_sq_mul_geometricMean_sq
    (X N : ℕ) :
    gFormulaPointwiseEnergy X N
      =
    ‖Q0MinorNormalizationBridge.q0NormFactor N‖ ^ 2 * ‖geometricMeanChannelScalar X N‖ ^ 2 := by
  unfold gFormulaPointwiseEnergy
  rw [norm_mul]
  ring

/--
Core `k`-slice energy underlying the frozen geometric witness at one `N`.

This is the cert-native object exposed by the `k`-slice reduction. It is the next genuine
geometric quantity to bound, rather than `G_formula` itself.
-/
noncomputable def gFormulaCorePointwiseEnergy (X N : ℕ) : ℝ :=
  ∑ k ∈ kSupport N, ‖geometricCoreSliceNZ X N k‖ ^ 2

/-- Windowed core `k`-slice energy underlying the frozen geometric witness. -/
noncomputable def gFormulaCoreWindowEnergy (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, gFormulaCorePointwiseEnergy X N

private lemma gFormulaCorePointwiseEnergy_nonneg (X N : ℕ) :
    0 ≤ gFormulaCorePointwiseEnergy X N := by
  unfold gFormulaCorePointwiseEnergy
  positivity

/--
Surrogate coefficient mass on one nonzero `k`-slice.

This is the geometric analogue of the SSU-side `coeffMassKNZ`, with the hard arithmetic weights
replaced by the frozen interval-window surrogate weights.
-/
noncomputable def geometricCoeffMassKNZ (X N : ℕ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfKNZ N k,
    ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2

/-- Even-parity geometric coefficient mass at one `N`. -/
noncomputable def geometricCoeffMassEven (X N : ℕ) : ℝ :=
  ∑ k ∈ (kSupport N).filter Even, geometricCoeffMassKNZ X N k

/-- Odd-parity geometric coefficient mass at one `N`. -/
noncomputable def geometricCoeffMassOdd (X N : ℕ) : ℝ :=
  ∑ k ∈ (kSupport N).filter (fun k => ¬ Even k), geometricCoeffMassKNZ X N k

/--
Surrogate kernel mass on one nonzero `k`-slice.

This keeps the α-frequency part visible before any parity or Toeplitz domination is applied.
-/
noncomputable def geometricKernelMassKNZ (X N : ℕ) (k : ℤ) : ℝ :=
  ∑ nm ∈ nmSupportOfKNZ N k,
    ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon (Q0MinorTTStarFrequencyExpansion.tFn N nm)‖ ^ 2

private lemma tFn_injective_on_nmSupportOfKNZ
    {N : ℕ} {k : ℤ} {nm₁ nm₂ : ℕ × ℕ}
    (h₁ : nm₁ ∈ nmSupportOfKNZ N k)
    (h₂ : nm₂ ∈ nmSupportOfKNZ N k)
    (ht : Q0MinorTTStarFrequencyExpansion.tFn N nm₁ = Q0MinorTTStarFrequencyExpansion.tFn N nm₂) :
    nm₁ = nm₂ := by
  have h₁' := (mem_nmSupportOfKNZ_iff (N := N) (k := k) (nm := nm₁)).1 h₁
  have h₂' := (mem_nmSupportOfKNZ_iff (N := N) (k := k) (nm := nm₂)).1 h₂
  have hk₁ : ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) = k := h₁'.2.2.1
  have hk₂ : ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) = k := h₂'.2.2.1
  have hm₁ : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + k := by
    have : (nm₁.2 : ℤ) = (nm₁.1 : ℤ) + ((nm₁.2 : ℤ) - (nm₁.1 : ℤ)) := by ring
    simpa [hk₁] using this
  have hm₂ : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + k := by
    have : (nm₂.2 : ℤ) = (nm₂.1 : ℤ) + ((nm₂.2 : ℤ) - (nm₂.1 : ℤ)) := by ring
    simpa [hk₂] using this
  have ht₁ :
      Q0MinorTTStarFrequencyExpansion.tFn N nm₁ = 2 * (nm₁.1 : ℤ) + k - (N : ℤ) := by
    simp [Q0MinorTTStarFrequencyExpansion.tFn, hm₁, two_mul, add_assoc, add_left_comm, add_comm,
      sub_eq_add_neg]
  have ht₂ :
      Q0MinorTTStarFrequencyExpansion.tFn N nm₂ = 2 * (nm₂.1 : ℤ) + k - (N : ℤ) := by
    simp [Q0MinorTTStarFrequencyExpansion.tFn, hm₂, two_mul, add_assoc, add_left_comm, add_comm,
      sub_eq_add_neg]
  have hfstZ : (nm₁.1 : ℤ) = (nm₂.1 : ℤ) := by
    have ht' : (2 * (nm₁.1 : ℤ) + k - (N : ℤ)) = (2 * (nm₂.1 : ℤ) + k - (N : ℤ)) := by
      simpa [ht₁, ht₂] using ht
    have ht'' : 2 * (nm₁.1 : ℤ) = 2 * (nm₂.1 : ℤ) := by linarith
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) ht''
  have hfst : nm₁.1 = nm₂.1 := by
    exact_mod_cast hfstZ
  have hsnd : nm₁.2 = nm₂.2 := by
    have hsndZ : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by
      simp [hm₁, hm₂, hfstZ]
    exact Int.ofNat.inj hsndZ
  cases nm₁
  cases nm₂
  simp at hfst hsnd
  simp [hfst, hsnd]

private lemma even_tFn_iff_even_k_of_mem_nmSupportOfKNZ
    {N : ℕ} {k : ℤ} {nm : ℕ × ℕ}
    (hN : Even N) (hnm : nm ∈ nmSupportOfKNZ N k) :
    Even (Q0MinorTTStarFrequencyExpansion.tFn N nm) ↔ Even k := by
  have hnmK : nm ∈ Q0MinorTTStarFrequencyExpansion.nmSupportOfK N k := (Finset.mem_filter.mp hnm).1
  have hnm' :=
    (Q0MinorTTStarFrequencyExpansion.mem_nmSupportOfK_iff (N := N) (k := k) (nm := nm)).1 hnmK
  have hk : ((nm.2 : ℤ) - (nm.1 : ℤ)) = k := hnm'.2.2
  have hm : (nm.2 : ℤ) = (nm.1 : ℤ) + k := by
    have : (nm.2 : ℤ) = (nm.1 : ℤ) + ((nm.2 : ℤ) - (nm.1 : ℤ)) := by ring
    simpa [hk] using this
  have ht :
      Q0MinorTTStarFrequencyExpansion.tFn N nm = 2 * (nm.1 : ℤ) + k - (N : ℤ) := by
    simp [Q0MinorTTStarFrequencyExpansion.tFn, hm, two_mul, add_assoc, add_left_comm, add_comm,
      sub_eq_add_neg]
  have hN' : Even (N : ℤ) := (Int.even_coe_nat N).2 hN
  have h2n : Even (2 * (nm.1 : ℤ)) := by simp [Int.even_mul]
  calc
    Even (Q0MinorTTStarFrequencyExpansion.tFn N nm)
        ↔ Even (2 * (nm.1 : ℤ) + k - (N : ℤ)) := by simpa [ht]
    _ ↔ (Even (2 * (nm.1 : ℤ) + k) ↔ Even (N : ℤ)) := by
          simpa [sub_eq_add_neg, add_assoc] using
            (Int.even_sub (m := 2 * (nm.1 : ℤ) + k) (n := (N : ℤ)))
    _ ↔ Even (2 * (nm.1 : ℤ) + k) := by simpa [hN']
    _ ↔ (Even (2 * (nm.1 : ℤ)) ↔ Even k) := by
          simpa [add_assoc] using (Int.even_add (m := 2 * (nm.1 : ℤ)) (n := k))
    _ ↔ Even k := by simpa [h2n]

private lemma geometricKernelMassKNZ_eq_sum_majorKernelSq
    (X N : ℕ) (k : ℤ) :
    geometricKernelMassKNZ X N k
      =
    ∑ nm ∈ nmSupportOfKNZ N k,
      ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
          (Q0MinorTTStarFrequencyExpansion.tFn N nm)‖ ^ 2 := by
  unfold geometricKernelMassKNZ
  refine Finset.sum_congr rfl ?_
  intro nm hnm
  have ht0 : Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0 := (Finset.mem_filter.mp hnm).2
  rw [Q0MinorTTStarAlgebra.minorArcWeightFourier_ne_zero
    (X := X) (Δ := TurnkeyRouteQ0.Δ_canon) (t := Q0MinorTTStarFrequencyExpansion.tFn N nm) ht0]
  simp

private lemma geometricKernelMassKNZ_le_kernelMassNZEven_of_even
    (X N : ℕ) (k : ℤ) (hN : Even N) (hk : Even k) :
    geometricKernelMassKNZ X N k
      ≤
    Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N := by
  classical
  rw [geometricKernelMassKNZ_eq_sum_majorKernelSq]
  have himage :
      (∑ nm ∈ nmSupportOfKNZ N k,
          ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
              (Q0MinorTTStarFrequencyExpansion.tFn N nm)‖ ^ 2)
        =
      ∑ t ∈ (nmSupportOfKNZ N k).image (Q0MinorTTStarFrequencyExpansion.tFn N),
        ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X TurnkeyRouteQ0.Δ_canon t‖ ^ 2 := by
    symm
    refine Finset.sum_image ?_
    intro nm₁ h₁ nm₂ h₂ ht
    exact tFn_injective_on_nmSupportOfKNZ h₁ h₂ ht
  rw [himage]
  have hsub :
      (nmSupportOfKNZ N k).image (Q0MinorTTStarFrequencyExpansion.tFn N)
        ⊆
      ((Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0).filter Even := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨nm, hnm, rfl⟩
    have hnm' := (mem_nmSupportOfKNZ_iff (N := N) (k := k) (nm := nm)).1 hnm
    have htS : Q0MinorTTStarFrequencyExpansion.tFn N nm ∈ Q0MinorTTStarFrequencyExpansion.tSupport N :=
      geometricMem_tSupport_of_mem_s hnm'.1 hnm'.2.1
    have ht0 : Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0 := hnm'.2.2.2
    have htEven : Even (Q0MinorTTStarFrequencyExpansion.tFn N nm) :=
      (even_tFn_iff_even_k_of_mem_nmSupportOfKNZ hN hnm).2 hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ht0, htS⟩, htEven⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

private lemma geometricKernelMassKNZ_le_kernelMassNZOdd_of_odd
    (X N : ℕ) (k : ℤ) (hN : Even N) (hk : ¬ Even k) :
    geometricKernelMassKNZ X N k
      ≤
    Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N := by
  classical
  rw [geometricKernelMassKNZ_eq_sum_majorKernelSq]
  have himage :
      (∑ nm ∈ nmSupportOfKNZ N k,
          ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X TurnkeyRouteQ0.Δ_canon
              (Q0MinorTTStarFrequencyExpansion.tFn N nm)‖ ^ 2)
        =
      ∑ t ∈ (nmSupportOfKNZ N k).image (Q0MinorTTStarFrequencyExpansion.tFn N),
        ‖Q0MajorTailTTStarAlgebra.majorArcWeightFourier X TurnkeyRouteQ0.Δ_canon t‖ ^ 2 := by
    symm
    refine Finset.sum_image ?_
    intro nm₁ h₁ nm₂ h₂ ht
    exact tFn_injective_on_nmSupportOfKNZ h₁ h₂ ht
  rw [himage]
  have hsub :
      (nmSupportOfKNZ N k).image (Q0MinorTTStarFrequencyExpansion.tFn N)
        ⊆
      ((Q0MinorTTStarFrequencyExpansion.tSupport N).erase 0).filter (fun t => ¬ Even t) := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨nm, hnm, rfl⟩
    have hnm' := (mem_nmSupportOfKNZ_iff (N := N) (k := k) (nm := nm)).1 hnm
    have htS : Q0MinorTTStarFrequencyExpansion.tFn N nm ∈ Q0MinorTTStarFrequencyExpansion.tSupport N :=
      geometricMem_tSupport_of_mem_s hnm'.1 hnm'.2.1
    have ht0 : Q0MinorTTStarFrequencyExpansion.tFn N nm ≠ 0 := hnm'.2.2.2
    have htParity : Even (Q0MinorTTStarFrequencyExpansion.tFn N nm) ↔ Even k :=
      even_tFn_iff_even_k_of_mem_nmSupportOfKNZ hN hnm
    have htOdd : ¬ Even (Q0MinorTTStarFrequencyExpansion.tFn N nm) := by
      intro htEven
      exact hk (htParity.mp htEven)
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ht0, htS⟩, htOdd⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

private lemma geometricCoeffMassKNZ_nonneg (X N : ℕ) (k : ℤ) :
    0 ≤ geometricCoeffMassKNZ X N k := by
  unfold geometricCoeffMassKNZ
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem geometricCoreSliceNZ_norm_sq_le_coeffMassKNZ_mul_kernelMassKNZ
    (X N : ℕ) (k : ℤ) :
    ‖geometricCoreSliceNZ X N k‖ ^ 2
      ≤
    geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k := by
  unfold geometricCoreSliceNZ geometricCoeffMassKNZ geometricKernelMassKNZ
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
      (s := nmSupportOfKNZ N k)
      (b := fun nm => uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2)
      (w := fun nm =>
        minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon (Q0MinorTTStarFrequencyExpansion.tFn N nm)))

theorem gFormulaCorePointwiseEnergy_le_sum_coeffMassKNZ_mul_kernelMassKNZ
    (X N : ℕ) :
    gFormulaCorePointwiseEnergy X N
      ≤
    ∑ k ∈ kSupport N, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k := by
  unfold gFormulaCorePointwiseEnergy
  refine Finset.sum_le_sum ?_
  intro k hk
  exact geometricCoreSliceNZ_norm_sq_le_coeffMassKNZ_mul_kernelMassKNZ X N k

/--
Pointwise cert-native parity domination for the geometric core energy.

This is the first honest comparison target below `gFormulaCoreWindowEnergy`: the geometric core is
dominated by the same even/odd Route-A kernel masses as the checked SSU path, but with geometric
coefficient masses replacing the arithmetic ones.
-/
theorem gFormulaCorePointwiseEnergy_le_publicParityKernelBound
    (X N : ℕ) (hN : Even N) :
    gFormulaCorePointwiseEnergy X N
      ≤
    (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
        * geometricCoeffMassEven X N
      +
    (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
        * geometricCoeffMassOdd X N := by
  let kEven : Finset ℤ := (kSupport N).filter Even
  let kOdd : Finset ℤ := (kSupport N).filter (fun k => ¬ Even k)
  have hsplit :
      (∑ k ∈ kSupport N, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k)
        =
      (∑ k ∈ kEven, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k)
        +
      (∑ k ∈ kOdd, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k) := by
    have :=
      (Finset.sum_filter_add_sum_filter_not
        (s := kSupport N)
        (p := Even)
        (f := fun k : ℤ => geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k))
    simpa [kEven, kOdd] using this.symm
  have hEven :
      (∑ k ∈ kEven, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k)
        ≤
      Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N
        * (∑ k ∈ kEven, geometricCoeffMassKNZ X N k) := by
    calc
      (∑ k ∈ kEven, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k)
          ≤
        ∑ k ∈ kEven,
          geometricCoeffMassKNZ X N k
            * Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hkEven : Even k := (Finset.mem_filter.mp hk).2
            exact mul_le_mul_of_nonneg_left
              (geometricKernelMassKNZ_le_kernelMassNZEven_of_even X N k hN hkEven)
              (geometricCoeffMassKNZ_nonneg X N k)
      _ =
        Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N
          * (∑ k ∈ kEven, geometricCoeffMassKNZ X N k) := by
            simp [Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  have hOdd :
      (∑ k ∈ kOdd, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k)
        ≤
      Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N
        * (∑ k ∈ kOdd, geometricCoeffMassKNZ X N k) := by
    calc
      (∑ k ∈ kOdd, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k)
          ≤
        ∑ k ∈ kOdd,
          geometricCoeffMassKNZ X N k
            * Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N := by
            refine Finset.sum_le_sum ?_
            intro k hk
            have hkOdd : ¬ Even k := (Finset.mem_filter.mp hk).2
            exact mul_le_mul_of_nonneg_left
              (geometricKernelMassKNZ_le_kernelMassNZOdd_of_odd X N k hN hkOdd)
              (geometricCoeffMassKNZ_nonneg X N k)
      _ =
        Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N
          * (∑ k ∈ kOdd, geometricCoeffMassKNZ X N k) := by
            simp [Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  calc
    gFormulaCorePointwiseEnergy X N
        ≤
      ∑ k ∈ kSupport N, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k := by
          exact gFormulaCorePointwiseEnergy_le_sum_coeffMassKNZ_mul_kernelMassKNZ X N
    _ =
      (∑ k ∈ kEven, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k)
        +
      (∑ k ∈ kOdd, geometricCoeffMassKNZ X N k * geometricKernelMassKNZ X N k) := hsplit
    _ ≤
      Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N
        * (∑ k ∈ kEven, geometricCoeffMassKNZ X N k)
        +
      Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N
        * (∑ k ∈ kOdd, geometricCoeffMassKNZ X N k) := add_le_add hEven hOdd
    _ = Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N
          * geometricCoeffMassEven X N
        +
        Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N
          * geometricCoeffMassOdd X N := by
          simp [geometricCoeffMassEven, geometricCoeffMassOdd, kEven, kOdd]

private lemma geometricCoeffMassKNZ_eq_sum_geometricNmSupportNZ
    (X N : ℕ) (k : ℤ) :
    geometricCoeffMassKNZ X N k
      =
    ∑ nm ∈ geometricNmSupportNZ N,
      ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
        (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)
        0 := by
  have hEq :
      nmSupportOfKNZ N k
        = (geometricNmSupportNZ N).filter (fun nm => Q0MinorTTStarFrequencyExpansion.kFn nm = k) := by
    ext nm
    simp [nmSupportOfKNZ, geometricNmSupportNZ, Q0MinorTTStarFrequencyExpansion.nmSupport,
      Q0MinorTTStarFrequencyExpansion.nmSupportOfK, Q0MinorTTStarFrequencyExpansion.kFn,
      Q0MinorTTStarFrequencyExpansion.tFn, and_left_comm, and_assoc, and_comm]
  calc
    geometricCoeffMassKNZ X N k
        = ∑ nm ∈ (geometricNmSupportNZ N).filter (fun nm => Q0MinorTTStarFrequencyExpansion.kFn nm = k),
            ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 := by
              simp [geometricCoeffMassKNZ, hEq]
    _ = ∑ nm ∈ geometricNmSupportNZ N,
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
            (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)
            0 := by
              simpa [Finset.sum_filter] using
                (Finset.sum_filter
                  (s := geometricNmSupportNZ N)
                  (p := fun nm => Q0MinorTTStarFrequencyExpansion.kFn nm = k)
                  (f := fun nm => ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)).symm

theorem geometricCoeffMassEven_eq_sum_filtered_geometricNmSupportNZ
    (X N : ℕ) :
    geometricCoeffMassEven X N
      =
    ∑ nm ∈ (geometricNmSupportNZ N).filter (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm)),
      ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 := by
  unfold geometricCoeffMassEven
  have hstep1 :
      (∑ k ∈ (kSupport N).filter Even, geometricCoeffMassKNZ X N k)
        =
      ∑ k ∈ (kSupport N).filter Even,
        ∑ nm ∈ geometricNmSupportNZ N,
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
            (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact geometricCoeffMassKNZ_eq_sum_geometricNmSupportNZ X N k
  rw [hstep1]
  have hswap :
      (∑ k ∈ (kSupport N).filter Even,
          ∑ nm ∈ geometricNmSupportNZ N,
            ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
              (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0)
        =
      ∑ nm ∈ geometricNmSupportNZ N,
        ∑ k ∈ (kSupport N).filter Even,
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
            (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm
        (s := (kSupport N).filter Even)
        (t := geometricNmSupportNZ N)
        (f := fun k nm =>
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
            (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0))
  rw [hswap]
  have hk_mem :
      ∀ {nm : ℕ × ℕ}, nm ∈ geometricNmSupportNZ N →
        Q0MinorTTStarFrequencyExpansion.kFn nm ∈ kSupport N := by
    intro nm hnm
    rcases mem_geometricNmSupportNZ_iff.mp hnm with ⟨hn, hm, _⟩
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
    have hlower : (-(N : ℤ)) ≤ (Q0MinorTTStarFrequencyExpansion.kFn nm) := by
      have := sub_le_sub hm0 hn_leZ
      simpa [Q0MinorTTStarFrequencyExpansion.kFn] using this
    have hupper : Q0MinorTTStarFrequencyExpansion.kFn nm ≤ (N : ℤ) := by
      have := sub_le_sub hm_leZ hn0
      simpa [Q0MinorTTStarFrequencyExpansion.kFn] using this
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  have hinner :
      ∀ nm ∈ geometricNmSupportNZ N,
        (∑ k ∈ (kSupport N).filter Even,
            ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
              (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0)
          =
        (if Even (Q0MinorTTStarFrequencyExpansion.kFn nm)
          then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2
          else 0) := by
    intro nm hnm
    by_cases hkEven : Even (Q0MinorTTStarFrequencyExpansion.kFn nm)
    · have hk :
          Q0MinorTTStarFrequencyExpansion.kFn nm ∈ (kSupport N).filter Even := by
            exact Finset.mem_filter.mpr ⟨hk_mem hnm, hkEven⟩
      simpa [hkEven] using
        (Finset.sum_ite_eq_of_mem
          (s := (kSupport N).filter Even)
          (a := Q0MinorTTStarFrequencyExpansion.kFn nm)
          (b := fun _ : ℤ => ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)
          hk)
    · have :
          (∑ k ∈ (kSupport N).filter Even,
              ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
                (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro k hk
          have hk' : Even k := (Finset.mem_filter.mp hk).2
          have hneq : Q0MinorTTStarFrequencyExpansion.kFn nm ≠ k := by
            intro hEq
            exact hkEven (hEq.symm ▸ hk')
          simp [hneq]
      simpa [hkEven] using this
  have hrewrite :
      (∑ nm ∈ geometricNmSupportNZ N,
          ∑ k ∈ (kSupport N).filter Even,
            ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
              (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0)
        =
      ∑ nm ∈ geometricNmSupportNZ N,
        if Even (Q0MinorTTStarFrequencyExpansion.kFn nm)
          then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2
          else 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    exact hinner nm hnm
  rw [hrewrite]
  simpa [Finset.sum_filter] using
    (Finset.sum_filter
      (s := geometricNmSupportNZ N)
      (p := fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))
      (f := fun nm => ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)).symm

theorem geometricCoeffMassOdd_eq_sum_filtered_geometricNmSupportNZ
    (X N : ℕ) :
    geometricCoeffMassOdd X N
      =
    ∑ nm ∈ (geometricNmSupportNZ N).filter (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)),
      ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 := by
  unfold geometricCoeffMassOdd
  have hstep1 :
      (∑ k ∈ (kSupport N).filter (fun k => ¬ Even k), geometricCoeffMassKNZ X N k)
        =
      ∑ k ∈ (kSupport N).filter (fun k => ¬ Even k),
        ∑ nm ∈ geometricNmSupportNZ N,
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
            (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0 := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact geometricCoeffMassKNZ_eq_sum_geometricNmSupportNZ X N k
  rw [hstep1]
  have hswap :
      (∑ k ∈ (kSupport N).filter (fun k => ¬ Even k),
          ∑ nm ∈ geometricNmSupportNZ N,
            ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
              (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0)
        =
      ∑ nm ∈ geometricNmSupportNZ N,
        ∑ k ∈ (kSupport N).filter (fun k => ¬ Even k),
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
            (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0 := by
    simpa [Finset.sum_sigma'] using
      (Finset.sum_comm
        (s := (kSupport N).filter (fun k => ¬ Even k))
        (t := geometricNmSupportNZ N)
        (f := fun k nm =>
          ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
            (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0))
  rw [hswap]
  have hk_mem :
      ∀ {nm : ℕ × ℕ}, nm ∈ geometricNmSupportNZ N →
        Q0MinorTTStarFrequencyExpansion.kFn nm ∈ kSupport N := by
    intro nm hnm
    rcases mem_geometricNmSupportNZ_iff.mp hnm with ⟨hn, hm, _⟩
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
    have hlower : (-(N : ℤ)) ≤ (Q0MinorTTStarFrequencyExpansion.kFn nm) := by
      have := sub_le_sub hm0 hn_leZ
      simpa [Q0MinorTTStarFrequencyExpansion.kFn] using this
    have hupper : Q0MinorTTStarFrequencyExpansion.kFn nm ≤ (N : ℤ) := by
      have := sub_le_sub hm_leZ hn0
      simpa [Q0MinorTTStarFrequencyExpansion.kFn] using this
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  have hinner :
      ∀ nm ∈ geometricNmSupportNZ N,
        (∑ k ∈ (kSupport N).filter (fun k => ¬ Even k),
            ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
              (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0)
          =
        (if ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)
          then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2
          else 0) := by
    intro nm hnm
    by_cases hkOdd : ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)
    · have hk :
          Q0MinorTTStarFrequencyExpansion.kFn nm ∈ (kSupport N).filter (fun k => ¬ Even k) := by
            exact Finset.mem_filter.mpr ⟨hk_mem hnm, hkOdd⟩
      simpa [hkOdd] using
        (Finset.sum_ite_eq_of_mem
          (s := (kSupport N).filter (fun k => ¬ Even k))
          (a := Q0MinorTTStarFrequencyExpansion.kFn nm)
          (b := fun _ : ℤ => ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)
          hk)
    · have :
          (∑ k ∈ (kSupport N).filter (fun k => ¬ Even k),
              ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
                (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro k hk
          have hk' : ¬ Even k := (Finset.mem_filter.mp hk).2
          have hneq : Q0MinorTTStarFrequencyExpansion.kFn nm ≠ k := by
            intro hEq
            exact hkOdd (hEq.symm ▸ hk')
          simp [hneq]
      simpa [hkOdd] using this
  have hrewrite :
      (∑ nm ∈ geometricNmSupportNZ N,
          ∑ k ∈ (kSupport N).filter (fun k => ¬ Even k),
            ite (Q0MinorTTStarFrequencyExpansion.kFn nm = k)
              (‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2) 0)
        =
      ∑ nm ∈ geometricNmSupportNZ N,
        if ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)
          then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2
          else 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    exact hinner nm hnm
  rw [hrewrite]
  simpa [Finset.sum_filter] using
    (Finset.sum_filter
      (s := geometricNmSupportNZ N)
      (p := fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))
      (f := fun nm => ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)).symm

private lemma geometricCoeffTerm_eq_zero_of_fst_not_mem_window
    (X : ℕ) (nm : ℕ × ℕ)
    (hn : nm.1 ∉ Finset.Icc (X / 2 - H) (X / 2 + H)) :
    ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 = 0 := by
  unfold uniformWindowScalarWeight
  simp [hn]

private lemma geometricCoeffTerm_eq_zero_of_snd_not_mem_window
    (X : ℕ) (nm : ℕ × ℕ)
    (hm : nm.2 ∉ Finset.Icc (X / 2 - H) (X / 2 + H)) :
    ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 = 0 := by
  unfold uniformWindowScalarWeight
  simp [hm]

theorem geometricCoeffMassEven_eq_sum_filtered_geometricWindowNmSupportNZ
    (X N : ℕ) :
    geometricCoeffMassEven X N
      =
    ∑ nm ∈ (geometricWindowNmSupportNZ X N).filter
        (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm)),
      ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 := by
  rw [geometricCoeffMassEven_eq_sum_filtered_geometricNmSupportNZ]
  let s := (geometricNmSupportNZ N).filter (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))
  let p := fun nm : ℕ × ℕ =>
    nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
      ∧ nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
  have hrewrite :
      (∑ nm ∈ s, ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)
        =
      ∑ nm ∈ s, if p nm then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 else 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    by_cases hwin : p nm
    · simp [hwin]
    · rcases not_and_or.mp hwin with hleft | hright
      · have hzero :
            ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 = 0 :=
          geometricCoeffTerm_eq_zero_of_fst_not_mem_window X nm hleft
        simpa [hwin] using hzero
      · have hzero :
            ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 = 0 :=
          geometricCoeffTerm_eq_zero_of_snd_not_mem_window X nm hright
        simpa [hwin] using hzero
  rw [hrewrite]
  have hfilter :
      (∑ nm ∈ s, if p nm then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 else 0)
        =
      ∑ nm ∈ s.filter p, ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 := by
    simpa [Finset.sum_filter] using
      (Finset.sum_filter
        (s := s)
        (p := p)
        (f := fun nm => ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)).symm
  rw [hfilter]
  have hs :
      s.filter p
        =
      (geometricWindowNmSupportNZ X N).filter
        (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm)) := by
    ext nm
    simp [s, p, geometricWindowNmSupportNZ, and_left_comm, and_assoc, and_comm]
  rw [hs]

theorem geometricCoeffMassOdd_eq_sum_filtered_geometricWindowNmSupportNZ
    (X N : ℕ) :
    geometricCoeffMassOdd X N
      =
    ∑ nm ∈ (geometricWindowNmSupportNZ X N).filter
        (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)),
      ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 := by
  rw [geometricCoeffMassOdd_eq_sum_filtered_geometricNmSupportNZ]
  let s := (geometricNmSupportNZ N).filter (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))
  let p := fun nm : ℕ × ℕ =>
    nm.1 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
      ∧ nm.2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
  have hrewrite :
      (∑ nm ∈ s, ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)
        =
      ∑ nm ∈ s, if p nm then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 else 0 := by
    refine Finset.sum_congr rfl ?_
    intro nm hnm
    by_cases hwin : p nm
    · simp [hwin]
    · rcases not_and_or.mp hwin with hleft | hright
      · have hzero :
            ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 = 0 :=
          geometricCoeffTerm_eq_zero_of_fst_not_mem_window X nm hleft
        simpa [hwin] using hzero
      · have hzero :
            ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 = 0 :=
          geometricCoeffTerm_eq_zero_of_snd_not_mem_window X nm hright
        simpa [hwin] using hzero
  rw [hrewrite]
  have hfilter :
      (∑ nm ∈ s, if p nm then ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 else 0)
        =
      ∑ nm ∈ s.filter p, ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2 := by
    simpa [Finset.sum_filter] using
      (Finset.sum_filter
        (s := s)
        (p := p)
        (f := fun nm => ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2)).symm
  rw [hfilter]
  have hs :
      s.filter p
        =
      (geometricWindowNmSupportNZ X N).filter
        (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)) := by
    ext nm
    simp [s, p, geometricWindowNmSupportNZ, and_left_comm, and_assoc, and_comm]
  rw [hs]

private lemma geometricCoeffTerm_eq_uniformWindowNormalization_four_of_mem_geometricWindowNmSupportNZ
    {X N : ℕ} {nm : ℕ × ℕ}
    (hnm : nm ∈ geometricWindowNmSupportNZ X N) :
    ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2
      = ‖uniformWindowNormalization X‖ ^ 4 := by
  rcases mem_geometricWindowNmSupportNZ_iff.mp hnm with ⟨_, hn1, hn2⟩
  rw [uniformWindowScalarWeight_eq_normalization_mul_indicator,
    uniformWindowScalarWeight_eq_normalization_mul_indicator]
  simp [uniformWindowSupportIndicator, hn1, hn2, norm_mul]
  ring

theorem geometricCoeffMassEven_eq_uniformWindowNormalization_four_mul_card
    (X N : ℕ) :
    geometricCoeffMassEven X N
      =
    ‖uniformWindowNormalization X‖ ^ 4
      * (((geometricWindowNmSupportNZ X N).filter
          (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ) := by
  let s :=
    (geometricWindowNmSupportNZ X N).filter
      (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))
  rw [geometricCoeffMassEven_eq_sum_filtered_geometricWindowNmSupportNZ]
  calc
    ∑ nm ∈ s, ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2
      = ∑ _nm ∈ s, ‖uniformWindowNormalization X‖ ^ 4 := by
          refine Finset.sum_congr rfl ?_
          intro nm hnm
          exact geometricCoeffTerm_eq_uniformWindowNormalization_four_of_mem_geometricWindowNmSupportNZ
            ((Finset.mem_filter.mp hnm).1)
    _ = (s.card : ℝ) * ‖uniformWindowNormalization X‖ ^ 4 := by
          simp
    _ = ‖uniformWindowNormalization X‖ ^ 4 * (s.card : ℝ) := by
          ring
    _ =
        ‖uniformWindowNormalization X‖ ^ 4
          * (((geometricWindowNmSupportNZ X N).filter
              (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ) := by
          simp [s]

theorem geometricCoeffMassOdd_eq_uniformWindowNormalization_four_mul_card
    (X N : ℕ) :
    geometricCoeffMassOdd X N
      =
    ‖uniformWindowNormalization X‖ ^ 4
      * (((geometricWindowNmSupportNZ X N).filter
          (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ) := by
  let s :=
    (geometricWindowNmSupportNZ X N).filter
      (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))
  rw [geometricCoeffMassOdd_eq_sum_filtered_geometricWindowNmSupportNZ]
  calc
    ∑ nm ∈ s, ‖uniformWindowScalarWeight X nm.1 * uniformWindowScalarWeight X nm.2‖ ^ 2
      = ∑ _nm ∈ s, ‖uniformWindowNormalization X‖ ^ 4 := by
          refine Finset.sum_congr rfl ?_
          intro nm hnm
          exact geometricCoeffTerm_eq_uniformWindowNormalization_four_of_mem_geometricWindowNmSupportNZ
            ((Finset.mem_filter.mp hnm).1)
    _ = (s.card : ℝ) * ‖uniformWindowNormalization X‖ ^ 4 := by
          simp
    _ = ‖uniformWindowNormalization X‖ ^ 4 * (s.card : ℝ) := by
          ring
    _ =
        ‖uniformWindowNormalization X‖ ^ 4
          * (((geometricWindowNmSupportNZ X N).filter
              (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ) := by
          simp [s]

noncomputable def geometricWindowSupport (X N : ℕ) : Finset ℕ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N).filter
    (fun n => n ∈ Finset.Icc (X / 2 - H) (X / 2 + H))

noncomputable def geometricWindowSupportEven (X N : ℕ) : Finset ℕ :=
  (geometricWindowSupport X N).filter Even

noncomputable def geometricWindowSupportOdd (X N : ℕ) : Finset ℕ :=
  (geometricWindowSupport X N).filter (fun n => ¬ Even n)

private lemma mem_geometricWindowSupport_iff {X N n : ℕ} :
    n ∈ geometricWindowSupport X N
      ↔
    n ∈ Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N
      ∧ n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by
  simp [geometricWindowSupport]

abbrev geometricWindowSupportLeft (X N : ℕ) : ℕ :=
  max 2 (X / 2 - H)

abbrev geometricWindowSupportRight (X N : ℕ) : ℕ :=
  min (N - 2) (X / 2 + H)

abbrev geometricWindowSupportLength (X N : ℕ) : ℕ :=
  geometricWindowSupportRight X N + 1 - geometricWindowSupportLeft X N

private lemma Icc_eq_image_range (a b : ℕ) :
    Finset.Icc a b = (Finset.range (b + 1 - a)).image (fun k : ℕ => a + k) := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨n - a, ?_, by omega⟩
    apply Finset.mem_range.mpr
    omega
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.le_add_right _ _
    · have hk' : k < b + 1 - a := Finset.mem_range.mp hk
      omega

theorem geometricWindowSupport_eq_interval
    (X N : ℕ) :
    geometricWindowSupport X N
      =
    Finset.Icc (geometricWindowSupportLeft X N) (geometricWindowSupportRight X N) := by
  ext n
  constructor
  · intro hn
    rcases mem_geometricWindowSupport_iff.mp hn with ⟨hs, hwin⟩
    rcases Finset.mem_Icc.mp hs with ⟨h2, hN⟩
    rcases Finset.mem_Icc.mp hwin with ⟨hL, hR⟩
    exact Finset.mem_Icc.mpr
      ⟨by
          dsimp [geometricWindowSupportLeft]
          exact max_le_iff.mpr ⟨h2, hL⟩,
        by
          dsimp [geometricWindowSupportRight]
          exact le_min_iff.mpr ⟨hN, hR⟩⟩
  · intro hn
    rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
    refine mem_geometricWindowSupport_iff.mpr ?_
    constructor
    · exact Finset.mem_Icc.mpr
        ⟨le_of_max_le_left hlo, (le_min_iff.mp hhi).1⟩
    · exact Finset.mem_Icc.mpr
        ⟨le_of_max_le_right hlo, (le_min_iff.mp hhi).2⟩

theorem geometricWindowSupport_eq_image_range
    (X N : ℕ) :
    geometricWindowSupport X N
      =
    (Finset.range (geometricWindowSupportLength X N)).image
      (fun k : ℕ => geometricWindowSupportLeft X N + k) := by
  rw [geometricWindowSupport_eq_interval]
  simpa [geometricWindowSupportLength] using
    Icc_eq_image_range (geometricWindowSupportLeft X N) (geometricWindowSupportRight X N)

theorem geometricWindowSupportEven_eq_image_range_filter
    (X N : ℕ) :
    geometricWindowSupportEven X N
      =
    if Even (geometricWindowSupportLeft X N) then
      (((Finset.range (geometricWindowSupportLength X N)).filter Even).image
        (fun k : ℕ => geometricWindowSupportLeft X N + k))
    else
      (((Finset.range (geometricWindowSupportLength X N)).filter Odd).image
        (fun k : ℕ => geometricWindowSupportLeft X N + k)) := by
  unfold geometricWindowSupportEven
  rw [geometricWindowSupport_eq_image_range]
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · simp [ha]
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨himg, hEven⟩
      rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
      simpa [Nat.even_add, ha] using hEven
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
      · simpa [Nat.even_add, ha] using (Finset.mem_filter.mp hk).2
  · simp [ha]
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨himg, hEven⟩
      rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
      simpa [Nat.even_add, ha] using hEven
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
      · simpa [Nat.even_add, ha] using (Finset.mem_filter.mp hk).2

theorem geometricWindowSupportOdd_eq_image_range_filter
    (X N : ℕ) :
    geometricWindowSupportOdd X N
      =
    if Even (geometricWindowSupportLeft X N) then
      (((Finset.range (geometricWindowSupportLength X N)).filter Odd).image
        (fun k : ℕ => geometricWindowSupportLeft X N + k))
    else
      (((Finset.range (geometricWindowSupportLength X N)).filter Even).image
        (fun k : ℕ => geometricWindowSupportLeft X N + k)) := by
  unfold geometricWindowSupportOdd
  rw [geometricWindowSupport_eq_image_range]
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · simp [ha]
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨himg, hOdd⟩
      rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
      have hkNotEven : ¬ Even k := by
        have hsumNotEven : ¬ Even (geometricWindowSupportLeft X N + k) :=
          Nat.not_even_iff_odd.mpr hOdd
        simpa [Nat.even_add, ha] using hsumNotEven
      exact Nat.not_even_iff_odd.mp hkNotEven
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
      · have hkNotEven : ¬ Even k := Nat.not_even_iff_odd.mpr ((Finset.mem_filter.mp hk).2)
        have hsumNotEven : ¬ Even (geometricWindowSupportLeft X N + k) := by
          simpa [Nat.even_add, ha] using hkNotEven
        exact Nat.not_even_iff_odd.mp hsumNotEven
  · simp [ha]
    ext n
    constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨himg, hOdd⟩
      rcases Finset.mem_image.mp himg with ⟨k, hk, rfl⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
      have hsumNotEven : ¬ Even (geometricWindowSupportLeft X N + k) :=
        Nat.not_even_iff_odd.mpr hOdd
      simpa [Nat.even_add, ha] using hsumNotEven
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact Finset.mem_image.mpr ⟨k, (Finset.mem_filter.mp hk).1, rfl⟩
      · have hsumNotEven : ¬ Even (geometricWindowSupportLeft X N + k) := by
          simpa [Nat.even_add, ha] using (Finset.mem_filter.mp hk).2
        exact Nat.not_even_iff_odd.mp hsumNotEven

theorem geometricWindowSupportEven_card_eq_range_parityCount
    (X N : ℕ) :
    (geometricWindowSupportEven X N).card
      =
    if Even (geometricWindowSupportLeft X N) then
      ((Finset.range (geometricWindowSupportLength X N)).filter Even).card
    else
      ((Finset.range (geometricWindowSupportLength X N)).filter Odd).card := by
  rw [geometricWindowSupportEven_eq_image_range_filter]
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · simp [ha]
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.range (geometricWindowSupportLength X N)).filter Even)
        (f := fun k : ℕ => geometricWindowSupportLeft X N + k)
        (by
          intro m n hmn
          exact Nat.add_left_cancel hmn))
  · simp [ha]
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.range (geometricWindowSupportLength X N)).filter Odd)
        (f := fun k : ℕ => geometricWindowSupportLeft X N + k)
        (by
          intro m n hmn
          exact Nat.add_left_cancel hmn))

theorem geometricWindowSupportOdd_card_eq_range_parityCount
    (X N : ℕ) :
    (geometricWindowSupportOdd X N).card
      =
    if Even (geometricWindowSupportLeft X N) then
      ((Finset.range (geometricWindowSupportLength X N)).filter Odd).card
    else
      ((Finset.range (geometricWindowSupportLength X N)).filter Even).card := by
  rw [geometricWindowSupportOdd_eq_image_range_filter]
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · simp [ha]
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.range (geometricWindowSupportLength X N)).filter Odd)
        (f := fun k : ℕ => geometricWindowSupportLeft X N + k)
        (by
          intro m n hmn
          exact Nat.add_left_cancel hmn))
  · simp [ha]
    simpa using
      (Finset.card_image_of_injective
        (s := (Finset.range (geometricWindowSupportLength X N)).filter Even)
        (f := fun k : ℕ => geometricWindowSupportLeft X N + k)
        (by
          intro m n hmn
          exact Nat.add_left_cancel hmn))

private lemma card_filter_even_range (L : ℕ) :
    ((Finset.range L).filter Even).card = (L + 1) / 2 := by
  rw [← Nat.count_eq_card_filter_range (p := Even) L]
  induction L with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.count_succ, ih]
      by_cases hn : Even n
      · rcases even_iff_exists_two_mul.mp hn with ⟨k, rfl⟩
        have h₂ : (2 * k + 1 + 1) / 2 = (2 * k + 1) / 2 + 1 := by
          exact Nat.succ_div_of_dvd (by simpa using (show Even (2 * k + 2) by simp).two_dvd)
        simpa [add_assoc] using h₂.symm
      · have hn' : Odd n := Nat.not_even_iff_odd.mp hn
        rcases odd_iff_exists_bit1.mp hn' with ⟨k, rfl⟩
        have h₂ : (2 * k + 1 + 1 + 1) / 2 = (2 * k + 1 + 1) / 2 := by
          exact Nat.succ_div_of_not_dvd (by simp)
        simpa [add_assoc] using h₂.symm

private lemma card_filter_odd_range (L : ℕ) :
    ((Finset.range L).filter Odd).card = L / 2 := by
  rw [← Nat.count_eq_card_filter_range (p := Odd) L]
  induction L with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.count_succ, ih]
      by_cases hn : Odd n
      · rcases odd_iff_exists_bit1.mp hn with ⟨k, rfl⟩
        have h₂ : (2 * k + 1 + 1) / 2 = (2 * k + 1) / 2 + 1 := by
          exact Nat.succ_div_of_dvd (by simpa using (show Even (2 * k + 2) by simp).two_dvd)
        simpa [add_assoc] using h₂.symm
      · have hn' : Even n := Nat.not_odd_iff_even.mp hn
        rcases even_iff_exists_two_mul.mp hn' with ⟨k, rfl⟩
        have h₂ : (2 * k + 1) / 2 = k := by
          simpa using (Nat.succ_div_of_not_dvd (by simp) : (2 * k + 1) / 2 = (2 * k) / 2)
        simp [hn, h₂]

theorem geometricWindowSupportEven_card_eq_length_formula
    (X N : ℕ) :
    ((geometricWindowSupportEven X N).card : ℕ)
      =
    if Even (geometricWindowSupportLeft X N) then
      (geometricWindowSupportLength X N + 1) / 2
    else
      geometricWindowSupportLength X N / 2 := by
  rw [geometricWindowSupportEven_card_eq_range_parityCount]
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · simp [ha, card_filter_even_range]
  · simp [ha, card_filter_odd_range]

theorem geometricWindowSupportOdd_card_eq_length_formula
    (X N : ℕ) :
    ((geometricWindowSupportOdd X N).card : ℕ)
      =
    if Even (geometricWindowSupportLeft X N) then
      geometricWindowSupportLength X N / 2
    else
      (geometricWindowSupportLength X N + 1) / 2 := by
  rw [geometricWindowSupportOdd_card_eq_range_parityCount]
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · simp [ha, card_filter_odd_range]
  · simp [ha, card_filter_even_range]

private lemma even_geometricWindowPair_subset
    (X N : ℕ) :
    ((geometricWindowNmSupportNZ X N).filter
        (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm)))
      ⊆
    (geometricWindowSupportEven X N).product (geometricWindowSupportEven X N)
      ∪
    (geometricWindowSupportOdd X N).product (geometricWindowSupportOdd X N) := by
  intro nm hnm
  rcases Finset.mem_filter.mp hnm with ⟨hnmWin, hkEven⟩
  rcases mem_geometricWindowNmSupportNZ_iff.mp hnmWin with ⟨hnmNZ, hn1win, hn2win⟩
  have hnmBase := mem_geometricNmSupportNZ_iff.mp hnmNZ
  have hsame :
      Even (nm.2 : ℤ) ↔ Even (nm.1 : ℤ) := by
    exact (Int.even_sub (m := (nm.2 : ℤ)) (n := (nm.1 : ℤ))).1 hkEven
  by_cases hm2Even : Even nm.2
  · have hm2EvenZ : Even (nm.2 : ℤ) := (Int.even_coe_nat nm.2).2 hm2Even
    have hn1EvenZ : Even (nm.1 : ℤ) := hsame.mp hm2EvenZ
    have hn1Even : Even nm.1 := (Int.even_coe_nat nm.1).1 hn1EvenZ
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.1, hn1win⟩, hn1Even⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.2.1, hn2win⟩, hm2Even⟩⟩
  · have hm2OddZ : ¬ Even (nm.2 : ℤ) := by
      intro hm2EvenZ
      exact hm2Even ((Int.even_coe_nat nm.2).1 hm2EvenZ)
    have hn1OddZ : ¬ Even (nm.1 : ℤ) := by
      intro hn1EvenZ
      exact hm2OddZ (hsame.mpr hn1EvenZ)
    have hn1Odd : ¬ Even nm.1 := by
      intro hn1Even
      exact hn1OddZ ((Int.even_coe_nat nm.1).2 hn1Even)
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.1, hn1win⟩, hn1Odd⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.2.1, hn2win⟩, hm2Even⟩⟩

private lemma odd_geometricWindowPair_subset
    (X N : ℕ) :
    ((geometricWindowNmSupportNZ X N).filter
        (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)))
      ⊆
    (geometricWindowSupportEven X N).product (geometricWindowSupportOdd X N)
      ∪
    (geometricWindowSupportOdd X N).product (geometricWindowSupportEven X N) := by
  intro nm hnm
  rcases Finset.mem_filter.mp hnm with ⟨hnmWin, hkOdd⟩
  rcases mem_geometricWindowNmSupportNZ_iff.mp hnmWin with ⟨hnmNZ, hn1win, hn2win⟩
  have hnmBase := mem_geometricNmSupportNZ_iff.mp hnmNZ
  have hnotIff : ¬ (Even (nm.2 : ℤ) ↔ Even (nm.1 : ℤ)) := by
    exact fun hmn =>
      hkOdd ((Int.even_sub (m := (nm.2 : ℤ)) (n := (nm.1 : ℤ))).2 hmn)
  by_cases hm2Even : Even nm.2
  · have hm2EvenZ : Even (nm.2 : ℤ) := (Int.even_coe_nat nm.2).2 hm2Even
    have hn1OddZ : ¬ Even (nm.1 : ℤ) := by
      intro hn1EvenZ
      exact hnotIff (by simpa [hm2EvenZ, hn1EvenZ])
    have hn1Odd : ¬ Even nm.1 := by
      intro hn1Even
      exact hn1OddZ ((Int.even_coe_nat nm.1).2 hn1Even)
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.1, hn1win⟩, hn1Odd⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.2.1, hn2win⟩, hm2Even⟩⟩
  · have hm2OddZ : ¬ Even (nm.2 : ℤ) := by
      intro hm2EvenZ
      exact hm2Even ((Int.even_coe_nat nm.2).1 hm2EvenZ)
    have hn1EvenZ : Even (nm.1 : ℤ) := by
      by_contra hn1OddZ
      exact hnotIff (by simp [hm2OddZ, hn1OddZ])
    have hn1Even : Even nm.1 := (Int.even_coe_nat nm.1).1 hn1EvenZ
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.1, hn1win⟩, hn1Even⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnmBase.2.1, hn2win⟩, hm2Even⟩⟩

private lemma kernelMassNZEven_nonneg (X N : ℕ) :
    0 ≤ Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma kernelMassNZOdd_nonneg (X N : ℕ) :
    0 ≤ Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem geometricWindowEvenPairCard_le_paritySupportMass
    (X N : ℕ) :
    (((geometricWindowNmSupportNZ X N).filter
        (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ)
      ≤
    (((geometricWindowSupportEven X N).card : ℝ)
        * ((geometricWindowSupportEven X N).card : ℝ))
      +
    (((geometricWindowSupportOdd X N).card : ℝ)
        * ((geometricWindowSupportOdd X N).card : ℝ)) := by
  let s :=
    ((geometricWindowNmSupportNZ X N).filter
      (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm)))
  let ee := geometricWindowSupportEven X N
  let oo := geometricWindowSupportOdd X N
  have hsubset : s ⊆ ee.product ee ∪ oo.product oo :=
    even_geometricWindowPair_subset X N
  have hcard : s.card ≤ (ee.product ee ∪ oo.product oo).card :=
    Finset.card_le_card hsubset
  have hunion : (ee.product ee ∪ oo.product oo).card ≤ (ee.product ee).card + (oo.product oo).card :=
    Finset.card_union_le _ _
  have hnat : s.card ≤ ee.card * ee.card + (oo.card * oo.card) := by
    refine le_trans hcard ?_
    simpa [Finset.card_product, ee, oo, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hunion
  change ((s.card : ℝ)
      ≤
    (((geometricWindowSupportEven X N).card : ℝ)
        * ((geometricWindowSupportEven X N).card : ℝ))
      +
    (((geometricWindowSupportOdd X N).card : ℝ)
        * ((geometricWindowSupportOdd X N).card : ℝ)))
  exact_mod_cast hnat

theorem geometricWindowOddPairCard_le_paritySupportMass
    (X N : ℕ) :
    (((geometricWindowNmSupportNZ X N).filter
        (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ)
      ≤
    (((geometricWindowSupportEven X N).card : ℝ)
        * ((geometricWindowSupportOdd X N).card : ℝ))
      +
    (((geometricWindowSupportOdd X N).card : ℝ)
        * ((geometricWindowSupportEven X N).card : ℝ)) := by
  let s :=
    ((geometricWindowNmSupportNZ X N).filter
      (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm)))
  let ee := geometricWindowSupportEven X N
  let oo := geometricWindowSupportOdd X N
  have hsubset : s ⊆ ee.product oo ∪ oo.product ee :=
    odd_geometricWindowPair_subset X N
  have hcard : s.card ≤ (ee.product oo ∪ oo.product ee).card :=
    Finset.card_le_card hsubset
  have hunion : (ee.product oo ∪ oo.product ee).card ≤ (ee.product oo).card + (oo.product ee).card :=
    Finset.card_union_le _ _
  have hnat : s.card ≤ ee.card * oo.card + (oo.card * ee.card) := by
    refine le_trans hcard ?_
    simpa [Finset.card_product, ee, oo, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hunion
  change ((s.card : ℝ)
      ≤
    (((geometricWindowSupportEven X N).card : ℝ)
        * ((geometricWindowSupportOdd X N).card : ℝ))
      +
    (((geometricWindowSupportOdd X N).card : ℝ)
        * ((geometricWindowSupportEven X N).card : ℝ)))
  exact_mod_cast hnat

noncomputable def geometricWindowParityMassEven (X N : ℕ) : ℝ :=
  (((geometricWindowSupportEven X N).card : ℝ)
      * ((geometricWindowSupportEven X N).card : ℝ))
    +
  (((geometricWindowSupportOdd X N).card : ℝ)
      * ((geometricWindowSupportOdd X N).card : ℝ))

noncomputable def geometricWindowParityMassOdd (X N : ℕ) : ℝ :=
  (((geometricWindowSupportEven X N).card : ℝ)
      * ((geometricWindowSupportOdd X N).card : ℝ))
    +
  (((geometricWindowSupportOdd X N).card : ℝ)
      * ((geometricWindowSupportEven X N).card : ℝ))

theorem geometricWindowParityMassEven_eq_length_formula
    (X N : ℕ) :
    geometricWindowParityMassEven X N
      =
    ((((geometricWindowSupportLength X N + 1) / 2 : ℕ) : ℝ) ^ 2)
      +
    ((((geometricWindowSupportLength X N / 2 : ℕ) : ℝ)) ^ 2) := by
  unfold geometricWindowParityMassEven
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · rw [geometricWindowSupportEven_card_eq_length_formula, geometricWindowSupportOdd_card_eq_length_formula]
    simp [ha, sq]
  · rw [geometricWindowSupportEven_card_eq_length_formula, geometricWindowSupportOdd_card_eq_length_formula]
    simp [ha, add_comm, sq]

theorem geometricWindowParityMassOdd_eq_length_formula
    (X N : ℕ) :
    geometricWindowParityMassOdd X N
      =
    2 * ((((geometricWindowSupportLength X N + 1) / 2 : ℕ) : ℝ)
      * (((geometricWindowSupportLength X N / 2 : ℕ) : ℝ))) := by
  unfold geometricWindowParityMassOdd
  by_cases ha : Even (geometricWindowSupportLeft X N)
  · rw [geometricWindowSupportEven_card_eq_length_formula, geometricWindowSupportOdd_card_eq_length_formula]
    ring_nf
    simp [ha]
  · rw [geometricWindowSupportEven_card_eq_length_formula, geometricWindowSupportOdd_card_eq_length_formula]
    ring_nf
    simp [ha, mul_comm]

private lemma geometricWindowSupportLeft_eq_on_window
    {X N : ℕ} (hX : X0 ≤ X) (_hN : N ∈ EvenIn X H) :
    geometricWindowSupportLeft X N = X / 2 - H := by
  have hbase : (2 : ℕ) ≤ X / 2 - H := by
    have hbase0 : (2 : ℕ) ≤ X0 / 2 - H := by norm_num [X0, H]
    have hmono : X0 / 2 - H ≤ X / 2 - H := by
      exact Nat.sub_le_sub_right (Nat.div_le_div_right hX) H
    exact le_trans hbase0 hmono
  dsimp [geometricWindowSupportLeft]
  exact max_eq_right hbase

private lemma geometricWindow_H_le_X_div2 {X : ℕ} (hX : X0 ≤ X) : H ≤ X / 2 := by
  have hbase : H ≤ X0 / 2 := by norm_num [H, X0]
  exact le_trans hbase (Nat.div_le_div_right hX)

private lemma geometricWindowSupportRight_eq_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    geometricWindowSupportRight X N = X / 2 + H := by
  have hHX : H ≤ X / 2 := geometricWindow_H_le_X_div2 (X := X) hX
  have hupperX : X / 2 + H ≤ X := by
    have h1 : X / 2 + H ≤ X / 2 + X / 2 := Nat.add_le_add_left hHX (X / 2)
    have h2 : X / 2 + X / 2 ≤ X := by
      have hmul : 2 * (X / 2) ≤ X := Nat.mul_div_le X 2
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using hmul
    exact le_trans h1 h2
  have hhalf_ge : H + 2 ≤ X / 2 := by
    have hbase : H + 2 ≤ X0 / 2 := by norm_num [H, X0]
    exact le_trans hbase (Nat.div_le_div_right hX)
  have hHminus2 : H ≤ X / 2 - 2 := by
    omega
  have hXminus2 : X / 2 + H ≤ X - 2 := by
    have h1 : X / 2 + H ≤ X / 2 + (X / 2 - 2) := Nat.add_le_add_left hHminus2 (X / 2)
    have h2 : X / 2 + (X / 2 - 2) ≤ X - 2 := by
      have hmul : X / 2 + X / 2 ≤ X := by
        simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using
          (Nat.mul_div_le X 2)
      omega
    exact le_trans h1 h2
  have hXleN : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  have hNge : X / 2 + H ≤ N - 2 := by
    omega
  dsimp [geometricWindowSupportRight]
  exact min_eq_right hNge

theorem geometricWindowSupportLength_eq_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    geometricWindowSupportLength X N = 2 * H + 1 := by
  unfold geometricWindowSupportLength
  rw [geometricWindowSupportLeft_eq_on_window hX hN, geometricWindowSupportRight_eq_on_window hX hN]
  set a : ℕ := X / 2
  have hHa : H ≤ a := by
    simpa [a] using geometricWindow_H_le_X_div2 (X := X) hX
  change (a + H) + 1 - (a - H) = 2 * H + 1
  omega

theorem geometricWindowParityMassEven_eq_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    geometricWindowParityMassEven X N
      =
    ((((2 * H + 1 + 1) / 2 : ℕ) : ℝ) ^ 2)
      +
    ((((2 * H + 1) / 2 : ℕ) : ℝ) ^ 2) := by
  rw [geometricWindowParityMassEven_eq_length_formula, geometricWindowSupportLength_eq_on_window hX hN]

theorem geometricWindowParityMassOdd_eq_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    geometricWindowParityMassOdd X N
      =
    2 * ((((2 * H + 1 + 1) / 2 : ℕ) : ℝ)
      * (((2 * H + 1) / 2 : ℕ) : ℝ)) := by
  rw [geometricWindowParityMassOdd_eq_length_formula, geometricWindowSupportLength_eq_on_window hX hN]

noncomputable def geometricWindowParityMassEvenConst : ℝ :=
  ((((2 * H + 1 + 1) / 2 : ℕ) : ℝ) ^ 2)
    +
  ((((2 * H + 1) / 2 : ℕ) : ℝ) ^ 2)

noncomputable def geometricWindowParityMassOddConst : ℝ :=
  2 * ((((2 * H + 1 + 1) / 2 : ℕ) : ℝ)
    * (((2 * H + 1) / 2 : ℕ) : ℝ))

theorem gFormulaCorePointwiseEnergy_le_publicParityKernelSupportMass
    (X N : ℕ) (hN : Even N) :
    gFormulaCorePointwiseEnergy X N
      ≤
    ‖uniformWindowNormalization X‖ ^ 4
      * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassEven X N)
          +
          ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassOdd X N)) := by
  have hEvenCard :=
    geometricWindowEvenPairCard_le_paritySupportMass (X := X) (N := N)
  have hOddCard :=
    geometricWindowOddPairCard_le_paritySupportMass (X := X) (N := N)
  have hke :
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
        * (((geometricWindowNmSupportNZ X N).filter
            (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ)
      ≤
    (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
      * geometricWindowParityMassEven X N := by
    exact mul_le_mul_of_nonneg_left hEvenCard (kernelMassNZEven_nonneg X N)
  have hko :
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
        * (((geometricWindowNmSupportNZ X N).filter
            (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ)
      ≤
    (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
      * geometricWindowParityMassOdd X N := by
    exact mul_le_mul_of_nonneg_left hOddCard (kernelMassNZOdd_nonneg X N)
  have hsum :
      ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
          * (((geometricWindowNmSupportNZ X N).filter
              (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))
        +
      ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
          * (((geometricWindowNmSupportNZ X N).filter
              (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))
      ≤
      ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
          * geometricWindowParityMassEven X N)
        +
      ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
          * geometricWindowParityMassOdd X N) := by
    exact add_le_add hke hko
  calc
    gFormulaCorePointwiseEnergy X N
        ≤
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
          * geometricCoeffMassEven X N
        +
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
          * geometricCoeffMassOdd X N := by
            exact gFormulaCorePointwiseEnergy_le_publicParityKernelBound X N hN
    _ ≤
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
          * (‖uniformWindowNormalization X‖ ^ 4
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))
        +
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
          * (‖uniformWindowNormalization X‖ ^ 4
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ)) := by
            rw [geometricCoeffMassEven_eq_uniformWindowNormalization_four_mul_card,
              geometricCoeffMassOdd_eq_uniformWindowNormalization_four_mul_card]
    _ =
      ‖uniformWindowNormalization X‖ ^ 4
        * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))
            +
            ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
              * (((geometricWindowNmSupportNZ X N).filter
                  (fun nm => ¬ Even (Q0MinorTTStarFrequencyExpansion.kFn nm))).card : ℝ))) := by
            ring
    _ ≤
      ‖uniformWindowNormalization X‖ ^ 4
        * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
              * geometricWindowParityMassEven X N)
            +
            ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
              * geometricWindowParityMassOdd X N)) := by
            exact mul_le_mul_of_nonneg_left hsum (pow_nonneg (norm_nonneg _) _)

theorem gFormulaCorePointwiseEnergy_le_publicParityKernelWindowConst
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    gFormulaCorePointwiseEnergy X N
      ≤
    ‖uniformWindowNormalization X‖ ^ 4
      * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassEvenConst)
          +
          ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassOddConst)) := by
  have hN_even : Even N := by
    exact Goldbach.Windows.even_of_isEven (Finset.mem_filter.mp hN).2
  calc
    gFormulaCorePointwiseEnergy X N
      ≤
    ‖uniformWindowNormalization X‖ ^ 4
      * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassEven X N)
          +
          ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassOdd X N)) := by
        exact gFormulaCorePointwiseEnergy_le_publicParityKernelSupportMass (X := X) (N := N) hN_even
    _ =
    ‖uniformWindowNormalization X‖ ^ 4
      * (((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassEvenConst)
          +
          ((Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N)
            * geometricWindowParityMassOddConst)) := by
        rw [geometricWindowParityMassEven_eq_on_window hX hN,
          geometricWindowParityMassOdd_eq_on_window hX hN]
        simp [geometricWindowParityMassEvenConst, geometricWindowParityMassOddConst]

private lemma card_evenIn_le_H_add_one (X : ℕ) :
    (EvenIn X H).card ≤ H + 1 := by
  classical
  unfold EvenIn IccShift
  have hsub :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)
        ⊆
      (Finset.range (H + 1)).image (fun k : ℕ => X + k) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcard_le :
      (((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)).card
        ≤
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card :=
    Finset.card_le_card hsub
  have hcard_eq :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card = H + 1 := by
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro a b hab
    exact Nat.add_left_cancel hab
  exact le_trans hcard_le (le_of_eq hcard_eq)

private lemma le_X_add_H_of_mem_EvenIn {X N : ℕ} (hN : N ∈ EvenIn X H) : N ≤ X + H := by
  unfold EvenIn IccShift at hN
  rcases Finset.mem_filter.mp hN with ⟨hmem, _⟩
  rcases Finset.mem_image.mp hmem with ⟨k, hk, rfl⟩
  have hklt : k < H + 1 := Finset.mem_range.mp hk
  omega

private lemma kernelMassNZEven_le_routeA_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N
      ≤
    Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X := by
  have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn hN
  calc
    Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N
      ≤
        Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon (X + H) := by
          exact Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven_mono_N hNle
    _ = Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X (1 : ℝ) (X + H) := by
          simp [TurnkeyRouteQ0.Δ_canon]
    _ ≤ Q0MajorTailTTStarStep5ToeplitzUpperBound.kernelMassNZEven_upper X := by
          exact Q0MajorTailTTStarStep5ToeplitzUpperBound.kernelMassNZEven_le_upper (X := X) hX
    _ ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X := by
          exact
            Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_le_routeA
              (hGcd := Goldbach.Cert.MajorArcModules.Q0TwoBoundsConventionalAxioms.ramanujanGcdBound)
              (X := X) hX

private lemma kernelMassNZOdd_le_routeA_on_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N
      ≤
    Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X := by
  have hNle : N ≤ X + H := le_X_add_H_of_mem_EvenIn hN
  calc
    Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N
      ≤
        Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon (X + H) := by
          exact Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd_mono_N hNle
    _ = Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X (1 : ℝ) (X + H) := by
          simp [TurnkeyRouteQ0.Δ_canon]
    _ ≤ Q0MajorTailTTStarStep5ToeplitzUpperBound.kernelMassNZOdd_upper X := by
          exact Q0MajorTailTTStarStep5ToeplitzUpperBound.kernelMassNZOdd_le_upper (X := X) hX
    _ ≤ Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X := by
          exact
            Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_le_routeA
              (hGcd := Goldbach.Cert.MajorArcModules.Q0TwoBoundsConventionalAxioms.ramanujanGcdBound)
              (X := X) hX

private lemma tSupport_erase_zero_card_nat (X : ℕ) :
    ((Q0MajorTailTTStarToeplitzScaffold.tSupport (X + H)).erase 0).card = 2 * (X + H) := by
  have h0 : (0 : ℤ) ∈ Q0MajorTailTTStarToeplitzScaffold.tSupport (X + H) := by
    refine Finset.mem_Icc.mpr ?_
    constructor
    · have hnonneg : (0 : ℤ) ≤ ((X + H : ℕ) : ℤ) := by exact_mod_cast (Nat.zero_le (X + H))
      simpa using (neg_nonpos.mpr hnonneg)
    · exact_mod_cast (Nat.zero_le (X + H))
  calc
    ((Q0MajorTailTTStarToeplitzScaffold.tSupport (X + H)).erase 0).card
        = (Q0MajorTailTTStarToeplitzScaffold.tSupport (X + H)).card - 1 := by
            simpa using Finset.card_erase_of_mem h0
    _ = (2 * (X + H) + 1) - 1 := by
          rw [Q0MajorTailTTStarToeplitzScaffold.tSupport, Goldbach.PPBoundCore.card_Icc_neg_to_pos]
    _ = 2 * (X + H) := by omega

private lemma tSupport_erase_zero_card (X : ℕ) :
    (((Q0MajorTailTTStarToeplitzScaffold.tSupport (X + H)).erase 0).card : ℝ)
      = 2 * ((X + H : ℕ) : ℝ) := by
  exact_mod_cast tSupport_erase_zero_card_nat X

private lemma evenBand_card_add_oddBand_card (X : ℕ) :
    (((Q0MajorTailTTStarStep5KernelMassBound.evenBand X).card : ℝ)
      + ((Q0MajorTailTTStarStep5KernelMassBound.oddBand X).card : ℝ))
      =
    2 * ((X + H : ℕ) : ℝ) := by
  let S : Finset ℤ := (Q0MajorTailTTStarToeplitzScaffold.tSupport (X + H)).erase 0
  have hsplit_nat :
      (Q0MajorTailTTStarStep5KernelMassBound.evenBand X).card
        + (Q0MajorTailTTStarStep5KernelMassBound.oddBand X).card
        = S.card := by
    simpa [Q0MajorTailTTStarStep5KernelMassBound.evenBand,
      Q0MajorTailTTStarStep5KernelMassBound.oddBand, S]
      using (Finset.filter_card_add_filter_neg_card_eq_card (s := S) (p := Even))
  calc
    (((Q0MajorTailTTStarStep5KernelMassBound.evenBand X).card : ℝ)
        + ((Q0MajorTailTTStarStep5KernelMassBound.oddBand X).card : ℝ))
        = (S.card : ℝ) := by exact_mod_cast hsplit_nat
    _ = 2 * ((X + H : ℕ) : ℝ) := tSupport_erase_zero_card X

/-- Combined unweighted Route-A kernel budget for the parity-summed nonzero Toeplitz masses. -/
noncomputable def kernelMassNZParity_upper_routeA_const : ℝ :=
  (1 + Q0MajorTailTTStarStep5KernelMassBound.δ_weightSplit)
    * (8 * ((23 : ℝ) ^ 2) + 64 * Q0MajorTailTTStarStep5LXBound.LXMeanSquareUpperCore)
  + (1 + 1 / Q0MajorTailTTStarStep5KernelMassBound.δ_weightSplit) * 9

private lemma kernelMassNZParity_upper_routeA_const_nonneg :
    0 ≤ kernelMassNZParity_upper_routeA_const := by
  have hcore_nonneg : 0 ≤ Q0MajorTailTTStarStep5LXBound.LXMeanSquareUpperCore := by
    rw [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCore_eq_collapsed]
    dsimp [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCoreCollapsed]
    positivity
  rw [kernelMassNZParity_upper_routeA_const]
  nlinarith [hcore_nonneg, Q0MajorTailTTStarStep5KernelMassBound.δ_weightSplit_pos]

theorem kernelMassNZParity_upper_routeA_le_const_div_X
    {X : ℕ} (hX : X0 ≤ X) :
    Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
      + Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
      ≤
    kernelMassNZParity_upper_routeA_const / (X : ℝ) := by
  have hXpos_nat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos_nat
  have hXH_le_twoX : X + H ≤ 2 * X := by
    have hHX : H ≤ X := le_trans (by decide : H ≤ X0) hX
    omega
  have hband :
      (((Q0MajorTailTTStarStep5KernelMassBound.evenBand X).card : ℝ)
        + ((Q0MajorTailTTStarStep5KernelMassBound.oddBand X).card : ℝ))
        =
      2 * ((X + H : ℕ) : ℝ) :=
    evenBand_card_add_oddBand_card X
  have hxh :
      ((X + H : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
    exact_mod_cast hXH_le_twoX
  have hcore_nonneg : 0 ≤ Q0MajorTailTTStarStep5LXBound.LXMeanSquareUpperCore := by
    rw [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCore_eq_collapsed]
    dsimp [Q0MajorTailTTStarStep5LXCoreCollapse.LXMeanSquareUpperCoreCollapsed]
    positivity
  have hcalc :
      (X : ℝ)
        * (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
            + Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X)
      ≤ kernelMassNZParity_upper_routeA_const := by
    rw [Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA,
      Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA,
      kernelMassNZParity_upper_routeA_const]
    have hband_le :
        (((Q0MajorTailTTStarStep5KernelMassBound.evenBand X).card : ℝ)
          + ((Q0MajorTailTTStarStep5KernelMassBound.oddBand X).card : ℝ))
          ≤
        4 * (X : ℝ) := by
      rw [hband]
      nlinarith
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    have hδ : Q0MajorTailTTStarStep5KernelMassBound.δ_weightSplit = (1 : ℝ) := rfl
    rw [hδ]
    field_simp [pow_two, hXne]
    nlinarith [hband_le, hxh, hcore_nonneg]
  exact (le_div_iff₀' hXpos).2 hcalc


/-- Route-A upper comparison for one pointwise geometric core energy on the canonical window. -/
theorem gFormulaCorePointwiseEnergy_le_routeAWindowConst
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    gFormulaCorePointwiseEnergy X N
      ≤
    ‖uniformWindowNormalization X‖ ^ 4
      * ((Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
            * geometricWindowParityMassEvenConst)
          +
          (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
            * geometricWindowParityMassOddConst)) := by
  have hpt := gFormulaCorePointwiseEnergy_le_publicParityKernelWindowConst hX hN
  have hke := kernelMassNZEven_le_routeA_on_window hX hN
  have hko := kernelMassNZOdd_le_routeA_on_window hX hN
  have hinside :
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZEven X TurnkeyRouteQ0.Δ_canon N
          * geometricWindowParityMassEvenConst)
        +
      (Q0MajorTailTTStarToeplitzScaffold.kernelMassNZOdd X TurnkeyRouteQ0.Δ_canon N
          * geometricWindowParityMassOddConst)
      ≤
      (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
          * geometricWindowParityMassEvenConst)
        +
      (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
          * geometricWindowParityMassOddConst) := by
    have hEvenConst_nonneg : 0 ≤ geometricWindowParityMassEvenConst := by
      norm_num [geometricWindowParityMassEvenConst, H]
    have hOddConst_nonneg : 0 ≤ geometricWindowParityMassOddConst := by
      norm_num [geometricWindowParityMassOddConst, H]
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_right hke hEvenConst_nonneg
    · exact mul_le_mul_of_nonneg_right hko hOddConst_nonneg
  exact le_trans hpt <| mul_le_mul_of_nonneg_left hinside (pow_nonneg (norm_nonneg _) _)

/-- Route-A upper comparison for the full geometric core window energy. -/
theorem gFormulaCoreWindowEnergy_le_routeAWindowConst
    {X : ℕ} (hX : X0 ≤ X) :
    gFormulaCoreWindowEnergy X
      ≤
    ((EvenIn X H).card : ℝ)
      * (‖uniformWindowNormalization X‖ ^ 4
          * ((Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
                * geometricWindowParityMassEvenConst)
              +
              (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
                * geometricWindowParityMassOddConst))) := by
  unfold gFormulaCoreWindowEnergy
  have hsum :
      ∑ N ∈ EvenIn X H, gFormulaCorePointwiseEnergy X N
        ≤
      ∑ _N ∈ EvenIn X H,
        ‖uniformWindowNormalization X‖ ^ 4
          * ((Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
                * geometricWindowParityMassEvenConst)
              +
              (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
                * geometricWindowParityMassOddConst)) := by
    refine Finset.sum_le_sum ?_
    intro N hN
    exact gFormulaCorePointwiseEnergy_le_routeAWindowConst hX hN
  let C : ℝ :=
    ‖uniformWindowNormalization X‖ ^ 4
      * ((Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZEven_upper_routeA X
            * geometricWindowParityMassEvenConst)
          +
          (Q0MajorTailTTStarStep5ToeplitzUpperBoundRouteA.kernelMassNZOdd_upper_routeA X
            * geometricWindowParityMassOddConst))
  have hconst : (∑ _N ∈ EvenIn X H, C) = ((EvenIn X H).card : ℝ) * C := by
    rw [Finset.sum_const, nsmul_eq_mul]
  exact le_trans hsum (by exact hconst.le)

end

end Q0MinorGFormulaRouteA
