import Goldbach.BG_Identity
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
import Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
import Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
import Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

/-!
Deterministic zero-mode / Type-I reduction for the `Q0`-minor frequency expansion.

This isolates the `t = 0` coefficient of the canonical minor expansion and bounds it by the
diagonal mass from the major-tail Toeplitz scaffold. No numeric calibration appears here yet.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorTypeIDeterministic

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarToeplitzScaffold
open Goldbach.Cert.MajorArcModules.Q0MinorFrequencySplit
open Goldbach.Cert.MajorArcModules.Q0MinorNormalizationBridge
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarFiniteSupport
open Goldbach.Cert.MajorArcModules.TurnkeyRouteQ0

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private abbrev aTerm (X : ℕ) (n : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm X n

private abbrev nmSupportZero (N : ℕ) : Finset (ℕ × ℕ) :=
  nmSupportOfT N 0

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

private lemma sub_mem_kSupport_of_mem_s {N n m : ℕ} (hn : n ∈ s N) (hm : m ∈ s N) :
    ((m : ℤ) - (n : ℤ)) ∈ kSupport N := by
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
  have hlower : (-(N : ℤ)) ≤ (m : ℤ) - (n : ℤ) := by
    have := sub_le_sub hm0 hn_leZ
    simpa using this
  have hupper : (m : ℤ) - (n : ℤ) ≤ (N : ℤ) := by
    have := sub_le_sub hm_leZ hn0
    simpa using this
  exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩

private lemma kFn_injOn_nmSupportZero (N : ℕ) :
    Set.InjOn kFn {nm | nm ∈ nmSupportZero N} := by
  intro nm₁ h₁ nm₂ h₂ hk
  have h₁' := mem_nmSupportOfT_iff.mp h₁
  have h₂' := mem_nmSupportOfT_iff.mp h₂
  have hsum₁ : (nm₁.1 : ℤ) + (nm₁.2 : ℤ) = (N : ℤ) := by
    have : (nm₁.1 : ℤ) + (nm₁.2 : ℤ) - (N : ℤ) = 0 := by simpa [tFn] using h₁'.2.2
    linarith
  have hsum₂ : (nm₂.1 : ℤ) + (nm₂.2 : ℤ) = (N : ℤ) := by
    have : (nm₂.1 : ℤ) + (nm₂.2 : ℤ) - (N : ℤ) = 0 := by simpa [tFn] using h₂'.2.2
    linarith
  have hnZ : (nm₁.1 : ℤ) = (nm₂.1 : ℤ) := by
    linarith
  have hmZ : (nm₁.2 : ℤ) = (nm₂.2 : ℤ) := by
    linarith
  have hn : nm₁.1 = nm₂.1 := by exact_mod_cast hnZ
  have hm : nm₁.2 = nm₂.2 := by exact Int.ofNat.inj hmZ
  cases nm₁
  cases nm₂
  simp at hn hm
  simp [hn, hm]

private lemma mem_image_kFn_subset_kSupport (N : ℕ) :
    (nmSupportZero N).image kFn ⊆ kSupport N := by
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨nm, hnm, rfl⟩
  rcases mem_nmSupportOfT_iff.mp hnm with ⟨hn, hm, _⟩
  exact sub_mem_kSupport_of_mem_s (N := N) hn hm

private lemma sum_image_eq_of_injOn {α β γ : Type*} [DecidableEq β] [AddCommMonoid γ]
    (s : Finset α) (f : α → β) (g : β → γ)
    (hinj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) :
    ∑ b ∈ s.image f, g b = ∑ a ∈ s, g (f a) := by
  classical
  revert hinj
  refine Finset.induction_on s ?_ ?_
  · intro _hinj
    simp
  · intro a s ha_not_mem ih hinj
    have hinj_s : ∀ b₁ ∈ s, ∀ b₂ ∈ s, f b₁ = f b₂ → b₁ = b₂ := by
      intro b₁ hb₁ b₂ hb₂ hEq
      exact hinj b₁ (by simp [hb₁, ha_not_mem]) b₂ (by simp [hb₂, ha_not_mem]) hEq
    have ih' : (s.image f).sum g = s.sum (fun b => g (f b)) := ih hinj_s
    have hfa_not_mem : f a ∉ s.image f := by
      intro hmem
      rcases Finset.mem_image.1 hmem with ⟨b, hb, hfb⟩
      have hab : a = b := hinj a (by simp [ha_not_mem]) b (by simp [hb, ha_not_mem]) hfb.symm
      exact ha_not_mem (hab ▸ hb)
    simp [Finset.image_insert, Finset.sum_insert, ha_not_mem, hfa_not_mem, ih']

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

private lemma sum_sq_norm_KHatH_le_one (N : ℕ) :
    (∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2) ≤ 1 := by
  have hsum :
      (∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2)
        ≤ ∑ k ∈ kSupport N, ‖KHatH k‖ := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk0 : 0 ≤ ‖KHatH k‖ := norm_nonneg _
    have hk1 : ‖KHatH k‖ ≤ 1 := norm_KHatH_le_one k
    nlinarith
  have hsum1 :
      (∑ k ∈ kSupport N, ‖KHatH k‖) ≤ 1 := by
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
  exact le_trans hsum hsum1

private lemma sum_sq_norm_KHatH_on_nmSupportZero_le_one (N : ℕ) :
    (∑ nm ∈ nmSupportZero N, ‖KHatH (kFn nm)‖ ^ 2) ≤ 1 := by
  classical
  have hinj :
      ∀ a₁ ∈ nmSupportZero N, ∀ a₂ ∈ nmSupportZero N, kFn a₁ = kFn a₂ → a₁ = a₂ := by
    intro a₁ ha₁ a₂ ha₂ hk
    exact kFn_injOn_nmSupportZero N ha₁ ha₂ hk
  have himage :
      ((nmSupportZero N).image kFn).sum (fun k : ℤ => ‖KHatH k‖ ^ 2)
        =
      (nmSupportZero N).sum (fun nm : ℕ × ℕ => ‖KHatH (kFn nm)‖ ^ 2) := by
    exact
      (sum_image_eq_of_injOn (s := nmSupportZero N) (f := kFn)
        (g := fun k : ℤ => ‖KHatH k‖ ^ 2) hinj)
  calc
    (∑ nm ∈ nmSupportZero N, ‖KHatH (kFn nm)‖ ^ 2)
        =
      ∑ k ∈ (nmSupportZero N).image kFn, ‖KHatH k‖ ^ 2 := by
          simpa using himage.symm
    _ ≤ ∑ k ∈ kSupport N, ‖KHatH k‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (mem_image_kFn_subset_kSupport N)
            (fun _ _ _ => sq_nonneg _)
    _ ≤ 1 := sum_sq_norm_KHatH_le_one N

/-- Exact `t = 0` formula for the canonical minor expansion. -/
theorem typeIPart_eq_q0NormFactor_mul_sum_nmSupport0 (X N : ℕ) :
    canonicalExpansion.typeIPart X N
      =
    q0NormFactor N
      * ∑ nm ∈ nmSupportZero N,
          aTerm X nm.1 * aTerm X nm.2
            * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
            * KHatH (kFn nm) := by
  unfold FrequencyExpansion.typeIPart canonicalExpansion coeff nmSupportZero
  apply congrArg (fun z : ℂ => q0NormFactor N * z)
  refine Finset.sum_congr rfl ?_
  intro nm hnm
  have ht0 : tFn N nm = 0 := (mem_nmSupportOfT_iff.mp hnm).2.2
  simp [atom, ht0, mul_assoc, mul_left_comm, mul_comm]

/-- Pointwise deterministic Type-I bound in terms of the diagonal mass. -/
theorem typeIPart_norm_sq_le_weight0_sq_mul_diagMass (X N : ℕ) :
    ‖canonicalExpansion.typeIPart X N‖ ^ 2
      ≤
    ‖q0NormFactor N‖ ^ 2
      * (‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 * diagMass X N) := by
  have hrepr := typeIPart_eq_q0NormFactor_mul_sum_nmSupport0 (X := X) (N := N)
  rw [hrepr]
  have hq0 :
      ‖q0NormFactor N * ∑ nm ∈ nmSupportZero N,
          aTerm X nm.1 * aTerm X nm.2
            * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
            * KHatH (kFn nm)‖ ^ 2
        =
      ‖q0NormFactor N‖ ^ 2
        * ‖∑ nm ∈ nmSupportZero N,
            aTerm X nm.1 * aTerm X nm.2
              * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
              * KHatH (kFn nm)‖ ^ 2 := by
    rw [norm_mul]
    ring
  rw [hq0]
  have hcs :
      ‖∑ nm ∈ nmSupportZero N,
          aTerm X nm.1 * aTerm X nm.2
            * (minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm))‖ ^ 2
        ≤
      (∑ nm ∈ nmSupportZero N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        *
      ∑ nm ∈ nmSupportZero N, ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm)‖ ^ 2 := by
    simpa [mul_assoc] using
      (norm_sum_mul_sq_le_sum_sq_mul_sum_sq
        (s := nmSupportZero N)
        (b := fun nm => aTerm X nm.1 * aTerm X nm.2)
        (w := fun nm => minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm)))
  have hker :
      (∑ nm ∈ nmSupportZero N, ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm)‖ ^ 2)
        ≤ ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 := by
    have hnorm :
        (∑ nm ∈ nmSupportZero N, ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm)‖ ^ 2)
          =
        ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2
          * (∑ nm ∈ nmSupportZero N, ‖KHatH (kFn nm)‖ ^ 2) := by
      calc
        (∑ nm ∈ nmSupportZero N, ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm)‖ ^ 2)
            =
          ∑ nm ∈ nmSupportZero N,
            (‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2) * (‖KHatH (kFn nm)‖ ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro nm hnm
              rw [norm_mul]
              ring
        _ =
          ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2
            * (∑ nm ∈ nmSupportZero N, ‖KHatH (kFn nm)‖ ^ 2) := by
              simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    rw [hnorm]
    have hle :
        ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2
          * (∑ nm ∈ nmSupportZero N, ‖KHatH (kFn nm)‖ ^ 2)
            ≤
        ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 * 1 := by
      exact
        mul_le_mul_of_nonneg_left
          (sum_sq_norm_KHatH_on_nmSupportZero_le_one N)
          (sq_nonneg ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖)
    simpa using hle
  have h0 :
      0 ≤ ∑ nm ∈ nmSupportZero N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2 := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hmul :
      (∑ nm ∈ nmSupportZero N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        *
      (∑ nm ∈ nmSupportZero N, ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm)‖ ^ 2)
        ≤
      (∑ nm ∈ nmSupportZero N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        * ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_left hker h0
  have hsum :
      (∑ nm ∈ nmSupportZero N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2) = diagMass X N := by
    change
      (∑ nm ∈ (((s N).product (s N)).filter
          (fun nm => ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)) = 0)),
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
        =
      ∑ nm ∈ (((s N).product (s N)).filter
          (fun nm => ((nm.1 : ℤ) + (nm.2 : ℤ) - (N : ℤ)) = 0)),
        ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2
    rfl
  have hmain :
      ‖∑ nm ∈ nmSupportZero N,
          aTerm X nm.1 * aTerm X nm.2
            * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
            * KHatH (kFn nm)‖ ^ 2
        ≤
      diagMass X N * ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 := by
    calc
      ‖∑ nm ∈ nmSupportZero N,
          aTerm X nm.1 * aTerm X nm.2
            * minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0
            * KHatH (kFn nm)‖ ^ 2
          ≤
        (∑ nm ∈ nmSupportZero N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          *
        (∑ nm ∈ nmSupportZero N, ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0 * KHatH (kFn nm)‖ ^ 2) := by
            simpa [mul_assoc] using hcs
      _ ≤
        (∑ nm ∈ nmSupportZero N, ‖aTerm X nm.1 * aTerm X nm.2‖ ^ 2)
          * ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 := hmul
      _ = diagMass X N * ‖minorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 := by
          rw [hsum]
  have hscaled :=
    mul_le_mul_of_nonneg_left hmain (sq_nonneg ‖q0NormFactor N‖)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- The Type-I pointwise bound rewritten via the hard-minor/major complement identity at `t = 0`. -/
theorem typeIPart_norm_sq_le_complement_weight_sq_mul_diagMass (X N : ℕ) :
    ‖canonicalExpansion.typeIPart X N‖ ^ 2
      ≤
    ‖q0NormFactor N‖ ^ 2
      * (‖1 - Q0MajorTailTTStarAlgebra.majorArcWeightFourier X TurnkeyRouteQ0.Δ_canon 0‖ ^ 2 * diagMass X N) := by
  simpa [minorArcWeightFourier_zero, mul_assoc, mul_left_comm, mul_comm] using
    typeIPart_norm_sq_le_weight0_sq_mul_diagMass (X := X) (N := N)

end

end Goldbach.Cert.MajorArcModules.Q0MinorTypeIDeterministic
