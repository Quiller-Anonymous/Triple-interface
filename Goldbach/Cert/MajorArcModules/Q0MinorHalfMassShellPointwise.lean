import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
import Goldbach.ProofTools

/-!
Pointwise deterministic bounds for the unscaled geometric zero slice on the canonical even window.

This file isolates the denominator-control input needed by the half-mass shell residual:

* a direct pointwise lower bound coming from the diagonal pair `n = m = N / 2`,
* a direct pointwise upper bound coming from the total tent-kernel mass on the finite interval
  window.

No new arithmetic estimates appear here. Everything is exact interval geometry plus the existing
`KHatH`/BG kernel API.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassTailShell
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarAlgebra
open Goldbach.Cert.MajorArcModules.Q0MinorTTStarFrequencyExpansion
open Goldbach.Cert.MajorArcModules.Q0MinorZeroModeEnvelope

noncomputable section

private abbrev s (N : ℕ) : Finset ℕ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N

private def uniformWindow (X : ℕ) : Finset ℕ :=
  Finset.Icc (X / 2 - H) (X / 2 + H)

private lemma Icc_eq_image_range (a b : ℕ) :
    Finset.Icc a b = (Finset.range (b + 1 - a)).image (fun k : ℕ => a + k) := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨n - a, ?_, by omega⟩
    exact Finset.mem_range.mpr (by omega)
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    refine Finset.mem_Icc.mpr ?_
    constructor
    · exact Nat.le_add_right _ _
    · have hk' : k < b + 1 - a := Finset.mem_range.mp hk
      omega

private lemma H_even_split : H = 2 * (H / 2) := by
  norm_num [H]

private lemma mem_s_sub_of_mem_s {N n : ℕ} (hn : n ∈ s N) : N - n ∈ s N := by
  rcases Finset.mem_Icc.mp hn with ⟨hn2, hnN⟩
  have hn_le : n ≤ N := le_trans hnN (Nat.sub_le N 2)
  have h2N : 2 ≤ N := le_trans hn2 hn_le
  have hNp2_le : n + 2 ≤ N := (Nat.le_sub_iff_add_le h2N).1 hnN
  have h2pN : 2 + n ≤ N := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hNp2_le
  have hNm_ge2 : 2 ≤ N - n := (Nat.le_sub_iff_add_le hn_le).2 h2pN
  have hNm_le : N - n ≤ N - 2 := Nat.sub_le_sub_left hn2 N
  exact Finset.mem_Icc.mpr ⟨hNm_ge2, hNm_le⟩

private lemma H_le_X_div2 {X : ℕ} (hX : X0 ≤ X) : H ≤ X / 2 := by
  have h2H : 2 * H ≤ X0 := by decide
  have h2H' : 2 * H ≤ X := le_trans h2H hX
  have hmul : H * 2 ≤ X := by simpa [Nat.mul_comm] using h2H'
  exact (Nat.le_div_iff_mul_le (by decide : 0 < (2 : ℕ))).2 hmul

private lemma window_card_eq (X : ℕ) (hX : X0 ≤ X) : (uniformWindow X).card = 2 * H + 1 := by
  classical
  have hHX : H ≤ X / 2 := H_le_X_div2 (X := X) hX
  set a : ℕ := X / 2 - H
  have ha : a + H = X / 2 := by
    simpa [a] using (Nat.sub_add_cancel hHX)
  have hb : X / 2 + H = a + 2 * H := by
    calc
      X / 2 + H = (a + H) + H := by simpa [ha, Nat.add_assoc]
      _ = a + (H + H) := by simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = a + 2 * H := by simp [two_mul, Nat.add_assoc]
  have hcard :
      (uniformWindow X).card = (X / 2 + H) + 1 - (X / 2 - H) := by
    simpa [uniformWindow] using (Finset.card_Icc (a := (X / 2 - H)) (b := (X / 2 + H)))
  calc
    (uniformWindow X).card
        = (a + 2 * H) + 1 - a := by simpa [hcard, a, hb]
    _ = (a + (2 * H + 1)) - a := by
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = 2 * H + 1 := by
          simpa using (Nat.add_sub_cancel_left a (2 * H + 1))

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

private lemma norm_KHatH_le_peak (k : ℤ) :
    ‖KHatH k‖ ≤ (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
  by_cases hk : k ∈ Goldbach.BG_Identity.S_BG
  · rw [KHatH_eq_of_mem_S_BG hk]
    have hpeak :=
      Goldbach.BG_Identity.K_full_peak_le (U := Goldbach.BG_Identity.Ucut) (k := k)
    have hnonneg : 0 ≤ Goldbach.BG_Identity.K_full k := Goldbach.BG_Identity.K_full_nonneg k
    calc
      ‖(Goldbach.BG_Identity.K_full k : ℂ)‖ = |Goldbach.BG_Identity.K_full k| := by simp
      _ ≤ (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
        simpa [Goldbach.BG_Identity.K_full, abs_of_nonneg hnonneg] using hpeak
  · rw [KHatH_eq_zero_of_not_mem_S_BG hk]
    have hU : 0 ≤ (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by positivity
    simpa using hU

private theorem unscaledGeometricZeroSliceMass_eq_singleSum
    (X N : ℕ) :
    unscaledGeometricZeroSliceMass X N
      =
    ∑ n ∈ s N,
      uniformWindowSupportIndicator X n
        * uniformWindowSupportIndicator X (N - n)
        * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ)) := by
  classical
  unfold unscaledGeometricZeroSliceMass
  have hsum :
      (∑ nm ∈ nmSupportOfT N 0,
          uniformWindowSupportIndicator X nm.1
            * uniformWindowSupportIndicator X nm.2
            * KHatH (kFn nm))
        =
      ∑ n ∈ s N, ∑ m ∈ s N,
        if n + m = N then
          uniformWindowSupportIndicator X n
            * uniformWindowSupportIndicator X m
            * KHatH ((m : ℤ) - (n : ℤ))
        else 0 := by
    unfold Q0MinorTTStarFrequencyExpansion.nmSupportOfT
      Q0MinorTTStarFrequencyExpansion.nmSupport
    rw [Finset.sum_filter]
    have hprod :
        (∑ a ∈ (s N).product (s N),
            if ((a.1 : ℤ) + (a.2 : ℤ) - (N : ℤ)) = 0 then
              uniformWindowSupportIndicator X a.1
                * uniformWindowSupportIndicator X a.2
                * KHatH ((a.2 : ℤ) - (a.1 : ℤ))
            else 0)
          =
        ∑ n ∈ s N, ∑ m ∈ s N,
          if ((n : ℤ) + (m : ℤ) - (N : ℤ)) = 0 then
            uniformWindowSupportIndicator X n
              * uniformWindowSupportIndicator X m
              * KHatH ((m : ℤ) - (n : ℤ))
          else 0 := by
            simp [Finset.sum_product]
    rw [hprod]
    refine Finset.sum_congr rfl ?_
    intro n hn
    refine Finset.sum_congr rfl ?_
    intro m hm
    by_cases hnm : n + m = N
    · have hnmz : ((n : ℤ) + (m : ℤ) - (N : ℤ)) = 0 := by
        have hcast : (((n + m : ℕ) : ℤ) : ℤ) = (N : ℤ) := by
          exact_mod_cast hnm
        omega
      simp [hnmz, hnm]
    · have hnmz : ((n : ℤ) + (m : ℤ) - (N : ℤ)) ≠ 0 := by
        intro hz
        exact hnm (by omega)
      simp [hnmz, hnm]
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hm : N - n ∈ s N := mem_s_sub_of_mem_s (N := N) (n := n) hn
  have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
  have huniq : ∀ {m : ℕ}, n + m = N → m = N - n := by
    intro m hnm
    have := congrArg (fun t : ℕ => t - n) hnm
    simpa [Nat.add_sub_cancel_left] using this
  have hcollapse :
      (∑ m ∈ s N,
          if n + m = N then
            uniformWindowSupportIndicator X n
              * uniformWindowSupportIndicator X m
              * KHatH ((m : ℤ) - (n : ℤ))
          else 0)
        =
      uniformWindowSupportIndicator X n
        * uniformWindowSupportIndicator X (N - n)
        * KHatH ((((N - n : ℕ)) : ℤ) - (n : ℤ)) := by
    rw [Finset.sum_eq_single (N - n)]
    · have hnm : n + (N - n) = N := Nat.add_sub_of_le hn_le
      simp [hnm]
    · intro m hm' hne
      by_cases hnm : n + m = N
      · exfalso
        exact hne (huniq hnm)
      · simp [hnm]
    · intro hnotmem
      exfalso
      exact hnotmem hm
  exact hcollapse

private lemma window_subset_s_on_even_window
    {X N n : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) (hn : n ∈ uniformWindow X) :
    n ∈ s N := by
  rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
  have hbase : H + 2 ≤ X / 2 := by
    have hbase0 : H + 2 ≤ X0 / 2 := by norm_num [X0, H]
    exact le_trans hbase0 (Nat.div_le_div_right hX)
  have hleft : 2 ≤ X / 2 - H := by omega
  have hrightX : X / 2 + H ≤ X - 2 := by
    have hHle : H ≤ X / 2 - 2 := by omega
    have h1 : X / 2 + H ≤ X / 2 + (X / 2 - 2) := Nat.add_le_add_left hHle (X / 2)
    have h2 : X / 2 + (X / 2 - 2) ≤ X - 2 := by
      have hmul : X / 2 + X / 2 ≤ X := by
        simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using
          (Nat.mul_div_le X 2)
      omega
    exact le_trans h1 h2
  have hXleN : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  have hrightN : X / 2 + H ≤ N - 2 := by omega
  exact Finset.mem_Icc.mpr ⟨le_trans hleft hlo, le_trans hhi hrightN⟩

private lemma midpoint_mem_uniformWindow
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    N / 2 ∈ uniformWindow X := by
  have hmem : N ∈ Goldbach.Windows.IccShift X H := (Goldbach.ProofTools.Windows.mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN |>.1
  rcases Goldbach.ProofTools.Windows.mem_IccShift_iff (X := X) (H := H) (N := N) |>.1 hmem with ⟨k, hk, rfl⟩
  refine Finset.mem_Icc.mpr ?_
  constructor
  · have hmono : X / 2 ≤ (X + k) / 2 := Nat.div_le_div_right (Nat.le_add_right X k)
    omega
  · have htwo : 0 < (2 : ℕ) := by decide
    rw [Nat.div_le_iff_le_mul_add_pred htwo]
    have hmod : X % 2 ≤ 1 := by
      exact Nat.le_pred_of_lt (Nat.mod_lt _ htwo)
    have hXbound : X ≤ 2 * (X / 2) + 1 := by
      calc
        X = 2 * (X / 2) + X % 2 := by
              simpa [Nat.mul_comm] using (Nat.div_add_mod X 2).symm
        _ ≤ 2 * (X / 2) + 1 := by gcongr
    omega

private lemma midpoint_mem_s_on_even_window
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    N / 2 ∈ s N := by
  exact window_subset_s_on_even_window hX hN (midpoint_mem_uniformWindow hN)

private lemma midpoint_add_midpoint_eq_of_even
    {N : ℕ} (hEven : Goldbach.Windows.IsEven N) :
    N / 2 + N / 2 = N := by
  rcases Goldbach.Windows.even_of_isEven hEven with ⟨k, hk⟩
  rw [hk]
  omega

private lemma midpoint_sub_halfH_mem_uniformWindow
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    N / 2 - H / 2 ∈ uniformWindow X := by
  have hmid : N / 2 ∈ uniformWindow X := midpoint_mem_uniformWindow hN
  rcases Finset.mem_Icc.mp hmid with ⟨hmid_lo, hmid_hi⟩
  refine Finset.mem_Icc.mpr ?_
  constructor
  · have hhalf_le : H / 2 ≤ H := Nat.div_le_self _ _
    have h1 : X / 2 - H ≤ X / 2 - H / 2 := Nat.sub_le_sub_left hhalf_le (X / 2)
    have hXN : X / 2 ≤ N / 2 :=
      Nat.div_le_div_right (Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN)
    have h2 : X / 2 - H / 2 ≤ N / 2 - H / 2 := Nat.sub_le_sub_right hXN (H / 2)
    exact le_trans h1 h2
  · exact le_trans (Nat.sub_le _ _) hmid_hi

private lemma midpoint_add_halfH_mem_uniformWindow
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    N / 2 + H / 2 ∈ uniformWindow X := by
  rcases Goldbach.ProofTools.Windows.mem_EvenIn_iff (X := X) (H := H) (N := N) |>.1 hN with
    ⟨hIcc, _⟩
  have hN_le : N ≤ X + H := Goldbach.ProofTools.Windows.le_right_of_mem_IccShift hIcc
  have hupper_half : N / 2 ≤ X / 2 + H / 2 := by
    have h1 : N / 2 ≤ (X + H) / 2 := Nat.div_le_div_right hN_le
    have h2 : (X + H) / 2 ≤ X / 2 + H / 2 := by
      rw [H_even_split]
      exact le_of_eq (by simpa using (Nat.add_mul_div_right X (H / 2) (by decide : 0 < 2)))
    exact le_trans h1 h2
  refine Finset.mem_Icc.mpr ?_
  constructor
  · exact le_trans ((Finset.mem_Icc.mp (midpoint_mem_uniformWindow hN)).1) (Nat.le_add_right _ _)
  · have hhalf : H / 2 + H / 2 = H := by
      simpa [two_mul] using H_even_split.symm
    have hsum : X / 2 + H / 2 + H / 2 = X / 2 + H := by
      calc
        X / 2 + H / 2 + H / 2 = X / 2 + (H / 2 + H / 2) := by omega
        _ = X / 2 + H := by rw [hhalf]
    calc
      N / 2 + H / 2 ≤ X / 2 + H / 2 + H / 2 := Nat.add_le_add_right hupper_half (H / 2)
      _ = X / 2 + H := hsum

private lemma coreWindowSubset_uniformWindow
    {X N n : ℕ} (hN : N ∈ EvenIn X H)
    (hn : n ∈ Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)) :
    n ∈ uniformWindow X := by
  have hleft : N / 2 - H / 2 ∈ uniformWindow X := midpoint_sub_halfH_mem_uniformWindow hN
  have hright : N / 2 + H / 2 ∈ uniformWindow X := midpoint_add_halfH_mem_uniformWindow hN
  rcases Finset.mem_Icc.mp hleft with ⟨hleft_lo, _⟩
  rcases Finset.mem_Icc.mp hright with ⟨_, hright_hi⟩
  rcases Finset.mem_Icc.mp hn with ⟨hn_lo, hn_hi⟩
  exact Finset.mem_Icc.mpr ⟨le_trans hleft_lo hn_lo, le_trans hn_hi hright_hi⟩

private lemma coreWindowSubset_s
    {X N n : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    (hn : n ∈ Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)) :
    n ∈ s N := by
  rcases Finset.mem_Icc.mp hn with ⟨hn_lo, hn_hi⟩
  have hNX : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
  have hNbig : H / 2 + 2 ≤ N / 2 := by
    have hbase : H / 2 + 2 ≤ X0 / 2 := by norm_num [X0, H]
    exact le_trans hbase (Nat.div_le_div_right (le_trans hX hNX))
  refine Finset.mem_Icc.mpr ?_
  constructor
  · omega
  · omega

private lemma core_reflect_mem
    {N n : ℕ} (hEven : Goldbach.Windows.IsEven N)
    (hn : n ∈ Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)) :
    N - n ∈ Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2) := by
  rcases Finset.mem_Icc.mp hn with ⟨hn_lo, hn_hi⟩
  have hNeq : N = 2 * (N / 2) := by
    simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (midpoint_add_midpoint_eq_of_even hEven).symm
  refine Finset.mem_Icc.mpr ?_
  constructor
  · omega
  · omega

private lemma core_term_eq_KHatH
    {X N n : ℕ} (hN : N ∈ EvenIn X H)
    (hn : n ∈ Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)) :
    uniformWindowSupportIndicator X n
      * uniformWindowSupportIndicator X (N - n)
      * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))
      =
    KHatH (((N - n : ℕ) : ℤ) - (n : ℤ)) := by
  have hnw : n ∈ uniformWindow X := coreWindowSubset_uniformWindow hN hn
  have hEven : Goldbach.Windows.IsEven N :=
    (Goldbach.ProofTools.Windows.mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN |>.2
  have hmw : N - n ∈ uniformWindow X :=
    coreWindowSubset_uniformWindow hN (core_reflect_mem hEven hn)
  have hnw' : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hnw
  have hmw' : N - n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hmw
  simp [uniformWindowSupportIndicator, hnw', hmw']

private lemma term_eq_zero_outside_core
    {X N n : ℕ} (hEven : Goldbach.Windows.IsEven N)
    (hn : n ∈ s N)
    (hout : n ∉ Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)) :
    uniformWindowSupportIndicator X n
      * uniformWindowSupportIndicator X (N - n)
      * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))
      =
    0 := by
  have hNeq : N = 2 * (N / 2) := by
    simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (midpoint_add_midpoint_eq_of_even hEven).symm
  have hk_out :
      (((N - n : ℕ) : ℤ) - (n : ℤ)) ∉ Goldbach.BG_Identity.S_BG := by
    rw [Goldbach.BG_Identity.mem_S_BG_iff]
    rcases Finset.mem_Icc.mp hn with ⟨_, hn_hi⟩
    have hcase :
        n < N / 2 - H / 2 ∨ N / 2 + H / 2 < n := by
      by_cases hlt : n < N / 2 - H / 2
      · exact Or.inl hlt
      · have hge : N / 2 - H / 2 ≤ n := le_of_not_gt hlt
        by_cases hgt : N / 2 + H / 2 < n
        · exact Or.inr hgt
        · exfalso
          exact hout (Finset.mem_Icc.mpr ⟨hge, le_of_not_gt hgt⟩)
    rcases hcase with hlt | hgt
    · have hk_gt : (H : ℤ) < (((N - n : ℕ) : ℤ) - (n : ℤ)) := by
        have hltz : (n : ℤ) < ((N / 2 - H / 2 : ℕ) : ℤ) := by
          exact_mod_cast hlt
        have : (((N - n : ℕ) : ℤ) - (n : ℤ)) = (N : ℤ) - 2 * (n : ℤ) := by
          have hn_le : n ≤ N := le_trans hn_hi (Nat.sub_le N 2)
          omega
        rw [this]
        have hNint : (N : ℤ) = 2 * ((N / 2 : ℕ) : ℤ) := by exact_mod_cast hNeq
        have hHint : (H : ℤ) = 2 * ((H / 2 : ℕ) : ℤ) := by exact_mod_cast H_even_split
        omega
      omega
    · have hk_lt : (((N - n : ℕ) : ℤ) - (n : ℤ)) < -(H : ℤ) := by
        have : (((N - n : ℕ) : ℤ) - (n : ℤ)) = (N : ℤ) - 2 * (n : ℤ) := by
          have hn_le : n ≤ N := le_trans hn_hi (Nat.sub_le N 2)
          omega
        rw [this]
        have hNint : (N : ℤ) = 2 * ((N / 2 : ℕ) : ℤ) := by exact_mod_cast hNeq
        have hHint : (H : ℤ) = 2 * ((H / 2 : ℕ) : ℤ) := by exact_mod_cast H_even_split
        omega
      omega
  rw [KHatH_eq_zero_of_not_mem_S_BG hk_out]
  simp

private lemma coreWindow_card
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    (Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)).card = H + 1 := by
  have hcard :
      (Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)).card
        =
      (N / 2 + H / 2) + 1 - (N / 2 - H / 2) := by
    simpa using (Finset.card_Icc (a := (N / 2 - H / 2)) (b := (N / 2 + H / 2)))
  have hHleN : H / 2 ≤ N / 2 := by
    have hXleN : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
    have hbase : H / 2 ≤ X0 / 2 := by norm_num [X0, H]
    exact le_trans hbase (Nat.div_le_div_right (le_trans hX hXleN))
  have hhalf : H / 2 + H / 2 = H := by
    simpa [two_mul] using H_even_split.symm
  calc
    (Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)).card
        = (N / 2 + H / 2) + 1 - (N / 2 - H / 2) := hcard
    _ = H + 1 := by
      omega

private theorem unscaledGeometricZeroSliceMass_eq_fixed_even_offset_sum
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    unscaledGeometricZeroSliceMass X N
      =
    ∑ k ∈ Finset.range (H + 1), KHatH ((H : ℤ) - (2 * k : ℕ)) := by
  let core : Finset ℕ := Finset.Icc (N / 2 - H / 2) (N / 2 + H / 2)
  let coreImage : Finset ℕ := (Finset.range (H + 1)).image (fun k : ℕ => (N / 2 - H / 2) + k)
  let term : ℕ → ℂ := fun n =>
    uniformWindowSupportIndicator X n
      * uniformWindowSupportIndicator X (N - n)
      * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))
  have hcore_subset : core ⊆ s N := by
    intro n hn
    exact coreWindowSubset_s hX hN hn
  have hEven : Goldbach.Windows.IsEven N :=
    (Goldbach.ProofTools.Windows.mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN |>.2
  rw [unscaledGeometricZeroSliceMass_eq_singleSum]
  have hzero_outside : ∀ n, n ∈ s N → n ∉ core → term n = 0 := by
    intro n hns hnnotcore
    exact term_eq_zero_outside_core hEven hns hnnotcore
  have hfilter_core : (s N).filter (fun n => n ∈ core) = core := by
    apply Finset.ext
    intro n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      exact Finset.mem_filter.mpr ⟨hcore_subset hn, hn⟩
  calc
    ∑ n ∈ s N, term n
        = Finset.sum (s N) (fun n =>
            if n ∈ core then KHatH (((N - n : ℕ) : ℤ) - (n : ℤ)) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro n hns
              by_cases hn : n ∈ core
              · simp [term, hn, core_term_eq_KHatH hN hn]
              · simp [hn, hzero_outside n hns hn]
    _ = Finset.sum ((s N).filter (fun n => n ∈ core))
          (fun n => KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))) := by
            rw [Finset.sum_filter]
    _ = ∑ n ∈ core, KHatH (((N - n : ℕ) : ℤ) - (n : ℤ)) := by
          rw [hfilter_core]
    _ = Finset.sum coreImage (fun n => KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))) := by
          have hcoreImage : core = coreImage := by
            ext n
            constructor
            · intro hn
              have hn' : N / 2 - H / 2 ≤ n ∧ n ≤ N / 2 + H / 2 := by
                simpa [core] using Finset.mem_Icc.mp hn
              refine Finset.mem_image.mpr ?_
              refine ⟨n - (N / 2 - H / 2), ?_, ?_⟩
              · have : n - (N / 2 - H / 2) < H + 1 := by
                  omega
                simpa [coreImage] using this
              · omega
            · intro hn
              rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
              have ha' : a < H + 1 := by simpa [coreImage] using ha
              have hXleN : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
              have hHleN : H / 2 ≤ N / 2 := by
                have hbase : H / 2 ≤ X0 / 2 := by norm_num [X0, H]
                exact le_trans hbase (Nat.div_le_div_right (le_trans hX hXleN))
              apply Finset.mem_Icc.mpr
              have haH : a ≤ H := Nat.le_of_lt_succ ha'
              constructor
              · exact Nat.le_add_right _ _
              · calc
                  (N / 2 - H / 2) + a ≤ (N / 2 - H / 2) + H := Nat.add_le_add_left haH _
                  _ = N / 2 + H / 2 := by
                    rw [H_even_split, two_mul]
                    calc
                      (N / 2 - H / 2) + (H / 2 + H / 2)
                          = ((N / 2 - H / 2) + H / 2) + H / 2 := by omega
                      _ = N / 2 + H / 2 := by rw [Nat.sub_add_cancel hHleN]
          rw [hcoreImage]
    _ = ∑ k ∈ Finset.range (H + 1),
          KHatH (((N - ((N / 2 - H / 2) + k) : ℕ) : ℤ) - (((N / 2 - H / 2) + k : ℕ) : ℤ)) := by
          dsimp [coreImage]
          symm
          rw [Finset.sum_image]
          · rfl
          · intro a _ b _ hab
            exact Nat.add_left_cancel hab
    _ = ∑ k ∈ Finset.range (H + 1), KHatH ((H : ℤ) - (2 * k : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hNeq : N = 2 * (N / 2) := by
            simpa [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (midpoint_add_midpoint_eq_of_even hEven).symm
          have hHint : H = 2 * (H / 2) := H_even_split
          have hXleN : X ≤ N := Goldbach.ProofTools.Windows.le_left_of_mem_EvenIn hN
          have hHleN : H / 2 ≤ N / 2 := by
            have hbase : H / 2 ≤ X0 / 2 := by norm_num [X0, H]
            exact le_trans hbase (Nat.div_le_div_right (le_trans hX hXleN))
          have hcalc :
              (((N - ((N / 2 - H / 2) + k) : ℕ) : ℕ) : ℤ) - (((N / 2 - H / 2) + k : ℕ) : ℤ)
                =
              (H : ℤ) - (2 * k : ℕ) := by
            have hk' : k ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            have hnk_le : (N / 2 - H / 2) + k ≤ N := by
              calc
                (N / 2 - H / 2) + k ≤ (N / 2 - H / 2) + H := Nat.add_le_add_left hk' _
                _ = N / 2 + H / 2 := by
                  rw [hHint]
                  omega
                _ ≤ N := by
                  omega
            have hsub :
                (((N - ((N / 2 - H / 2) + k) : ℕ) : ℕ) : ℤ) =
                  (N : ℤ) - (((N / 2 - H / 2) + k : ℕ) : ℤ) := by
              exact Int.ofNat_sub hnk_le
            rw [hsub]
            have hNint : (N : ℤ) = 2 * ((N / 2 : ℕ) : ℤ) := by exact_mod_cast hNeq
            have hHintInt : (H : ℤ) = 2 * ((H / 2 : ℕ) : ℤ) := by exact_mod_cast hHint
            have hsubInt :
                (((N / 2 - H / 2 : ℕ) : ℕ) : ℤ) = ((N / 2 : ℕ) : ℤ) - ((H / 2 : ℕ) : ℤ) := by
              exact Int.ofNat_sub hHleN
            have harg :
                ((((N / 2 - H / 2) + k : ℕ) : ℕ) : ℤ)
                  = ((N / 2 : ℕ) : ℤ) - ((H / 2 : ℕ) : ℤ) + (k : ℤ) := by
              calc
                ((((N / 2 - H / 2) + k : ℕ) : ℕ) : ℤ)
                    = (((N / 2 - H / 2 : ℕ) : ℕ) : ℤ) + (k : ℤ) := by
                        rw [Nat.cast_add]
                _ = ((N / 2 : ℕ) : ℤ) - ((H / 2 : ℕ) : ℤ) + (k : ℤ) := by
                      rw [hsubInt]
            rw [harg, hNint, hHintInt]
            norm_num [Nat.cast_mul]
            ring
          exact congrArg KHatH hcalc

/-- The unscaled geometric zero slice is exactly constant on the canonical even window. -/
theorem unscaledGeometricZeroSliceMass_eq_of_mem_even_window
    {X N M : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) (hM : M ∈ EvenIn X H) :
    unscaledGeometricZeroSliceMass X N = unscaledGeometricZeroSliceMass X M := by
  rw [unscaledGeometricZeroSliceMass_eq_fixed_even_offset_sum hX hN,
    unscaledGeometricZeroSliceMass_eq_fixed_even_offset_sum hX hM]

private lemma unscaledGeometricZeroSliceMass_term_re_nonneg
    (X N n : ℕ) :
    0 ≤
      (uniformWindowSupportIndicator X n
        * uniformWindowSupportIndicator X (N - n)
        * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))).re := by
  by_cases hn : n ∈ uniformWindow X
  · by_cases hm : N - n ∈ uniformWindow X
    · have hn' : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hn
      have hm' : N - n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hm
      by_cases hk : (((N - n : ℕ) : ℤ) - (n : ℤ)) ∈ Goldbach.BG_Identity.S_BG
      · rw [KHatH_eq_of_mem_S_BG hk]
        simp [uniformWindowSupportIndicator, hn', hm', Goldbach.BG_Identity.K_full_nonneg]
      · rw [KHatH_eq_zero_of_not_mem_S_BG hk]
        simp [uniformWindowSupportIndicator, hn', hm']
    · have hn' : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hn
      have hm' : N - n ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hm
      simp [uniformWindowSupportIndicator, hn', hm']
  · have hn' : n ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hn
    simp [uniformWindowSupportIndicator, hn']

private lemma unscaledGeometricZeroSliceMass_re_nonneg
    (X N : ℕ) :
    0 ≤ (unscaledGeometricZeroSliceMass X N).re := by
  rw [unscaledGeometricZeroSliceMass_eq_singleSum]
  rw [Complex.re_sum]
  exact Finset.sum_nonneg (fun n hn => unscaledGeometricZeroSliceMass_term_re_nonneg X N n)

private lemma midpoint_term_eq_KHatH_zero
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    uniformWindowSupportIndicator X (N / 2)
      * uniformWindowSupportIndicator X (N - N / 2)
      * KHatH (((N - N / 2 : ℕ) : ℤ) - ((N / 2 : ℕ) : ℤ))
      =
    KHatH 0 := by
  have hmid : N / 2 ∈ uniformWindow X := midpoint_mem_uniformWindow hN
  have hmid' : N / 2 ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hmid
  have hEven : Goldbach.Windows.IsEven N := (Goldbach.ProofTools.Windows.mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN |>.2
  have hsum : N / 2 + N / 2 = N := midpoint_add_midpoint_eq_of_even hEven
  have hsub : N - N / 2 = N / 2 := (Nat.eq_sub_of_add_eq hsum).symm
  simp [uniformWindowSupportIndicator, hmid', hsub]

private lemma unscaledGeometricZeroSliceMass_re_lower
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    Goldbach.BG_Identity.K_full (0 : ℤ) ≤ (unscaledGeometricZeroSliceMass X N).re := by
  rw [unscaledGeometricZeroSliceMass_eq_singleSum]
  rw [Complex.re_sum]
  have hmid_s : N / 2 ∈ s N := midpoint_mem_s_on_even_window hX hN
  have hnonneg :
      ∀ n ∈ s N,
        0 ≤
          (uniformWindowSupportIndicator X n
            * uniformWindowSupportIndicator X (N - n)
            * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))).re := by
    intro n hn
    exact unscaledGeometricZeroSliceMass_term_re_nonneg X N n
  have hsingle :
      (uniformWindowSupportIndicator X (N / 2)
        * uniformWindowSupportIndicator X (N - N / 2)
        * KHatH (((N - N / 2 : ℕ) : ℤ) - ((N / 2 : ℕ) : ℤ))).re
      ≤
      (∑ n ∈ s N,
        (uniformWindowSupportIndicator X n
          * uniformWindowSupportIndicator X (N - n)
          * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))).re) := by
    exact Finset.single_le_sum hnonneg hmid_s
  have hK0 : KHatH 0 = (Goldbach.BG_Identity.K_full 0 : ℂ) := by
    exact KHatH_eq_of_mem_S_BG Goldbach.BG_Identity.mem_S_BG_zero
  calc
    Goldbach.BG_Identity.K_full (0 : ℤ)
        =
      (uniformWindowSupportIndicator X (N / 2)
        * uniformWindowSupportIndicator X (N - N / 2)
        * KHatH (((N - N / 2 : ℕ) : ℤ) - ((N / 2 : ℕ) : ℤ))).re := by
          rw [midpoint_term_eq_KHatH_zero hN, hK0]
          simp [Goldbach.BG_Identity.K_full_nonneg]
    _ ≤
      (∑ n ∈ s N,
        (uniformWindowSupportIndicator X n
          * uniformWindowSupportIndicator X (N - n)
          * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))).re) := hsingle

private lemma unscaledGeometricZeroSliceMass_norm_le_two
    (X N : ℕ) (hX : X0 ≤ X) :
    ‖unscaledGeometricZeroSliceMass X N‖ ≤ 2 := by
  rw [unscaledGeometricZeroSliceMass_eq_singleSum]
  have htri :
      ‖∑ n ∈ s N,
          uniformWindowSupportIndicator X n
            * uniformWindowSupportIndicator X (N - n)
            * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖
        ≤
      ∑ n ∈ s N,
        ‖uniformWindowSupportIndicator X n
          * uniformWindowSupportIndicator X (N - n)
          * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖ := by
    simpa using
      (norm_sum_le (s := s N)
        (f := fun n =>
          uniformWindowSupportIndicator X n
            * uniformWindowSupportIndicator X (N - n)
            * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))))
  have hpoint :
      ∀ n ∈ s N,
        ‖uniformWindowSupportIndicator X n
          * uniformWindowSupportIndicator X (N - n)
          * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖
            ≤
        if n ∈ uniformWindow X then (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ else 0 := by
    intro n hn
    by_cases hnw : n ∈ uniformWindow X
    · have hnw' : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hnw
      by_cases hmw : N - n ∈ uniformWindow X
      · have hmw' : N - n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hmw
        calc
          ‖uniformWindowSupportIndicator X n
              * uniformWindowSupportIndicator X (N - n)
              * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖
              =
            ‖KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖ := by
              simp [uniformWindowSupportIndicator, hnw', hmw', norm_mul]
          _ ≤ (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := norm_KHatH_le_peak _
          _ = if n ∈ uniformWindow X then (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ else 0 := by
              simp [hnw]
      · have hmw' : N - n ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hmw
        have hnonneg : 0 ≤ (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by positivity
        simpa [uniformWindowSupportIndicator, hnw', hmw', hnw] using hnonneg
    · have hnw' : n ∉ Finset.Icc (X / 2 - H) (X / 2 + H) := by simpa [uniformWindow] using hnw
      simp [uniformWindowSupportIndicator, hnw', hnw]
  have hmajor :
      ∑ n ∈ s N,
        ‖uniformWindowSupportIndicator X n
          * uniformWindowSupportIndicator X (N - n)
          * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖
        ≤
      ∑ n ∈ uniformWindow X, (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
    let c : ℝ := (Goldbach.BG_Identity.Ucut : ℝ)⁻¹
    have hs :
        (s N).filter (fun n => n ∈ uniformWindow X) ⊆ uniformWindow X := by
      intro n hn
      exact (Finset.mem_filter.mp hn).2
    have hcard_le : ((s N).filter (fun n => n ∈ uniformWindow X)).card ≤ (uniformWindow X).card :=
      Finset.card_le_card hs
    have hcard_le' : (((s N).filter (fun n => n ∈ uniformWindow X)).card : ℝ) ≤ ((uniformWindow X).card : ℝ) := by
      exact_mod_cast hcard_le
    have hU_nonneg : 0 ≤ (Goldbach.BG_Identity.Ucut : ℝ) := by
      norm_num [Goldbach.BG_Identity.Ucut, H]
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      exact inv_nonneg.mpr hU_nonneg
    have hsum_filter :
        ∑ n ∈ (s N).filter (fun n => n ∈ uniformWindow X), c
          = (((s N).filter (fun n => n ∈ uniformWindow X)).card : ℝ) * c := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hsum_window :
        ∑ n ∈ uniformWindow X, c = ((uniformWindow X).card : ℝ) * c := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc
      ∑ n ∈ s N,
        ‖uniformWindowSupportIndicator X n
          * uniformWindowSupportIndicator X (N - n)
          * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖
          ≤
      ∑ n ∈ s N, if n ∈ uniformWindow X then c else 0 := by
        exact Finset.sum_le_sum (fun n hn => hpoint n hn)
      _ = ∑ n ∈ (s N).filter (fun n => n ∈ uniformWindow X), c := by
        rw [Finset.sum_filter]
      _ = (((s N).filter (fun n => n ∈ uniformWindow X)).card : ℝ) * c := hsum_filter
      _ ≤ ((uniformWindow X).card : ℝ) * c := by
        exact mul_le_mul_of_nonneg_right hcard_le' hc_nonneg
      _ = ∑ n ∈ uniformWindow X, c := by
        rw [hsum_window]
  have htwo :
      ((2 * H + 1 : ℕ) : ℝ) * (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ ≤ 2 := by
    norm_num [Goldbach.BG_Identity.Ucut, H]
  exact le_trans htri <| by
    calc
      ∑ n ∈ s N,
        ‖uniformWindowSupportIndicator X n
          * uniformWindowSupportIndicator X (N - n)
          * KHatH (((N - n : ℕ) : ℤ) - (n : ℤ))‖
          ≤
      ∑ n ∈ uniformWindow X, (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := hmajor
      _ = ((2 * H + 1 : ℕ) : ℝ) * (Goldbach.BG_Identity.Ucut : ℝ)⁻¹ := by
            simp [window_card_eq X hX]
      _ ≤ 2 := htwo

/-- Explicit pointwise canonical-window norm control for the unscaled geometric zero slice. -/
theorem unscaledGeometricZeroSliceMassWindowNormTarget_explicit :
    UnscaledGeometricZeroSliceMassWindowNormTarget (Goldbach.BG_Identity.K_full (0 : ℤ)) 2 := by
  refine
    { c0_pos := Goldbach.BG_Identity.K_full_pos_at_zero
      c1_nonneg := by norm_num
      lower := ?_
      upper := ?_ }
  · intro X N hX hN
    have hre_nonneg : 0 ≤ (unscaledGeometricZeroSliceMass X N).re :=
      unscaledGeometricZeroSliceMass_re_nonneg X N
    calc
      Goldbach.BG_Identity.K_full (0 : ℤ) ≤ (unscaledGeometricZeroSliceMass X N).re :=
        unscaledGeometricZeroSliceMass_re_lower hX hN
      _ ≤ |(unscaledGeometricZeroSliceMass X N).re| := by
        simp [abs_of_nonneg hre_nonneg]
      _ ≤ ‖unscaledGeometricZeroSliceMass X N‖ := by
        simpa using (Complex.abs_re_le_norm (unscaledGeometricZeroSliceMass X N))
  · intro X N _hX _hN
    exact unscaledGeometricZeroSliceMass_norm_le_two X N _hX

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellPointwise
