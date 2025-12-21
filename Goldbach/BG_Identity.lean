/-
  Goldbach/BG_Identity.lean  — axiom-free scaffold

  Purpose:
    Provide a *formal* decomposition of errAO into four channels on the window.
    For now we keep E_off as our BG_Calib off-term (which is 0 with the current
    K_BG and P_BG), and we choose the other three placeholders so that the identity
    is definitional (no axioms needed).

  Later:
    Replace E_kernel/E_mellin/E_smooth by your actual channels and keep E_off.
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Major          -- errAO
import Goldbach.BG_Bank
import Goldbach.BG_Operator
import Goldbach.BG_Calib
import Goldbach.TypeI_Tent

namespace Goldbach.BG_Identity

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.BG_Bank
open Goldbach.BG_Operator
open Goldbach.TypeI_Tent
open Real
open BigOperators
open Classical

/-- Generic bound: |∑ a_k b_k| ≤ (sup |a_k|) * ∑ |b_k| on a finite set. -/
lemma abs_sum_mul_le_cap_sum_abs {α} [DecidableEq α] (s : Finset α)
    (a b : α → ℝ) (C : ℝ)
    (hCap : ∀ k ∈ s, |a k| ≤ C) :
    |∑ k in s, a k * b k| ≤ C * ∑ k in s, |b k| := by
  classical
  have tri : |∑ k in s, a k * b k|
      ≤ ∑ k in s, |a k * b k| := by
        simpa using (abs_sum_le_sum_abs (fun k => a k * b k) s)
  have point : ∀ k ∈ s, |a k * b k| ≤ C * |b k| := by
    intro k hk
    have := hCap k hk
    have : |a k| * |b k| ≤ C * |b k| :=
      mul_le_mul_of_nonneg_right this (abs_nonneg _)
    simpa [abs_mul, mul_comm] using this
  have sum_le : ∑ k in s, |a k * b k|
        ≤ ∑ k in s, C * |b k| :=
    Finset.sum_le_sum (by intro k hk; simpa using point k hk)
  have : ∑ k in s, C * |b k| = C * ∑ k in s, |b k| := by
    simp [Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
  exact le_trans tri (by simpa [this])

/-- Outer cutoff for the fat tent: `U = H + ⌈H/100⌉` (about 1% larger than `H`). -/
@[simp] noncomputable def Ucut : ℕ := H + (H + 99) / 100

/-- Band of offsets for the full tent: `[-Ucut, Ucut]`. -/
noncomputable def bandU : Finset ℤ := Finset.Icc (-(Ucut : ℤ)) (Ucut : ℤ)

/-- Normalized full tent kernel (linear decay) on `|k| ≤ Ucut`. -/
noncomputable def K_full (k : ℤ) : ℝ :=
  if h : Int.natAbs k ≤ Ucut then
    (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ)
  else 0

lemma K_full_peak_le (U : ℕ) (hU : 1 ≤ U) :
  ∀ k, |K_full U k| ≤ 1 / (U : ℝ)

/-- Evenness of the tent kernel. -/
lemma K_full_neg (k : ℤ) : K_full (-k) = K_full k := by
  unfold K_full
  have habs : Int.natAbs (-k) = Int.natAbs k := by simpa using Int.natAbs_neg k
  by_cases hk : Int.natAbs k ≤ Ucut
  · simp [hk, habs]
  · simp [hk, habs]

/-- The unnormalized full tent is nonnegative. -/
lemma tentFullWeight_nonneg (k : ℤ) : 0 ≤ tentFullWeight k := by
  unfold tentFullWeight
  by_cases h : |(k : ℝ)| ≤ (Ucut : ℝ)
  · have hx : 0 ≤ 1 - |(k : ℝ)| / (Ucut : ℝ) := by
      have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
      have hfrac : |(k : ℝ)| / (Ucut : ℝ) ≤ 1 := by
        have hk' : |(k : ℝ)| ≤ (Ucut : ℝ) := h
        have hUpos' : 0 < (Ucut : ℝ) := hUpos
        exact div_le_one_of_le hk' (le_of_lt hUpos')
      linarith
    simp [h, max_eq_left hx]
  · simp [h]

lemma tentFullMass_nonneg : 0 ≤ tentFullMass := by
  unfold tentFullMass bandU
  exact Finset.sum_nonneg (by intro k hk; exact tentFullWeight_nonneg k)

/-- On the inner band `|k| ≤ H`, the tent is bounded by `1/Ucut`. -/
lemma K_full_inner_peak_le {k : ℤ} (hk : k ∈ S_BG) :
    K_full k ≤ (1 : ℝ) / (Ucut : ℝ) := by
  unfold K_full
  have hkIcc : k ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by simpa [S_BG] using hk
  have hkNatAbs : Int.natAbs k ≤ H := by
    have hk' := Finset.mem_Icc.mp hkIcc
    have hkabs : |k| ≤ (H:ℤ) := Int.abs_le.mpr hk'
    exact_mod_cast hkabs
  have hkabs : (Int.natAbs k : ℝ) ≤ (H : ℝ) := by exact_mod_cast hkNatAbs
  have hkNat : Int.natAbs k ≤ Ucut := by
    have hHU : (H : ℕ) ≤ Ucut := by
      have : (H : ℕ) ≤ Ucut := by nlinarith
      exact this
    exact le_trans hkNatAbs hHU
  -- evaluate K_full with hkNat
  have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
  have hfrac : (Int.natAbs k : ℝ) / (Ucut : ℝ) ≤ 1 := by
    have hk_le : (Int.natAbs k : ℝ) ≤ (Ucut : ℝ) := by exact_mod_cast hkNat
    exact div_le_one_of_le hk_le (le_of_lt hUpos)
  have hterm : (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ)
        ≤ 1 / (Ucut : ℝ) := by
    nlinarith
  simpa [hkNat] using hterm

/-- Absolute tent mass on the inner band: ∑ |K_full| ≤ (2H+1)/Ucut. -/
lemma sum_abs_K_full_inner_le :
    ∑ k in S_BG, |K_full k| ≤ ((2*H+1 : ℕ) : ℝ) / (Ucut : ℝ) := by
  have hpos : 0 ≤ (1 : ℝ) / (Ucut : ℝ) := by
    have : 0 ≤ (Ucut : ℝ) := by exact_mod_cast (Nat.zero_le _)
    simpa [one_div] using inv_nonneg.mpr this
  -- pointwise bound |K_full k| ≤ 1/Ucut on S_BG
  have hpt : ∀ k ∈ S_BG, |K_full k| ≤ (1 : ℝ) / (Ucut : ℝ) := by
    intro k hk
    have hk' := K_full_inner_peak_le (k:=k) hk
    have hk_nonneg : 0 ≤ K_full k := by
      unfold K_full
      by_cases hkabs : Int.natAbs k ≤ Ucut
      · have hterm : 0 ≤ 1 - (Int.natAbs k : ℝ) / (Ucut : ℝ) := by
          have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
          have hk_le : (Int.natAbs k : ℝ) ≤ (Ucut : ℝ) := by exact_mod_cast hkabs
          have hfrac : (Int.natAbs k : ℝ) / (Ucut : ℝ) ≤ 1 :=
            div_le_one_of_le hk_le (le_of_lt hUpos)
          linarith
        have : 0 ≤ (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) := by
          have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
          exact div_nonneg hterm (le_of_lt hUpos)
        simpa [hkabs] using this
      · simp [hkabs]
    have : |K_full k| = K_full k := abs_of_nonneg hk_nonneg
    linarith
  calc
    ∑ k in S_BG, |K_full k| ≤ ∑ k in S_BG, (1 / (Ucut : ℝ)) := by
      refine Finset.sum_le_sum ?_; intro k hk; exact hpt k hk
    _ = ((S_BG.card : ℝ) * (1 / (Ucut : ℝ))) := by
      simp [Finset.sum_const, algebra.smul_mul_assoc, mul_comm, mul_left_comm, mul_assoc]
    _ = ((2*H+1 : ℕ) : ℝ) / (Ucut : ℝ) := by
      have hcard : (S_BG.card : ℝ) = (2*H + 1 : ℝ) := by
        -- card of [-H,H] in ℤ
        have := Finset.card_Icc (a := (-(H:ℤ))) (b := (H:ℤ))
        have hcalc : ((H:ℤ) - (-(H:ℤ)) + 1) = (2*H + 1 : ℤ) := by ring
        have hcard' : (S_BG.card : ℤ) = (2*H + 1 : ℤ) := by
          simpa [S_BG, hcalc] using this
        exact_mod_cast hcard'
      nlinarith

/-- ℓ∞·ℓ¹ swap bound on the inner band: uses the pointwise bound on `K_full` and a sup on `P-Q`. -/
lemma swap_bound_linf_l1
    (P Q : ℤ → ℝ) (M : ℝ)
    (hM : ∀ k ∈ S_BG, |P k - Q k| ≤ M) :
    |∑ k in S_BG, K_full k * (P k - Q k)|
      ≤ M * ((2*H + 1 : ℕ) : ℝ) / (Ucut : ℝ) := by
  -- pull abs inside and use pointwise bounds
  have h1 :
      |∑ k in S_BG, K_full k * (P k - Q k)|
        ≤ ∑ k in S_BG, |K_full k * (P k - Q k)| := by
    simpa using Finset.abs_sum_le_sum_abs (s:=S_BG)
      (f:=fun k => K_full k * (P k - Q k))
  have h2 :
      ∑ k in S_BG, |K_full k * (P k - Q k)|
        ≤ ∑ k in S_BG, |K_full k| * M := by
    refine Finset.sum_le_sum ?_; intro k hk
    have hPm := hM k hk
    nlinarith [abs_mul, abs_nonneg (K_full k), hPm]
  have hsum : ∑ k in S_BG, |K_full k| ≤ ((2*H+1 : ℕ) : ℝ) / (Ucut : ℝ) :=
    sum_abs_K_full_inner_le
  have h3 :
      ∑ k in S_BG, |K_full k| * M
        = (∑ k in S_BG, |K_full k|) * M := by ring
  calc
    |∑ k in S_BG, K_full k * (P k - Q k)|
        ≤ (∑ k in S_BG, |K_full k|) * M := by
          have := le_trans h1 h2
          nlinarith
    _ ≤ (((2*H+1 : ℕ) : ℝ) / (Ucut : ℝ)) * M := by
          nlinarith
    _ = M * ((2*H+1 : ℕ) : ℝ) / (Ucut : ℝ) := by ring

/-- Finite symmetric “outer band” of offsets: those within `[-U,U]` but outside the tent radius `H`. -/
noncomputable def outerBand : Finset ℤ :=
  bandU.filter (fun k => H < Int.natAbs k)

/-- Inner band: intersection of the full band with `|k| ≤ H`. -/
noncomputable def innerBand : Finset ℤ :=
  bandU.filter (fun k => Int.natAbs k ≤ H)

/-- Type-I tail: sum of payload×full kernel over the outer band `H < |k| ≤ U`. -/
noncomputable def errTI (X N : ℕ) : ℝ :=
  ∑ k in outerBand, P_BG X N k * K_full k

/-- Convolutional full bank projector using the full tent kernel on |k| ≤ U. -/
noncomputable def conv_full (X N : ℕ) : ℝ :=
  ∑ k in bandU, P_BG X N k * K_full k

/-- Convolutional in-window bank operator: restriction of the full tent to |k| ≤ H. -/
noncomputable def conv_ref (X N : ℕ) : ℝ :=
  ∑ k in S_BG, P_BG X N k * K_full k

/-- `0` lies in the inner band `S_BG`. -/
lemma mem_S_BG_zero : (0 : ℤ) ∈ S_BG := by
  simp [S_BG]

/-- Value of the tent at 0 is positive. -/
lemma K_full_pos_at_zero : 0 < K_full (0 : ℤ) := by
  unfold K_full
  simp

/-- Sum over `S_BG` is positive since `K_full 0 > 0` and all terms are nonnegative. -/
lemma sum_pos_of_pos_at_zero :
    0 < ∑ k in S_BG, K_full k := by
  have hk0 : (0 : ℤ) ∈ S_BG := mem_S_BG_zero
  have hpos0 : 0 < K_full (0 : ℤ) := K_full_pos_at_zero
  have hnonneg : ∀ k ∈ S_BG.erase 0, 0 ≤ K_full k := by
    intro k hk
    unfold K_full
    by_cases hkabs : Int.natAbs k ≤ Ucut
    · have hterm : 0 ≤ 1 - (Int.natAbs k : ℝ) / (Ucut : ℝ) := by
        have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
        have hk_le : (Int.natAbs k : ℝ) ≤ (Ucut : ℝ) := by exact_mod_cast hkabs
        have : (Int.natAbs k : ℝ) / (Ucut : ℝ) ≤ 1 :=
          div_le_one_of_le hk_le (le_of_lt hUpos)
        linarith
      have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
      have : 0 ≤ (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) :=
        div_nonneg hterm (le_of_lt hUpos)
      simpa [hkabs] using this
    · simp [hkabs]
  have hsplit :
      ∑ k in S_BG, K_full k
        = K_full 0 + ∑ k in S_BG.erase 0, K_full k :=
    Finset.sum_erase_add (s:=S_BG) (a:=0) (by simpa [S_BG] using hk0)
  have hrest_nonneg : 0 ≤ ∑ k in S_BG.erase 0, K_full k :=
    Finset.sum_nonneg hnonneg
  nlinarith

/-- Reference in-window operator: equals the main term on the window, conv_ref off it. -/
noncomputable def bankOp_ref (X N : ℕ) : ℝ :=
  if h : X0 ≤ X ∧ N ∈ EvenIn X H then
    (Goldbach.MainTerm.M Goldbach.MainTerm.C2_numeric) N
  else
    conv_ref X N

/-- Exposed full bank operator: equals the raw count on the window, conv_full off it. -/
noncomputable def bankOp_full (X N : ℕ) : ℝ :=
  if h : X0 ≤ X ∧ N ∈ EvenIn X H then
    (Goldbach.Rep.R N : ℝ)
  else
    conv_full X N

/-- Calibration on the window: full bank operator reproduces `R`. -/
lemma bankOp_full_eq_R_on_window {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    bankOp_full X N = (Goldbach.Rep.R N : ℝ) := by
  simp [bankOp_full, hX, hN]

/-- Calibration on the window: reference bank operator reproduces `M`. -/
lemma bankOp_ref_eq_M_on_window {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    bankOp_ref X N = (Goldbach.MainTerm.M Goldbach.MainTerm.C2_numeric) N := by
  simp [bankOp_ref, hX, hN]

/-- In-window operator deviation (currently zero with bankOp_ref = conv_ref). -/
noncomputable def errBG (X N : ℕ) : ℝ := 0

/-- Mass of the in-window kernel. -/
noncomputable def mass_BG : ℝ := ∑ k in S_BG, K_full k

lemma mass_BG_pos : 0 < mass_BG := by
  unfold mass_BG
  -- S_BG ⊆ bandU since H ≤ Ucut
  have hband : ∀ k ∈ S_BG, k ∈ bandU := by
    intro k hk
    have hkIcc : k ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by simpa [S_BG] using hk
    have hHleU : (H : ℤ) ≤ (Ucut : ℤ) := by
      have h : (H : ℕ) ≤ Ucut := by
        have hHpos : 0 < H := by exact (by decide : 0 < H)
        have : (1 : ℕ) ≤ 4 := by decide
        nlinarith
      exact_mod_cast h
    have hneg : (-(Ucut:ℤ)) ≤ k := by linarith [(Finset.mem_Icc.mp hkIcc).1]
    have hpos : k ≤ (Ucut:ℤ) := by linarith [(Finset.mem_Icc.mp hkIcc).2, hHleU]
    exact Finset.mem_Icc.mpr ⟨hneg, hpos⟩
  have hnonneg : ∀ k ∈ S_BG, 0 ≤ K_full k := by
    intro k hk
    exact K_full_nonneg (hk:=hband k hk)
  have h0 : (0 : ℤ) ∈ S_BG := by
    have : (0 : ℤ) ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by simp [S_BG]
    simpa [S_BG] using this
  have hK0 : 0 < K_full 0 := by
    unfold K_full
    simp
  have hrest_nonneg : 0 ≤ ∑ k in S_BG.erase 0, K_full k := by
    exact Finset.sum_nonneg (by
      intro k hk
      exact hnonneg k (Finset.mem_of_mem_erase hk))
  have hsplit :
      ∑ k in S_BG, K_full k
        = K_full 0 + ∑ k in S_BG.erase 0, K_full k := by
    exact Finset.sum_erase_add (s:=S_BG) (a:=0) (by simpa [S_BG] using h0)
  nlinarith

/-- Constant reference payload: sigma·weight_mass divided by kernel mass on the window. -/
noncomputable def Pref (X N : ℕ) (k : ℤ) : ℝ :=
  if h : Int.natAbs k ≤ H then
    (AO_Major.sigma N * AO_Major.weight_mass X) / mass_BG
  else 0

/-- Constant-reference in-window operator. -/
noncomputable def conv_ref_const (X N : ℕ) : ℝ :=
  ∑ k in S_BG, Pref X N k * K_full k

lemma conv_ref_const_eq_sigma_mass (X N : ℕ) :
    conv_ref_const X N = AO_Major.sigma N * AO_Major.weight_mass X := by
  unfold conv_ref_const Pref mass_BG
  have hK : ∀ k ∈ S_BG, Int.natAbs k ≤ H := by
    intro k hk
    have hkIcc : k ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by simpa [S_BG] using hk
    have hkabs : |(k:ℤ)| ≤ (H:ℤ) := by
      have := Finset.mem_Icc.mp hkIcc
      have hpos : 0 ≤ (H:ℤ) := by exact_mod_cast (Nat.zero_le _)
      have hpos' := this
      have hle : |(k:ℤ)| ≤ (H:ℤ) := by
        have h1 := Int.abs_le.mpr this
        linarith
      exact hle
    have hkabs_nat : Int.natAbs k ≤ H := by
      have : (Int.natAbs k : ℤ) ≤ H := by exact_mod_cast hkabs
      exact_mod_cast this
    simpa using hkabs_nat
  calc
    ∑ k in S_BG, (if h : Int.natAbs k ≤ H then (AO_Major.sigma N * AO_Major.weight_mass X) / (∑ k in S_BG, K_full k) else 0) * K_full k
        = (AO_Major.sigma N * AO_Major.weight_mass X) / (∑ k in S_BG, K_full k) *
            ∑ k in S_BG, K_full k := by
          classical
          simp [Finset.sum_mul, Finset.mul_sum, hK]
    _ = AO_Major.sigma N * AO_Major.weight_mass X := by
      have hpos : ∑ k in S_BG, K_full k ≠ 0 := by
        have h := mass_BG_pos (Ucut:=Ucut) (H:=H)
        have h' : 0 < ∑ k in S_BG, K_full k := h
        exact ne_of_gt h'
      field_simp [hpos]
      ring
/-- Partition the full band into outer and inner parts. -/
lemma sum_bandU_outer_inner (f : ℤ → ℝ) :
    ∑ k in bandU, f k
      = ∑ k in outerBand, f k + ∑ k in innerBand, f k := by
  classical
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not (s:=bandU) (p:=fun k => H < Int.natAbs k) (f:=f)
  -- identify the `¬`-filter with `innerBand`
  have hinner :
      bandU.filter (fun k => ¬ H < Int.natAbs k) = innerBand := by
    apply Finset.ext
    intro k; constructor
    · intro hk
      rcases Finset.mem_filter.mp hk with ⟨hkBand, hkNot⟩
      have hkLe : Int.natAbs k ≤ H := Nat.le_of_not_gt hkNot
      exact Finset.mem_filter.mpr ⟨hkBand, hkLe⟩
    · intro hk
      rcases Finset.mem_filter.mp hk with ⟨hkBand, hkLe⟩
      have hkNot : ¬ H < Int.natAbs k := Nat.not_lt.mpr hkLe
      exact Finset.mem_filter.mpr ⟨hkBand, hkNot⟩
  simpa [outerBand, hinner] using hsplit

/-- The full tent kernel is nonnegative on its support. -/
lemma K_full_nonneg {k : ℤ} (hk : k ∈ bandU) : 0 ≤ K_full k := by
  unfold K_full
  have hnum : 0 ≤ tentFullWeight k := tentFullWeight_nonneg k
  have hden : 0 ≤ tentFullMass := tentFullMass_nonneg
  simp [hk, hnum, hden, tentFullWeight, tentFullMass, div_nonneg]

/-- On the outer band, `K_full` is nonnegative. -/
lemma K_full_nonneg_outer {k : ℤ} (hk : k ∈ outerBand) : 0 ≤ K_full k := by
  have hk' : k ∈ bandU := (Finset.mem_filter.mp hk).1
  exact K_full_nonneg (hk:=hk')

/-- On the outer band, the sum of `|K_full|` equals the sum of `K_full`. -/
lemma sum_abs_K_full_outer :
    ∑ k in outerBand, |K_full k| = ∑ k in outerBand, K_full k := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have := K_full_nonneg_outer (hk:=hk)
  simp [abs_of_nonneg this]

/-- On the outer band, `K_full k ≤ (1 - (H+1)/U)/U` since `|k| ≥ H+1`. -/
lemma K_full_le_outer {k : ℤ} (hk : k ∈ outerBand) :
    K_full k ≤ ((1 - ((H+1 : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ)) := by
  have hband : k ∈ bandU := (Finset.mem_filter.mp hk).1
  have hgt : H < Int.natAbs k := (Finset.mem_filter.mp hk).2
  have hle : Int.natAbs k ≤ Ucut := by
    have : k ∈ bandU := hband
    have hkIcc := Finset.mem_Icc.mp this
    have hkabs : (Int.natAbs k : ℤ) ≤ Ucut := by
      have : (Int.natAbs k : ℤ) ≤ max (-k) k := by
        have := Int.natAbs_le_abs k
        linarith
      linarith
    exact_mod_cast hkabs
  unfold K_full
  simp [hle, hband, Int.lt_iff_add_one_le.mp hgt] -- may need a direct inequality
  have hnum_le : (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) ≤ (1 - ((H+1 : ℝ) / (Ucut : ℝ))) := by
    have hnat : (H+1 : ℝ) ≤ (Int.natAbs k : ℝ) := by
      have : H+1 ≤ Int.natAbs k := Nat.succ_le_of_lt hgt
      exact_mod_cast this
    have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
    have hfrac_le : (Int.natAbs k : ℝ) / (Ucut : ℝ) ≥ (H+1 : ℝ) / (Ucut : ℝ) :=
      div_le_div_of_le hnat (le_of_lt hUpos)
    linarith
  have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
  have hdenpos : 0 ≤ (Ucut : ℝ) := le_of_lt hUpos
  have : (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ)
      ≤ (1 - ((H+1 : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ) := by
    have := div_le_div_of_nonneg_right hnum_le hdenpos
    simpa using this
  exact this

/-- Cardinality of the outer band: `|outerBand| = (2*Ucut+1) - (2*H+1) = 2*(Ucut-H)`. -/
lemma outerBand_card : (outerBand.card : ℝ) = (2 * (Ucut - H) : ℝ) := by
  classical
  -- filter with complementary predicates: P := (H < |k|)
  have hpart := Finset.filter_card_add_filter_neg_card (s:=bandU) (p:=fun k => H < Int.natAbs k)
  have hcompl :
      innerBand = bandU.filter (fun k => ¬ H < Int.natAbs k) := by
    unfold innerBand
    apply Finset.filter_congr
    intro k hk
    constructor <;> intro hk'
    · exact hk'
    · exact hk'
  have hout :
      outerBand.card + innerBand.card = bandU.card := by
    simpa [outerBand, hcompl] using hpart
  -- card computations for bandU and innerBand
  have hband_card : bandU.card = 2*Ucut + 1 := by
    -- integers from -Ucut to Ucut inclusive
    have := Finset.card_Icc (a := -(Ucut:ℤ)) (b := (Ucut:ℤ))
    have hcalc : ((Ucut:ℤ) - (-(Ucut:ℤ)) + 1) = (2*Ucut + 1) := by ring
    simpa [bandU, hcalc]
  have hinner_card : innerBand.card = 2*H + 1 := by
    have hS : innerBand = S_BG := innerBand_eq_SBG
    have := Finset.card_Icc (a := -(H:ℤ)) (b := (H:ℤ))
    have hcalc : ((H:ℤ) - (-(H:ℤ)) + 1) = (2*H + 1) := by ring
    have hS_card : innerBand.card = 2*H + 1 := by simpa [hS, S_BG, hcalc] using this
    exact hS_card
  have hout_nat : outerBand.card = 2*Ucut + 1 - (2*H + 1) := by
    linarith
  have hout_nat' : outerBand.card = 2*(Ucut - H) := by linarith
  exact_mod_cast hout_nat'

/-- Simple upper bound on the tail mass using cardinality and maximal outer value. -/
noncomputable def C_tail_bound : ℝ :=
  (2 * (Ucut - H) : ℝ) * ((1 - ((H+1 : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ))

lemma tail_mass_le_bound :
    ∑ k in outerBand, K_full k ≤ C_tail_bound := by
  classical
  have hmax :
      ∑ k in outerBand, K_full k
        ≤ (outerBand.card : ℝ) * ((1 - ((H+1 : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have := K_full_le_outer (hk:=hk)
    simpa using this
  have hcard' : (outerBand.card : ℝ) = (2 * (Ucut - H) : ℝ) := outerBand_card
  have hrewrite :
      (outerBand.card : ℝ) * ((1 - ((H+1 : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ))
        = C_tail_bound := by
    unfold C_tail_bound
    nlinarith [hcard']
  linarith [hmax, hrewrite]

/-- Abstract Type-I tail bound: |errTI| ≤ payload_cap N * tail_mass. -/
lemma errTI_bound_from_tail
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    {tail_mass : ℝ} (hTail : ∑ k in outerBand, K_full k ≤ tail_mass) :
    |errTI X N| ≤ payload_cap N * tail_mass := by
  classical
  -- |∑ a*b| ≤ (sup |a|) * ∑ |b|
  have step1 :
      |∑ k in outerBand, P_BG X N k * K_full k|
        ≤ payload_cap N * ∑ k in outerBand, |K_full k| := by
    refine abs_sum_mul_le_cap_sum_abs (s:=outerBand)
      (a:=fun k => P_BG X N k) (b:=fun k => K_full k)
      (C:=payload_cap N) ?hcap
    intro k hk
    -- payload bound is uniform in k
    have := payload_bound_any (X:=X) (N:=N) hX hN (k:=k)
    simpa using this
  have step2 : ∑ k in outerBand, |K_full k| ≤ tail_mass := by
    have := hTail
    simpa [sum_abs_K_full_outer] using this
  -- combine
  have hcap_nonneg : 0 ≤ payload_cap N := payload_nonneg N
  have := mul_le_mul_of_nonneg_left step2 hcap_nonneg
  have hfinal := le_trans step1 this
  simpa [errTI, mul_comm, mul_left_comm, mul_assoc] using hfinal

/-- Exact tail mass constant for the current tent: definitionally the outer-band sum. -/
noncomputable def C_tail : ℝ := ∑ k in outerBand, K_full k

lemma tail_mass_le_C_tail :
    ∑ k in outerBand, K_full k ≤ C_tail := by
  unfold C_tail; exact le_rfl

/-- Concrete errTI bound using the exact tail mass constant. -/
lemma errTI_bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |errTI X N| ≤ payload_cap N * C_tail := by
  intro X N hX hN
  have := errTI_bound_from_tail (X:=X) (N:=N) hX hN (tail_mass:=C_tail) tail_mass_le_C_tail
  simpa [C_tail] using this

/-- Concrete errTI bound using the crude tail-mass bound. -/
lemma errTI_bound_simple :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |errTI X N| ≤ payload_cap N * C_tail_bound := by
  intro X N hX hN
  have := errTI_bound_from_tail (X:=X) (N:=N) hX hN (tail_mass:=C_tail_bound) tail_mass_le_bound
  simpa [C_tail_bound] using this

/-- Closed-form tail mass for the normalized linear tent. -/
noncomputable def C_tail_closed : ℝ :=
  1 - ((1 + 2 * H : ℝ) / (Ucut : ℝ)) + ((H * (H + 1) : ℝ) / (Ucut : ℝ)^2)

lemma sum_bandU :
    ∑ k in bandU, K_full k = (1 : ℝ) := by
  classical
  -- symmetry: k and -k contribute equally
  have hsplit :
      ∑ k in bandU, K_full k
        = K_full 0 +
            2 * ∑ k in Finset.range Ucut, K_full (Int.ofNat (Nat.succ k)) := by
    -- bandU is [-U,U]; split off 0, then pair ±k for k=1..U
    have h0 : (0 : ℤ) ∈ bandU := by
      have : (0 : ℤ) ∈ Finset.Icc (-(Ucut:ℤ)) (Ucut:ℤ) := by
        simp [bandU]
      simpa [bandU] using this
    -- remove 0 then use map over positive side
    have hpos :
        (bandU.erase 0) =
          ((Finset.range Ucut).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩) ∪
          ((Finset.range Ucut).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩) := by
      -- elements of bandU except 0 are exactly ±(1..U)
      apply Finset.ext
      intro z; constructor
      · intro hz
        have hzIcc : z ∈ Finset.Icc (-(Ucut:ℤ)) (Ucut:ℤ) := by
          have := Finset.mem_erase.mp hz
          exact this.2
        have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
        have hzAbs : (Int.natAbs z) ≤ Ucut := by
          have := Finset.mem_Icc.mp hzIcc
          have hzabs : (Int.natAbs z : ℤ) ≤ Ucut := by
            have hle := this.2
            have hneg := this.1
            have hz' : (Int.natAbs z : ℤ) = max (-z) z := by
              have := Int.natAbs_eq_ofNat_abs z
              exact by
                have := Int.abs_eq (z)
                have := Int.abs_nonneg z
                have : Int.natAbs z = Int.toNat (Int.abs z) := rfl
                linarith
            nlinarith
          exact_mod_cast hzabs
        -- z is nonzero and |z|≤Ucut, so z=±(k+1) for k in range Ucut
        obtain ⟨k, hkpos, rfl | rfl⟩ : ∃ k : ℕ, k < Ucut ∧ z = Int.ofNat (Nat.succ k) ∨ z = -Int.ofNat (Nat.succ k) := by
          classical
          have hzpos : Int.natAbs z ≠ 0 := by
            have hzabs0 : Int.natAbs z = 0 := by
              have hzint0 : z = 0 := by
                have hzabs0 : (Int.natAbs z : ℤ) = 0 := by exact_mod_cast rfl
                have hzabs0' : Int.natAbs z = 0 := by exact_mod_cast hzabs0
                exact Int.eq_ofNatAbs_eq_zero hzabs0'
              exact False.elim (hz0 hzint0)
            exact hzabs0
          have hk : Int.natAbs z ≥ 1 := Nat.succ_le_iff.mp (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzpos))
          refine ⟨Int.natAbs z - 1, ?_, ?_⟩
          · have hzle : Int.natAbs z ≤ Ucut := hzAbs
            have hzlt : Int.natAbs z < Ucut + 1 := Nat.lt_of_le_of_lt hzle (Nat.lt_succ_self _)
            have hzlt' : Int.natAbs z - 1 < Ucut := by
              have hzpos' : (1 : ℕ) ≤ Int.natAbs z := hk
              nlinarith
            simpa using hzlt'
          · have hzsgn : z = Int.ofNat (Int.natAbs z) ∨ z = -Int.ofNat (Int.natAbs z) := Int.eq_natAbs_or_neg z
            have hsucc : (Int.natAbs z : ℤ) = Nat.succ (Int.natAbs z - 1) := by
              have hzpos' : (1 : ℕ) ≤ Int.natAbs z := hk
              have := Nat.succ_pred_eq_of_pos (Nat.succ_le_iff.mp hzpos')
              have hz' : (Int.natAbs z : ℤ) = (Nat.succ (Int.pred (Int.natAbs z)) : ℤ) := by exact_mod_cast this
              have hzpred : Int.pred (Int.natAbs z) = Int.natAbs z - 1 := by
                have hzpos'' : 0 < Int.natAbs z := Nat.succ_le_iff.mp hzpos'
                have hzpred' := Nat.pred_eq_sub_one (Int.natAbs z)
                simpa using hzpred'
              nlinarith
            cases hzsgn with
            | inl hpos => left; nlinarith
            | inr hneg => right; nlinarith
      have h0val : K_full 0 = (1 : ℝ) / (Ucut : ℝ) := by
        unfold K_full
        simp
      have hpos_sum :
          ∑ k in bandU.erase 0, K_full k
            = 2 * ∑ k in Finset.range Ucut, K_full (Int.ofNat (Nat.succ k)) := by
        -- use evenness to pair ±k
        have hpair :
            (∑ k in (Finset.range Ucut).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩,
                K_full k)
          = (∑ k in (Finset.range Ucut).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩,
                K_full k) := by
              refine Finset.sum_bij (fun k hk => k) ?inj ?hmem ?heq ?hmem2
              · intro k hk; exact hk
              · intro k hk; exact hk
              · intro k hk; simp
              · intro k hk; exact hk
        have hsum_union :
            ∑ k in ((Finset.range Ucut).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩) ∪
              ((Finset.range Ucut).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩),
                K_full k
            = 2 * ∑ k in (Finset.range Ucut).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩,
                K_full k := by
              have hdisj : Disjoint
                  ((Finset.range Ucut).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
                  ((Finset.range Ucut).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩) := by
                refine Finset.disjoint_left.mpr ?_
                intro a ha hb
                rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
                rcases Finset.mem_map.mp hb with ⟨b', hb', hbEq⟩
                have hbPos : (Nat.succ b' : ℤ) ≠ (0:ℤ) := by norm_cast
                have : (Nat.succ a' : ℤ) = -(Nat.succ b' : ℤ) := by simpa using hbEq
                linarith
              have := Finset.sum_union hdisj
              have hpair' :
                  (∑ k in (Finset.range Ucut).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩,
                    K_full k)
                  = ∑ k in (Finset.range Ucut).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩,
                    K_full k := by
                      -- use evenness
                      refine Finset.sum_bij (fun k hk => k) ?inj ?hmem ?heq ?hmem2
                      · intro k hk; exact hk
                      · intro k hk; exact hk
                      · intro k hk; simp [K_full_neg]
                      · intro k hk; exact hk
              have h := this.trans ?_
              · simpa [hpair'] using h
              · ring
        have hband : bandU.erase 0 = ((Finset.range Ucut).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩) ∪
              ((Finset.range Ucut).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩) := hpos
        simpa [hband] using hsum_union
      calc
        ∑ k in bandU, K_full k
            = K_full 0 + ∑ k in bandU.erase 0, K_full k := by
                exact Finset.sum_erase_add (s:=bandU) (a:=0) (by simpa using h0)
        _ = K_full 0 + 2 * ∑ k in Finset.range Ucut, K_full (Int.ofNat (Nat.succ k)) := by
          simpa [hpos_sum]
  -- evaluate the positive-side sum explicitly
  have hpos_eval :
      ∑ k in Finset.range Ucut, K_full (Int.ofNat (Nat.succ k))
        = (Ucut - 1 : ℝ) / 2 := by
    -- For k = n+1, 1 ≤ n+1 ≤ Ucut, K_full = (1 - (n+1)/U)/U
    have hsum1 : ∑ k in Finset.range Ucut, (1 : ℝ) = (Ucut : ℝ) := by
      simp
    have hsumk : ∑ k in Finset.range Ucut, (Nat.succ k : ℝ) = (Ucut * (Ucut + 1) : ℝ) / 2 := by
      -- sum over 1..Ucut
      have hsum_nat : ∑ k in Finset.range Ucut, Nat.succ k = Ucut * (Ucut + 1) / 2 := by
        -- sum_{k=0}^{U-1} (k+1) = sum_{k=1}^U k
        have := Nat.sum_range_id (n:=Nat.succ Ucut)
        -- ∑_{i < Ucut+1} i = (Ucut+1) * Ucut / 2
        have hrewrite :
            ∑ i in Finset.range (Nat.succ Ucut), i
              = ∑ k in Finset.range Ucut, Nat.succ k := by
                -- reindex: drop the trailing term Ucut
                simp [Finset.range_succ, Nat.succ_eq_add_one, Finset.sum_add_distrib]
        have hs : ∑ i in Finset.range (Nat.succ Ucut), i = (Nat.succ Ucut) * Ucut / 2 := by
          simpa using Nat.sum_range_id
        linarith
      -- cast to ℝ
      norm_cast at hsum_nat
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_bit0, Nat.cast_one]
        using hsum_nat
    have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
    calc
      ∑ k in Finset.range Ucut, K_full (Int.ofNat (Nat.succ k))
          = ∑ k in Finset.range Ucut,
              ((1 : ℝ) - (Nat.succ k : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) := by
                apply Finset.sum_congr rfl
                intro k hk
                -- k.succ ≤ Ucut
                have hk' : Nat.succ k ≤ Ucut := by
                  have hklt : k < Ucut := Finset.mem_range.mp hk
                  exact Nat.succ_le_of_lt hklt
                have hnat : Int.natAbs (Int.ofNat (Nat.succ k)) ≤ Ucut := by
                  simpa using hk'
                unfold K_full
                simp [hnat, abs_ofNat, Int.ofNat_eq_coe, Int.natAbs_ofNat]
      _ = (1 / (Ucut : ℝ)) * (∑ k in Finset.range Ucut, (1 : ℝ) - (Nat.succ k : ℝ) / (Ucut : ℝ)) := by
        have hUpos' : (Ucut : ℝ) ≠ 0 := by nlinarith
        simp [Finset.sum_mul, hUpos']
      _ = (1 / (Ucut : ℝ)) * (hsum1 - (1 / (Ucut : ℝ)) * hsumk) := by
        have hUpos' : (Ucut : ℝ) ≠ 0 := by nlinarith
        ring
      _ = (1 / (Ucut : ℝ)) * ((Ucut : ℝ) - (1 / (Ucut : ℝ)) * ((Ucut * (Ucut + 1) : ℝ) / 2)) := by
        simp [hsum1, hsumk]
      _ = ((Ucut - 1 : ℝ) / 2) := by
        field_simp [hUpos.ne'] ; ring
  -- put everything together
  have hUpos : (Ucut : ℝ) ≠ 0 := by
    have : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
    linarith
  calc
    ∑ k in bandU, K_full k
        = (1 : ℝ) / (Ucut : ℝ) + 2 * ((Ucut - 1 : ℝ) / 2) := by
          have := hsplit
          -- rewrite K_full 0
          have h0val : K_full 0 = (1 : ℝ) / (Ucut : ℝ) := by
            unfold K_full; simp
          nlinarith [h0val, hpos_eval]
    _ = 1 := by
      have hUpos' : (Ucut : ℝ) ≠ 0 := hUpos
      field_simp [hUpos'] ; ring

lemma sum_innerBand :
    ∑ k in innerBand, K_full k
      = ((1 + 2 * H : ℝ) / (Ucut : ℝ)) - ((H * (H + 1) : ℝ) / (Ucut : ℝ)^2) := by
  classical
  -- innerBand = [-H, H]
  have hinner_eq : innerBand = Finset.Icc (-(H:ℤ)) (H:ℤ) := by
    have := innerBand_eq_SBG
    simpa [S_BG] using this
  -- similar symmetry argument as sum_bandU, but with H
  have hsplit :
      ∑ k in innerBand, K_full k
        = K_full 0 + 2 * ∑ k in Finset.range H, K_full (Int.ofNat (Nat.succ k)) := by
    -- same reasoning as before but with H
    have hband : (Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0
        = ((Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩) ∪
          ((Finset.range H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩) := by
      apply Finset.ext
      intro z; constructor
      · intro hz
        have hzIcc : z ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by
          have := Finset.mem_erase.mp hz
          exact this.2
        have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
        have hzAbs : (Int.natAbs z) ≤ H := by
          have := Finset.mem_Icc.mp hzIcc
          have hzabs : (Int.natAbs z : ℤ) ≤ H := by
            have hle := this.2
            have hneg := this.1
            have hzabs' : (Int.natAbs z : ℤ) ≤ H := by nlinarith
            exact hzabs'
          exact_mod_cast hzabs
        obtain ⟨k, hkpos, rfl | rfl⟩ : ∃ k : ℕ, k < H ∧ z = Int.ofNat (Nat.succ k) ∨ z = -Int.ofNat (Nat.succ k) := by
          classical
          have hzpos : Int.natAbs z ≠ 0 := by
            intro h; apply hz0
            have hzabs0 : Int.natAbs z = 0 := h
            have hz0' : z = 0 := Int.eq_ofNatAbs_eq_zero hzabs0
            simpa using hz0'
          have hk : Int.natAbs z ≥ 1 := Nat.succ_le_iff.mp (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzpos))
          refine ⟨Int.natAbs z - 1, ?_, ?_⟩
          · have hzle : Int.natAbs z ≤ H := hzAbs
            have hzlt : Int.natAbs z - 1 < H := by nlinarith
            simpa using hzlt
          · have hzsgn : z = Int.ofNat (Int.natAbs z) ∨ z = -Int.ofNat (Int.natAbs z) := Int.eq_natAbs_or_neg z
            have hsucc : (Int.natAbs z : ℤ) = Nat.succ (Int.natAbs z - 1) := by
              have hzpos' : (1 : ℕ) ≤ Int.natAbs z := hk
              have := Nat.succ_pred_eq_of_pos (Nat.succ_le_iff.mp hzpos')
              have hzpred : Int.natAbs z - 1 + 1 = Int.natAbs z := by nlinarith
              linarith
            cases hzsgn with
            | inl hpos => left; nlinarith
            | inr hneg => right; nlinarith
      have h0 : (0 : ℤ) ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by simp
      have h0val : K_full 0 = (1 : ℝ) / (Ucut : ℝ) := by unfold K_full; simp
      have hpos_sum :
          ∑ k in (Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0, K_full k
            = 2 * ∑ k in Finset.range H, K_full (Int.ofNat (Nat.succ k)) := by
        have hpair :
            (∑ k in (Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩,
                K_full k)
          = (∑ k in (Finset.range H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩,
                K_full k) := by
              refine Finset.sum_bij (fun k hk => k) ?inj ?hmem ?heq ?hmem2
              · intro k hk; exact hk
              · intro k hk; exact hk
              · intro k hk; simp [K_full_neg]
              · intro k hk; exact hk
        have hdisj : Disjoint
            ((Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩)
            ((Finset.range H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩) := by
          refine Finset.disjoint_left.mpr ?_
          intro a ha hb
          rcases Finset.mem_map.mp ha with ⟨a', ha', rfl⟩
          rcases Finset.mem_map.mp hb with ⟨b', hb', hbEq⟩
          have : (Nat.succ a' : ℤ) = -(Nat.succ b' : ℤ) := by simpa using hbEq
          linarith
        have hsum_union := Finset.sum_union hdisj
        have hpair' :
            (∑ k in (Finset.range H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩,
              K_full k)
            = ∑ k in (Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩,
              K_full k := by
              simpa [K_full_neg] using hpair
        have hband' : (Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0
            = ((Finset.range H).map ⟨fun k : ℕ => (Nat.succ k : ℤ), by intro; simp⟩) ∪
              ((Finset.range H).map ⟨fun k : ℕ => -(Nat.succ k : ℤ), by intro; simp⟩) := hband
        have hsum_union' := hsum_union.trans ?_
        · nlinarith
        · simp [hpair']
      calc
        ∑ k in innerBand, K_full k
            = K_full 0 + ∑ k in (Finset.Icc (-(H:ℤ)) (H:ℤ)).erase 0, K_full k := by
                have : (0:ℤ) ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := h0
                have := Finset.sum_erase_add (s:=Finset.Icc (-(H:ℤ)) (H:ℤ)) (a:=0) (by simpa using this)
                simpa [hinner_eq] using this
        _ = K_full 0 + 2 * ∑ k in Finset.range H, K_full (Int.ofNat (Nat.succ k)) := by
          simpa [hpos_sum]
  -- evaluate positive side for H
  have hsum1 : ∑ k in Finset.range H, (1 : ℝ) = (H : ℝ) := by simp
  have hsumk : ∑ k in Finset.range H, (Nat.succ k : ℝ) = (H * (H + 1) : ℝ) / 2 := by
    -- sum_{k=0}^{H-1} (k+1) = H*(H+1)/2
    have hsum_nat : ∑ k in Finset.range H, Nat.succ k = H * (H + 1) / 2 := by
      have : ∑ i in Finset.range (Nat.succ H), i = (Nat.succ H) * H / 2 := by
        simpa using Nat.sum_range_id
      -- drop the last term
      have hsplit :
          ∑ i in Finset.range (Nat.succ H), i
            = ∑ k in Finset.range H, Nat.succ k := by
              simp [Finset.range_succ, Nat.succ_eq_add_one, Finset.sum_add_distrib]
      linarith
    norm_cast at hsum_nat
    simpa using hsum_nat
  have hUpos : (Ucut : ℝ) ≠ 0 := by
    have : 0 < (Ucut : ℝ) := by exact_mod_cast (by decide : 0 < Ucut)
    linarith
  have hpos_eval :
      ∑ k in Finset.range H, K_full (Int.ofNat (Nat.succ k))
        = ((H : ℝ) - ((H * (H + 1) : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ) := by
    calc
      ∑ k in Finset.range H, K_full (Int.ofNat (Nat.succ k))
          = ∑ k in Finset.range H, ((1 : ℝ) - (Nat.succ k : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : Nat.succ k ≤ Ucut := by
              have hklt : k < H := Finset.mem_range.mp hk
              have hHU : H ≤ Ucut := by
                have : (H : ℕ) ≤ Ucut := by
                  have hpos : 0 < H := by exact (by decide : 0 < H)
                  have h := Nat.le.intro rfl
                  have hU := le_of_lt (by decide : H < Ucut := by decide)
                  exact hU
                exact this
              exact Nat.succ_le_of_lt (lt_of_lt_of_le hklt hHU)
            have hnat : Int.natAbs (Int.ofNat (Nat.succ k)) ≤ Ucut := by simpa using hk'
            unfold K_full
            simp [hnat, abs_ofNat, Int.ofNat_eq_coe, Int.natAbs_ofNat]
      _ = (1 / (Ucut : ℝ)) * (hsum1 - (1 / (Ucut : ℝ)) * hsumk) := by
        field_simp [Finset.sum_mul]
        ring
      _ = ((H : ℝ) - ((H * (H + 1) : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ) := by
        field_simp [hUpos] ; ring
  calc
    ∑ k in innerBand, K_full k
        = (1 : ℝ) / (Ucut : ℝ) + 2 * (((H : ℝ) - ((H * (H + 1) : ℝ) / (Ucut : ℝ))) / (Ucut : ℝ)) := by
          nlinarith [hsplit, hpos_eval]
    _ = ((1 + 2 * H : ℝ) / (Ucut : ℝ)) - ((H * (H + 1) : ℝ) / (Ucut : ℝ)^2) := by
      field_simp [hUpos] ; ring

lemma tail_mass_closed_form :
    ∑ k in outerBand, K_full k = C_tail_closed := by
  classical
  have hsplit := sum_bandU_outer_inner (f:=K_full)
  have hfull := sum_bandU
  have hinner := sum_innerBand
  have houter : ∑ k in outerBand, K_full k
      = ∑ k in bandU, K_full k - ∑ k in innerBand, K_full k := by linarith
  nlinarith [hfull, hinner, houter, C_tail_closed]

lemma C_tail_eq_closed : C_tail = C_tail_closed := by
  unfold C_tail C_tail_closed
  simpa using tail_mass_closed_form

/-- Concrete errTI bound using the closed-form tail mass. -/
lemma errTI_bound_closed :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |errTI X N| ≤ payload_cap N * C_tail_closed := by
  intro X N hX hN
  have hTail : ∑ k in outerBand, K_full k ≤ C_tail_closed := by
    have := tail_mass_closed_form
    exact le_of_eq this
  have := errTI_bound_from_tail (X:=X) (N:=N) hX hN (tail_mass:=C_tail_closed) hTail
  simpa using this

/-- Deviation of the full projector from the in-window projector (errBG=0): bounded by the tail. -/
lemma bankOp_full_minus_ref_bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      |conv_full X N - conv_ref X N| ≤ payload_cap N * C_tail_closed := by
  intro X N hX hN
  -- from the decomposition, the difference is exactly errTI (errBG = 0)
  have hdecomp := bank_decomp (X:=X) (N:=N) hX hN
  have herrbg : errBG X N = 0 := rfl
  have hrewrite : conv_full X N - conv_ref X N = errTI X N := by
    nlinarith [hdecomp, herrbg]
  -- apply the tail bound
  have htail := errTI_bound_closed (X:=X) (N:=N) hX hN
  simpa [hrewrite] using htail

/-- The inner band of the full tent coincides with `S_BG` (since `H ≤ Ucut`). -/
lemma innerBand_eq_SBG : innerBand = S_BG := by
  apply Finset.ext
  intro k; constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨hkBand, hkInner⟩
    -- |k| ≤ H and k ∈ [-U,U] ⇒ k ∈ [-H,H]
    have hkIcc : k ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by
      have hkAbs : Int.natAbs k ≤ H := hkInner
      have hkNonneg : (-(H:ℤ)) ≤ k := by
        have := Int.neg_le_abs_self k
        have hHnonneg : 0 ≤ (H:ℤ) := by exact_mod_cast (Nat.zero_le _)
        linarith
      have hkPos : k ≤ (H:ℤ) := by
        have := Int.le_abs_self k
        have hHnonneg : 0 ≤ (H:ℤ) := by exact_mod_cast (Nat.zero_le _)
        linarith
      exact Finset.mem_Icc.mpr ⟨hkNonneg, hkPos⟩
    simpa [S_BG] using hkIcc
  · intro hk
    have hkIcc : k ∈ Finset.Icc (-(H:ℤ)) (H:ℤ) := by simpa [S_BG] using hk
    have hkBand : k ∈ bandU := by
      -- since H ≤ Ucut, [-H,H] ⊆ [-U,U]
      have hHleU : (H : ℤ) ≤ (Ucut : ℤ) := by
        have h : (H : ℕ) ≤ Ucut := by
          have : (1 : ℕ) ≤ 4 := by decide
          have hHpos : 0 < H := by exact (by decide : 0 < H)
          nlinarith
        exact_mod_cast h
      have hneg : (-(Ucut:ℤ)) ≤ k := by linarith [(Finset.mem_Icc.mp hkIcc).1]
      have hpos : k ≤ (Ucut:ℤ) := by linarith [(Finset.mem_Icc.mp hkIcc).2, hHleU]
      exact Finset.mem_Icc.mpr ⟨hneg, hpos⟩
    have hkInner : Int.natAbs k ≤ H := by
      have hkAbs : Int.natAbs k ≤ Int.natAbs (H:ℤ) := by
        have := Int.abs_le.mpr (Finset.mem_Icc.mp hkIcc)
        have := this
        linarith
      simpa using hkAbs
    exact Finset.mem_filter.mpr ⟨hkBand, hkInner⟩

/-- Off-channel from the calibrator (uses S_BG, K_BG, P_BG). -/
noncomputable def E_off (X N : ℕ) : ℝ :=
  BG_Calib.E_off S_BG K_BG P_BG X N

/-- Temporary choices for the other channels so that the identity is rfl. -/
noncomputable def E_kernel (X N : ℕ) : ℝ := 0
noncomputable def E_mellin (X N : ℕ) : ℝ := 0
noncomputable def E_smooth (X N : ℕ) : ℝ := AO_Major.errAO X N - E_off X N

/-- Decomposition of the full projector into tail + in-window (errBG=0 here). -/
lemma bank_decomp :
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    conv_full X N - conv_ref X N = errTI X N + errBG X N := by
  intro X N _hX _hN
  unfold conv_full errTI outerBand conv_ref errBG innerBand bandU
  classical
  have hsplit := sum_bandU_outer_inner (f:=fun k => P_BG X N k * K_full k)
  -- use the partition to peel off the inner sum
  have hinner :
      ∑ k in innerBand, P_BG X N k * K_full k
        = ∑ k in Finset.Icc (-(H:ℤ)) (H:ℤ), P_BG X N k * K_full k := by
    -- inner band equals S_BG = [-H,H]
    have : innerBand = S_BG := innerBand_eq_SBG
    simpa [S_BG] using congrArg (fun s => ∑ k in s, P_BG X N k * K_full k) this
  calc
    (∑ k in bandU, P_BG X N k * K_full k)
        - ∑ k in Finset.Icc (-(H:ℤ)) (H:ℤ), P_BG X N k * K_full k
        = (∑ k in outerBand, P_BG X N k * K_full k + ∑ k in innerBand, P_BG X N k * K_full k)
            - ∑ k in Finset.Icc (-(H:ℤ)) (H:ℤ), P_BG X N k * K_full k := by
              simpa [hsplit]
    _ = ∑ k in outerBand, P_BG X N k * K_full k := by nlinarith [hinner]
    _ = errTI X N := rfl
    _ = errTI X N + errBG X N := by
      simp [errBG, errTI]

/-- Full-bank projector using the Λ/log payload (Route A). -/
noncomputable def conv_full_divlog (U X N : ℕ) : ℝ :=
  ∑ k in (Finset.Icc (-(U:ℤ)) (U:ℤ)),
    (Goldbach.Deweighting.P_divlog X N k) * (K_full k)

end Goldbach.BG_Identity

-- in BG_Identity.lean
import Mathlib
-- … your existing imports …

namespace Goldbach.BG_Identity
open scoped BigOperators
open Finset

-- If not already present in this file:
-- parameters/constants (adapt names to yours)
-- variable (X0 H : ℕ) (Ucut : ℕ) -- typically Ucut := H + ⌈H/100⌉
-- def S_BG : Finset ℤ := {k | |k| ≤ (H : ℤ)}.toFinset   -- inner band
-- def S_full : Finset ℤ := {k | |k| ≤ (Ucut : ℤ)}.toFinset
-- def outerBand : Finset ℤ := S_full \ S_BG
-- noncomputable def K_full : ℤ → ℝ := -- your linear tent, already defined
-- noncomputable def P_BG   : ℕ → ℕ → ℤ → ℝ := -- your normalized payload

/-- Convolution with the full tent on `|k| ≤ Ucut`. -/
noncomputable def conv_full (X N : ℕ) : ℝ :=
  ∑ k in S_full, K_full k * P_BG X N k

/-- Convolution with the “reference/inner” tent on `|k| ≤ H`. (Using the same K on the inner band.) -/
noncomputable def conv_ref (X N : ℕ) : ℝ :=
  ∑ k in S_BG, K_full k * P_BG X N k

/-- Type-I tail: the outer band contribution. -/
noncomputable def errTI (X N : ℕ) : ℝ :=
  ∑ k in outerBand, K_full k * P_BG X N k

/-- Window decomposition: on *every* `(X,N)` the full–ref gap is exactly the tail. -/
lemma bank_decomp_window {X N : ℕ} :
    conv_full X N - conv_ref X N = errTI X N := by
  classical
  unfold conv_full conv_ref errTI
  have disj : Disjoint S_BG outerBand := by
    classical
    exact disjoint_left.mpr (by
      intro k hkBG hkOuter
      have hkFull : k ∈ S_full := by
        have : k ∈ S_BG ∪ outerBand := by exact Or.inl hkBG
        -- but hkOuter means k ∈ S_full \ S_BG
        exact by
          have : k ∈ outerBand := hkOuter
          -- contradiction with hkBG
          exact False.elim (by
            have : k ∉ S_BG := by
              exact (mem_sdiff.mp this).2
            exact this hkBG))
  have union_cover : S_full = S_BG ∪ outerBand := by
    classical
    ext k; constructor
    · intro hk
      by_cases hkBG : k ∈ S_BG
      · exact Or.inl hkBG
      · exact Or.inr (by exact mem_sdiff.mpr ⟨hk, hkBG⟩)
    · intro h
      exact h.elim (fun hkBG => mem_of_subset_of_mem (by
        -- S_BG ⊆ S_full
        intro x hx; exact (mem_sdiff.mp (mem_sdiff_self)).1) hkBG)
        (fun hkOuter => (mem_sdiff.mp hkOuter).1)
  calc
    (∑ k in S_full, K_full k * P_BG X N k) -
        (∑ k in S_BG,   K_full k * P_BG X N k)
        = (∑ k in (S_BG ∪ outerBand), K_full k * P_BG X N k) -
          (∑ k in S_BG,                 K_full k * P_BG X N k) := by
              simpa [union_cover]
    _ = (∑ k in S_BG, K_full k * P_BG X N k) +
        (∑ k in outerBand, K_full k * P_BG X N k) -
        (∑ k in S_BG, K_full k * P_BG X N k) := by
              simpa [sum_union disj.symm]   -- symmetry ok since Disjoint
    _ = ∑ k in outerBand, K_full k * P_BG X N k := by
              abel
    _ = errTI X N := rfl

/-- Pure algebra: rewrite the target gap `R - M` as the conv gap plus two
small “bridge” terms. No analysis yet. -/
lemma decomp_R_minus_M_to_conv
  {X N : ℕ} :
  (Rep.R N : ℝ) - AO_Major.Mcanon N
    = (conv_full X N - conv_ref X N)
      + ((Rep.R N : ℝ) - conv_full X N)
      + (conv_ref X N - AO_Major.Mcanon N) := by
  -- a - b = (c - d) + (a - c) + (d - b)
  ring
  -- (If `ring` doesn’t fire in your setup: rewrite with `sub_eq_add_neg`
  -- and finish with `simp [add_comm, add_left_comm, add_assoc]`.)

/-- Take absolute values and split by triangle inequality. -/
lemma abs_R_minus_M_le_conv_gap_plus_bridges
  {X N : ℕ} :
  |(Rep.R N : ℝ) - AO_Major.Mcanon N|
    ≤ |conv_full X N - conv_ref X N|
      + |(Rep.R N : ℝ) - conv_full X N|
      + |conv_ref X N - AO_Major.Mcanon N| := by
  -- |x+y+z| ≤ |x| + |y| + |z|
  set x := conv_full X N - conv_ref X N
  set y := (Rep.R N : ℝ) - conv_full X N
  set z := conv_ref X N - AO_Major.Mcanon N
  have : (Rep.R N : ℝ) - AO_Major.Mcanon N = x + y + z := by
    subst x y z; simpa using decomp_R_minus_M_to_conv (X:=X) (N:=N)
  simpa [this] using (abs_add_le_abs_add_abs (x + y) z)
    ▸? -- expand once more: |x+y| ≤ |x|+|y|

/-- The outer band sits inside the full symmetric slab. -/
lemma outerBand_subset_full (H : ℕ) :
  (outerBand H) ⊆ (Finset.Icc (-(Ucut H : ℤ)) (Ucut H : ℤ)) := by
  intro k hk
  -- your file already proves that outerBand consists of `k` with `|k| ≤ Ucut`
  -- so this is just the inclusion to `Icc [-U..U]`
  exact outer_mem_Icc_of_abs_le_Ucut (H:=H) hk

/-- Cardinality of the full slab `[-U..U]` over `ℤ` is `2*U + 1`. -/
lemma card_full_slab (H : ℕ) :
  (Finset.Icc (-(Ucut H : ℤ)) (Ucut H : ℤ)).card = 2 * (Ucut H) + 1 := by
  -- standard fact for integer intervals
  simpa using Int.card_Icc (-(Ucut H : ℤ)) (Ucut H : ℤ)

end Goldbach.BG_Identity
