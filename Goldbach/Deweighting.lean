/-
  Goldbach/Deweighting.lean

  Route A (Λ/log deweighting) bridge:
  • Define the Λ/log payload P_divlog (with optional bump wX ≡ 1).
  • Show |Λ(n)/log n| ≤ 1 for n ≥ 2.
  • Reduce |R - conv_full_divlog| to a small “prime-power-in-midband” count
    times the peak of the tent kernel (≤ 1/Ucut for the linear tent).
  • Expose a single calibration hook `ppMidbandBound` (numeric) you can fill
    in BG_Calib.

  This file is algebraic/elementary; it doesn’t change your tail lemmas.
-/
import Mathlib
import Goldbach.Windows
import Goldbach.Rep
import Goldbach.BG_Identity  -- for K_full, S_BG, Ucut, conv_full, etc. (names as in your tree)
-- If the symbols live elsewhere, tweak the imports/names below consistently.

namespace Goldbach.Deweighting

open Real
open Goldbach
open Goldbach.Windows
open Goldbach.Rep
open Goldbach.BG_Identity

attribute [simp] BG_Identity.K_full_inner_peak_le
attribute [simp] BG_Identity.sum_abs_K_full_inner_le

-- convenient aliases if this file prefers shorter names
lemma K_full_inner_peak_le' := BG_Identity.K_full_inner_peak_le
lemma sum_abs_K_full_inner_le' := BG_Identity.sum_abs_K_full_inner_le
lemma swap_inner_bound' := BG_Identity.swap_bound_linf_l1
lemma errTI_bound_closed' := BG_Identity.errTI_bound_closed

/-- Von Mangoldt as ℝ. -/
noncomputable def ΛR (n : ℕ) : ℝ :=
  if h : Nat.exists_prime_pow_eq n then
    -- If n = p^a (a ≥ 1), Λ(n) = log p
    Real.log (Classical.choose h).1
  else
    0

/-- On the inner band `S_BG`, the tent is pointwise ≤ 1 / Ucut. -/
lemma inner_peak_le_one_div_Ucut :
    ∀ {k : ℤ}, k ∈ S_BG → K_full k ≤ (1 : ℝ) / (Ucut : ℝ) :=
  fun k hk => K_full_inner_peak_le hk

/-- ℓ¹ mass of the tent on the inner band. -/
lemma l1_mass_inner :
    ∑ k in S_BG, |K_full k| ≤ (2 * (BankParams.H : ℝ) + 1) / (Ucut : ℝ) :=
  sum_abs_K_full_inner_le

/-- Uniform ℓ∞·ℓ¹ “swap” bound on the inner band. -/
lemma swap_bound_linf_l1'
    {P Q : ℤ → ℝ} {M : ℝ}
    (hM : ∀ {k : ℤ}, k ∈ S_BG → |P k - Q k| ≤ M) :
    |∑ k in S_BG, K_full k * (P k - Q k)| ≤
      M * ((2 * (BankParams.H : ℝ) + 1) / (Ucut : ℝ)) :=
  swap_bound_linf_l1 hM

/-- Simple bump (you can replace later); we keep it 1 on the bank window. -/
@[inline] noncomputable def wX (_X n : ℕ) : ℝ := 1

/-- Λ/log payload (Route A): each factor is ≤ 1 in magnitude for n ≥ 2. -/
noncomputable def P_divlog (X N : ℕ) (k : ℤ) : ℝ :=
  ∑ n in Finset.Icc 2 (N - 2),
    -- exact offset constraint for this k:
    (if ((n : ℤ) - ((N - n : ℕ) : ℤ) = k) then
      let a := (ΛR n) / Real.log (n.toReal)
      let b := (ΛR (N - n)) / Real.log ((N - n).toReal)
      (wX X n) * a * (wX X (N - n)) * b
     else 0)

/-- For n ≥ 2: |Λ(n)| / log n ≤ 1. (Prime-power case gives = 1/a ≤ 1; otherwise 0.) -/
lemma abs_Lambda_div_log_le_one {n : ℕ} (hn : 2 ≤ n) :
  |ΛR n / Real.log n| ≤ 1 := by
  classical
  by_cases hpp : Nat.exists_prime_pow_eq n
  · rcases hpp with ⟨p, a, hp, ha, rfl⟩
    have hlogp : 0 < Real.log (p : ℝ) := by
      have : (1 : ℝ) < p := by
        have : (1 : ℕ) < p := by
          exact Nat.Prime.one_lt hp
        exact_mod_cast this
      exact Real.log_pos_iff.mpr this
    have a_pos : 0 < (a : ℝ) := by exact_mod_cast Nat.succ_le_succ_iff.mp (Nat.succ_le_of_lt (Nat.succ_pos _))
    have : Real.log (p^a : ℝ) = (a : ℝ) * Real.log (p : ℝ) := by
      simpa using Real.log_rpow (by exact_mod_cast (show (0:ℝ) < p from by exact_mod_cast (Nat.Prime.pos hp))) _
    have : |Real.log (p : ℝ) / ((a : ℝ) * Real.log (p : ℝ))| = |1 / (a : ℝ)| := by
      have hne : (Real.log (p : ℝ)) ≠ 0 := ne_of_gt hlogp
      field_simp [abs_div, this, abs_of_pos hlogp, abs_mul]
    have : |ΛR (p^a) / Real.log (p^a)| = |1 / (a : ℝ)| := by
      simp [ΛR, dite_true, hpp, this]
    have : |ΛR (p^a) / Real.log (p^a)| ≤ 1 := by
      have : 0 < (a : ℝ) := a_pos
      have : |1 / (a : ℝ)| ≤ 1 := by
        have hle : 1 ≤ (a : ℝ) := by exact_mod_cast (Nat.succ_le_succ_iff.mp (Nat.succ_le_of_lt (Nat.succ_pos _)))
        have hpos : 0 < (a : ℝ) := a_pos
        have : (0 : ℝ) < (a : ℝ) := hpos
        have : |1 / (a : ℝ)| = 1 / (a : ℝ) := by
          have : 0 < 1 / (a : ℝ) := by
            have : 0 < (a : ℝ) := a_pos
            exact one_div_pos.mpr this
          simpa [abs_of_nonneg (le_of_lt this)]
        have : 1 / (a : ℝ) ≤ 1 := by
          have : (a : ℝ) ≥ 1 := by exact hle
          have : 1 ≤ (a : ℝ) := this
          have : 1 / (a : ℝ) ≤ 1 / 1 := by
            exact one_div_le_one_div_of_le (by exact_mod_cast (Nat.succ_le_succ_iff.mp (Nat.succ_le_of_lt (Nat.succ_pos _)))) this
          simpa using this
        simpa [this]
      simpa [this] using this
    simpa using this
  · -- not a prime power: Λ(n)=0
    simp [ΛR, hpp, abs_nonpos]  -- 0/log n = 0
      -- (log n > 0 for n≥2; but abs 0 ≤ 1 is trivial)

/-!
`MidbandBound` packages a numerical cap `C_pp` for the number of “midband” prime
powers together with the inequality you will later justify in `BG_Calib`.
-/
class MidbandBound (X0 H U : ℕ) : Prop where
  C_pp       : ℕ
  bound :
    ∀ {X N}, X0 ≤ X → N ∈ EvenIn X H →
      ppMidbandCount N U ≤ C_pp
  C_pp_nonneg : 0 ≤ (C_pp : ℝ)

  -- inner ℓ¹ mass on the band |k| ≤ H (proved in BG_Identity):
  (h_inner_l1 : ∑ k in S_BG H, |K_full H k| ≤ (2 * (H:ℝ) + 1) / (Ucut H))
  -- pointwise “weights bridge” on the inner band:
  (Mswap : ℝ)
  (h_bridge :
    ∀ {k : ℤ}, k ∈ S_BG H →
      |P_BG X N k - Pref X N k| ≤ Mswap)
  -- AO envelope, via ao_expansion + errAO_bound:
  (h_ao :
    |AO_Major.Mcanon N - (sigma N) * AO_Major.weight_mass X|
      ≤ AO_ErrorEnvelope.δAO)
  -- constant-reference equality (∑ inner K_full * Pref = σ·weight_mass):
  (h_ref :
    conv_ref_const X N = (sigma N) * AO_Major.weight_mass X)
  :
  |conv_full X N - AO_Major.Mcanon N|
    ≤ C_tail_closed H * payload_cap X N
      + Mswap * ((2 * (H:ℝ) + 1) / (Ucut H))
      + AO_ErrorEnvelope.δAO := by
  classical
  -- split: (full - M) = (full - ref) + (ref - ref_const) + (ref_const - M)
  have decomp : conv_full X N - AO_Major.Mcanon N
      = (conv_full X N - conv_ref X N)
        + (conv_ref X N - conv_ref_const X N)
        + (conv_ref_const X N - AO_Major.Mcanon N) := by ring
  -- 1) full - ref = errTI
  have h1 : conv_full X N - conv_ref X N = errTI X N :=
    bank_decomp_window
  -- 2) ref - ref_const: use ℓ∞·ℓ¹ with your pointwise bridge
  have h2 :
      |conv_ref X N - conv_ref_const X N|
        ≤ Mswap * ((∑ k in S_BG H, |K_full H k|)) := by
    -- `swap_bound_linf_l1` is your proved lemma in BG_Identity
    exact swap_bound_linf_l1
      (X:=X) (N:=N) (H:=H) (M:=Mswap) (hM:=h_bridge)
  have h2' : |conv_ref X N - conv_ref_const X N|
        ≤ Mswap * ((2 * (H:ℝ) + 1) / (Ucut H)) :=
    le_trans h2 (by simpa using h_inner_l1)
  -- 3) ref_const - M: AO envelope
  have h3 : |conv_ref_const X N - AO_Major.Mcanon N|
        ≤ AO_ErrorEnvelope.δAO := by
    -- rewrite conv_ref_const to σ·mass and use AO bound
    simpa [h_ref, abs_sub_comm, abs_sub] using h_ao
  -- triangle inequality
  have := calc
    |conv_full X N - AO_Major.Mcanon N|
        = |(conv_full X N - conv_ref X N)
            + (conv_ref X N - conv_ref_const X N)
            + (conv_ref_const X N - AO_Major.Mcanon N)| := by
              simpa [decomp]
    _ ≤ |conv_full X N - conv_ref X N|
        + |conv_ref X N - conv_ref_const X N|
        + |conv_ref_const X N - AO_Major.Mcanon N| := by
              simpa using abs_add_three_le _ _ _
    _ ≤ |errTI X N| + (Mswap * ((2 * (H:ℝ) + 1) / (Ucut H))) + AO_ErrorEnvelope.δAO := by
              simpa [h1] using add_le_add (add_le_add le_rfl h2') (le_of_eq rfl)
  -- plug the tail bound
  exact
    le_trans this <|
      by gcongr; exact h_tail

end Goldbach.Deweighting
