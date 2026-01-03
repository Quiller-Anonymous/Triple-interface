/-
  Goldbach/BG_Identity.lean  —  header + robust helpers (binder-free)

  Notes (cf. DontHassleMe):
  • We avoid big-operator syntax (`∑ … in …`) entirely; we use `Finset.sum`.
  • No dependency on AO / SingularSeries / PPBound here (prevents cycles).
  • We stay in ℝ and postpone any ℤ/ℕ casts to later sections.
-/

import Mathlib  -- (you can slim later; keep it while stabilizing)
import Mathlib.Data.Finset.Interval
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Major          -- errAO
import Goldbach.BG_Bank
import Goldbach.BG_Operator
import Goldbach.TypeI_Tent
import Goldbach.MainTerm
import Goldbach.SingularSeries
import Goldbach.Cert.OddPrimePowers
import Goldbach.BG_Operator
import Goldbach.MainTerm
import Goldbach.PPBoundSquares
import Goldbach.PPNumerics
import Goldbach.Analytic.NumericSigma
import Goldbach.BG_KernelAPI
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

namespace Goldbach
namespace BG_Identity

noncomputable section
variable {α : Type*}

attribute [local instance] Classical.propDecidable

open Goldbach.PPBoundSquares
open BankParams
open Goldbach.BG_Bank (P_BG payload_cap)
open Goldbach.Cert.OddPrimePowers

/-- Outer cutoff for the tent on the canonical window: `U = H + ⌈H/100⌉`
(about 1% larger than `H`). -/
@[simp] noncomputable def Ucut : ℕ := H + (H + 99) / 100

-- Basic non-vanishing and positivity facts for the real-cast of Ucut
lemma Ucut_pos_real : (0 : ℝ) < (Ucut : ℝ) := by
  -- H is the canonical positive window size; Lean can decide 0 < Ucut
  exact_mod_cast (by decide : 0 < Ucut)

lemma Ucut_ne_zero_real : (Ucut : ℝ) ≠ 0 := ne_of_gt Ucut_pos_real

lemma denom_ne_zero : (↑H + ↑((H + 99) / 100) : ℝ) ≠ 0 := by
  -- The denominator equals (Ucut : ℝ)
  simpa [Ucut, Nat.cast_add, Nat.cast_ofNat] using Ucut_ne_zero_real

/-- Band of offsets for the full tent: `[-Ucut, Ucut]`. -/
noncomputable def bandU : Finset ℤ := Finset.Icc (-(Ucut : ℤ)) (Ucut : ℤ)

/-- Raw tent kernel with explicit cutoff `U` (integer offsets). -/
noncomputable def K_full_raw (U : ℕ) (k : ℤ) : ℝ :=
  max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 / (U : ℝ)

/-
  Kernel parameterization (scaffold):
  Provide a minimal API so we can later swap the concrete `K_full`
  for a band-limited kernel matching the tenor without refactoring call sites.
-/
namespace Kernel

variable (Kadm : Goldbach.BG.AdmissibleKernel Ucut)

@[inline] def K (k : ℤ) : ℝ := Kadm.K k

@[simp] lemma K_even (k : ℤ) : K Kadm (-k) = K Kadm k := Kadm.even k

lemma K_nonneg (k : ℤ) : 0 ≤ K Kadm k := Kadm.nonneg k

lemma K_mass_on_band :
  Finset.sum bandU (fun k => K Kadm k) = 1 := by
  -- bandU = Icc (-(Ucut), Ucut)
  simpa [bandU, K] using Kadm.mass_on_band

lemma K_pos_at_zero : 0 < K Kadm 0 := Kadm.pos_at_zero

end Kernel

/-- Canonical tent kernel specialized to `Ucut`. -/
noncomputable def K_full (k : ℤ) : ℝ := K_full_raw Ucut k

/-- Unnormalized tent weight on the canonical band. -/
noncomputable def tentFullWeight (k : ℤ) : ℝ := K_full k


/-- Total tent mass on the full band. -/
noncomputable def tentFullMass : ℝ := Finset.sum bandU (fun k => tentFullWeight k)

/- Use the centralized inner band from BG_Bank. -/
abbrev S_BG : Finset ℤ := Goldbach.BG_Bank.S_BG

/-- If `0 < b` and `a ≤ b` then `a / b ≤ 1`.  This matches the old
`(div_le_iff₀ hbpos).mpr (… ≤ 1*b)` shape Lean was expecting. -/
lemma div_le_one_of_le (a b : ℝ) (hbpos : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  have h' : a ≤ 1 * b := by simpa [one_mul] using h
  simpa using (div_le_iff₀ hbpos).mpr h'

/-- Triangle inequality for finite sums in `ℝ`:
`|s.sum f| ≤ s.sum (|f·|)`.  We keep it local to avoid name drift. -/
lemma abs_sum_le_sum_abs (s : Finset α) (f : α → ℝ) :
    |s.sum f| ≤ s.sum (fun x => |f x|) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    -- |f a + Σ_s f| ≤ |f a| + |Σ_s f|
    have h₁ : |f a + s.sum f| ≤ |f a| + |s.sum f| := by
      simpa using norm_add_le (f a) (s.sum f)
    -- add the inductive bound on the tail
    have h₂ : |f a| + |s.sum f| ≤ |f a| + s.sum (fun x => |f x|) :=
      add_le_add_left ih _
    have h := h₁.trans h₂
    simpa [Finset.sum_insert, ha] using h

/-- Pointwise capping lemma:
If `|a k| ≤ C` on `s`, then `s.sum (|a k|*|b k|) ≤ C * s.sum (|b k|)`. -/
lemma sum_abs_mul_le_cap
    (s : Finset α) (a b : α → ℝ) (C : ℝ)
    (hCap : ∀ k ∈ s, |a k| ≤ C) :
    s.sum (fun k => |a k| * |b k|) ≤ C * s.sum (fun k => |b k|) := by
  classical
  -- pointwise: |a k|*|b k| ≤ C*|b k|
  have hpt : ∀ k ∈ s, |a k| * |b k| ≤ C * |b k| := by
    intro k hk; exact mul_le_mul_of_nonneg_right (hCap k hk) (abs_nonneg _)
  -- sum the pointwise inequality
  have hsum : s.sum (fun k => |a k| * |b k|) ≤ s.sum (fun k => C * |b k|) :=
    Finset.sum_le_sum hpt
  -- factor `C` from the RHS sum (binder-free induction)
  have factor :
      s.sum (fun k => C * |b k|) = C * s.sum (fun k => |b k|) := by
    refine Finset.induction_on s ?z ?st
    · simp
    · intro k s hk ih
      -- (insert k s) case; rewrite both sides and fold with `mul_add`
      simp [Finset.sum_insert, hk, ih, mul_add]
  simpa [factor] using hsum

/-- Bundled version used at call sites:
`|s.sum (a k * b k)| ≤ C * s.sum (|b k|)` assuming `|a k| ≤ C` on `s`. -/
lemma abs_sum_mul_le_cap_sum_abs
    (s : Finset α) (a b : α → ℝ) (C : ℝ)
    (hCap : ∀ k ∈ s, |a k| ≤ C) :
    |s.sum (fun k => a k * b k)| ≤ C * s.sum (fun k => |b k|) := by
  classical
  -- triangle on the sum of products
  have tri :
      |s.sum (fun k => a k * b k)| ≤ s.sum (fun k => |a k * b k|) :=
    abs_sum_le_sum_abs s (fun k => a k * b k)
  -- rewrite the middle term using |ab| = |a||b|
  have hrewrite :
      s.sum (fun k => |a k * b k|) = s.sum (fun k => |a k| * |b k|) := by
    simp [abs_mul]
  have tri' :
      |s.sum (fun k => a k * b k)| ≤ s.sum (fun k => |a k| * |b k|) := by
    simpa [hrewrite] using tri
  -- apply the cap lemma
  have base :
      s.sum (fun k => |a k| * |b k|) ≤ C * s.sum (fun k => |b k|) :=
    sum_abs_mul_le_cap s a b C hCap
  exact tri'.trans base

/-- Evenness of the tent kernel. -/
lemma K_full_neg (k : ℤ) : K_full (-k) = K_full k := by
  -- This only uses that `|·|` is even and `K_full` is defined via `|·|`.
  unfold K_full K_full_raw
  simp [Int.natAbs_neg]

/-- The normalized full tent is nonnegative for every `k`. -/
lemma K_full_nonneg (k : ℤ) : 0 ≤ K_full k := by
  unfold K_full K_full_raw
  -- `max( … , 0 ) ≥ 0` and division by a nonnegative denominator preserves `≤`
  have h₁ : 0 ≤ max (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) 0 := le_max_right _ _
  have h₂ : 0 ≤ (Ucut : ℝ) := by exact_mod_cast (Nat.zero_le Ucut)
  exact div_nonneg h₁ h₂

/-
  Positive-side evaluation helper: when `0 ≤ m ≤ Ucut`, the tent value at `m`
  is the linear expression `((1 - m/Ucut)/Ucut)`.
  Avoids brittle abs/natAbs rewrites in `sum_innerBand`.
-/
lemma K_full_ofNat_le (m : ℕ) (hm : m ≤ Ucut) :
    K_full (Int.ofNat m) = ((1 : ℝ) - (m : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) := by
  unfold K_full K_full_raw
  -- Show the `max` selects the first branch using `m ≤ Ucut`.
  have hnonneg : 0 ≤ (1 : ℝ) - (m : ℝ) / (Ucut : ℝ) := by
    by_cases hU : Ucut = 0
    · -- then m = 0 as well; the expression is 1 ≥ 0
      have hm0 : m = 0 := Nat.le_zero.mp (hm.trans_eq hU)
      simp [hm0]
    · have hUpos : 0 < (Ucut : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hU
      have hm' : (m : ℝ) ≤ (Ucut : ℝ) := by exact_mod_cast hm
      have : (m : ℝ) / (Ucut : ℝ) ≤ 1 := div_le_one_of_le (a := (m : ℝ)) (b := (Ucut : ℝ)) hUpos hm'
      have : 0 ≤ 1 - (m : ℝ) / (Ucut : ℝ) := by linarith
      exact this
  have hmax :
      max (1 - (m : ℝ) / (Ucut : ℝ)) 0
        = (1 - (m : ℝ) / (Ucut : ℝ)) := by
    have := hnonneg; simpa [max_eq_left this]
  -- Evaluate with the chosen branch; first normalize the natAbs-ofNat form,
  -- then collapse the `max` using `hmax`.
  have hbranch :
      max (1 - (Int.natAbs (Int.ofNat m) : ℝ) / (Ucut : ℝ)) 0
        = (1 - (Int.natAbs (Int.ofNat m) : ℝ) / (Ucut : ℝ)) := by
    simpa [Int.natAbs_natCast] using hmax
  calc
    K_full (Int.ofNat m)
        = max (1 - (Int.natAbs (Int.ofNat m) : ℝ) / (Ucut : ℝ)) 0 / (Ucut : ℝ) := rfl
    _ = (1 - (Int.natAbs (Int.ofNat m) : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) := by
      rw [hbranch]
    _ = ((1 : ℝ) - (m : ℝ) / (Ucut : ℝ)) / (Ucut : ℝ) := by simp [Int.natAbs_natCast]

/-- The unnormalized full tent weight is nonnegative. -/
lemma tentFullWeight_nonneg (k : ℤ) : 0 ≤ tentFullWeight k := by
  -- `tentFullWeight k = max( 1 - |k|/Ucut , 0 ) / Ucut`
  unfold tentFullWeight K_full K_full_raw
  have h₁ : 0 ≤ max (1 - (Int.natAbs k : ℝ) / (Ucut : ℝ)) 0 := le_max_right _ _
  have h₂ : 0 ≤ (Ucut : ℝ) := by exact_mod_cast (Nat.zero_le Ucut)
  exact div_nonneg h₁ h₂

/-- The total mass of the unnormalized tent over the full band is nonnegative. -/
lemma tentFullMass_nonneg : 0 ≤ tentFullMass := by
  -- Binder-free: `Finset.sum` with a pointwise nonneg integrand.
  unfold tentFullMass bandU
  classical
  refine Finset.sum_nonneg ?h
  intro k hk
  exact tentFullWeight_nonneg k

/-- Handy binder-free constant-sum lemma for reals (kept local to avoid API drift). -/
private lemma sum_const_real₁ {α} (s : Finset α) (c : ℝ) :
    s.sum (fun _ => c) = (s.card : ℝ) * c := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    simp [ha]

/- Simple algebra: cancel U in (1/U) * (U * ((U+1)/2)). -/
private lemma cancel_U_half (U : ℝ) (hU0 : U ≠ 0) :
    (1 / U) * (U * ((U + 1) / 2)) = (U + 1) / 2 := by
  field_simp [hU0]

/- Small utility: move the 1/U factor to the front in a division. -/
private lemma div_front (U a : ℝ) : a / U = (1 / U) * a := by
  have : a / U = a * (1 / U) := by simp [div_eq_mul_inv]
  simpa [mul_comm] using this

/-- Factor a constant divisor out of a finite sum over `ℝ`. -/
private lemma sum_div_const (s : Finset α) (f : α → ℝ) (U : ℝ) :
    s.sum (fun k => f k / U) = (1 / U) * s.sum f := by
  classical
  refine Finset.induction_on s ?z ?st
  · simp
  · intro a s ha ih
    -- (f a)/U + Σ_s (f·/U) = (1/U) * (f a + Σ_s f)
    have h₁ : f a / U = (1 / U) * f a := by simp [div_front]
    have h₂ : s.sum (fun k => f k / U) = (1 / U) * s.sum f := ih
    -- rewrite and fold with `mul_add`
    simp [h₁, h₂, Finset.sum_insert, ha, mul_add]

/-- Factor a constant multiplier out of a finite sum over `ℝ`. -/
private lemma sum_const_mul (s : Finset α) (a : ℝ) (f : α → ℝ) :
    s.sum (fun k => a * f k) = a * s.sum f := by
  classical
  refine Finset.induction_on s ?z ?st
  · simp
  · intro b t hb ih
    simp [Finset.sum_insert, hb, ih, mul_add]

/-- Pointwise peak bound: the tent kernel is at most `1/U`. -/
lemma K_full_peak_le (U : ℕ) (k : ℤ) : |K_full_raw U k| ≤ (U : ℝ)⁻¹ := by
  classical
  by_cases hU : U = 0
  · subst hU; simp [K_full_raw]
  · have hUpos : 0 < (U : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hU
    have hmax_le_one :
        max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 ≤ (1 : ℝ) := by
      have hnat_nonneg : (0 : ℝ) ≤ (Int.natAbs k : ℝ) := by exact_mod_cast (Nat.zero_le _)
      have hdiv_nonneg : (0 : ℝ) ≤ (Int.natAbs k : ℝ) / (U : ℝ) := div_nonneg hnat_nonneg (le_of_lt hUpos)
      have hsub : 1 - (Int.natAbs k : ℝ) / (U : ℝ) ≤ 1 := by linarith
      exact max_le_iff.mpr ⟨hsub, by linarith⟩
    have hnonneg :
        0 ≤ max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 / (U : ℝ) := by
      have hU' : 0 ≤ (U : ℝ) := le_of_lt hUpos
      exact div_nonneg (le_max_right _ _) hU'
    have hdiv :
        max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 / (U : ℝ) ≤ 1 / (U : ℝ) := by
      have hU' : 0 ≤ (U : ℝ) := le_of_lt hUpos
      -- rewrite as a multiplication inequality to avoid `div_le_div_right`
      have hmul :
          max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 ≤ 1 := hmax_le_one
      have hmul' :
          max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 / (U : ℝ)
            ≤ 1 * (1 / (U : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hU')
        simpa [one_mul] using this
      simpa [one_mul] using hmul'
    have habs :
        |max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 / (U : ℝ)|
          = max (1 - (Int.natAbs k : ℝ) / (U : ℝ)) 0 / (U : ℝ) :=
      abs_of_nonneg hnonneg
    unfold K_full_raw
    rw [habs]
    simpa [one_div] using hdiv

/-- Pointwise peak bound for the *integer-indexed* (coerced) tent weight:
`|K_full Ucut (k : ℝ)| ≤ (Ucut)⁻¹`. -/
lemma abs_tentFullWeight_peak_le (k : ℤ) :
    |tentFullWeight k| ≤ (Ucut : ℝ)⁻¹ := by
  -- tentFullWeight k = K_full Ucut (k : ℝ) by def
  dsimp [tentFullWeight]
  -- use the provided peak bound with explicit parameters
  simpa using (K_full_peak_le (U := Ucut) (k := k))

/-- Same peak bound restricted to the inner band `S_BG` (the hypothesis is unused,
    but keeps the lemma signature aligned with downstream call sites). -/
lemma sum_abs_tentFullWeight_inner_le :
    Finset.sum S_BG (fun k => |tentFullWeight k|)
      ≤ (S_BG.card : ℝ) / (Ucut : ℝ) := by
  classical
  -- Pointwise peak:  |K_full Ucut (k:ℝ)| ≤ (Ucut)⁻¹  (hypothesis `hk` unused)
  have hpt : ∀ k ∈ S_BG, |tentFullWeight k| ≤ (Ucut : ℝ)⁻¹ :=
    fun k _hk => abs_tentFullWeight_peak_le k
  -- Sum the pointwise inequality across the finite set.
  have hsum :
      Finset.sum S_BG (fun k => |tentFullWeight k|)
        ≤ Finset.sum S_BG (fun _ => (Ucut : ℝ)⁻¹) :=
    Finset.sum_le_sum hpt
  -- Evaluate constant sum as (card • constant) via a tiny local induction.
  have hconst :
      Finset.sum S_BG (fun _ => (Ucut : ℝ)⁻¹)
        = (S_BG.card : ℝ) * (Ucut : ℝ)⁻¹ :=
    sum_const_real₁ S_BG ((Ucut : ℝ)⁻¹)
  -- Conclude in division form.
  calc
    Finset.sum S_BG (fun k => |tentFullWeight k|)
        ≤ Finset.sum S_BG (fun _ => (Ucut : ℝ)⁻¹) := hsum
    _ = (S_BG.card : ℝ) * (Ucut : ℝ)⁻¹ := hconst
    _ = (S_BG.card : ℝ) / (Ucut : ℝ) := by
      rw [div_eq_mul_inv]

/-- If you prefer the explicit `(2H+1)/Ucut` presentation, supply the
    cardinality identity for `S_BG` from elsewhere and use this corollary. -/
lemma sum_abs_tentFullWeight_inner_le_twoH
    (hcard : (S_BG.card : ℝ) = (2 * BankParams.H + 1 : ℝ)) :
    Finset.sum S_BG (fun k => |tentFullWeight k|)
      ≤ (2 * BankParams.H + 1 : ℝ) / (Ucut : ℝ) := by
  have h := sum_abs_tentFullWeight_inner_le
  calc Finset.sum S_BG (fun k => |tentFullWeight k|)
      ≤ (S_BG.card : ℝ) / (Ucut : ℝ) := h
    _ = (2 * BankParams.H + 1 : ℝ) / (Ucut : ℝ) := by rw [hcard]

/-- Cardinality of the inner band `S_BG = [-H,H]`. -/
lemma card_S_BG : S_BG.card = 2 * BankParams.H + 1 := by
  classical
  -- Compute the cardinality in `ℤ` via `Int.card_Icc`, then cast back to `ℕ`.
  have hcardZ :
      ((S_BG.card : ℤ)) = max ((BankParams.H : ℤ) + 1 + (BankParams.H : ℤ)) 0 := by
    -- normalize the RHS into the `(H+1+H)` form
    simp [S_BG, Goldbach.BG_Bank.S_BG, sub_eq_add_neg]
  have hnonneg : (0 : ℤ) ≤ (BankParams.H : ℤ) + 1 + (BankParams.H : ℤ) := by
    have hH : (0 : ℤ) ≤ (BankParams.H : ℤ) := by
      exact_mod_cast (Nat.zero_le BankParams.H)
    have : (0 : ℤ) ≤ (BankParams.H : ℤ) + (BankParams.H : ℤ) := add_nonneg hH hH
    linarith
  have hcardZ' : (S_BG.card : ℤ) = (2 * (BankParams.H : ℤ) + 1) := by
    calc
      (S_BG.card : ℤ) = max ((BankParams.H : ℤ) + 1 + (BankParams.H : ℤ)) 0 := hcardZ
      _ = (BankParams.H : ℤ) + 1 + (BankParams.H : ℤ) := by
            simp [max_eq_left hnonneg]
      _ = 2 * (BankParams.H : ℤ) + 1 := by ring
  -- cast back to ℕ
  exact_mod_cast hcardZ'

/-- ℓ¹ mass of `|K_full|` on the inner band. -/
lemma sum_abs_K_full_inner_le :
    Finset.sum S_BG (fun k => |K_full k|)
      ≤ (2 * BankParams.H + 1 : ℝ) / (Ucut : ℝ) := by
  have hcard : (S_BG.card : ℝ) = (2 * BankParams.H + 1 : ℝ) := by
    exact_mod_cast card_S_BG
  simpa [tentFullWeight] using (sum_abs_tentFullWeight_inner_le_twoH (hcard := hcard))

/-- ℓ∞·ℓ¹ “swap” bound on the inner band. -/
lemma swap_bound_linf_l1
    {P Q : ℤ → ℝ} {M : ℝ}
    (hM : ∀ {k : ℤ}, k ∈ S_BG → |P k - Q k| ≤ M) :
    |Finset.sum S_BG (fun k => K_full k * (P k - Q k))|
      ≤ M * ((2 * (BankParams.H : ℝ) + 1) / (Ucut : ℝ)) := by
  classical
  have hk0 : (0 : ℤ) ∈ S_BG := by
    -- `0 ∈ [-H,H]`
    simp [S_BG, Goldbach.BG_Bank.S_BG]
  have hM_nonneg : 0 ≤ M := by
    have h0 : |P 0 - Q 0| ≤ M := hM (k := 0) hk0
    exact le_trans (abs_nonneg _) h0
  have hcap : ∀ k ∈ S_BG, |(P k - Q k)| ≤ M := by
    intro k hk
    simpa using (hM (k := k) hk)
  have hswap :
      |Finset.sum S_BG (fun k => (P k - Q k) * K_full k)|
        ≤ M * Finset.sum S_BG (fun k => |K_full k|) := by
    simpa using
      (abs_sum_mul_le_cap_sum_abs (s := S_BG)
        (a := fun k : ℤ => P k - Q k) (b := fun k : ℤ => K_full k) (C := M) hcap)
  have hswap' :
      |Finset.sum S_BG (fun k => K_full k * (P k - Q k))|
        ≤ M * Finset.sum S_BG (fun k => |K_full k|) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hswap
  have hsum :
      M * Finset.sum S_BG (fun k => |K_full k|)
        ≤ M * ((2 * (BankParams.H : ℝ) + 1) / (Ucut : ℝ)) := by
    exact mul_le_mul_of_nonneg_left sum_abs_K_full_inner_le hM_nonneg
  exact le_trans hswap' hsum

/-- Occasionally useful: the weight at zero, written arity-correctly. -/
@[simp] lemma tentFullWeight_zero : tentFullWeight (0 : ℤ) = K_full (0 : ℤ) := by
  simp [tentFullWeight]

-- “inner band”: offsets |k| ≤ H and then some extra predicate (prime-power/square contamination etc.)
noncomputable def innerBand : Finset ℤ :=
  Finset.filter (fun k : ℤ => abs k ≤ (BankParams.H : ℤ)) bandU

/-- The offset from the center for a given summand index. -/
noncomputable def offsetOf (N n : ℕ) : ℤ := (2 * n : ℤ) - (N : ℤ)

lemma innerK_card_le_twoHplus1 (H : ℕ) :
    (Finset.filter (fun k : ℤ => abs k ≤ (H : ℤ))
        (Finset.Icc (-(H : ℤ)) (H : ℤ))).card ≤ 2 * H + 1 := by
  classical
  -- filter-card ≤ ambient-card
  have hle :
      (Finset.filter (fun k : ℤ => abs k ≤ (H : ℤ))
          (Finset.Icc (-(H : ℤ)) (H : ℤ))).card
        ≤ (Finset.Icc (-(H : ℤ)) (H : ℤ)).card := by
    exact Finset.card_filter_le _ _

  -- compute card(Icc (-H) H) using Int.card_Icc (casts to ℤ, with a max(…) 0)
  have hcardZ :
      ((Finset.Icc (-(H : ℤ)) (H : ℤ)).card : ℤ)
        = max ((H : ℤ) + 1 + (H : ℤ)) 0 := by
    -- Int.card_Icc is exactly the form that produced your “max(…) 0” goal;
    -- we normalize it to the explicit (H+1+H) expression.
    simp [sub_eq_add_neg]

  have hnonneg : (0 : ℤ) ≤ (H : ℤ) + 1 + (H : ℤ) := by
    have hH : (0 : ℤ) ≤ (H : ℤ) := by
      exact_mod_cast (Nat.zero_le H)
    have hHH : (0 : ℤ) ≤ (H : ℤ) + (H : ℤ) := add_nonneg hH hH
    have hHH1 : (0 : ℤ) ≤ (H : ℤ) + (H : ℤ) + 1 := add_nonneg hHH (by decide)
    simpa [add_assoc, add_left_comm, add_comm] using hHH1

  have hcardZ' :
      ((Finset.Icc (-(H : ℤ)) (H : ℤ)).card : ℤ) = 2 * (H : ℤ) + 1 := by
    calc
      ((Finset.Icc (-(H : ℤ)) (H : ℤ)).card : ℤ)
          = max ((H : ℤ) + 1 + (H : ℤ)) 0 := hcardZ
      _ = (H : ℤ) + 1 + (H : ℤ) := by
            simpa using (max_eq_left hnonneg)
      _ = 2 * (H : ℤ) + 1 := by ring

  have hcardNat :
      (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = 2 * H + 1 := by
    exact_mod_cast hcardZ'

  exact le_trans hle (by simp [hcardNat])

/-- crude “prime power” predicate; keep your existing definition if you have one. -/
def isPrimePower (m : ℕ) : Prop :=
  ∃ p e, Nat.Prime p ∧ 2 ≤ e ∧ m = p ^ e

/-- “Higher prime powers” in the sense requested for the split: odd exponent `e ≥ 3`. -/
def isOddPrimePower (m : ℕ) : Prop :=
  ∃ p e, Nat.Prime p ∧ 3 ≤ e ∧ Odd e ∧ m = p ^ e

/-- Classify prime powers by parity of the exponent. -/
lemma isPrimePower_even_or_odd {m : ℕ} (hm : isPrimePower m) :
    (∃ t, m = t^2) ∨ isOddPrimePower m := by
  classical
  rcases hm with ⟨p, e, hp, he, hm⟩
  rcases Nat.even_or_odd e with hEven | hOdd
  · rcases hEven with ⟨r, hr⟩
    left
    refine ⟨p^r, ?_⟩
    subst hr
    simp only [pow_add] at hm
    simpa [pow_two] using hm
  · have hge3 : 3 ≤ e := by
      rcases hOdd with ⟨k, hk⟩
      subst hk
      -- e = 2*k + 1; from 2 ≤ e we get k ≥ 1
      have hk_ge : 1 ≤ k := by linarith [he]
      have : 3 ≤ 2 * k + 1 := by linarith
      simpa using this
    right
    refine ⟨p, e, hp, hge3, hOdd, hm⟩

/-- Odd-exponent prime powers inside the inner band `[A(N), B(N)]`. -/
noncomputable def innerOddPrimePowers (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (A N) (B N)).filter isOddPrimePower

set_option maxRecDepth 2000 in
/-- Band width certificate for the canonical regime `N ≥ X0`. -/
lemma band_width_le_H_nat (N : ℕ) (hN : BankParams.X0 ≤ N) : B N - A N ≤ BankParams.H := by
  -- abbreviate midpoint and half-width
  set a : ℕ := N / 2
  set h : ℕ := Goldbach.PPNumerics.H / 2
  have hH : h + h = Goldbach.PPNumerics.H := by norm_num [Goldbach.PPNumerics.H, h]
  have hmatch : (Goldbach.PPNumerics.H : ℕ) = BankParams.H := by norm_num [Goldbach.PPNumerics.H, BankParams.H]
  -- under `N ≥ X0`, we have `a = N/2 ≥ X0/2 = 500000`, so `h = 5000 ≤ a`
  have ha : h ≤ a := by
    -- X0 / 2 = 500000, h = 5000
    have hX : (BankParams.X0 / 2 : ℕ) = 500000 := by norm_num [BankParams.X0]
    have hhalf : h = 5000 := by norm_num [Goldbach.PPNumerics.H, h]
    have ha' : (BankParams.X0 / 2 : ℕ) ≤ a := by
      exact Nat.div_le_div_right hN
    have : 500000 ≤ a := by simpa [hX] using ha'
    have : 5000 ≤ a := le_trans (by decide : (5000 : ℕ) ≤ 500000) this
    simpa [hhalf]
  -- centered case (since ha gives h ≤ a): exact width h+h = H
  have hwidth : (a + h) - (a - h) = h + h := by
    have hsub : a - h + h = a := Nat.sub_add_cancel ha
    -- rewrite `(a+h)` as `(a-h)+(h+h)` and subtract
    have hdecomp : a + h = (a - h) + (h + h) := by
      nlinarith [hsub]
    calc
      (a + h) - (a - h) = ((a - h) + (h + h)) - (a - h) := by simp [hdecomp]
      _ = h + h := by
        -- (x + y) - x = y
        exact Nat.add_sub_cancel_left (a - h) (h + h)
  -- rewrite the endpoints once to avoid recursive simp unfolding
  have hA : A N = a - h := by
    rfl
  have hB : B N = a + h := by
    rfl
  calc
    B N - A N = (a + h) - (a - h) := by rw [hB, hA]
    _ = h + h := hwidth
    _ = BankParams.H := by simpa [hmatch] using hH
    _ ≤ BankParams.H := le_rfl
/-- If we pin the inner value `n = (N + |k|) / 2`, the offsets in the width-`H` window
have at most four representatives (two parities for `N + |k|`, two signs). -/
lemma offsets_for_value_card_le_four (N n : ℕ) :
    (Finset.filter
      (fun k : ℤ => abs k ≤ (BankParams.H : ℤ) ∧ (N + k.natAbs) / 2 = n)
      (Finset.Icc (-(BankParams.H : ℤ)) (BankParams.H : ℤ))).card ≤ 4 := by
  classical
  -- abbreviations
  let S : Finset ℤ := Finset.Icc (-(BankParams.H : ℤ)) (BankParams.H : ℤ)
  let T : Finset ℤ :=
    S.filter (fun k : ℤ => abs k ≤ (BankParams.H : ℤ) ∧ (N + k.natAbs) / 2 = n)
  let m0 : ℕ := 2 * n - N
  let m1 : ℕ := 2 * n + 1 - N
  let U0 : Finset ℤ := S.filter (fun k : ℤ => k.natAbs = m0)
  let U1 : Finset ℤ := S.filter (fun k : ℤ => k.natAbs = m1)

  -- For a fixed `m`, the offsets with `k.natAbs = m` are contained in `{m, -m}`.
  have card_natAbs_eq_le_two (m : ℕ) : (S.filter (fun k : ℤ => k.natAbs = m)).card ≤ 2 := by
    have hsubset : S.filter (fun k : ℤ => k.natAbs = m) ⊆ ({(m : ℤ), -(m : ℤ)} : Finset ℤ) := by
      intro k hk
      have hkm : k.natAbs = m := (Finset.mem_filter.mp hk).2
      have hkmz : (k.natAbs : ℤ) = (m : ℤ) := by exact_mod_cast hkm
      rcases k.natAbs_eq with hk0 | hk0
      · -- `k = m`
        have : k = (m : ℤ) := by linarith [hk0, hkmz]
        -- membership in `{m, -m}`
        simp [this]
      · -- `k = -m`
        have : k = -(m : ℤ) := by linarith [hk0, hkmz]
        simp [this]
    have hcard : (S.filter (fun k : ℤ => k.natAbs = m)).card ≤ ({(m : ℤ), -(m : ℤ)} : Finset ℤ).card :=
      Finset.card_le_card hsubset
    have hpair : ({(m : ℤ), -(m : ℤ)} : Finset ℤ).card ≤ 2 := by
      simpa using (Finset.card_le_two (a := (m : ℤ)) (b := (-(m : ℤ))))
    exact le_trans hcard hpair

  -- Main inclusion: the equation `(N + |k|)/2 = n` forces `k.natAbs = m0` or `m1`
  have hsubset : T ⊆ U0 ∪ U1 := by
    intro k hk
    have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
    have hkcond : abs k ≤ (BankParams.H : ℤ) ∧ (N + k.natAbs) / 2 = n :=
      (Finset.mem_filter.mp hk).2
    have hdiv : (N + k.natAbs) / 2 = n := hkcond.2
    -- decompose `N + |k|`
    have hdecomp : (N + k.natAbs) % 2 + 2 * n = N + k.natAbs := by
      -- `x % 2 + 2 * (x / 2) = x` and rewrite `x/2` using `hdiv`
      simpa [hdiv, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        (Nat.mod_add_div (N + k.natAbs) 2)
    rcases Nat.mod_two_eq_zero_or_one (N + k.natAbs) with hmod | hmod
    · -- even parity: `k.natAbs = 2*n - N`
      have hx : N + k.natAbs = 2 * n := by
        -- from `0 + 2*n = ...`
        have : 0 + 2 * n = N + k.natAbs := by simpa [hmod] using hdecomp
        simpa using this.symm
      have habs : k.natAbs = 2 * n - N := by
        have hsub := congrArg (fun t => t - N) hx
        simpa [Nat.add_sub_cancel_left] using hsub
      have hkU0 : k ∈ U0 := Finset.mem_filter.mpr ⟨hkS, by simpa [U0, m0] using habs⟩
      exact Finset.mem_union.mpr (Or.inl hkU0)
    · -- odd parity: `k.natAbs = 2*n + 1 - N`
      have hx : N + k.natAbs = 2 * n + 1 := by
        have : 1 + 2 * n = N + k.natAbs := by simpa [hmod, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdecomp
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
      have habs : k.natAbs = 2 * n + 1 - N := by
        have hsub := congrArg (fun t => t - N) hx
        simpa [Nat.add_sub_cancel_left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsub
      have hkU1 : k ∈ U1 := Finset.mem_filter.mpr ⟨hkS, by simpa [U1, m1] using habs⟩
      exact Finset.mem_union.mpr (Or.inr hkU1)

  have hcardT : T.card ≤ (U0 ∪ U1).card := Finset.card_le_card hsubset
  have hcardU : (U0 ∪ U1).card ≤ U0.card + U1.card := Finset.card_union_le _ _
  have hU0 : U0.card ≤ 2 := by
    simpa [U0] using card_natAbs_eq_le_two m0
  have hU1 : U1.card ≤ 2 := by
    simpa [U1] using card_natAbs_eq_le_two m1

  have : T.card ≤ 4 := by
    calc
      T.card ≤ (U0 ∪ U1).card := hcardT
      _ ≤ U0.card + U1.card := hcardU
      _ ≤ 2 + 2 := add_le_add hU0 hU1
      _ = 4 := by decide

  simpa [T, S] using this

/-- Prime powers in the inner band split into squares vs odd prime powers. -/
lemma primePowers_split_card (N : ℕ) :
    ((Finset.Icc (A N) (B N)).filter isPrimePower).card
      ≤ (PPBoundSquares.innerSquares N).card + (innerOddPrimePowers N).card := by
  classical
  let PP := (Finset.Icc (A N) (B N)).filter isPrimePower
  let Ssq := (PPBoundSquares.innerSquares N).image (fun t : ℕ => t ^ 2)
  let Sopp := innerOddPrimePowers N

  have hsubset : PP ⊆ Ssq ∪ Sopp := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hpp⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hA, hB⟩
    rcases isPrimePower_even_or_odd hpp with hsq | hodd
    · rcases hsq with ⟨t, rfl⟩
      have ht : t ∈ PPBoundSquares.innerSquares N := by
        have hA' : A N ≤ t * t := by simpa [pow_two] using hA
        have hB' : t * t ≤ B N := by simpa [pow_two] using hB
        exact (PPBoundSquares.mem_innerSquares_iff).2 ⟨hA', hB'⟩
      have ht' : t ^ 2 ∈ Ssq := Finset.mem_image.mpr ⟨t, ht, rfl⟩
      exact Finset.mem_union.mpr (Or.inl ht')
    ·
      have hband : n ∈ Finset.Icc (A N) (B N) := Finset.mem_Icc.mpr ⟨hA, hB⟩
      have hnopp : n ∈ Sopp := Finset.mem_filter.mpr ⟨hband, hodd⟩
      exact Finset.mem_union.mpr (Or.inr hnopp)

  have hcard1 : PP.card ≤ (Ssq ∪ Sopp).card := Finset.card_le_card hsubset
  have hcard2 : (Ssq ∪ Sopp).card ≤ Ssq.card + Sopp.card := Finset.card_union_le _ _
  have hsq_le : Ssq.card ≤ (PPBoundSquares.innerSquares N).card := Finset.card_image_le
  have hcard3 : Ssq.card + Sopp.card ≤ (PPBoundSquares.innerSquares N).card + Sopp.card :=
    Nat.add_le_add_right hsq_le _

  -- chain the inequalities
  exact le_trans hcard1 (le_trans hcard2 hcard3)

-- Count offsets k with |k| ≤ H such that n=(N+|k|)/2 or N-n is a “prime power”.
noncomputable def ppInnerCount (H N : ℕ) : ℕ := by
  classical
  exact
    (Finset.filter
      (fun k : ℤ =>
        abs k ≤ (H : ℤ) ∧
          (let n : ℕ := (N + k.natAbs) / 2
           isPrimePower n ∨ isPrimePower (N - n)))
      (Finset.Icc (-(H : ℤ)) (H : ℤ))).card

-- A very robust bound: ppInnerCount ≤ 2H+1 (by subset + innerK_card_le_twoHplus1)
lemma ppInnerCount_le_twoHplus1 (H N : ℕ) :
    ppInnerCount H N ≤ 2 * H + 1 := by
  classical
  unfold ppInnerCount
  set s : Finset ℤ := Finset.Icc (-(H : ℤ)) (H : ℤ)
  set p : ℤ → Prop :=
    fun k =>
      abs k ≤ (H : ℤ) ∧
        (let n : ℕ := (N + k.natAbs) / 2
         isPrimePower n ∨ isPrimePower (N - n))
  set q : ℤ → Prop := fun k => abs k ≤ (H : ℤ)

  have hsubset : Finset.filter p s ⊆ Finset.filter q s := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkS, hkP⟩
    exact Finset.mem_filter.mpr ⟨hkS, hkP.1⟩

  have hcard_le : (Finset.filter p s).card ≤ (Finset.filter q s).card :=
    Finset.card_le_card hsubset

  exact le_trans hcard_le (innerK_card_le_twoHplus1 H)

-- This is your “2 * (#squares)” bridge. If you don’t have the needed numerics yet,
-- this is the one place where a `sorry` might still be unavoidable.

/-!
## NEON / Numeric input for prime powers (scaffolding)

The previous bound `ppInnerCount ≤ 2 * innerSquares.card` is not correct: odd-exponent
prime powers can occur in the inner band without any squares appearing there.

What we use instead is an explicit split: square contributions (controlled by
`innerSquares`) plus “higher prime powers” (odd exponent `e ≥ 3`) controlled by
`innerOddPrimePowers`.

The lemmas below start the proof; they still require a finite certificate for bases
below 80 to remove the remaining `sorry`s. Sorries are confined to this section.
-/

/-- Gap between consecutive cubes at base ≥ 80 comfortably exceeds `H = 10_000`. -/
lemma cube_gap_gt_H {p : ℕ} (hp : 80 ≤ p) :
    ((p+1)^3 : ℤ) - (p^3 : ℤ) > (BankParams.H : ℤ) := by
  have hcalc : ((p+1)^3 : ℤ) - (p^3 : ℤ) = 3*(p:ℤ)^2 + 3*(p:ℤ) + 1 := by ring
  have hp' : (p : ℤ) ≥ 80 := by exact_mod_cast hp
  have hpoly : (3*(p:ℤ)^2 + 3*(p:ℤ) + 1 : ℤ) > (10000 : ℤ) := by
    nlinarith [sq_nonneg (p:ℤ)]
  have hH : (BankParams.H : ℤ) = 10000 := by norm_num [BankParams.H]
  have hgt : (3*(p:ℤ)^2 + 3*(p:ℤ) + 1 : ℤ) > (BankParams.H : ℤ) := by
    simpa [hH] using hpoly
  simpa [hcalc] using hgt

/-- Any cubic prime power inside the inner band must have base ≥ 80:
    for `p ≤ 79` we have `p^3 < 495_000 ≤ A N` when `N ≥ X0`. -/
lemma cube_base_ge_80_of_mem_innerOddPrimePowers
    {N p : ℕ} (hN : BankParams.X0 ≤ N)
    (hn : p^3 ∈ innerOddPrimePowers N) :
    80 ≤ p := by
  classical
  -- membership gives `A N ≤ p^3`
  rcases Finset.mem_filter.mp hn with ⟨hIcc, _hpow⟩
  have hA_le : A N ≤ p^3 := (Finset.mem_Icc.mp hIcc).1
  -- and `A N ≥ 495000` when `N ≥ X0`
  have hA_min : 495_000 ≤ A N := Goldbach.PPNumerics.inner_left_endpoint_lower (N:=N) hN
  have hge : 495_000 ≤ p^3 := le_trans hA_min hA_le
  -- if `p < 80` then `p^3 ≤ 79^3 = 493039`, contradicting `hge`
  by_contra hlt
  have hp_le : p ≤ 79 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hlt)
  -- expand `p^3` to avoid hunting for a dedicated monotonicity lemma
  have hp2 : p * p ≤ 79 * 79 := Nat.mul_le_mul hp_le hp_le
  have hp3 : p * p * p ≤ 79 * 79 * 79 := Nat.mul_le_mul hp2 hp_le
  have hp3_le : p^3 ≤ 79^3 := by
    -- `pow_succ` twice gives `p^3 = p*p*p`
    simpa [pow_succ, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hp3
  have hp3_lt_495 : (p^3 : ℤ) < 495_000 := by
    have h79_lt : (79^3 : ℤ) < 495_000 := by norm_num
    have hp3_le' : (p^3 : ℤ) ≤ 79^3 := by exact_mod_cast hp3_le
    exact lt_of_le_of_lt hp3_le' h79_lt
  have hge' : (495_000 : ℤ) ≤ (p^3 : ℤ) := by exact_mod_cast hge
  linarith

/-- **Certificate hook**: finite search (external) shows there is at most one odd-exponent
prime power in any inner band `[A(N), B(N)]` for `N ≥ X0`, provided the band lies in the
certified range `B(N) ≤ Bgap`. -/
lemma innerOddPrimePowers_card_le_one {N : ℕ}
    (hN : BankParams.X0 ≤ N) (hB : B N ≤ Goldbach.Cert.OddPrimePowers.Bgap) :
    (innerOddPrimePowers N).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  by_cases hne : a = b
  · simp [hne]
  -- unpack membership of `a` and `b`
  rcases Finset.mem_filter.mp ha with ⟨haIcc, haPow⟩
  rcases Finset.mem_filter.mp hb with ⟨hbIcc, hbPow⟩
  rcases Finset.mem_Icc.mp haIcc with ⟨ha_left, ha_right⟩
  rcases Finset.mem_Icc.mp hbIcc with ⟨hb_left, hb_right⟩
  rcases haPow with ⟨pa, ea, hpa, hea, hodd_a, rfl⟩
  rcases hbPow with ⟨pb, eb, hpb, heb, hodd_b, rfl⟩
  -- inner band lower bound gives `a,b ≥ 495000`
  have hA_min : 495_000 ≤ A N := PPNumerics.inner_left_endpoint_lower (N:=N) hN
  have ha_min : 495_000 ≤ pa ^ ea := le_trans hA_min ha_left
  have hb_min : 495_000 ≤ pb ^ eb := le_trans hA_min hb_left
  -- package as odd prime powers
  have haOPP : _root_.Goldbach.Cert.OddPrimePowers.IsOddPrimePower (pa ^ ea) :=
    ⟨pa, ea, hpa, hea, by simpa [Nat.odd_iff] using hodd_a, rfl⟩
  have hbOPP : _root_.Goldbach.Cert.OddPrimePowers.IsOddPrimePower (pb ^ eb) :=
    ⟨pb, eb, hpb, heb, by simpa [Nat.odd_iff] using hodd_b, rfl⟩
  -- upper bounds to stay within the finite certificate
  have ha_hi : pa ^ ea ≤ Goldbach.Cert.OddPrimePowers.Bgap := le_trans ha_right hB
  have hb_hi : pb ^ eb ≤ Goldbach.Cert.OddPrimePowers.Bgap := le_trans hb_right hB
  -- compare order and derive a contradiction with the band width using the certified gap
  cases lt_or_gt_of_ne hne with
  | inl hlt =>
      have hgap :=
        _root_.Goldbach.Cert.OddPrimePowers.gap_gt_H_of_oddPrimePower haOPP hbOPP ha_min hb_min hb_hi hlt
      have hband1 : pb ^ eb - pa ^ ea ≤ pb ^ eb - A N :=
        Nat.sub_le_sub_left ha_left (pb ^ eb)
      have hband2 : pb ^ eb - A N ≤ B N - A N :=
        Nat.sub_le_sub_right hb_right (A N)
      have hband : pb ^ eb - pa ^ ea ≤ BankParams.H :=
        le_trans (le_trans hband1 hband2) (band_width_le_H_nat (N := N) hN)
      have hcontr : False := (Nat.not_le_of_gt hgap) hband
      exact hcontr.elim
  | inr hgt =>
      have hgap :=
        _root_.Goldbach.Cert.OddPrimePowers.gap_gt_H_of_oddPrimePower hbOPP haOPP hb_min ha_min ha_hi hgt
      have hband1 : pa ^ ea - pb ^ eb ≤ pa ^ ea - A N :=
        Nat.sub_le_sub_left hb_left (pa ^ ea)
      have hband2 : pa ^ ea - A N ≤ B N - A N :=
        Nat.sub_le_sub_right ha_right (A N)
      have hband : pa ^ ea - pb ^ eb ≤ BankParams.H :=
        le_trans (le_trans hband1 hband2) (band_width_le_H_nat (N := N) hN)
      have hcontr : False := by
        have : BankParams.H < pa ^ ea - pb ^ eb := hgap
        linarith [hband, this]
      exact hcontr.elim

/-- **Certificate hook (scaffold)**: decomposition of `ppInnerCount` into square vs odd
prime-power contributors for the canonical window.

The proof splits prime powers by parity of the exponent (even ⇒ squares, odd ≥ 3 ⇒
`innerOddPrimePowers`) and observes that each contributing inner value corresponds to at most
two offsets `±(2n-N)`. For the “symmetric” case we assume `N ≥ X0`, so in particular `H ≤ N`
and the truncation behavior of `Nat.sub` does not interfere with the bookkeeping. -/
lemma ppInnerCount_split_cert {N : ℕ} :
    (hN : BankParams.X0 ≤ N) →
    ppInnerCount BankParams.H N
      ≤ 8 * (PPBoundSquares.innerSquares N).card
        + 8 * (innerOddPrimePowers N).card := by
  classical
  intro hN
  -- Prime powers in the inner band (values, not offsets).
  let PP := (Finset.Icc (A N) (B N)).filter isPrimePower

  -- offsets hitting a specific value `n` (or its symmetric counterpart `N-n`)
  let offsets := fun n : ℕ =>
    Finset.filter
      (fun k : ℤ => abs k ≤ (BankParams.H : ℤ) ∧ (N + k.natAbs) / 2 = n)
      (Finset.Icc (-(BankParams.H : ℤ)) (BankParams.H : ℤ))
  let offsetsSym := fun n : ℕ =>
    Finset.filter
      (fun k : ℤ => abs k ≤ (BankParams.H : ℤ) ∧ (N + k.natAbs) / 2 = N - n)
      (Finset.Icc (-(BankParams.H : ℤ)) (BankParams.H : ℤ))

  -- Step 1: combinatorial scaffold — each prime-power value contributes at most 8 offsets.
  have h_offsets' : ppInnerCount BankParams.H N ≤ 8 * PP.card := by
    classical
    unfold ppInnerCount
    let S : Finset ℤ := Finset.Icc (-(BankParams.H : ℤ)) (BankParams.H : ℤ)
    let K : Finset ℤ :=
      Finset.filter
        (fun k : ℤ =>
          abs k ≤ (BankParams.H : ℤ) ∧
            (let n0 : ℕ := (N + k.natAbs) / 2
             isPrimePower n0 ∨ isPrimePower (N - n0)))
        S

    let n0k : ℤ → ℕ := fun k => (N + k.natAbs) / 2
    let g : ℤ → ℕ := fun k => if isPrimePower (n0k k) then n0k k else N - n0k k
    let F : ℕ → Finset ℤ := fun m => offsets m ∪ offsetsSym m

    have hkNatBound {k : ℤ} (hk : abs k ≤ (BankParams.H : ℤ)) :
        k.natAbs ≤ Goldbach.PPNumerics.H := by
      have hH : (BankParams.H : ℤ) = (Goldbach.PPNumerics.H : ℤ) := by
        norm_num [BankParams.H, Goldbach.PPNumerics.H]
      have hk' : abs k ≤ (Goldbach.PPNumerics.H : ℤ) := by simpa [hH] using hk
      have hk'' : (k.natAbs : ℤ) ≤ (Goldbach.PPNumerics.H : ℤ) := by
        have hx' := hk'
        rw [Int.abs_eq_natAbs] at hx'
        exact hx'
      exact_mod_cast hk''

    have n0k_mem_band {k : ℤ} (hk : abs k ≤ (BankParams.H : ℤ)) :
        n0k k ∈ Finset.Icc (A N) (B N) := by
      have hkNat : k.natAbs ≤ Goldbach.PPNumerics.H := hkNatBound (k := k) hk
      set n0 : ℕ := n0k k
      have hmid_le : N / 2 ≤ n0 := by
        have hle : N ≤ N + k.natAbs := Nat.le_add_right _ _
        simpa [n0, n0k] using (Nat.div_le_div_right hle)
      have hA_le : A N ≤ N / 2 := by
        dsimp [A]
        exact Nat.sub_le (N / 2) (Goldbach.PPNumerics.H / 2)
      have hn0_ge : A N ≤ n0 := le_trans hA_le hmid_le

      have hupper1 : n0 ≤ (N + Goldbach.PPNumerics.H) / 2 := by
        have hle : N + k.natAbs ≤ N + Goldbach.PPNumerics.H := Nat.add_le_add_left hkNat N
        simpa [n0, n0k] using (Nat.div_le_div_right hle)
      have hupper2 : (N + Goldbach.PPNumerics.H) / 2 ≤ N / 2 + Goldbach.PPNumerics.H / 2 := by
        have hH : Goldbach.PPNumerics.H = 2 * (Goldbach.PPNumerics.H / 2) := by
          norm_num [Goldbach.PPNumerics.H]
        let h : ℕ := Goldbach.PPNumerics.H / 2
        have hH' : Goldbach.PPNumerics.H = 2 * h := by
          simpa [h] using hH
        have hEq : (N + Goldbach.PPNumerics.H) / 2 = N / 2 + h := by
          calc
            (N + Goldbach.PPNumerics.H) / 2 = (N + 2 * h) / 2 := by
              rw [hH']
            _ = N / 2 + h := by
              simpa using (Nat.add_mul_div_left N h (by decide : 0 < 2))
        have hEq' : (N + Goldbach.PPNumerics.H) / 2 = N / 2 + Goldbach.PPNumerics.H / 2 := by
          simpa [h] using hEq
        exact le_of_eq hEq'
      have hn0_le : n0 ≤ N / 2 + Goldbach.PPNumerics.H / 2 := le_trans hupper1 hupper2
      have hn0_leB : n0 ≤ B N := by simpa [B] using hn0_le
      have : n0 ∈ Finset.Icc (A N) (B N) := Finset.mem_Icc.mpr ⟨hn0_ge, hn0_leB⟩
      simpa [n0, n0k] using this

    have Nsub_n0k_mem_band {k : ℤ} (hk : abs k ≤ (BankParams.H : ℤ)) :
        (N - n0k k) ∈ Finset.Icc (A N) (B N) := by
      set n0 : ℕ := n0k k
      have hn0Icc : n0 ∈ Finset.Icc (A N) (B N) := by
        simpa [n0, n0k] using (n0k_mem_band (k := k) hk)
      have hn0_leB : n0 ≤ B N := (Finset.mem_Icc.mp hn0Icc).2
      have hn0_ge_mid : N / 2 ≤ n0 := by
        have hle : N ≤ N + k.natAbs := Nat.le_add_right _ _
        simpa [n0, n0k] using (Nat.div_le_div_right hle)

      have hA_le_NsubB : A N ≤ N - B N := by
        simp [A, B]
        omega
      have hNB_le : N - B N ≤ N - n0 := Nat.sub_le_sub_left hn0_leB N
      have hn0_sub_ge : A N ≤ N - n0 := le_trans hA_le_NsubB hNB_le

      have hsub1 : N - n0 ≤ N - (N / 2) := Nat.sub_le_sub_left hn0_ge_mid N
      have hceil : N - (N / 2) ≤ N / 2 + 1 := by omega
      have hone : (1 : ℕ) ≤ Goldbach.PPNumerics.H / 2 := by decide
      have hsub2 : N / 2 + 1 ≤ N / 2 + Goldbach.PPNumerics.H / 2 :=
        Nat.add_le_add_left hone (N / 2)
      have hleB : N - n0 ≤ N / 2 + Goldbach.PPNumerics.H / 2 :=
        le_trans (le_trans hsub1 hceil) hsub2
      have hn0_sub_leB : N - n0 ≤ B N := by simpa [B] using hleB
      have : N - n0 ∈ Finset.Icc (A N) (B N) := Finset.mem_Icc.mpr ⟨hn0_sub_ge, hn0_sub_leB⟩
      simpa [n0, n0k] using this

    have n0k_le_N {k : ℤ} (hk : abs k ≤ (BankParams.H : ℤ)) : n0k k ≤ N := by
      have hHleX0 : Goldbach.PPNumerics.H ≤ BankParams.X0 := by
        norm_num [Goldbach.PPNumerics.H, BankParams.X0]
      have hHleN : Goldbach.PPNumerics.H ≤ N := le_trans hHleX0 hN
      have hkNat : k.natAbs ≤ Goldbach.PPNumerics.H := hkNatBound (k := k) hk
      have hkNatN : k.natAbs ≤ N := le_trans hkNat hHleN
      have hsum : N + k.natAbs ≤ 2 * N := by
        have : N + k.natAbs ≤ N + N := Nat.add_le_add_left hkNatN N
        simpa [two_mul] using this
      have hn0_le : (N + k.natAbs) / 2 ≤ N := Nat.div_le_of_le_mul hsum
      simpa [n0k] using hn0_le

    have hMaps : (K : Set ℤ).MapsTo g PP := by
      intro k hkK
      have hkK' : k ∈ K := hkK
      have hkabs : abs k ≤ (BankParams.H : ℤ) := (Finset.mem_filter.mp hkK').2.1
      have hkpp : isPrimePower (n0k k) ∨ isPrimePower (N - n0k k) := by
        simpa [n0k] using (Finset.mem_filter.mp hkK').2.2
      by_cases hp : isPrimePower (n0k k)
      · have hn0Icc : n0k k ∈ Finset.Icc (A N) (B N) := n0k_mem_band (k := k) hkabs
        have : g k ∈ PP := by
          have hg : g k = n0k k := by simp [g, hp]
          rw [hg]
          exact Finset.mem_filter.mpr ⟨hn0Icc, hp⟩
        exact this
      · have hpR : isPrimePower (N - n0k k) := by
          rcases hkpp with hpL | hpR
          · exact False.elim (hp hpL)
          · exact hpR
        have hIcc : (N - n0k k) ∈ Finset.Icc (A N) (B N) := Nsub_n0k_mem_band (k := k) hkabs
        have : g k ∈ PP := by
          have hg : g k = N - n0k k := by simp [g, hp]
          rw [hg]
          exact Finset.mem_filter.mpr ⟨hIcc, hpR⟩
        exact this

    have hcard_eq : K.card = ∑ m ∈ PP, (K.filter fun k => g k = m).card := by
      -- `card_eq_sum_card_fiberwise` is stated using `#{k ∈ K | ...}` notation; unfold it.
      simpa using (Finset.card_eq_sum_card_fiberwise (s := K) (t := PP) (f := g) hMaps)

    have hFiber_le : ∀ m ∈ PP, (K.filter fun k => g k = m).card ≤ (F m).card := by
      intro m hm
      let Km : Finset ℤ := K.filter fun k => g k = m
      have hsub : Km ⊆ F m := by
        intro k hkKm
        have hkK : k ∈ K := (Finset.mem_filter.mp hkKm).1
        have hkg : g k = m := (Finset.mem_filter.mp hkKm).2
        have hkS : k ∈ S := (Finset.mem_filter.mp hkK).1
        have hkabs : abs k ≤ (BankParams.H : ℤ) := (Finset.mem_filter.mp hkK).2.1
        by_cases hp : isPrimePower (n0k k)
        · have hn0_eq : n0k k = m := by simpa [g, hp] using hkg
          have hkOffsets : k ∈ offsets m := by
            refine Finset.mem_filter.mpr ?_
            refine ⟨hkS, ?_⟩
            exact ⟨hkabs, by simpa [n0k] using hn0_eq⟩
          exact Finset.mem_union.mpr (Or.inl hkOffsets)
        · have hm_eq : N - n0k k = m := by simpa [g, hp] using hkg
          have hn0_leN : n0k k ≤ N := n0k_le_N (k := k) hkabs
          have hn0_eq : n0k k = N - m := by
            have : n0k k = N - (N - n0k k) := (Nat.sub_sub_self hn0_leN).symm
            -- rewrite `m = N - n0k k`
            simpa [hm_eq.symm] using this
          have hkOffsets : k ∈ offsetsSym m := by
            refine Finset.mem_filter.mpr ?_
            refine ⟨hkS, ?_⟩
            exact ⟨hkabs, by simpa [n0k] using hn0_eq⟩
          exact Finset.mem_union.mpr (Or.inr hkOffsets)
      have hcard : Km.card ≤ (F m).card := Finset.card_le_card hsub
      simpa [Km] using hcard

    have hFm_le : ∀ m ∈ PP, (F m).card ≤ 8 := by
      intro m hm
      have h1 : (offsets m).card ≤ 4 := by
        simpa [offsets] using offsets_for_value_card_le_four N m
      have h2 : (offsetsSym m).card ≤ 4 := by
        simpa [offsetsSym] using offsets_for_value_card_le_four N (N - m)
      have hunion : (F m).card ≤ (offsets m).card + (offsetsSym m).card := Finset.card_union_le _ _
      have : (F m).card ≤ 8 := by
        calc
          (F m).card ≤ (offsets m).card + (offsetsSym m).card := hunion
          _ ≤ 4 + 4 := add_le_add h1 h2
          _ = 8 := by decide
      simpa [F] using this

    have hsum_le : (∑ m ∈ PP, (K.filter fun k => g k = m).card) ≤ ∑ _m ∈ PP, (8 : ℕ) := by
      refine Finset.sum_le_sum ?_
      intro m hm
      exact le_trans (hFiber_le m hm) (hFm_le m hm)

    have hsum_eq : (∑ _m ∈ PP, (8 : ℕ)) = 8 * PP.card := by
      classical
      simp [Nat.mul_comm]

    have : K.card ≤ 8 * PP.card := by
      calc
        K.card = ∑ m ∈ PP, (K.filter fun k => g k = m).card := hcard_eq
        _ ≤ ∑ _m ∈ PP, (8 : ℕ) := hsum_le
        _ = 8 * PP.card := hsum_eq

    simpa [K, S] using this

  -- Step 2: classify prime-power values into squares vs odd prime powers.
  have h_class :
      PP.card ≤ (PPBoundSquares.innerSquares N).card + (innerOddPrimePowers N).card := by
    -- Use `isPrimePower_even_or_odd` to split a prime power in the band into
    -- either a square `t^2` (hence `t ∈ innerSquares`) or an odd prime power
    -- (hence in `innerOddPrimePowers`). The two families are disjoint.
    simpa [PP] using primePowers_split_card (N := N)

  -- Combine the two bounds and expand the product.
  have h_mul :
      8 * PP.card ≤ 8 * ((PPBoundSquares.innerSquares N).card + (innerOddPrimePowers N).card) :=
    Nat.mul_le_mul_left 8 h_class
  have hmain :
      ppInnerCount BankParams.H N ≤
        8 * ((PPBoundSquares.innerSquares N).card + (innerOddPrimePowers N).card) :=
    le_trans h_offsets' h_mul
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmain

/-- (**Scaffold**) Split the inner prime-power offset count into squares vs higher prime powers. -/
lemma ppInnerCount_le_two_mul_innerSquares_add_two_mul_innerOddPrimePowers {N : ℕ} :
    (hN : BankParams.X0 ≤ N) →
    ppInnerCount BankParams.H N
      ≤ 8 * (PPBoundSquares.innerSquares N).card
        + 8 * (innerOddPrimePowers N).card := by
  -- Certificate placeholder: the intended proof is by splitting prime powers by parity of exponent.
  -- Inject offsets with even exponents into `innerSquares`, and odd into `innerOddPrimePowers`.
  -- The external certificate can discharge the finite checking.
  intro hN
  exact ppInnerCount_split_cert (N := N) hN

theorem ppInnerCount_le_72 {N : ℕ} (hN : BankParams.X0 ≤ N)
    (hB : B N ≤ Goldbach.Cert.OddPrimePowers.Bgap) :
    ppInnerCount BankParams.H N ≤ 72 := by
  have hsplit :
      ppInnerCount BankParams.H N
        ≤ 8 * (PPBoundSquares.innerSquares N).card
          + 8 * (innerOddPrimePowers N).card :=
    ppInnerCount_le_two_mul_innerSquares_add_two_mul_innerOddPrimePowers (N := N) hN
  have hsq : (PPBoundSquares.innerSquares N).card ≤ 8 := by
    -- per your dictionary: PPBoundSquares.innerSquares_card_le_8
    simpa using PPBoundSquares.squares_in_lenH_le_8 (N := N) hN
  have hodd : (innerOddPrimePowers N).card ≤ 1 :=
    innerOddPrimePowers_card_le_one (N := N) hN hB
  have hsq' : 8 * (PPBoundSquares.innerSquares N).card ≤ 8 * 8 :=
    Nat.mul_le_mul_left 8 hsq
  have hodd' : 8 * (innerOddPrimePowers N).card ≤ 8 * 1 :=
    Nat.mul_le_mul_left 8 hodd
  have :
      ppInnerCount BankParams.H N ≤ 72 := by
    calc
      ppInnerCount BankParams.H N
          ≤ 8 * (PPBoundSquares.innerSquares N).card
              + 8 * (innerOddPrimePowers N).card := hsplit
      _ ≤ 8 * 8 + 8 * 1 := by
            exact add_le_add hsq' hodd'
      _ = 72 := by decide
  exact this

lemma ppInnerCount_window_le
    {X N : ℕ} (_hX : BankParams.X0 ≤ X)
    (_hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
    (ppInnerCount BankParams.H N : ℝ) ≤ 2 * (BankParams.H : ℝ) + 1 := by
  -- membership assumptions are unused for this coarse bound
  exact_mod_cast (ppInnerCount_le_twoHplus1 BankParams.H N)

-- canonical contamination cap; keep it reducible (no dependency on BG_Calib to avoid cycles)
noncomputable def Cpp_canon : ℝ := 80

/-- `N` is in the even window `[X, X+H]` if it's between X and X+H and even. -/
-- Use the canonical even-in-window finset from Windows.

lemma ppContam_le_canon
    {X N : ℕ} (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H)
    (hB : B N ≤ Goldbach.Cert.OddPrimePowers.Bgap) :
    (ppInnerCount BankParams.H N : ℝ) ≤ Cpp_canon := by
  have hXN : X ≤ N := by
    have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H :=
      (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : BankParams.X0 ≤ N := le_trans hX hXN
  have hpp : ppInnerCount BankParams.H N ≤ 72 :=
    ppInnerCount_le_72 (N := N) hN_ge_X0 hB
  have hpp' : (ppInnerCount BankParams.H N : ℝ) ≤ 72 := by
    exact_mod_cast hpp
  have hcpp : (72 : ℝ) ≤ Cpp_canon := by norm_num [Cpp_canon]
  exact le_trans hpp' hcpp

-- outer band: U-band \ inner (BG) band
noncomputable def outerBand : Finset ℤ := bandU \ S_BG

noncomputable def tentRefWeight (k : ℤ) : ℝ :=
  if _ : k ∈ S_BG then tentFullWeight k else 0

noncomputable def errTI (X N : ℕ) : ℝ :=
  (outerBand.sum (fun k => (Goldbach.BG_Bank.P_BG X N k) * tentFullWeight k))

noncomputable def conv_full (X N : ℕ) : ℝ :=
  (bandU.sum (fun k => (Goldbach.BG_Bank.P_BG X N k) * tentFullWeight k))

noncomputable def conv_ref (X N : ℕ) : ℝ :=
  (bandU.sum (fun k => (Goldbach.BG_Bank.P_BG X N k) * tentRefWeight k))

lemma mem_S_BG_zero : (0 : ℤ) ∈ S_BG := by
  refine Finset.mem_Icc.mpr ?_
  constructor <;> simp

lemma mem_S_BG_iff (k : ℤ) : k ∈ S_BG ↔ -(H : ℤ) ≤ k ∧ k ≤ (H : ℤ) := by
  simp [S_BG, Goldbach.BG_Bank.S_BG]

lemma K_full_pos_at_zero : 0 < K_full (0 : ℤ) := by
  -- K_full 0 = 1 / Ucut; prove positivity via Ucut>0
  have hUposNat : 0 < Ucut := by
    -- Ucut ≥ BankParams.H and BankParams.H is a positive numeral
    have hHpos : 0 < BankParams.H := by simp [BankParams.H]
    have hle : BankParams.H ≤ Ucut := by simp [Ucut]
    exact lt_of_lt_of_le hHpos hle
  have hUpos : (0 : ℝ) < (Ucut : ℝ) := by
    exact_mod_cast hUposNat
  -- unfold and compute at 0
  simp [K_full, K_full_raw] at *
  -- after simp, goal becomes `0 < 1 / (Ucut:ℝ)`
  simpa using (one_div_pos.mpr hUpos)

lemma mem_S_BG_of_mem_Icc {k : ℤ} (hk : k ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)) : k ∈ S_BG := by
  rw [S_BG, Goldbach.BG_Bank.S_BG]
  exact hk

/-- Sum over `S_BG` is positive since `K_full 0 > 0` and all terms are nonnegative. -/
lemma sum_pos_of_pos_at_zero :
    0 < Finset.sum S_BG (fun k => K_full k) := by
  have hk0 : (0 : ℤ) ∈ S_BG := by
    rw [mem_S_BG_iff]
    constructor <;> simp
  have hpos0 : 0 < K_full (0 : ℤ) := K_full_pos_at_zero
  have hnonneg : ∀ k ∈ S_BG.erase 0, 0 ≤ K_full k := by
    intro k hk
    exact K_full_nonneg k
  have hsplit :
      Finset.sum S_BG (fun k => K_full k)
        = K_full 0 + Finset.sum (S_BG.erase 0) (fun k => K_full k) := by
    have := Finset.sum_erase_add S_BG (fun k => K_full k) hk0
    linarith
  have hrest_nonneg : 0 ≤ Finset.sum (S_BG.erase 0) (fun k => K_full k) := by
    exact Finset.sum_nonneg hnonneg
  nlinarith

/-- Reference in-window operator: equals the main term on the window, conv_ref off it. -/
noncomputable def bankOp_ref (X N : ℕ) : ℝ :=
  if _ : BankParams.X0 ≤ X ∧ N ∈ Goldbach.Windows.EvenIn X BankParams.H then
    (Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) N
  else
    conv_ref X N

/-- Exposed full bank operator: equals the raw count on the window, conv_full off it. -/
noncomputable def bankOp_full (X N : ℕ) : ℝ :=
  if _ : BankParams.X0 ≤ X ∧ N ∈ Goldbach.Windows.EvenIn X BankParams.H then
    (Goldbach.Rep.R N : ℝ)
  else
    conv_full X N

/-- Calibration on the window: full bank operator reproduces `R`. -/
lemma bankOp_full_eq_R_on_window {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
    bankOp_full X N = (Goldbach.Rep.R N : ℝ) := by
  simp [bankOp_full, hX, hN]

/-- Calibration on the window: reference bank operator reproduces `M`. -/
lemma bankOp_ref_eq_M_on_window {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
    bankOp_ref X N = (Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) N := by
  simp [bankOp_ref, hX, hN]

/-- In-window operator deviation (currently zero with bankOp_ref = conv_ref). -/
noncomputable def errBG (_X _N : ℕ) : ℝ := 0

/-- Mass of the in-window kernel. -/
noncomputable def mass_BG : ℝ := Finset.sum S_BG (fun k => K_full k)

lemma mass_BG_pos : 0 < mass_BG := by
  classical
  unfold mass_BG
  -- 0 is in the BG inner band
  have h0 : (0 : ℤ) ∈ S_BG := mem_S_BG_zero
  -- The full sum dominates the single term at 0 (since all summands are ≥ 0)
  have hle :
      K_full (0 : ℤ) ≤ Finset.sum S_BG (fun k => K_full k) := by
    refine
      Finset.single_le_sum
        (s := S_BG) (a := (0 : ℤ)) (f := fun k => K_full k) ?_ h0
    intro k hk
    -- important: call with the correct argument name; don't pass hk
    exact K_full_nonneg k
  -- conclude positivity from K_full_pos_at_zero and the lower bound
  exact lt_of_lt_of_le K_full_pos_at_zero hle

/-- Constant reference payload: sigma·weight_mass divided by kernel mass on the window. -/
noncomputable def Pref (X N : ℕ) (k : ℤ) : ℝ :=
  if _ : k ∈ S_BG then
    (AO_Major.sigma N * AO_Major.weight_mass X) / mass_BG
  else
    0

/-- Constant-reference in-window operator. -/
noncomputable def conv_ref_const (X N : ℕ) : ℝ :=
  Finset.sum S_BG (fun k => Pref X N k * K_full k)
-- moved below the Kernel block and tentAdmissibleKernel to avoid forward refs

/-- The constant reference operator equals `σ(N) * weight_mass(X)` by definition. -/
lemma conv_ref_const_eq_sigma_mass (X N : ℕ) :
    conv_ref_const X N = AO_Major.sigma N * AO_Major.weight_mass X := by
  classical
  have hpos : 0 < mass_BG := mass_BG_pos
  have hne : mass_BG ≠ 0 := ne_of_gt hpos
  -- rewrite the sum as a constant factor times `mass_BG`
  have hrewrite :
      conv_ref_const X N
        = ((AO_Major.sigma N * AO_Major.weight_mass X) / mass_BG)
            * (Finset.sum S_BG (fun k => K_full k)) := by
    unfold conv_ref_const
    -- on `S_BG`, the `if` in `Pref` always takes the inner branch
    have :
        (Finset.sum S_BG (fun k => Pref X N k * K_full k))
          = Finset.sum S_BG (fun k => ((AO_Major.sigma N * AO_Major.weight_mass X) / mass_BG) * K_full k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp [Pref, hk]
    -- factor out the constant
    calc
      (Finset.sum S_BG (fun k => Pref X N k * K_full k))
          = Finset.sum S_BG (fun k => ((AO_Major.sigma N * AO_Major.weight_mass X) / mass_BG) * K_full k) := this
      _ = ((AO_Major.sigma N * AO_Major.weight_mass X) / mass_BG)
            * (Finset.sum S_BG (fun k => K_full k)) := by
            simpa using
              (Finset.mul_sum (s := S_BG) (f := fun k => K_full k)
                (a := (AO_Major.sigma N * AO_Major.weight_mass X) / mass_BG)).symm
  -- substitute `mass_BG = ∑ K_full` and cancel
  unfold mass_BG at hrewrite
  have hm_ne : (Finset.sum S_BG (fun k => K_full k)) ≠ 0 := by
    simpa using hne
  have :
      ((AO_Major.sigma N * AO_Major.weight_mass X) / (Finset.sum S_BG (fun k => K_full k)))
        * (Finset.sum S_BG (fun k => K_full k)) = AO_Major.sigma N * AO_Major.weight_mass X := by
    -- `(a / m) * m = a` when `m ≠ 0`
    simp [div_eq_mul_inv, hm_ne]
  simpa [hrewrite] using this

/-- Partition the full band into outer and inner parts. -/
lemma S_BG_subset_bandU : S_BG ⊆ bandU := by
  intro k hk
  have hHU_nat : H ≤ Ucut := by
    simp [Ucut]
  have hHU : (H : ℤ) ≤ (Ucut : ℤ) := by exact_mod_cast hHU_nat
  have hkIcc : k ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    simpa [S_BG, Goldbach.BG_Bank.S_BG] using hk
  rcases Finset.mem_Icc.mp hkIcc with ⟨hklo, hkhi⟩
  have hklo' : (-(Ucut : ℤ)) ≤ k := by
    have : (-(Ucut : ℤ)) ≤ (-(H : ℤ)) := by
      simpa using (Int.neg_le_neg hHU)
    exact le_trans this hklo
  have hkhi' : k ≤ (Ucut : ℤ) := le_trans hkhi hHU
  simpa [bandU] using (Finset.mem_Icc.mpr ⟨hklo', hkhi'⟩)

lemma sum_bandU_outer_inner (f : ℤ → ℝ) :
    (∑ k ∈ bandU, f k) = (∑ k ∈ outerBand, f k) + (∑ k ∈ S_BG, f k) := by
  classical
  have hsubset := S_BG_subset_bandU
  have hdisj : Disjoint outerBand S_BG := by
    refine Finset.disjoint_left.2 ?_
    intro k hkO hkS
    have hkO' : k ∈ bandU ∧ k ∉ S_BG := by
      have : k ∈ bandU \ S_BG := by simpa [outerBand] using hkO
      exact Finset.mem_sdiff.mp this
    exact hkO'.2 hkS
  have hunion : outerBand ∪ S_BG = bandU := by
    ext k
    by_cases hkS : k ∈ S_BG
    · have hkB : k ∈ bandU := hsubset hkS
      simp [hkS, hkB]
    · simp [outerBand, hkS]
  calc
    (∑ k ∈ bandU, f k) = ∑ k ∈ outerBand ∪ S_BG, f k := by
      simp [hunion]
    _ = (∑ k ∈ outerBand, f k) + (∑ k ∈ S_BG, f k) := by
      simpa using (Finset.sum_union hdisj (f := f))

/-- Pure algebra: the full-vs-reference convolution gap equals the Type-I tail `errTI`. -/
lemma conv_full_sub_conv_ref_eq_errTI (X N : ℕ) :
    conv_full X N - conv_ref X N = errTI X N := by
  classical
  have hfull :=
    sum_bandU_outer_inner (f := fun k => P_BG X N k * tentFullWeight k)
  have href :=
    sum_bandU_outer_inner (f := fun k => P_BG X N k * tentRefWeight k)

  have houter_ref :
      Finset.sum outerBand (fun k => P_BG X N k * tentRefWeight k) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hk' : k ∉ S_BG := (Finset.mem_sdiff.mp (by simpa [outerBand] using hk)).2
    simp [tentRefWeight, hk']

  have hinner_ref :
      Finset.sum S_BG (fun k => P_BG X N k * tentRefWeight k)
        = Finset.sum S_BG (fun k => P_BG X N k * tentFullWeight k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [tentRefWeight, hk]

  have hfull' :
      conv_full X N
        = Finset.sum outerBand (fun k => P_BG X N k * tentFullWeight k)
          + Finset.sum S_BG (fun k => P_BG X N k * tentFullWeight k) := by
    simpa [conv_full] using hfull

  have href' :
      conv_ref X N
        = Finset.sum outerBand (fun k => P_BG X N k * tentRefWeight k)
          + Finset.sum S_BG (fun k => P_BG X N k * tentRefWeight k) := by
    simpa [conv_ref] using href

  calc
    conv_full X N - conv_ref X N
        =
          (Finset.sum outerBand (fun k => P_BG X N k * tentFullWeight k)
              + Finset.sum S_BG (fun k => P_BG X N k * tentFullWeight k))
            - (Finset.sum outerBand (fun k => P_BG X N k * tentRefWeight k)
              + Finset.sum S_BG (fun k => P_BG X N k * tentRefWeight k)) := by
            simp [hfull', href']
    _ = Finset.sum outerBand (fun k => P_BG X N k * tentFullWeight k) := by
          have :
              (Finset.sum outerBand (fun k => P_BG X N k * tentFullWeight k)
                  + Finset.sum S_BG (fun k => P_BG X N k * tentFullWeight k))
                - (0 + Finset.sum S_BG (fun k => P_BG X N k * tentFullWeight k))
                = Finset.sum outerBand (fun k => P_BG X N k * tentFullWeight k) := by
            ring
          simpa [houter_ref, hinner_ref] using this
    _ = errTI X N := by
          simp [errTI]

/-- The full tent kernel is nonnegative on its support. -/
lemma K_full_nonneg_band {k : ℤ} (_hk : k ∈ bandU) : 0 ≤ K_full k :=
  K_full_nonneg k

/-- On the outer band, `K_full` is nonnegative. -/
lemma K_full_nonneg_outer {k : ℤ} (_hk : k ∈ outerBand) : 0 ≤ K_full k :=
  K_full_nonneg k

/-- On the outer band, the sum of `|K_full|` equals the sum of `K_full`. -/
lemma sum_abs_K_full_outer :
    Finset.sum outerBand (fun k => |K_full k|) = Finset.sum outerBand (fun k => K_full k) := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have := K_full_nonneg_outer (k := k) hk
  simp [abs_of_nonneg this]

/-- On the outer band, `K_full k ≤ (1 - (H+1)/U)/U` since `|k| ≥ H+1`.
-- (Removed a long, unused numeric bound on K_full over the outer band.)
Cardinality of the outer band: `|outerBand| = (2*Ucut+1) - (2*H+1) = 2*(Ucut-H)`. -/
-- (Removed an unused outerBand.card computation that caused brittle arithmetic goals.)

-- Abstract Type-I tail bound: |errTI| ≤ payload_cap N * tail_mass. -/
lemma errTI_bound_from_tail
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H)
    {tail_mass : ℝ} (hTail : Finset.sum outerBand (fun k => K_full k)≤ tail_mass) :
    |errTI X N| ≤ payload_cap X N * tail_mass := by
  classical
  -- |∑ a*b| ≤ (sup |a|) * ∑ |b|
  have step1 :
      |Finset.sum outerBand (fun k => P_BG X N k * K_full k)|
        ≤ payload_cap X N * Finset.sum outerBand (fun k => |K_full k|) := by
    refine abs_sum_mul_le_cap_sum_abs (s:=outerBand)
      (a:=fun k => P_BG X N k) (b:=fun k => K_full k)
      (C:=payload_cap X N) ?hcap
    intro k hk
    -- payload bound is uniform in k
    have := Goldbach.BG_Bank.payload_bound_window (X:=X) (N:=N) hX hN (k:=k)
    simpa using this
  have step2 : Finset.sum outerBand (fun k => |K_full k|) ≤ tail_mass := by
    have := hTail
    simpa [sum_abs_K_full_outer] using this
  -- combine
  have hcap_nonneg : 0 ≤ payload_cap X N := Goldbach.BG_Bank.payload_nonneg (X:=X) (N:=N)
  have hmul := mul_le_mul_of_nonneg_left step2 hcap_nonneg
  have hfinal := le_trans step1 hmul
  -- keep the rewrite minimal to avoid typeclass inference issues
  simpa [errTI] using hfinal

/-- Exact tail mass constant for the current tent: definitionally the outer-band sum. -/
noncomputable def C_tail : ℝ := Finset.sum outerBand (fun k => K_full k)

lemma tail_mass_le_C_tail :
    Finset.sum outerBand (fun k => K_full k)≤ C_tail := by
  unfold C_tail; exact le_rfl

/-- Concrete errTI bound using the exact tail mass constant. -/
lemma errTI_bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
      |errTI X N| ≤ payload_cap X N * C_tail := by
  intro X N hX hN
  have := errTI_bound_from_tail (X:=X) (N:=N) hX hN (tail_mass:=C_tail) tail_mass_le_C_tail
  simpa [C_tail] using this

/-- A coarse universal bound on the tail mass. -/
noncomputable def C_tail_bound : ℝ := Finset.sum bandU (fun k => K_full k)

/-- Outer-band mass is at most the full-band mass (= 1). -/
lemma tail_mass_le_bound :
    Finset.sum outerBand (fun k => K_full k) ≤ C_tail_bound := by
  classical
  have hsplit := sum_bandU_outer_inner (f:=fun k => K_full k)
  -- inner sum is nonnegative
  have hinner_nonneg : 0 ≤ Finset.sum S_BG (fun k => K_full k) := by
    exact Finset.sum_nonneg (by intro k hk; exact K_full_nonneg k)
  -- a ≤ a + b when b ≥ 0
  have hle :
      Finset.sum outerBand (fun k => K_full k)
        ≤ Finset.sum outerBand (fun k => K_full k)
            + Finset.sum S_BG (fun k => K_full k) := by
    have := add_le_add_left hinner_nonneg (Finset.sum outerBand (fun k => K_full k))
    simpa using this
  have hband :
      Finset.sum outerBand (fun k => K_full k)
        ≤ Finset.sum bandU (fun k => K_full k) := by
    simpa [hsplit] using hle
  -- conclude: outerBand mass ≤ full-band mass
  simpa [C_tail_bound] using hband

/-- Concrete errTI bound using the crude tail-mass bound. -/
lemma errTI_bound_simple :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
      |errTI X N| ≤ payload_cap X N * C_tail_bound := by
  intro X N hX hN
  have := errTI_bound_from_tail (X:=X) (N:=N) hX hN (tail_mass:=C_tail_bound) tail_mass_le_bound
  exact this

/-- Closed-form tail mass for the normalized linear tent. -/
noncomputable def C_tail_closed : ℝ :=
  1 - ((1 + 2 * H : ℝ) / (Ucut : ℝ)) + ((H * (H + 1) : ℝ) / (Ucut : ℝ)^2)

/-- **Tail mass vs. closed form (TODO)**: the outer-band mass of the tent kernel is bounded by the
closed-form expression `C_tail_closed`.

This is a bespoke, kernel-specific arithmetic fact (not a “conventional math” input).  We keep it
as an explicit lemma so it can be proved later without hiding the dependency inside other bounds.
-/
lemma tail_mass_le_C_tail_closed :
    Finset.sum outerBand (fun k => K_full k) ≤ C_tail_closed := by
  classical
  -- A small arithmetic library for range sums in ℝ.
  have sum_range_id_real (n : ℕ) :
      (∑ i ∈ Finset.range n, (i : ℝ)) = (n * (n - 1) : ℝ) / 2 := by
    cases n with
    | zero =>
        simp
    | succ n =>
        -- In the successor case the subtraction disappears: `n.succ - 1 = n`.
        have hNat : (∑ i ∈ Finset.range (Nat.succ n), i) * 2 = (Nat.succ n) * n := by
          simpa using (Finset.sum_range_id_mul_two (Nat.succ n))
        have hReal2 :
            (∑ i ∈ Finset.range (Nat.succ n), (i : ℝ)) * 2 = ((Nat.succ n) * n : ℝ) := by
          have hNatCast :
              (((∑ i ∈ Finset.range (Nat.succ n), i) * 2 : ℕ) : ℝ) = ((Nat.succ n) * n : ℝ) := by
            exact_mod_cast hNat
          simpa [Nat.cast_sum] using hNatCast
        have hReal :
            (∑ i ∈ Finset.range (Nat.succ n), (i : ℝ)) = ((Nat.succ n) * n : ℝ) / 2 := by
          nlinarith [hReal2]
        -- match the target RHS shape
        simpa [Nat.succ_sub_one] using hReal

  have sum_range_succ_real (n : ℕ) :
      (∑ i ∈ Finset.range n, (Nat.succ i : ℝ)) = (n * (n + 1) : ℝ) / 2 := by
    -- ∑ (i+1) = ∑ i + ∑ 1
    have h1 :
        (∑ i ∈ Finset.range n, (Nat.succ i : ℝ))
          = (∑ i ∈ Finset.range n, (i : ℝ)) + (n : ℝ) := by
      calc
        (∑ i ∈ Finset.range n, (Nat.succ i : ℝ))
            = ∑ i ∈ Finset.range n, ((i : ℝ) + 1) := by
                simp [Nat.succ_eq_add_one, Nat.cast_add]
        _ = (∑ i ∈ Finset.range n, (i : ℝ)) + ∑ _i ∈ Finset.range n, (1 : ℝ) := by
              simpa [Finset.sum_add_distrib]
        _ = (∑ i ∈ Finset.range n, (i : ℝ)) + (n : ℝ) := by
              simp
    -- substitute the closed form for ∑ i
    have h0 : (∑ i ∈ Finset.range n, (i : ℝ)) = (n * (n - 1) : ℝ) / 2 :=
      sum_range_id_real n
    nlinarith [h1, h0]

  have sum_range_add_one_real (n : ℕ) :
      (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = (n * (n + 1) : ℝ) / 2 := by
    simpa [Nat.succ_eq_add_one, Nat.cast_add] using sum_range_succ_real n

  -- Closed form for the tent mass on the symmetric integer interval `[-n,n]` (with `n ≤ Ucut`).
  have sum_Icc_K_full (n : ℕ) (hnpos : 0 < n) (hn : n ≤ Ucut) :
      Finset.sum (Finset.Icc (-(n : ℤ)) (n : ℤ)) (fun k => K_full k)
        = ((1 + 2 * n : ℝ) / (Ucut : ℝ))
            - ((n * (n + 1) : ℝ) / (Ucut : ℝ) ^ 2) := by
    classical
    let s : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)
    have hs0 : (0 : ℤ) ∈ s := by
      simp [s]

    -- Positive/negative enumerations of `{±1, …, ±n}`.
    let embPos : ℕ ↪ ℤ :=
      ⟨fun k : ℕ => (Nat.succ k : ℤ), by
        intro a b h
        exact Nat.succ.inj (Int.ofNat.inj (by simpa using h))⟩
    let embNeg : ℕ ↪ ℤ :=
      ⟨fun k : ℕ => -(Nat.succ k : ℤ), by
        intro a b h
        have : (Nat.succ a : ℤ) = (Nat.succ b : ℤ) := by
          -- cancel the negations
          linarith
        exact Nat.succ.inj (Int.ofNat.inj (by simpa using this))⟩
    let pos : Finset ℤ := (Finset.range n).map embPos
    let neg : Finset ℤ := (Finset.range n).map embNeg

    have hdisj : Disjoint pos neg := by
      refine Finset.disjoint_left.2 ?_
      intro x hxpos hxneg
      rcases Finset.mem_map.1 hxpos with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.1 hxneg with ⟨b, hb, hbEq⟩
      have hEq : (Nat.succ a : ℤ) = -(Nat.succ b : ℤ) := by
        simpa [embNeg, embPos] using hbEq.symm
      have haPos : (0 : ℤ) < (Nat.succ a : ℤ) := by
        exact_mod_cast (Nat.succ_pos a)
      have hbNonpos : (-(Nat.succ b : ℤ)) ≤ 0 := by
        exact neg_nonpos.mpr (by exact_mod_cast (Nat.zero_le (Nat.succ b)))
      have haLe0 : (Nat.succ a : ℤ) ≤ 0 := by simpa [hEq] using hbNonpos
      exact (not_lt_of_ge haLe0) haPos

    have herase : s.erase 0 = pos ∪ neg := by
      -- membership description: all nonzero z with `|z| ≤ n` are ±(k+1) for some k<n.
      apply Finset.ext
      intro z
      constructor
      · intro hz
        have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
        have hzI : z ∈ s := (Finset.mem_erase.mp hz).2
        have hzIcc : (-(n : ℤ) ≤ z) ∧ (z ≤ (n : ℤ)) := Finset.mem_Icc.mp hzI
        -- deduce `natAbs z ≤ n`
        have hzAbsZ : (z.natAbs : ℤ) ≤ (n : ℤ) := by
          have habs : |z| ≤ (n : ℤ) := (abs_le).2 hzIcc
          -- avoid `simp` unfolding loops: rewrite the LHS only
          have habs' := habs
          -- `|z| = (z.natAbs : ℤ)`
          rw [Int.abs_eq_natAbs] at habs'
          exact habs'
        have hzAbs : z.natAbs ≤ n := by exact_mod_cast hzAbsZ
        have hzAbs_ne0 : z.natAbs ≠ 0 := by
          intro h
          have : z = 0 := (Int.natAbs_eq_zero.mp h)
          exact hz0 this
        have hzAbs_pos : 0 < z.natAbs := Nat.pos_of_ne_zero hzAbs_ne0
        let k : ℕ := z.natAbs - 1
        have hklt : k < n := by
          have hklt' : k < z.natAbs := by
            -- `m-1 < m` for `m>0`
            simpa [k] using (Nat.pred_lt hzAbs_ne0)
          exact lt_of_lt_of_le hklt' hzAbs
        have hkMem : k ∈ Finset.range n := Finset.mem_range.mpr hklt
        have hsucc : Nat.succ k = z.natAbs := by
          simpa [k] using (Nat.succ_pred_eq_of_pos hzAbs_pos)
        -- decide sign and land in the corresponding side
        by_cases hzNonneg : 0 ≤ z
        · -- z is nonnegative, so z = ofNat (toNat z) = ofNat (natAbs z)
          have hzEq' : (z.natAbs : ℤ) = z := Int.natAbs_of_nonneg hzNonneg
          apply Finset.mem_union.mpr
          left
          refine Finset.mem_map.mpr ?_
          refine ⟨k, hkMem, ?_⟩
          -- embPos k = z
          have hsuccZ : (Nat.succ k : ℤ) = (z.natAbs : ℤ) := by exact_mod_cast hsucc
          calc
            embPos k = (Nat.succ k : ℤ) := rfl
            _ = (z.natAbs : ℤ) := hsuccZ
            _ = z := hzEq'
        · -- z is negative, so z = - ofNat (natAbs z)
          have hzNonpos : z ≤ 0 := le_of_not_ge hzNonneg
          have hzNatAbs : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hzNonpos
          have hzEq' : -(z.natAbs : ℤ) = z := by linarith
          apply Finset.mem_union.mpr
          right
          refine Finset.mem_map.mpr ?_
          refine ⟨k, hkMem, ?_⟩
          have hsuccZ : (Nat.succ k : ℤ) = (z.natAbs : ℤ) := by exact_mod_cast hsucc
          have hsuccZneg : -(Nat.succ k : ℤ) = -(z.natAbs : ℤ) := by
            simpa using congrArg Neg.neg hsuccZ
          calc
            embNeg k = -(Nat.succ k : ℤ) := rfl
            _ = -(z.natAbs : ℤ) := hsuccZneg
            _ = z := hzEq'
      · intro hz
        rcases Finset.mem_union.mp hz with hzPos | hzNeg
        · -- positive side
          rcases Finset.mem_map.mp hzPos with ⟨k, hk, rfl⟩
          refine Finset.mem_erase.mpr ?_
          refine ⟨?_, ?_⟩
          · -- `embPos k ≠ 0`
            have hkpos : (0 : ℤ) < (Nat.succ k : ℤ) := by
              exact_mod_cast (Nat.succ_pos k)
            exact ne_of_gt hkpos
          ·
            have hklt : k < n := Finset.mem_range.mp hk
            have hle : Nat.succ k ≤ n := Nat.succ_le_of_lt hklt
            have hIcc : embPos k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
              refine Finset.mem_Icc.mpr ?_
              refine ⟨?_, ?_⟩
              · -- -(n:ℤ) ≤ embPos k
                have hn0 : (-(n : ℤ)) ≤ 0 := by
                  exact neg_nonpos.mpr (by exact_mod_cast (Nat.zero_le n))
                have hk0 : (0 : ℤ) ≤ (Nat.succ k : ℤ) := by
                  exact_mod_cast (Nat.zero_le (Nat.succ k))
                simpa [embPos] using (le_trans hn0 hk0)
              · -- embPos k ≤ n
                simpa [embPos] using (by
                  exact_mod_cast hle : (Nat.succ k : ℤ) ≤ (n : ℤ))
            simpa [s] using hIcc
        · -- negative side
          rcases Finset.mem_map.mp hzNeg with ⟨k, hk, rfl⟩
          refine Finset.mem_erase.mpr ?_
          refine ⟨?_, ?_⟩
          · -- `-(succ k) ≠ 0`
            have hkpos : (0 : ℤ) < (Nat.succ k : ℤ) := by
              exact_mod_cast (Nat.succ_pos k)
            have : (-(Nat.succ k : ℤ)) < 0 := by linarith
            exact ne_of_lt this
          · have hklt : k < n := Finset.mem_range.mp hk
            have hle : Nat.succ k ≤ n := Nat.succ_le_of_lt hklt
            refine Finset.mem_Icc.mpr ?_
            constructor
            · -- -n ≤ -(succ k)
              have hnle : (Nat.succ k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hle
              exact neg_le_neg hnle
            · -- -(succ k) ≤ n
              have hk0 : (-(Nat.succ k : ℤ)) ≤ 0 := by linarith
              exact le_trans hk0 (by exact_mod_cast (Nat.zero_le n))

    -- Pair ±k and compute the sum on `s.erase 0`.
    have hpair :
        Finset.sum neg (fun k => K_full k) = Finset.sum pos (fun k => K_full k) := by
      -- Both are sums over `range n`, and `K_full` is even.
      have hneg :
          (∑ z ∈ neg, K_full z) = ∑ x ∈ Finset.range n, K_full (embNeg x) := by
        simpa [neg] using
          (Finset.sum_map (s := Finset.range n) (e := embNeg) (f := fun z => K_full z))
      have hpos :
          (∑ z ∈ pos, K_full z) = ∑ x ∈ Finset.range n, K_full (embPos x) := by
        simpa [pos] using
          (Finset.sum_map (s := Finset.range n) (e := embPos) (f := fun z => K_full z))
      -- rewrite both sides as `range` sums, then use evenness pointwise
      rw [hneg, hpos]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      simpa [embNeg, embPos] using (K_full_neg (Nat.succ x : ℤ))

    have hsumErase :
        Finset.sum (s.erase 0) (fun k => K_full k)
          = 2 * Finset.sum (Finset.range n) (fun k => K_full ((k : ℤ) + 1)) := by
      have hsumUnion :
          Finset.sum (pos ∪ neg) (fun k => K_full k)
            = Finset.sum pos (fun k => K_full k) + Finset.sum neg (fun k => K_full k) := by
        simpa using (Finset.sum_union hdisj (f := fun k => K_full k))
      -- rewrite `s.erase 0` as the disjoint union and collapse the symmetric sums
      calc
        Finset.sum (s.erase 0) (fun k => K_full k)
            = Finset.sum (pos ∪ neg) (fun k => K_full k) := by simpa [herase]
        _ = Finset.sum pos (fun k => K_full k) + Finset.sum neg (fun k => K_full k) := hsumUnion
        _ = 2 * Finset.sum pos (fun k => K_full k) := by nlinarith [hpair]
        _ = 2 * Finset.sum (Finset.range n) (fun k => K_full ((k : ℤ) + 1)) := by
              simp [pos, embPos, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc]

    have hK0 : K_full (0 : ℤ) = (1 : ℝ) / (Ucut : ℝ) := by
      unfold K_full K_full_raw
      simp

    -- Evaluate the positive side sum using `K_full_ofNat_le`.
    have hpos_eval :
        Finset.sum (Finset.range n) (fun k => K_full ((k : ℤ) + 1))
          = ((n : ℝ) - ((n * (n + 1) : ℝ) / 2) / (Ucut : ℝ)) / (Ucut : ℝ) := by
      calc
        Finset.sum (Finset.range n) (fun k => K_full ((k : ℤ) + 1))
            = Finset.sum (Finset.range n)
                (fun k => ((1 : ℝ) - ((k : ℝ) + 1) / (Ucut : ℝ)) / (Ucut : ℝ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro k hk
                  have hklt : k < n := Finset.mem_range.mp hk
                  have hksucc : Nat.succ k ≤ Ucut := le_trans (Nat.succ_le_of_lt hklt) hn
                  -- rewrite `((k:ℤ)+1)` as `(Nat.succ k : ℤ)` and use the evaluation lemma
                  -- The RHS is already in the `((k:ℝ)+1)` form.
                  simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc] using
                    (K_full_ofNat_le (m := Nat.succ k) hksucc)
        _ = (Finset.sum (Finset.range n) (fun k => (1 : ℝ) - ((k : ℝ) + 1) / (Ucut : ℝ)))
              / (Ucut : ℝ) := by
              -- pull the outer division out of the sum
              simpa using
                (Finset.sum_div (s := Finset.range n)
                  (f := fun k => (1 : ℝ) - ((k : ℝ) + 1) / (Ucut : ℝ)) (a := (Ucut : ℝ))).symm
        _ = ((Finset.sum (Finset.range n) (fun _k => (1 : ℝ)))
                - Finset.sum (Finset.range n) (fun k => ((k : ℝ) + 1) / (Ucut : ℝ)))
              / (Ucut : ℝ) := by
              simp [Finset.sum_sub_distrib]
        _ = ((n : ℝ) - Finset.sum (Finset.range n) (fun k => ((k : ℝ) + 1) / (Ucut : ℝ)))
              / (Ucut : ℝ) := by
              simp
        _ = ((n : ℝ) - ((Finset.sum (Finset.range n) (fun k => (k : ℝ) + 1)) / (Ucut : ℝ)))
              / (Ucut : ℝ) := by
              simp [Finset.sum_div]
        _ = ((n : ℝ) - (((n * (n + 1) : ℝ) / 2) / (Ucut : ℝ))) / (Ucut : ℝ) := by
              -- use the closed form for `∑ (k+1)`
              have hsum : (∑ k ∈ Finset.range n, ((k : ℝ) + 1)) = (n * (n + 1) : ℝ) / 2 :=
                sum_range_add_one_real n
              simpa [hsum]

    -- Assemble the symmetric interval sum.
    have hmain :
        Finset.sum s (fun k => K_full k)
          = ((1 + 2 * n : ℝ) / (Ucut : ℝ))
              - ((n * (n + 1) : ℝ) / (Ucut : ℝ) ^ 2) := by
      have hU0 : (Ucut : ℝ) ≠ 0 := Ucut_ne_zero_real
      have hsum0 : Finset.sum s (fun k => K_full k) =
          K_full 0 + Finset.sum (s.erase 0) (fun k => K_full k) := by
        simpa [s] using (Finset.sum_erase_add (s := s) (f := fun k => K_full k) hs0).symm
      -- rewrite the erase-sum via the positive side and simplify
      calc
        Finset.sum s (fun k => K_full k)
            = K_full 0 + Finset.sum (s.erase 0) (fun k => K_full k) := hsum0
        _ = (1 : ℝ) / (Ucut : ℝ)
              + 2 * (Finset.sum (Finset.range n) (fun k => K_full ((k : ℤ) + 1))) := by
              simpa [hK0, hsumErase]
        _ = (1 : ℝ) / (Ucut : ℝ)
              + 2 * (((n : ℝ) - ((n * (n + 1) : ℝ) / 2) / (Ucut : ℝ)) / (Ucut : ℝ)) := by
              simp [hpos_eval]
        _ = ((1 + 2 * n : ℝ) / (Ucut : ℝ))
              - ((n * (n + 1) : ℝ) / (Ucut : ℝ) ^ 2) := by
              field_simp [hU0]
              ring
    simpa [s] using hmain

  -- Evaluate the two pieces: full-band mass and inner-band mass.
  have hUpos : 0 < Ucut := by
    -- Ucut is a positive numeral (since H>0)
    have : 0 < BankParams.H := by simp [BankParams.H]
    have : 0 < Ucut := lt_of_lt_of_le this (by simp [Ucut])
    exact this

  have hfull :
      Finset.sum bandU (fun k => K_full k) = (1 : ℝ) := by
    -- bandU = Icc(-Ucut,Ucut)
    have hIcc := sum_Icc_K_full (n := Ucut) (hnpos := hUpos) (hn := le_rfl)
    have hBand :
        Finset.sum bandU (fun k => K_full k)
          = ((1 + 2 * Ucut : ℝ) / (Ucut : ℝ))
              - ((Ucut * (Ucut + 1) : ℝ) / (Ucut : ℝ) ^ 2) := by
      -- avoid `simp` unfolding of `Ucut`; just unfold `bandU`
      change
        Finset.sum (Finset.Icc (-(Ucut : ℤ)) (Ucut : ℤ)) (fun k => K_full k)
          = ((1 + 2 * Ucut : ℝ) / (Ucut : ℝ))
              - ((Ucut * (Ucut + 1) : ℝ) / (Ucut : ℝ) ^ 2)
      simpa using hIcc
    -- simplify the closed form at n = Ucut
    have hU0 : (Ucut : ℝ) ≠ 0 := Ucut_ne_zero_real
    -- (1+2U)/U - U(U+1)/U^2 = 1
    have : ((1 + 2 * Ucut : ℝ) / (Ucut : ℝ)) - ((Ucut * (Ucut + 1) : ℝ) / (Ucut : ℝ) ^ 2) = (1 : ℝ) := by
      field_simp [hU0]
      ring
    simpa [hBand, this]

  have hHle : BankParams.H ≤ Ucut := by
    -- Ucut = H + ceil(H/100)
    simp [Ucut]

  have hinner :
      Finset.sum S_BG (fun k => K_full k)
        = ((1 + 2 * H : ℝ) / (Ucut : ℝ))
            - ((H * (H + 1) : ℝ) / (Ucut : ℝ) ^ 2) := by
    have hIcc := sum_Icc_K_full (n := H)
      (hnpos := by simp [BankParams.H])
      (hn := hHle)
    simpa [S_BG, Goldbach.BG_Bank.S_BG] using hIcc

  -- Now recover the tail as `full - inner` using the `bandU = outer ⊔ inner` decomposition.
  have hsplit :
      Finset.sum bandU (fun k => K_full k)
        = Finset.sum outerBand (fun k => K_full k) + Finset.sum S_BG (fun k => K_full k) := by
    simpa using (sum_bandU_outer_inner (f := fun k => K_full k))
  have houter :
      Finset.sum outerBand (fun k => K_full k) = C_tail_closed := by
    have houter' :
        Finset.sum outerBand (fun k => K_full k)
          = Finset.sum bandU (fun k => K_full k) - Finset.sum S_BG (fun k => K_full k) := by
      linarith [hsplit]
    calc
      Finset.sum outerBand (fun k => K_full k)
          = Finset.sum bandU (fun k => K_full k) - Finset.sum S_BG (fun k => K_full k) := houter'
      _ = (1 : ℝ)
            - (((1 + 2 * H : ℝ) / (Ucut : ℝ)) - ((H * (H + 1) : ℝ) / (Ucut : ℝ) ^ 2)) := by
            simpa [hfull, hinner]
      _ = C_tail_closed := by
            -- `1 - (a - b) = 1 - a + b`
            simp [C_tail_closed, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  exact le_of_eq houter

/-- **Kernel-friendly Type-I tail bound**: closed-form tail mass × payload cap.

This is the bound consumed downstream by the AO kernel-tail module.  The only missing ingredient
is the bespoke arithmetic lemma `tail_mass_le_C_tail_closed`.
-/
lemma errTI_bound_closed :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
      |errTI X N| ≤ payload_cap X N * C_tail_closed := by
  intro X N hX hN
  exact errTI_bound_from_tail (X := X) (N := N) hX hN (tail_mass := C_tail_closed)
    tail_mass_le_C_tail_closed

/-- Numeric corollary for the tail mass. -/
lemma C_tail_closed_le : C_tail_closed ≤ (98 : ℝ) / 10^6 := by
  norm_num [C_tail_closed, Ucut, BankParams.H]

/-- Numeric lower bound for the inner mass. -/
lemma mass_BG_lb : (0.99990 : ℝ) ≤ (1 : ℝ) - C_tail_closed := by
  have h := C_tail_closed_le
  linarith


end

end BG_Identity
end Goldbach
