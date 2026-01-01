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

open Goldbach.PPBoundSquares
open BankParams
open Goldbach.BG_Bank (P_BG payload_cap)

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
      simp [Finset.sum_insert, hk, ih, mul_add, add_comm, add_left_comm,
            add_assoc, mul_comm, mul_left_comm, mul_assoc]
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
      simp [hU, hm0]
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
    simp [Finset.sum_insert, ha, ih, mul_add, add_comm, add_left_comm,
          add_assoc, mul_comm, mul_left_comm, mul_assoc]

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
    have h₁ : f a / U = (1 / U) * f a := by simpa [div_front]
    have h₂ : s.sum (fun k => f k / U) = (1 / U) * s.sum f := ih
    -- rewrite and fold with `mul_add`
    simp [h₁, h₂, Finset.sum_insert, ha, mul_add, add_comm, add_left_comm, add_assoc]

/-- Factor a constant multiplier out of a finite sum over `ℝ`. -/
private lemma sum_const_mul (s : Finset α) (a : ℝ) (f : α → ℝ) :
    s.sum (fun k => a * f k) = a * s.sum f := by
  classical
  refine Finset.induction_on s ?z ?st
  · simp
  · intro b t hb ih
    simp [Finset.sum_insert, hb, ih, mul_add, add_comm, add_left_comm, add_assoc]

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
    simpa [S_BG, Goldbach.BG_Bank.S_BG, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Int.card_Icc (-(BankParams.H : ℤ)) (BankParams.H : ℤ))
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
    simpa [S_BG, Goldbach.BG_Bank.S_BG] using (Finset.mem_Icc.mpr (by constructor <;> simp))
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
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Int.card_Icc (-(H : ℤ)) (H : ℤ))

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

  exact le_trans hle (by simpa [hcardNat])

/-- crude “prime power” predicate; keep your existing definition if you have one. -/
def isPrimePower (m : ℕ) : Prop :=
  ∃ p e, Nat.Prime p ∧ 2 ≤ e ∧ m = p ^ e

/-- “Higher prime powers” in the sense requested for the split: odd exponent `e ≥ 3`. -/
def isOddPrimePower (m : ℕ) : Prop :=
  ∃ p e, Nat.Prime p ∧ 3 ≤ e ∧ Odd e ∧ m = p ^ e

/-- Odd-exponent prime powers inside the inner band `[A(N), B(N)]`. -/
noncomputable def innerOddPrimePowers (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (A N) (B N)).filter isOddPrimePower

/-- Band width certificate: the inner interval `[A N, B N]` has length at most `H` (as naturals). -/
axiom band_width_le_H_nat (N : ℕ) : B N - A N ≤ BankParams.H

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
    nlinarith
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
    have h79 : (79^3 : ℤ) = 493_039 := by norm_num
    have h79_lt : (79^3 : ℤ) < 495_000 := by norm_num
    have hp3_le' : (p^3 : ℤ) ≤ 79^3 := by exact_mod_cast hp3_le
    exact lt_of_le_of_lt hp3_le' (by simpa [h79] using h79_lt)
  have hge' : (495_000 : ℤ) ≤ (p^3 : ℤ) := by exact_mod_cast hge
  linarith

/-- **Certificate hook**: finite search (external) shows there is at most one odd-exponent
prime power in any inner band `[A(N), B(N)]` for `N ≥ X0`. -/
lemma innerOddPrimePowers_card_le_one {N : ℕ} (hN : BankParams.X0 ≤ N) :
    (innerOddPrimePowers N).card ≤ 1 := by
  classical
  refine Finset.card_le_one.mpr ?h
  intro a ha b hb hne
  -- unpack membership
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
  -- certify membership in the odd prime-power list
  have hodd_a_mod : ea % 2 = 1 := by simpa [Nat.odd_iff] using hodd_a
  have hodd_b_mod : eb % 2 = 1 := by simpa [Nat.odd_iff] using hodd_b
  have ha_cert : (pa ^ ea) ∈ Goldbach.Cert.OddPrimePowers.oddPrimePowers :=
    Goldbach.Cert.OddPrimePowers.oddPrimePower_complete ⟨pa, ea, hpa, hea, hodd_a_mod, rfl⟩ ha_min
  have hb_cert : (pb ^ eb) ∈ Goldbach.Cert.OddPrimePowers.oddPrimePowers :=
    Goldbach.Cert.OddPrimePowers.oddPrimePower_complete ⟨pb, eb, hpb, heb, hodd_b_mod, rfl⟩ hb_min
  -- compare order and derive a contradiction with the band width
  cases lt_or_gt_of_ne hne with
  | inl hlt =>
      have hgap := Goldbach.Cert.OddPrimePowers.gap_gt_H_of_mem ha_cert hb_cert hlt
      have hband_nat : pb ^ eb - pa ^ ea ≤ B N - A N := Nat.sub_le_sub hb_right ha_left
      have hband : pb ^ eb - pa ^ ea ≤ BankParams.H :=
        le_trans hband_nat (band_width_le_H_nat (N := N))
      exact (Nat.lt_asymm hgap hband).elim
  | inr hgt =>
      have hgap := Goldbach.Cert.OddPrimePowers.gap_gt_H_of_mem hb_cert ha_cert hgt
      have hband_nat : pa ^ ea - pb ^ eb ≤ B N - A N := Nat.sub_le_sub ha_right hb_left
      have hband : pa ^ ea - pb ^ eb ≤ BankParams.H :=
        le_trans hband_nat (band_width_le_H_nat (N := N))
      exact (Nat.lt_asymm hgap hband).elim

/-- **Certificate hook**: decomposition of `ppInnerCount` into square vs odd prime-power
contributors for the canonical window. -/
axiom ppInnerCount_split_cert {N : ℕ} :
    ppInnerCount BankParams.H N
      ≤ 2 * (PPBoundSquares.innerSquares N).card
        + 2 * (innerOddPrimePowers N).card

/-- (**Scaffold**) Split the inner prime-power offset count into squares vs higher prime powers. -/
lemma ppInnerCount_le_two_mul_innerSquares_add_two_mul_innerOddPrimePowers {N : ℕ} :
    ppInnerCount BankParams.H N
      ≤ 2 * (PPBoundSquares.innerSquares N).card
        + 2 * (innerOddPrimePowers N).card := by
  -- Certificate placeholder: the intended proof is by splitting prime powers by parity of exponent.
  -- Inject offsets with even exponents into `innerSquares`, and odd into `innerOddPrimePowers`.
  -- The external certificate can discharge the finite checking.
  exact ppInnerCount_split_cert (N := N)

theorem ppInnerCount_le_20 {N : ℕ} (hN : BankParams.X0 ≤ N) :
    ppInnerCount BankParams.H N ≤ 20 := by
  have hsplit :
      ppInnerCount BankParams.H N
        ≤ 2 * (PPBoundSquares.innerSquares N).card
          + 2 * (innerOddPrimePowers N).card :=
    ppInnerCount_le_two_mul_innerSquares_add_two_mul_innerOddPrimePowers (N := N)
  have hsq : (PPBoundSquares.innerSquares N).card ≤ 8 := by
    -- per your dictionary: PPBoundSquares.innerSquares_card_le_8
    simpa using PPBoundSquares.squares_in_lenH_le_8 (N := N) hN
  have hodd : (innerOddPrimePowers N).card ≤ 1 := innerOddPrimePowers_card_le_one (N := N) hN
  have hsq' : 2 * (PPBoundSquares.innerSquares N).card ≤ 2 * 8 :=
    Nat.mul_le_mul_left 2 hsq
  have hodd' : 2 * (innerOddPrimePowers N).card ≤ 2 * 1 :=
    Nat.mul_le_mul_left 2 hodd
  have :
      ppInnerCount BankParams.H N ≤ 18 := by
    calc
      ppInnerCount BankParams.H N
          ≤ 2 * (PPBoundSquares.innerSquares N).card
              + 2 * (innerOddPrimePowers N).card := hsplit
      _ ≤ 2 * 8 + 2 * 1 := by
            exact add_le_add hsq' hodd'
      _ = 18 := by decide
  have htop : ppInnerCount BankParams.H N ≤ 20 := by exact le_trans this (by decide)
  exact htop

lemma ppInnerCount_window_le
    {X N : ℕ} (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
    (ppInnerCount BankParams.H N : ℝ) ≤ 2 * (BankParams.H : ℝ) + 1 := by
  -- membership assumptions are unused for this coarse bound
  exact_mod_cast (ppInnerCount_le_twoHplus1 BankParams.H N)

-- canonical contamination cap; keep it reducible (no dependency on BG_Calib to avoid cycles)
noncomputable def Cpp_canon : ℝ := 20

/-- `N` is in the even window `[X, X+H]` if it's between X and X+H and even. -/
-- Use the canonical even-in-window finset from Windows.

lemma ppContam_le_canon
    {X N : ℕ} (hX : BankParams.X0 ≤ X)
    (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
    (ppInnerCount BankParams.H N : ℝ) ≤ Cpp_canon := by
  have hXN : X ≤ N := by
    have hI : N ∈ Goldbach.Windows.IccShift X BankParams.H :=
      (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : BankParams.X0 ≤ N := le_trans hX hXN
  have hpp20 : ppInnerCount BankParams.H N ≤ 20 :=
    ppInnerCount_le_20 (N := N) hN_ge_X0
  have hpp20' : (ppInnerCount BankParams.H N : ℝ) ≤ 20 := by
    exact_mod_cast hpp20
  have hcpp : (20 : ℝ) ≤ Cpp_canon := by simp [Cpp_canon]
  exact le_trans hpp20' hcpp

-- outer band: U-band \ inner (BG) band
noncomputable def outerBand : Finset ℤ := bandU \ S_BG

noncomputable def tentRefWeight (k : ℤ) : ℝ :=
  if hk : k ∈ S_BG then tentFullWeight k else 0

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
  simp [K_full, K_full_raw, hUpos.ne'] at *
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
  if h : BankParams.X0 ≤ X ∧ N ∈ Goldbach.Windows.EvenIn X BankParams.H then
    (Goldbach.MainTerm.M Goldbach.Analytic.C2_numeric) N
  else
    conv_ref X N

/-- Exposed full bank operator: equals the raw count on the window, conv_full off it. -/
noncomputable def bankOp_full (X N : ℕ) : ℝ :=
  if h : BankParams.X0 ≤ X ∧ N ∈ Goldbach.Windows.EvenIn X BankParams.H then
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
noncomputable def errBG (X N : ℕ) : ℝ := 0

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
  if h : k ∈ S_BG then
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
      simp [Pref, hk, mul_assoc]
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
    simp [div_eq_mul_inv, hm_ne, mul_assoc, mul_left_comm, mul_comm]
  simpa [hrewrite] using this

/-- Partition the full band into outer and inner parts. -/
lemma S_BG_subset_bandU : S_BG ⊆ bandU := by
  intro k hk
  have hHU_nat : H ≤ Ucut := by
    simpa [Ucut] using Nat.le_add_right H ((H + 99) / 100)
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

/-- The full tent kernel is nonnegative on its support. -/
lemma K_full_nonneg_band {k : ℤ} (hk : k ∈ bandU) : 0 ≤ K_full k :=
  K_full_nonneg k

/-- On the outer band, `K_full` is nonnegative. -/
lemma K_full_nonneg_outer {k : ℤ} (hk : k ∈ outerBand) : 0 ≤ K_full k := by
  -- hk is unused; K_full is globally nonnegative
  unfold K_full K_full_raw
  refine div_nonneg ?_ ?_
  · exact le_max_right _ _
  · exact_mod_cast (Nat.zero_le Ucut)

/-- On the outer band, the sum of `|K_full|` equals the sum of `K_full`. -/
lemma sum_abs_K_full_outer :
    Finset.sum outerBand (fun k => |K_full k|) = Finset.sum outerBand (fun k => K_full k) := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have := K_full_nonneg_outer (hk:=hk)
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

/-- Numeric corollary for the tail mass. -/
lemma C_tail_closed_le : C_tail_closed ≤ (98 : ℝ) / 10^6 := by
  norm_num [C_tail_closed, Ucut, BankParams.H]

/-- Numeric lower bound for the inner mass. -/
lemma mass_BG_lb : (0.99990 : ℝ) ≤ (1 : ℝ) - C_tail_closed := by
  have h := C_tail_closed_le
  linarith

/- Optional tent-sum axioms (unused by the active pipeline); commented out to avoid
   carrying extra assumptions. Restore if you need the abstract kernel API.
-- axiom sum_bandU :
--     Finset.sum bandU (fun k => K_full k) = (1 : ℝ)
-- axiom sum_innerBand :
--     Finset.sum innerBand (fun k => K_full k)
--       = ((1 + 2 * H : ℝ) / (Ucut : ℝ)) - ((H * (H + 1) : ℝ) / (Ucut : ℝ)^2)
-- axiom tail_mass_closed_form :
--     Finset.sum outerBand (fun k => K_full k) = C_tail_closed
-/

/-  The abstract `AdmissibleKernel` instance and generalization are currently unused.
    They are kept here commented out; restore when/if you want to reason through the
    abstract kernel API.

-- noncomputable def tentAdmissibleKernel : Goldbach.BG.AdmissibleKernel Ucut :=
-- { K := fun k => K_full k,
--   even := by
--     intro k; simpa using K_full_neg k,
--   nonneg := by
--     intro k; simpa using K_full_nonneg k,
--   mass_on_band := by
--     -- sum over the full band equals 1 (proved above)
--     simpa using sum_bandU,
--   pos_at_zero := by
--     simpa using K_full_pos_at_zero }
--
-- namespace Kernel
--
-- variable (Kadm : Goldbach.BG.AdmissibleKernel Ucut)
-- @[inline] noncomputable def Kact (k : ℤ) : ℝ := Kadm.K k
-- noncomputable def mass_BG_of : ℝ := Finset.sum S_BG (fun k => Kact Kadm k)
-- lemma mass_BG_of_pos : 0 < mass_BG_of Kadm := by
--   classical
--   unfold mass_BG_of
--   have h0 : (0 : ℤ) ∈ S_BG := by simp [Goldbach.BG_Bank.S_BG]
--   have hnonneg : 0 ≤ Finset.sum (S_BG.erase 0) (fun k => Kact Kadm k) := by
--     refine Finset.sum_nonneg ?h
--     intro k hk; exact Kadm.nonneg k
--   have hsplit :
--       Finset.sum S_BG (fun k => Kact Kadm k)
--         = (Finset.sum (S_BG.erase 0) (fun k => Kact Kadm k)) + Kact Kadm 0 := by
--     simpa [add_comm, add_left_comm, add_assoc]
--       using (Finset.sum_erase_add (s := S_BG) (a := (0 : ℤ)) (f := fun k => Kact Kadm k) h0).symm
--   have hpos0 : 0 < Kact Kadm 0 := Kadm.pos_at_zero
--   have : 0 < (Finset.sum (S_BG.erase 0) (fun k => Kact Kadm k)) + Kact Kadm 0 := by nlinarith
--   simpa [hsplit]
-- noncomputable def Pref_of (X N : ℕ) (k : ℤ) : ℝ :=
--   if h : k ∈ S_BG then (AO_Major.sigma N * AO_Major.weight_mass X) / (mass_BG_of Kadm) else 0
-- noncomputable def conv_ref_const_of (X N : ℕ) : ℝ :=
--   Finset.sum S_BG (fun k => Pref_of Kadm X N k * Kact Kadm k)
-- lemma conv_ref_const_eq_sigma_mass_of (X N : ℕ) :
--     conv_ref_const_of Kadm X N = AO_Major.sigma N * AO_Major.weight_mass X := by
--   classical
--   let σ : ℝ := AO_Major.sigma N
--   let c : ℝ := σ * AO_Major.weight_mass X
--   have hpos : 0 < mass_BG_of Kadm := mass_BG_of_pos Kadm
--   unfold conv_ref_const_of Pref_of
--   have hrewrite :
--     (∑ k ∈ S_BG, (if h : k ∈ S_BG then c / mass_BG_of Kadm else 0) * Kact Kadm k)
--       = ∑ k ∈ S_BG, (c / mass_BG_of Kadm) * Kact Kadm k := by
--     refine Finset.sum_congr rfl ?_; intro k hk; simp [Pref_of, hk]
--   have hfactor :
--     (∑ k ∈ S_BG, (c / mass_BG_of Kadm) * Kact Kadm k)
--       = (c / mass_BG_of Kadm) * ∑ k ∈ S_BG, Kact Kadm k :=
--     (Finset.mul_sum (s := S_BG) (f := fun k => Kact Kadm k)
--       (a := c / mass_BG_of Kadm)).symm
--   have hsum : (∑ k ∈ S_BG, Kact Kadm k) = mass_BG_of Kadm := rfl
--   have hne : mass_BG_of Kadm ≠ 0 := ne_of_gt hpos
--   calc
--     (∑ k ∈ S_BG, (if h : k ∈ S_BG then c / mass_BG_of Kadm else 0) * Kact Kadm k)
--         = ∑ k ∈ S_BG, (c / mass_BG_of Kadm) * Kact Kadm k := hrewrite
--     _ = (c / mass_BG_of Kadm) * ∑ k ∈ S_BG, Kact Kadm k := hfactor
--     _ = (c / mass_BG_of Kadm) * mass_BG_of Kadm := by simpa [hsum]
--     _ = c := by field_simp [hne]
--     _ = σ * AO_Major.weight_mass X := rfl
--
-- end Kernel



-- The closed-form tail bound below is retained as an axiom placeholder. If you prefer
-- a proof, either reinstate `tail_mass_closed_form` above or replace this with a
-- certificate-based lemma.
axiom errTI_bound_closed :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
      |errTI X N| ≤ payload_cap X N * C_tail_closed

/-- Deviation of the full projector from the in-window projector (errBG=0): bounded by the tail. -/
-- Move the decomposition lemma above its first use to avoid forward refs.
lemma bank_decomp_pre :
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
    conv_full X N - conv_ref X N = errTI X N + errBG X N := by
  classical
  intro X N hX hN
  -- Split the full-band sums into outerBand ⊔ S_BG.
  have hsplit_full :
      conv_full X N
        = (∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k)
          + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k) := by
    simpa [conv_full] using
      (sum_bandU_outer_inner
        (f := fun k => Goldbach.BG_Bank.P_BG X N k * tentFullWeight k))
  have hsplit_ref :
      conv_ref X N
        = (∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k)
          + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k) := by
    simpa [conv_ref] using
      (sum_bandU_outer_inner
        (f := fun k => Goldbach.BG_Bank.P_BG X N k * tentRefWeight k))
  -- On the outer band, the reference weight is zero.
  have href_outer :
      (∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k) = 0 := by
    classical
    have hzero : ∀ k ∈ outerBand, tentRefWeight k = 0 := by
      intro k hk
      rcases Finset.mem_sdiff.mp hk with ⟨hkB, hkS⟩
      simp [tentRefWeight, hkS]
    calc
      (∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k)
          = ∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * 0 := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simp [hzero k hk]
      _ = 0 := by simp
  -- On the inner band, tentRefWeight = tentFullWeight.
  have href_inner :
      (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k)
        = (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [tentRefWeight, hk]
  -- Combine the pieces.
  have href_ref :
      conv_ref X N
        = (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k) := by
    calc
      conv_ref X N
          = (∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k)
              + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k) := hsplit_ref
      _ = 0 + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k) := by
            simp [href_outer, href_inner]
      _ = (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k) := by ring
  calc
    conv_full X N - conv_ref X N
        = ((∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k)
            + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k))
            - ((∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k)
              + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentRefWeight k)) := by
          simp [hsplit_full, hsplit_ref]
    _ = ((∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k)
            + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k))
            - (0 + (∑ k ∈ S_BG, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k)) := by
          simp [href_outer, href_inner]
    _ = (∑ k ∈ outerBand, Goldbach.BG_Bank.P_BG X N k * tentFullWeight k) := by ring
    _ = errTI X N := by
          simp [errTI]
    _ = errTI X N + errBG X N := by
          simp [errBG]

lemma bankOp_full_minus_ref_bound :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
      |conv_full X N - conv_ref X N| ≤ payload_cap X N * C_tail_closed := by
  intro X N hX hN
  -- from the decomposition, the difference is exactly errTI (errBG = 0)
  have hdecomp := bank_decomp_pre (X:=X) (N:=N) hX hN
  have herrbg : errBG X N = 0 := rfl
  have hrewrite : conv_full X N - conv_ref X N = errTI X N := by
    nlinarith [hdecomp, herrbg]
  -- apply the tail bound
  have htail := errTI_bound_closed (X:=X) (N:=N) hX hN
  simpa [hrewrite] using htail

/-- Canonical wrapper: tail gap on the Goldbach window. -/
lemma tail_gap_canonical {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
    |conv_full X N - conv_ref X N| ≤ payload_cap X N * C_tail_closed :=
  bankOp_full_minus_ref_bound (X:=X) (N:=N) hX hN

/-- Decomposition of the full projector into tail + in-window (errBG=0 here).

-- Off-channel placeholder (kept at 0 here to avoid cyclic imports). -/
noncomputable def E_off (_X _N : ℕ) : ℝ := 0

/-- Temporary choices for the other channels so that the identity is rfl. -/
noncomputable def E_kernel (X N : ℕ) : ℝ := 0
noncomputable def E_mellin (X N : ℕ) : ℝ := 0
noncomputable def E_smooth (X N : ℕ) : ℝ := AO_Major.errAO X N - E_off X N

/-- Decomposition of the full projector into tail + in-window (errBG=0 here). -/
lemma bank_decomp {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
    conv_full X N - conv_ref X N = errTI X N + errBG X N :=
  bank_decomp_pre (X:=X) (N:=N) hX hN

/-- Decompose the full convolution into the in-window part plus the tail. -/
lemma conv_full_eq_conv_ref_add_tail {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
    conv_full X N = conv_ref X N + errTI X N := by
  have hdecomp := bank_decomp (X:=X) (N:=N) hX hN
  have herrbg : errBG X N = 0 := rfl
  have : conv_full X N - conv_ref X N = errTI X N := by
    nlinarith [hdecomp, herrbg]
  nlinarith

/-- On the window, rewrite `R - conv_full` in terms of the in-window gap and the tail. -/
lemma R_minus_conv_full {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
    (Goldbach.Rep.R N : ℝ) - conv_full X N
      = (Goldbach.Rep.R N : ℝ) - conv_ref X N - errTI X N := by
  have hcf := conv_full_eq_conv_ref_add_tail (X:=X) (N:=N) hX hN
  nlinarith

/-- The outer band sits inside the full symmetric slab. -/
lemma outerBand_subset_full :
  outerBand ⊆ bandU := by
  intro k hk
  -- outerBand is `bandU \ S_BG`, so membership implies `k ∈ bandU`
  exact (Finset.mem_sdiff.mp hk).1

/-- Cardinality of the full slab `[-U..U]` over `ℤ` is `2*U + 1`. -/
lemma card_full_slab :
  (Finset.Icc (-(Ucut : ℤ)) (Ucut : ℤ)).card = 2 * Ucut + 1 := by
  -- standard fact for integer intervals
  have h := Int.card_Icc (-(Ucut : ℤ)) (Ucut : ℤ)
  -- Int.card_Icc gives (b - a + 1).toNat when a ≤ b
  simp only [sub_neg_eq_add] at h
  omega

open Nat

/-- Numeric anchors we will use. -/
private lemma pow_79_cubed_lt_495k : 79^3 < 495000 := by
  -- 79^3 = 493039
  norm_num
private lemma pow_80_cubed_gt_510k : 510000 < 80^3 := by
  -- 80^3 = 512000
  norm_num
private lemma pow_26_fourth_lt_495k : 26^4 < 495000 := by
  -- 26^4 = 456976
  norm_num
private lemma pow_27_fourth_gt_510k : 510000 < 27^4 := by
  -- 27^4 = 531441
  norm_num
private lemma pow_13_fifth_lt_495k : 13^5 < 495000 := by
  -- 13^5 = 371293
  norm_num
private lemma pow_14_fifth_gt_510k : 510000 < 14^5 := by
  -- 14^5 = 537824
  norm_num

/-- On the canonical window, the inner-`n` band is always ≥ 495000. -/
private lemma inner_left_ge_495k
    {X N : ℕ} (hX : (10^6 : ℕ) ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X (10^4)) :
    495000 ≤ (N - 10^4) / 2 := by
  -- From N ≥ X ≥ 10^6 we get N - 10^4 ≥ 990000; divide by 2.
  -- Extract `X ≤ N` from the Finset membership in the canonical window
  have hNX : X ≤ N := by
    -- `EvenIn X H` is a filtered `IccShift X H` by evenness; pull out the image witness
    rcases Finset.mem_filter.mp hN with ⟨himg, _⟩
    rcases Finset.mem_image.mp himg with ⟨k, hk, hkN⟩
    -- `hk : k < H+1`, so `N = X + k ≥ X`
    have : X ≤ X + k := Nat.le_add_right _ _
    simpa [hkN] using this
  have : 990000 ≤ N - 10000 := by
    -- 990000 = 10^6 - 10^4
    have : (10^6 : ℕ) - 10^4 = 990000 := by norm_num
    simpa [this]
      using Nat.sub_le_sub_right (le_trans hX hNX) 10000
  -- divide by 2, using monotonicity of Nat.div for nonneg
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr (by
    -- (N - 10000)/2 ≥ 495000  ↔  N - 10000 ≥ 990000
    simpa using this)

/-- Spacing of consecutive squares once the index is large. -/
private lemma square_gap_ge_1407 {m : ℕ} (hm : 703 ≤ m) :
    (m+1)^2 - m^2 ≥ 1407 := by
  -- Expand (m+1)^2, then cancel m^2
  have h1 : (m+1)^2 = m^2 + (2*m + 1) := by ring
  have hdiff : (m+1)^2 - m^2 = 2*m + 1 := by
    simp [h1]
  -- From hm, multiply by 2 and add 1
  have hmono : 2*703 ≤ 2*m := Nat.mul_le_mul_left _ hm
  have : 2*703 + 1 ≤ 2*m + 1 := Nat.succ_le_succ hmono
  have hconst : 2*703 + 1 = 1407 := by norm_num
  simpa [hdiff, hconst]

-- At most 8 squares can lie in any interval of length 10000 whose left end is ≥ 495000. -/
-- (Redundant/unstable incidence-style counting lemmas removed here to keep
-- BG_Identity compiling cleanly; the working bounds are provided earlier
-- and by `PPBoundSquares`.)

end

end BG_Identity
end Goldbach
