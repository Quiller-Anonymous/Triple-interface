import Mathlib
import Mathlib.Data.Finset.Interval
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.Rep

namespace Goldbach.BG_Bank

open Real
open scoped BigOperators

-- If these are not already present in this file, keep them here.
noncomputable def Λ (n : ℕ) : ℝ := if Nat.Prime n then Real.log n else 0

-- Canonical window params (shared with the rest of the pipeline).
abbrev X0 : ℕ := Goldbach.BankParams.X0
abbrev H  : ℕ := Goldbach.BankParams.H

/--
Smoothed weight `wX(X,n)` for the bank payload.

This repo’s major-arc / TT* certificate work requires that the underlying von Mangoldt weights
are `X`-local so that the relevant `ℓ²` coefficient masses do not grow like `Θ(X)`.

Implementation choice (deterministic and easy to audit):
- `wX(X,n) = 1` if `n` lies in a fixed-width window around `X/2`,
- and `0` otherwise.

In particular, `|wX| ≤ 1` and `wX ≥ 0` everywhere.
-/
noncomputable def wScale (X : ℕ) : ℝ :=
  (1 : ℝ) / (Real.log (X : ℝ) * (2 * (H : ℝ) + 1))

noncomputable def wX (X n : ℕ) : ℝ :=
  if n ∈ Finset.Icc (X / 2 - H) (X / 2 + H) then wScale X else 0

lemma wScale_nonneg (X : ℕ) : 0 ≤ wScale X := by
  by_cases hX0 : X = 0
  · simp [wScale, hX0]
  have hXpos : 1 ≤ X := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hX0)
  have hlog : 0 ≤ Real.log (X : ℝ) := by
    have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
    exact Real.log_nonneg this
  have hH : 0 ≤ (2 * (H : ℝ) + 1) := by positivity
  have hden : 0 ≤ Real.log (X : ℝ) * (2 * (H : ℝ) + 1) := mul_nonneg hlog hH
  simpa [wScale] using (one_div_nonneg.mpr hden)

lemma wScale_le_one (X : ℕ) : wScale X ≤ 1 := by
  -- If `X ≤ 1` then `log X = 0` and `wScale X = 0`.
  by_cases hX : X ≤ 1
  · have : X = 0 ∨ X = 1 := by
      exact (Nat.le_one_iff_eq_zero_or_eq_one.mp hX)
    rcases this with rfl | rfl <;> simp [wScale]
  -- Otherwise `2 ≤ X`, hence the denominator is > 1, so `1/den ≤ 1`.
  have h2X : 2 ≤ X := Nat.succ_le_iff.mp (lt_of_not_ge hX)
  have hx : (1 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
  have hlogXpos : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hHpos : 0 < (2 * (H : ℝ) + 1) := by positivity
  have hden_pos : 0 < Real.log (X : ℝ) * (2 * (H : ℝ) + 1) := mul_pos hlogXpos hHpos
  have hlog2_le : Real.log (2 : ℝ) ≤ Real.log (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h2X
    exact Real.log_le_log (by norm_num : (0 : ℝ) < (2 : ℝ)) this
  have hlog_lower : (0.6931471803 : ℝ) < Real.log (X : ℝ) :=
    lt_of_lt_of_le Real.log_two_gt_d9 hlog2_le
  have hden_gt_one : (1 : ℝ) < Real.log (X : ℝ) * (2 * (H : ℝ) + 1) := by
    have hH1 : (1 : ℝ) < (0.6931471803 : ℝ) * (2 * (H : ℝ) + 1) := by
      norm_num [H, Goldbach.BankParams.H]
    have hmul :
        (0.6931471803 : ℝ) * (2 * (H : ℝ) + 1) < Real.log (X : ℝ) * (2 * (H : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hlog_lower (by positivity : 0 < (2 * (H : ℝ) + 1))
    exact lt_trans hH1 hmul
  have hden_ge_one : (1 : ℝ) ≤ Real.log (X : ℝ) * (2 * (H : ℝ) + 1) := le_of_lt hden_gt_one
  have : (1 : ℝ) / (Real.log (X : ℝ) * (2 * (H : ℝ) + 1)) ≤ 1 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden_ge_one
    simpa using this
  simpa [wScale] using this

lemma wX_nonneg (X n : ℕ) : 0 ≤ wX X n := by
  by_cases hn : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
  · simp [wX, hn, wScale_nonneg]
  · simp [wX, hn]

lemma wX_le_one (X n : ℕ) : wX X n ≤ 1 := by
  by_cases hn : n ∈ Finset.Icc (X / 2 - H) (X / 2 + H)
  · simp [wX, hn, wScale_le_one]
  · simp [wX, hn]

lemma abs_wX_le_one (X n : ℕ) : |wX X n| ≤ 1 := by
  have h0 : 0 ≤ wX X n := wX_nonneg X n
  have h1 : wX X n ≤ 1 := wX_le_one X n
  simpa [abs_of_nonneg h0] using h1

/-- Working-band offsets S_BG = { k ∈ ℤ | |k| ≤ H }. -/
def S_BG : Finset ℤ := (Finset.Icc (-(H:ℤ)) (H:ℤ))

/-- Full (log-normalized) payload. -/
noncomputable def P_BG (X N : ℕ) (k : ℤ) : ℝ :=
  ((1 / 800 : ℝ) * (1 / (Real.log (N:ℝ))^2)) *
    ∑ n ∈ Finset.Icc 2 (N - 2),
      (if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
       then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
       else 0)

/-- Cap we want to prove: scaled `(log (N+1) / log N)^2`. -/
noncomputable def payload_cap (_X N : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (Real.log ((N:ℝ) + 1) / Real.log (N:ℝ))^2

lemma payload_nonneg (X N : ℕ) : 0 ≤ payload_cap X N := by
  have hsq : 0 ≤ (Real.log ((N:ℝ) + 1) / Real.log (N:ℝ))^2 := sq_nonneg _
  have hconst : 0 ≤ (1 / 800 : ℝ) := by norm_num
  unfold payload_cap
  exact mul_nonneg hconst hsq

lemma inv_le_inv_of_le_real {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'

  have hpos : 0 ≤ a⁻¹ * b⁻¹ := by
    exact mul_nonneg (le_of_lt (inv_pos.2 ha)) (le_of_lt (inv_pos.2 hb))

  have hmul : a * (a⁻¹ * b⁻¹) ≤ b * (a⁻¹ * b⁻¹) :=
    mul_le_mul_of_nonneg_right hab hpos

  -- Now simplify each side *separately* (no fragile global simp)
  have hL : a * (a⁻¹ * b⁻¹) = b⁻¹ := by
    -- a*(a⁻¹*b⁻¹) = (a*a⁻¹)*b⁻¹ = b⁻¹
    calc
      a * (a⁻¹ * b⁻¹) = (a * a⁻¹) * b⁻¹ := by
        ring_nf
      _ = 1 * b⁻¹ := by simp [ha0]
      _ = b⁻¹ := by simp

  have hR : b * (a⁻¹ * b⁻¹) = a⁻¹ := by
    -- b*(a⁻¹*b⁻¹) = a⁻¹*(b*b⁻¹) = a⁻¹
    calc
      b * (a⁻¹ * b⁻¹) = a⁻¹ * (b * b⁻¹) := by
        ring_nf
      _ = a⁻¹ * 1 := by simp [hb0]
      _ = a⁻¹ := by simp

  -- finish
  simpa [hL, hR] using hmul

/-- On the canonical range X ≥ X0 we have log X > 0. -/
private lemma log_pos_of_large {X : ℕ} (hX : X0 ≤ X) : 0 < Real.log (X:ℝ) := by
  have h2X0 : (2:ℕ) ≤ X0 := by
    -- X0 = 10^6
    simpa [X0, Goldbach.BankParams.X0] using (by decide : (2:ℕ) ≤ 10^6)
  have h2X : (2:ℕ) ≤ X := le_trans h2X0 hX
  have hx : (1:ℝ) < (X:ℝ) := by
    have : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast h2X
    exact lt_of_lt_of_le (by norm_num : (1:ℝ) < (2:ℝ)) this
  exact Real.log_pos hx

/-- For n ∈ [2, N-2], we have `|Λ n| ≤ log (N+1)`. -/
private lemma abs_Lambda_le_logNs (N n : ℕ)
    (hn_min : 2 ≤ n) (hn_max : n ≤ N - 2) :
    |Λ n| ≤ Real.log ((N:ℝ) + 1) := by
  unfold Λ
  by_cases hp : Nat.Prime n
  · -- log monotone on (0,∞), and n ≤ N < N+1
    have hn_pos : 0 < (n:ℝ) := by
      have : 0 < n := Nat.zero_lt_of_lt (Nat.lt_of_succ_le (Nat.succ_le_of_lt (Nat.lt_of_succ_le hn_min)))
      exact Nat.cast_pos.mpr this
    have hn_le : (n:ℝ) ≤ (N.succ : ℝ) := by
      have : n ≤ N := le_trans hn_max (by exact Nat.sub_le _ _)
      exact_mod_cast Nat.le_succ_of_le this
    -- simpler: use `Real.log_le_iff_le_exp` also works; but we can just bound by `log (N+1)`
    have : Real.log (n:ℝ) ≤ Real.log (N.succ : ℝ) := by
      exact Real.log_le_log hn_pos hn_le
    have hn_ge_one : 1 ≤ (n:ℝ) := by
      have : 1 ≤ n := Nat.one_le_of_lt (Nat.lt_of_succ_le hn_min)
      exact_mod_cast this
    have hlog_nn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn_ge_one
    simpa [hp, abs_of_nonneg hlog_nn] using this
  · have hlog_nn : 0 ≤ Real.log ((N:ℝ)+1) := by
      have : 1 ≤ (N:ℝ) + 1 := by
        have : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        linarith
      exact Real.log_nonneg this
    simpa [hp, abs_of_nonneg hlog_nn]
      -- since Λ n = 0 when n not prime

/-- At most one `n` solves `↑n - (↑N - ↑n) = k`. Hence the filtered set has card ≤ 1. -/
private lemma card_filter_offset_le_one (N : ℕ) (k : ℤ) :
    (Finset.filter (fun n : ℕ => ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k ))
      (Finset.Icc 2 (N - 2))).card ≤ 1 := by
  classical
  refine Finset.card_le_one_iff.mpr ?_
  intro a b ha_mem hb_mem
  -- unwrap membership in the filter to get the equalities
  rcases Finset.mem_filter.mp ha_mem with ⟨haI, haEq⟩
  rcases Finset.mem_filter.mp hb_mem with ⟨hbI, hbEq⟩
  -- Turn both into `2 * a = k + N` and `2 * b = k + N` over ℤ
  have h2a : (2:ℤ) * (a:ℤ) = k + (N:ℤ) := by
    have := congrArg (fun z => z + (N:ℤ)) haEq
    -- (a - (N - a)) + N = 2a
    simp only [sub_eq_add_neg, two_mul] at this ⊢
    ring_nf at this ⊢
    exact this
  have h2b : (2:ℤ) * (b:ℤ) = k + (N:ℤ) := by
    have := congrArg (fun z => z + (N:ℤ)) hbEq
    simp only [sub_eq_add_neg, two_mul] at this ⊢
    ring_nf at this ⊢
    exact this
  -- cancel the `2` on the left, coe ℕ injective
  have : (a:ℤ) = (b:ℤ) := by
    have h2ne : (2:ℤ) ≠ 0 := by decide
    have : (2:ℤ) * (a:ℤ) = (2:ℤ) * (b:ℤ) := by simpa [h2b] using h2a
    exact mul_left_cancel₀ h2ne this
  exact Int.ofNat.inj this

/-- Uniform payload bound on the window: for `X ≥ X0`, `N ∈ EvenIn X H`, and `k ∈ S_BG`. -/
lemma payload_bound_window
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) {k : ℤ} :
  |P_BG X N k| ≤ payload_cap X N := by
  have hXN : X ≤ N := by
    have hI : N ∈ Goldbach.Windows.IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : X0 ≤ N := le_trans hX hXN
  have hlogNpos  : 0 < Real.log (N:ℝ) := log_pos_of_large (X := N) hN_ge_X0
  have hlogNsqNN : 0 ≤ (Real.log (N:ℝ))^2 := by exact sq_nonneg _
  have hlogNN   : 0 ≤ 1 / (Real.log (N:ℝ))^2 := one_div_nonneg.mpr hlogNsqNN
  have hlogNabs  : |1 / (Real.log (N:ℝ))^2| = 1 / (Real.log (N:ℝ))^2 :=
    abs_of_nonneg hlogNN

  -- bound the inner sum by at most one term of size (log (N+1))^2
  have hterm :
    ∀ n ∈ Finset.Icc 2 (N - 2),
      |if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
        then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
        else 0|
      ≤ (Real.log ((N:ℝ) + 1))^2 := by
        intro n hn
        -- Either the indicator is false (trivial), or true and we bound the product
        by_cases hcond : ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
        · -- bound product by (log(N+1))^2 (and |wX| ≤ 1)
          have hn_min : 2 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn_max : n ≤ N - 2 := (Finset.mem_Icc.mp hn).2
          have hΛn  : |Λ n| ≤ Real.log ((N:ℝ) + 1)     := abs_Lambda_le_logNs N n hn_min hn_max
          have hm_min : 2 ≤ N - n := by
            -- from n ≤ N-2 ⇒ n+2 ≤ N ⇒ 2 ≤ N - n
            omega
          have hm_max : N - n ≤ N := Nat.sub_le _ _
          have hΛm : |Λ (N - n)| ≤ Real.log ((N:ℝ) + 1) := by
            -- `N - n ∈ [2, N]`, so same bound applies.
            -- A tiny duplication to reuse the same helper; or inline log monotonicity again.
            -- We inline a short bound:
            unfold Λ
            by_cases hp : Nat.Prime (N - n)
            · have hNm_pos : 0 < (N - n : ℝ) := by
                have : 0 < N - n := Nat.sub_pos_of_lt (by omega : n < N)
                have : n ≤ N := by omega
                rw [← Nat.cast_sub this]
                exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt (by omega : n < N))
              have hNm_ge_one : 1 ≤ (N - n : ℝ) := by
                have : 1 ≤ N - n := Nat.one_le_of_lt (Nat.lt_of_succ_le hm_min)
                have hn_le : n ≤ N := by omega
                have : (1 : ℝ) ≤ ↑(N - n) := Nat.one_le_cast.mpr this
                simp only [Nat.cast_sub hn_le] at this
                exact this
              have hlog_Nm_nn : 0 ≤ Real.log (N - n : ℝ) := Real.log_nonneg hNm_ge_one
              have : (N - n : ℝ) ≤ (N.succ : ℝ) := by
                have hn_le : n ≤ N := by omega
                simp only [Nat.cast_succ, Nat.cast_sub hn_le]
                have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
                linarith
              have hlog_ineq : Real.log (N - n : ℝ) ≤ Real.log (N.succ : ℝ) :=
                Real.log_le_log hNm_pos this
              rw [show (N.succ : ℝ) = (N : ℝ) + 1 by simp] at hlog_ineq
              simp [hp, abs_of_nonneg hlog_Nm_nn]
              have hn_le : n ≤ N := by omega
              rw [Nat.cast_sub hn_le, abs_of_nonneg hlog_Nm_nn]
              exact hlog_ineq
            · have hlog_Np1_nn : 0 ≤ Real.log ((N : ℝ) + 1) := by
                apply Real.log_nonneg
                have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
                linarith
              simp [hp, abs_of_nonneg hlog_Np1_nn]
              exact hlog_Np1_nn
          -- |wX| ≤ 1 (by construction, wX ∈ {0,1})
          have hw1 : |wX X n| ≤ 1 := abs_wX_le_one X n
          have hw2 : |wX X (N - n)| ≤ 1 := abs_wX_le_one X (N - n)
          have : |(wX X n * Λ n) * (wX X (N - n) * Λ (N - n))|
                  ≤ (Real.log ((N:ℝ) + 1))^2 := by
            -- |ab| ≤ |a||b|, then bound each factor by log(N+1)
            have hlogNp1_nn : 0 ≤ Real.log ((N:ℝ) + 1) := by
              apply Real.log_nonneg
              have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
              linarith
            have h_prod_nn : 0 ≤ |wX X n| * Real.log ((N:ℝ) + 1) :=
                mul_nonneg (abs_nonneg _) hlogNp1_nn
            calc |(wX X n * Λ n) * (wX X (N - n) * Λ (N - n))|
                  = |wX X n| * |Λ n| * (|wX X (N - n)| * |Λ (N - n)|) := by
                    simp [abs_mul, mul_assoc, mul_comm, mul_left_comm]
                _ ≤ 1 * |Λ n| * (1 * |Λ (N - n)|) := by
                    apply mul_le_mul (mul_le_mul hw1 le_rfl (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1))
                    · exact mul_le_mul hw2 le_rfl (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
                    · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
                    · exact mul_nonneg (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg _)
                _ = |Λ n| * |Λ (N - n)| := by simp
                _ ≤ Real.log ((N:ℝ) + 1) * Real.log ((N:ℝ) + 1) :=
                    mul_le_mul hΛn hΛm (abs_nonneg _) hlogNp1_nn
                _ = (Real.log ((N:ℝ) + 1))^2 := by ring
          simpa [hcond]
        · -- indicator false → zero
          have hlog_nn : 0 ≤ (Real.log ((N:ℝ) + 1))^2 := by exact sq_nonneg _
          simpa [hcond, abs_of_nonneg (by norm_num : (0:ℝ) ≥ 0)] using hlog_nn

  -- rewrite sum over Icc with a filter, then use card≤1
  have hsum :
    |Finset.sum (Finset.Icc 2 (N - 2))
       (fun n => if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
        then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
        else 0)|
  ≤ (Real.log ((N:ℝ) + 1))^2 := by
    let S := Finset.filter (fun n : ℕ => (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k) (Finset.Icc 2 (N - 2))
    have h_sum_S :
        Finset.sum (Finset.Icc 2 (N - 2))
          (fun n =>
            if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
            then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
            else 0)
        = Finset.sum S
            (fun n => (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))) := by
      classical
      -- `sum_filter` moves the indicator into a filtered domain.
      have := (Finset.sum_filter
        (s := Finset.Icc 2 (N - 2))
        (p := fun n : ℕ => (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k)
        (f := fun n => (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))))
      -- `sum_filter` is oriented the other way, so take its symmetry.
      simpa [S] using this.symm
    have :
      |Finset.sum S (fun n => (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)))|
        ≤ (Real.log ((N:ℝ) + 1))^2 := by
      classical
      calc
        |Finset.sum S (fun n => (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)))|
            ≤ Finset.sum S
                (fun n => |(wX X n * Λ n) * (wX X (N - n) * Λ (N - n))|) := by
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (s := S)
                  (f := fun n => (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))))
        _ ≤ Finset.sum S (fun _ => (Real.log ((N:ℝ) + 1))^2) := by
              apply Finset.sum_le_sum
              intro n hn
              have hn' : n ∈ Finset.Icc 2 (N - 2) := (Finset.mem_filter.mp hn).1
              have hcond : ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k ) := (Finset.mem_filter.mp hn).2
              have hterm' :
                  |(wX X n * Λ n) * (wX X (N - n) * Λ (N - n))|
                    ≤ (Real.log ((N:ℝ) + 1))^2 := by
                simpa [hcond] using (hterm n hn')
              simpa using hterm'
        _ ≤ S.card • (Real.log ((N:ℝ) + 1))^2 := by
              apply Finset.sum_le_card_nsmul
              intro n hn
              have hn' : n ∈ Finset.Icc 2 (N - 2) := (Finset.mem_filter.mp hn).1
              have hcond : ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k ) := (Finset.mem_filter.mp hn).2
              have hterm' :
                  |(wX X n * Λ n) * (wX X (N - n) * Λ (N - n))|
                    ≤ (Real.log ((N:ℝ) + 1))^2 := by
                simpa [hcond] using (hterm n hn')
              simpa using hterm'
        _ ≤ 1 • (Real.log ((N:ℝ) + 1))^2 := by
              have hcard_nat : S.card ≤ 1 := by
                simpa [S] using card_filter_offset_le_one N k
              have hcard : (S.card : ℝ) ≤ 1 := by exact_mod_cast hcard_nat
              have hlog : 0 ≤ (Real.log ((N:ℝ) + 1))^2 := sq_nonneg _
              -- use monotonicity of multiplication by a nonnegative constant
              have := mul_le_mul_of_nonneg_right hcard hlog
              simpa [nsmul_eq_mul, one_mul] using this
        _ = (Real.log ((N:ℝ) + 1))^2 := one_nsmul _
    -- replace original sum with the filtered version, then apply the bound above
    simpa [h_sum_S] using this

  -- Put everything together: factor (1/800)/(log N)^2 out of the absolute value
  unfold P_BG payload_cap
  calc
    |((1 / 800 : ℝ) * (1 / (Real.log (N:ℝ))^2)) *
      Finset.sum (Finset.Icc 2 (N - 2))
        (fun n =>
          if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
          then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
          else 0)|
        = (1 / 800 : ℝ) * |1 / (Real.log (N:ℝ))^2| *
          |Finset.sum (Finset.Icc 2 (N - 2))
             (fun n =>
               if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
               then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
               else 0)| := by
              have hconst : |(1 / 800 : ℝ)| = (1 / 800 : ℝ) := by norm_num
              rw [abs_mul, abs_mul, hconst, hlogNabs]

    _ = (1 / 800 : ℝ) * (1 / (Real.log (N:ℝ))^2) *
          |Finset.sum (Finset.Icc 2 (N - 2))
             (fun n =>
               if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
               then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
               else 0)| := by
              simp [hlogNabs, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ (1 / 800 : ℝ) * (1 / (Real.log (N:ℝ))^2) * (Real.log ((N:ℝ) + 1))^2 :=
          by
            have hpos : 0 ≤ (1 / 800 : ℝ) := by norm_num
            have := mul_le_mul_of_nonneg_left hsum hlogNN
            nlinarith [hpos]
    _ = (1 / 800 : ℝ) * (Real.log ((N:ℝ) + 1) / Real.log (N:ℝ))^2 := by
          field_simp [one_div, mul_comm, mul_left_comm, mul_assoc, pow_two]

/-- Uniform numeric cap on the canonical window. -/
lemma payload_cap_window
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
  payload_cap X N
    ≤ (1 / 800 : ℝ) * (1 + Real.log 2 / Real.log (X0 : ℝ))^2 := by
  have hXN : X ≤ N := by
    have hI : N ∈ Goldbach.Windows.IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : X0 ≤ N := le_trans hX hXN
  have hlogX0pos : 0 < Real.log (X0 : ℝ) := log_pos_of_large (X := X0) (le_rfl)
  have hlogNpos : 0 < Real.log (N : ℝ) := log_pos_of_large (X := N) hN_ge_X0
  have hlog2_nonneg : 0 ≤ Real.log 2 := by
    have : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    simpa using Real.log_nonneg this

  have hnum :
      Real.log ((N : ℝ) + 1) ≤ Real.log (2 * (N : ℝ)) := by
    have hpos : 0 < (N : ℝ) + 1 := by nlinarith
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < X0) hN_ge_X0)
    have hle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by
        have : (1 : ℕ) ≤ N := le_trans (by decide : (1 : ℕ) ≤ X0) hN_ge_X0
        exact_mod_cast this
      nlinarith
    exact Real.log_le_log hpos hle

  have hratio :
      Real.log ((N : ℝ) + 1) / Real.log (N : ℝ)
        ≤ 1 + Real.log 2 / Real.log (X0 : ℝ) := by
    have hratio1 :
        Real.log ((N : ℝ) + 1) / Real.log (N : ℝ)
          ≤ Real.log (2 * (N : ℝ)) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hlogNpos)
    have hlog_mul : Real.log (2 * (N : ℝ)) = Real.log (N : ℝ) + Real.log 2 := by
      have hNpos : 0 < (N : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < X0) hN_ge_X0)
      have hne_two : (2 : ℝ) ≠ 0 := by norm_num
      have hne_N : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have h' : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log (N : ℝ) := by
        simpa using Real.log_mul hne_two hne_N
      simpa [add_comm, add_left_comm, add_assoc] using h'
    have hlog_rewrite :
        Real.log (2 * (N : ℝ)) / Real.log (N : ℝ)
          = 1 + Real.log 2 / Real.log (N : ℝ) := by
      have hlogN_ne : (Real.log (N : ℝ)) ≠ 0 := ne_of_gt hlogNpos
      calc
        Real.log (2 * (N : ℝ)) / Real.log (N : ℝ)
            = (Real.log (N : ℝ) + Real.log 2) / Real.log (N : ℝ) := by simpa [hlog_mul]
        _ = Real.log (N : ℝ) / Real.log (N : ℝ) + Real.log 2 / Real.log (N : ℝ) := by
              simpa [add_div]
        _ = 1 + Real.log 2 / Real.log (N : ℝ) := by
              simp [div_self, hlogN_ne, add_comm, add_left_comm, add_assoc]
    have hden_le : Real.log (X0 : ℝ) ≤ Real.log (N : ℝ) := by
      have hx0pos : 0 < (X0 : ℝ) := by exact_mod_cast (by decide : (0:ℕ) < X0)
      have hle : (X0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge_X0
      exact Real.log_le_log hx0pos hle
    have hinv : (Real.log (N : ℝ))⁻¹ ≤ (Real.log (X0 : ℝ))⁻¹ :=
      inv_le_inv_of_le_real hlogX0pos hden_le
    have hmul :
        Real.log 2 * (Real.log (N : ℝ))⁻¹ ≤ Real.log 2 * (Real.log (X0 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hlog2_nonneg
    have hmono : Real.log 2 / Real.log (N : ℝ) ≤ Real.log 2 / Real.log (X0 : ℝ) := by
      simpa [div_eq_mul_inv] using hmul
    have h2 :
        Real.log (2 * (N : ℝ)) / Real.log (N : ℝ)
          ≤ 1 + Real.log 2 / Real.log (X0 : ℝ) := by
      have : 1 + Real.log 2 / Real.log (N : ℝ) ≤ 1 + Real.log 2 / Real.log (X0 : ℝ) :=
        add_le_add_left hmono 1
      simpa [hlog_rewrite] using this
    exact le_trans hratio1 (by simpa [hlog_rewrite] using h2)

  have hratio_nonneg : 0 ≤ Real.log ((N : ℝ) + 1) / Real.log (N : ℝ) := by
    have h1le : (1 : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
    have hnum_nonneg : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg h1le
    exact div_nonneg hnum_nonneg (le_of_lt hlogNpos)

  have hsq :
      (Real.log ((N : ℝ) + 1) / Real.log (N : ℝ))^2
        ≤ (1 + Real.log 2 / Real.log (X0 : ℝ))^2 :=
    pow_le_pow_left₀ hratio_nonneg hratio 2
  have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hsq hconst_nonneg
  simpa [payload_cap] using hmul

/-
/-- Crude window cap: replace `N` by the right end of the window. -/
lemma payload_cap_window_const
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
  payload_cap X N
    ≤ (1 / 800 : ℝ) *
        (Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ))^2 := by

  -- Extract k with N = X + k and k ≤ H from window membership
  have hIn := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hIn with ⟨k, hk, hkN⟩
  rcases Finset.mem_range.mp hk with hk_lt
  have hk_le : k ≤ H := Nat.le_of_lt_succ hk_lt

  have hN_le : N + 1 ≤ X + H + 1 := by
    -- N = X + k ≤ X + H
    have : X + k ≤ X + H := Nat.add_le_add_left hk_le X
    -- add 1 and rewrite
    have : X + k + 1 ≤ X + H + 1 := Nat.succ_le_succ this
    simpa [hkN] using this

  have hlog_num :
      Real.log ((N:ℝ) + 1) ≤ Real.log ((X + H + 1 : ℕ) : ℝ) := by
    have hpos : 0 < ((N:ℝ) + 1) := by nlinarith
    have hle : (N:ℝ) + 1 ≤ ((X + H + 1 : ℕ) : ℝ) := by exact_mod_cast hN_le
    exact Real.log_le_log hpos hle

  have hlogX_pos : 0 < Real.log (X:ℝ) := log_pos_of_large hX
  have hlogX0_pos : 0 < Real.log (X0:ℝ) := log_pos_of_large (X := X0) (le_rfl)

  have hlog_den : Real.log (X0 : ℝ) ≤ Real.log (X : ℝ) := by
    have hx0 : (0:ℝ) < (X0:ℝ) := by exact_mod_cast (by decide : (0:ℕ) < X0)
    have hle : (X0:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
    exact Real.log_le_log hx0 hle

  -- Define c = (X0+H+1)/X0
  set c : ℝ := ((X0 + H + 1 : ℕ) : ℝ) / (X0 : ℝ)

  have hX0_pos : 0 < (X0:ℝ) := by
    exact_mod_cast (by decide : (0:ℕ) < X0)
  have hX0_ne : (X0:ℝ) ≠ 0 := ne_of_gt hX0_pos

  have hc_pos : 0 < c := by
    have hnum_pos : 0 < ((X0 + H + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_pos _)
    simpa [c] using (div_pos hnum_pos hX0_pos)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos

  -- Key nat inequality: (X+H+1)*X0 ≤ X*(X0+H+1)
  have hmul_nat : (X + H + 1) * X0 ≤ X * (X0 + H + 1) := by
    have h1 : (H+1) * X0 ≤ (H+1) * X := Nat.mul_le_mul_left (H+1) hX
    have h2 : X * X0 + (H+1) * X0 ≤ X * X0 + (H+1) * X :=
      Nat.add_le_add_left h1 (X * X0)
    -- rewrite both sides
    simpa [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
           Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2

  have hmul_real :
      (((X + H + 1 : ℕ) : ℝ) * (X0:ℝ))
        ≤ ((X:ℝ) * ((X0 + H + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hmul_nat

  have hXH_le : ((X + H + 1 : ℕ) : ℝ) ≤ (X:ℝ) * c := by
    -- use le_div_iff with X0>0
    have : ((X + H + 1 : ℕ) : ℝ)
            ≤ ((X:ℝ) * ((X0 + H + 1 : ℕ) : ℝ)) / (X0:ℝ) := by
      exact (le_div_iff₀ hX0_pos).2 (by simpa [mul_assoc] using hmul_real)
    -- rewrite /X0 as *c
    simpa [c, div_eq_mul_inv, mul_assoc] using this

  -- log(X+H+1) ≤ log(X*c) = log X + log c
  have hlog_XH : Real.log ((X + H + 1 : ℕ) : ℝ) ≤ Real.log ((X:ℝ) * c) := by
    have hpos1 : 0 < ((X + H + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_pos _)
    exact Real.log_le_log hpos1 hXH_le

  have hratio_XH :
      Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X:ℝ)
        ≤ 1 + Real.log c / Real.log (X:ℝ) := by
    have hX_ne : (X:ℝ) ≠ 0 := (ne_of_gt (by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < X0) hX)))
    have hlogmul : Real.log ((X:ℝ) * c) = Real.log (X:ℝ) + Real.log c := by
      -- Real.log_mul gives log X + log c (possibly in swapped order)
      simpa [mul_comm, add_comm, add_left_comm, add_assoc] using Real.log_mul hX_ne hc_ne

    have hdiv :
        Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X:ℝ)
          ≤ Real.log ((X:ℝ) * c) / Real.log (X:ℝ) :=
      div_le_div_of_nonneg_right hlog_XH (le_of_lt hlogX_pos)

    have hlogX_ne : Real.log (X:ℝ) ≠ 0 := ne_of_gt hlogX_pos
    calc
      Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X:ℝ)
          ≤ Real.log ((X:ℝ) * c) / Real.log (X:ℝ) := hdiv
      _ = (Real.log (X:ℝ) + Real.log c) / Real.log (X:ℝ) := by simpa [hlogmul]
      _ = 1 + Real.log c / Real.log (X:ℝ) := by
            -- (a+b)/a = 1 + b/a
            simp [add_div, div_self, hlogX_ne, add_comm, add_left_comm, add_assoc]

  -- log c ≥ 0 since c = 1 + (H+1)/X0 ≥ 1
  have hlogc_nonneg : 0 ≤ Real.log c := by
    have hH1_nonneg : 0 ≤ ((H+1:ℕ):ℝ) / (X0:ℝ) :=
      div_nonneg (by exact_mod_cast (Nat.zero_le (H+1))) (le_of_lt hX0_pos)
    have hc1 : (1:ℝ) ≤ c := by
      have hc_eq : c = 1 + ((H+1:ℕ):ℝ) / (X0:ℝ) := by
        -- expand (X0+H+1)/X0
        simp [c, Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm,
              add_div, div_self hX0_ne]
      have : (1:ℝ) ≤ 1 + ((H+1:ℕ):ℝ) / (X0:ℝ) := by linarith
      simpa [hc_eq] using this
    exact Real.log_nonneg hc1

  -- monotonicity: log c / log X ≤ log c / log X0
  have hfrac_le :
      Real.log c / Real.log (X:ℝ) ≤ Real.log c / Real.log (X0:ℝ) := by
    have hinv : (Real.log (X:ℝ))⁻¹ ≤ (Real.log (X0:ℝ))⁻¹ :=
      inv_le_inv_of_le_real hlogX0_pos hlog_den
    have hmul :
        Real.log c * (Real.log (X:ℝ))⁻¹ ≤ Real.log c * (Real.log (X0:ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hlogc_nonneg
    simpa [div_eq_mul_inv] using hmul

  -- identify 1 + log c/log X0 with log(X0+H+1)/log X0
  have hRHS :
      (1 + Real.log c / Real.log (X0:ℝ))
        = Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0:ℝ) := by
    have hlogX0_ne : Real.log (X0:ℝ) ≠ 0 := ne_of_gt hlogX0_pos
    have hX0c : (X0:ℝ) * c = ((X0 + H + 1 : ℕ) : ℝ) := by
      simp only [c]
      field_simp
    have hlog_target : Real.log ((X0 + H + 1 : ℕ) : ℝ) = Real.log (X0:ℝ) + Real.log c := by
      have hlogmul : Real.log ((X0:ℝ) * c) = Real.log (X0:ℝ) + Real.log c := by
        simpa [mul_comm, add_comm, add_left_comm, add_assoc] using Real.log_mul hX0_ne hc_ne
      simpa [hX0c] using hlogmul
    calc
      (1 + Real.log c / Real.log (X0:ℝ))
          = (Real.log (X0:ℝ) / Real.log (X0:ℝ)) + Real.log c / Real.log (X0:ℝ) := by
              simp [div_self, hlogX0_ne]
      _ = (Real.log (X0:ℝ) + Real.log c) / Real.log (X0:ℝ) := by simp [add_div]
      _ = Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0:ℝ) := by
            simp only [Nat.cast_add, Nat.cast_one] at hlog_target ⊢
            rw [hlog_target]

  have hratio_end :
      Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X:ℝ)
        ≤ Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0:ℝ) := by
    have h1 :
        Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X:ℝ)
          ≤ 1 + Real.log c / Real.log (X0:ℝ) :=
      le_trans hratio_XH (add_le_add_left hfrac_le 1)
    simpa [hRHS] using h1

  have hratio_final :
      Real.log ((N:ℝ) + 1) / Real.log (X:ℝ)
        ≤ Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0:ℝ) := by
    have hdiv1 := div_le_div_of_nonneg_right hlog_num (le_of_lt hlogX_pos)
    exact le_trans hdiv1 hratio_end

  -- square and scale
  have hnonneg : 0 ≤ Real.log ((N:ℝ) + 1) / Real.log (X:ℝ) := by
    have h1le : (1:ℝ) ≤ (N:ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
    have hnum_nonneg : 0 ≤ Real.log ((N:ℝ) + 1) := Real.log_nonneg h1le
    exact div_nonneg hnum_nonneg (le_of_lt hlogX_pos)

  have hsq :
      (Real.log ((N:ℝ) + 1) / Real.log (X:ℝ))^2
        ≤ (Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0:ℝ))^2 :=
    pow_le_pow_left₀ hnonneg hratio_final 2

  have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hsq hconst_nonneg
  simpa [payload_cap] using hmul
-/

/-- Numeric log fact (proved from coarse analytic bounds). -/
lemma log_ratio_sq_le :
  (Real.log (1010001:ℝ) / Real.log (1000000:ℝ))^2 ≤ (62591 : ℝ) / 62500 := by
  have hlog2 : (69 : ℝ) / 100 < Real.log 2 := by
    have h₁ : (69 : ℝ) / 100 < (0.6931471803 : ℝ) := by norm_num
    exact lt_trans h₁ Real.log_two_gt_d9

  have hlog125 : (2 : ℝ) / 9 ≤ Real.log ((5 : ℝ) / 4) := by
    have h :=
      Real.le_log_one_add_of_nonneg (x := (4 : ℝ)⁻¹) (by positivity : (0 : ℝ) ≤ (4 : ℝ)⁻¹)
    have hL : (2 : ℝ) * (4 : ℝ)⁻¹ / ((4 : ℝ)⁻¹ + 2) = (2 : ℝ) / 9 := by norm_num
    have hR : (1 : ℝ) + (4 : ℝ)⁻¹ = (5 : ℝ) / 4 := by norm_num
    simpa [hL, hR] using h

  have hlogX0_lb : (2063 : ℝ) / 150 ≤ Real.log (1000000 : ℝ) := by
    have hX : (1000000 : ℝ) = (2 : ℝ) ^ 18 * ((5 : ℝ) / 4) ^ 6 := by norm_num
    have hlog :
        Real.log (1000000 : ℝ) =
          (18 : ℝ) * Real.log 2 + (6 : ℝ) * Real.log ((5 : ℝ) / 4) := by
      have hmul :
          Real.log ((2 : ℝ) ^ 18 * ((5 : ℝ) / 4) ^ 6) =
            Real.log ((2 : ℝ) ^ 18) + Real.log (((5 : ℝ) / 4) ^ 6) := by
        simpa using
          Real.log_mul (pow_ne_zero 18 (by norm_num : (2 : ℝ) ≠ 0))
            (pow_ne_zero 6 (by norm_num : ((5 : ℝ) / 4) ≠ 0))
      calc
        Real.log (1000000 : ℝ)
            = Real.log ((2 : ℝ) ^ 18 * ((5 : ℝ) / 4) ^ 6) := by simpa [hX]
        _ = Real.log ((2 : ℝ) ^ 18) + Real.log (((5 : ℝ) / 4) ^ 6) := hmul
        _ = (18 : ℝ) * Real.log 2 + (6 : ℝ) * Real.log ((5 : ℝ) / 4) := by
              simp [Real.log_pow, add_comm, add_left_comm, add_assoc]

    have hlog2' : (69 : ℝ) / 100 ≤ Real.log 2 := le_of_lt hlog2
    have h18 : 0 ≤ (18 : ℝ) := by norm_num
    have h6 : 0 ≤ (6 : ℝ) := by norm_num
    have hcomb :
        (18 : ℝ) * ((69 : ℝ) / 100) + (6 : ℝ) * ((2 : ℝ) / 9) ≤
          (18 : ℝ) * Real.log 2 + (6 : ℝ) * Real.log ((5 : ℝ) / 4) :=
      add_le_add (mul_le_mul_of_nonneg_left hlog2' h18) (mul_le_mul_of_nonneg_left hlog125 h6)
    have hleft :
        (2063 : ℝ) / 150 = (18 : ℝ) * ((69 : ℝ) / 100) + (6 : ℝ) * ((2 : ℝ) / 9) := by
      norm_num
    simpa [hleft, hlog] using hcomb

  have hlogX0_pos : 0 < Real.log (1000000 : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2063 : ℝ) / 150) hlogX0_lb
  have hlogX0_ne : Real.log (1000000 : ℝ) ≠ 0 := ne_of_gt hlogX0_pos

  let c : ℝ := (1010001 : ℝ) / (1000000 : ℝ)

  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos

  have hlogc_le : Real.log c ≤ (10001 : ℝ) / 1000000 := by
    have h := Real.log_le_sub_one_of_pos (x := c) hc_pos
    have : c - 1 = (10001 : ℝ) / 1000000 := by
      dsimp [c]
      norm_num
    simpa [this] using h

  have hlogc_nonneg : 0 ≤ Real.log c := by
    have : (1 : ℝ) ≤ c := by
      dsimp [c]
      norm_num
    exact Real.log_nonneg this

  have hratio_eq :
      Real.log (1010001 : ℝ) / Real.log (1000000 : ℝ) =
        1 + Real.log c / Real.log (1000000 : ℝ) := by
    have hm : (1000000 : ℝ) * c = (1010001 : ℝ) := by
      dsimp [c]
      field_simp
    have hlogmul : Real.log ((1000000 : ℝ) * c) = Real.log (1000000 : ℝ) + Real.log c := by
      simpa using Real.log_mul (by norm_num : (1000000 : ℝ) ≠ 0) hc_ne
    calc
      Real.log (1010001 : ℝ) / Real.log (1000000 : ℝ)
          = Real.log ((1000000 : ℝ) * c) / Real.log (1000000 : ℝ) := by simpa [hm]
      _ = (Real.log (1000000 : ℝ) + Real.log c) / Real.log (1000000 : ℝ) := by
            simp [hlogmul]
      _ = 1 + Real.log c / Real.log (1000000 : ℝ) := by
            simp [add_div, div_self, hlogX0_ne]

  have hratio_nonneg : 0 ≤ Real.log (1010001 : ℝ) / Real.log (1000000 : ℝ) := by
    have hnum_pos : 0 ≤ Real.log (1010001 : ℝ) := by
      have : (1 : ℝ) ≤ (1010001 : ℝ) := by norm_num
      exact Real.log_nonneg this
    exact div_nonneg hnum_pos (le_of_lt hlogX0_pos)

  have hfrac_le :
      Real.log c / Real.log (1000000 : ℝ) ≤
        ((10001 : ℝ) / 1000000) / ((2063 : ℝ) / 150) := by
    have hden_pos : 0 < (2063 : ℝ) / 150 := by norm_num
    have hinv :
        (1 / Real.log (1000000 : ℝ)) ≤ (1 / ((2063 : ℝ) / 150)) :=
      one_div_le_one_div_of_le hden_pos hlogX0_lb
    have hstep1 :
        Real.log c / Real.log (1000000 : ℝ) ≤ Real.log c / ((2063 : ℝ) / 150) := by
      have hmul := mul_le_mul_of_nonneg_left hinv hlogc_nonneg
      simpa [div_eq_mul_inv] using hmul
    have hstep2 :
        Real.log c / ((2063 : ℝ) / 150) ≤ ((10001 : ℝ) / 1000000) / ((2063 : ℝ) / 150) := by
      have hpos : 0 ≤ (1 / ((2063 : ℝ) / 150)) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hlogc_le hpos
      simpa [div_eq_mul_inv] using hmul
    exact le_trans hstep1 hstep2

  have hratio_le :
      Real.log (1010001 : ℝ) / Real.log (1000000 : ℝ) ≤
        1 + ((10001 : ℝ) / 1000000) / ((2063 : ℝ) / 150) := by
    have h := add_le_add_left hfrac_le 1
    simpa [hratio_eq] using h

  have hsq :
      (Real.log (1010001 : ℝ) / Real.log (1000000 : ℝ)) ^ 2 ≤
        (1 + ((10001 : ℝ) / 1000000) / ((2063 : ℝ) / 150)) ^ 2 :=
    pow_le_pow_left₀ hratio_nonneg hratio_le 2

  have hfinal :
      (1 + ((10001 : ℝ) / 1000000) / ((2063 : ℝ) / 150)) ^ 2 ≤ (62591 : ℝ) / 62500 := by
    norm_num

  exact le_trans hsq hfinal

/-- Numeric corollary on the canonical window. -/
lemma payload_cap_window_num
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
  payload_cap X N ≤ (1252 : ℝ) / 10^6 := by
  have hXN : X ≤ N := by
    have hI : N ∈ Goldbach.Windows.IccShift X H := (Finset.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hI with ⟨k, hk, rfl⟩
    exact Nat.le_add_right X k
  have hN_ge_X0 : X0 ≤ N := le_trans hX hXN
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < X0) hN_ge_X0)
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hlogNpos : 0 < Real.log (N : ℝ) := by
    have h1lt : (1 : ℝ) < (N : ℝ) := by
      have : (1 : ℕ) < N := lt_of_lt_of_le (by decide : (1:ℕ) < X0) hN_ge_X0
      exact_mod_cast this
    exact Real.log_pos h1lt

  -- `log (N+1) = log N + log(1+1/N)` and `log(1+1/N) ≤ 1/N`.
  have hlog_step :
      Real.log ((N : ℝ) + 1) ≤ Real.log (N : ℝ) + (N : ℝ)⁻¹ := by
    have hmul : (N : ℝ) * (1 + (N : ℝ)⁻¹) = (N : ℝ) + 1 := by
      calc
        (N : ℝ) * (1 + (N : ℝ)⁻¹) = (N : ℝ) + (N : ℝ) * (N : ℝ)⁻¹ := by ring
        _ = (N : ℝ) + 1 := by simp [hN0]
    have hx_pos : 0 < (1 + (N : ℝ)⁻¹) := by
      have : 0 < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
      linarith
    have hx_ne : (1 + (N : ℝ)⁻¹) ≠ 0 := ne_of_gt hx_pos
    have hlog_mul :
        Real.log ((N : ℝ) * (1 + (N : ℝ)⁻¹))
          = Real.log (N : ℝ) + Real.log (1 + (N : ℝ)⁻¹) := by
      simpa using Real.log_mul hN0 hx_ne
    have hlogx : Real.log (1 + (N : ℝ)⁻¹) ≤ (1 + (N : ℝ)⁻¹) - 1 :=
      Real.log_le_sub_one_of_pos hx_pos
    have hlogx' : Real.log (1 + (N : ℝ)⁻¹) ≤ (N : ℝ)⁻¹ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlogx
    calc
      Real.log ((N : ℝ) + 1)
          = Real.log ((N : ℝ) * (1 + (N : ℝ)⁻¹)) := by simpa [hmul]
      _ = Real.log (N : ℝ) + Real.log (1 + (N : ℝ)⁻¹) := hlog_mul
      _ ≤ Real.log (N : ℝ) + (N : ℝ)⁻¹ := by gcongr

  have hratio_le :
      Real.log ((N : ℝ) + 1) / Real.log (N : ℝ)
        ≤ 1 + (N : ℝ)⁻¹ / Real.log (N : ℝ) := by
    have hlogN_ne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogNpos
    have hdiv :
        Real.log ((N : ℝ) + 1) / Real.log (N : ℝ)
          ≤ (Real.log (N : ℝ) + (N : ℝ)⁻¹) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right hlog_step (le_of_lt hlogNpos)
    have hrepl :
        (Real.log (N : ℝ) + (N : ℝ)⁻¹) / Real.log (N : ℝ)
          = 1 + (N : ℝ)⁻¹ / Real.log (N : ℝ) := by
      simp [add_div, div_self, hlogN_ne, add_comm, add_left_comm, add_assoc]
    simpa [hrepl] using hdiv

  have hratio_nonneg : 0 ≤ Real.log ((N : ℝ) + 1) / Real.log (N : ℝ) := by
    have h1le : (1 : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
    have hnum_nonneg : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg h1le
    exact div_nonneg hnum_nonneg (le_of_lt hlogNpos)

  -- Bound `(1/N)/log N` by a purely rational constant (using `log 2 > 69/100`).
  have hlog2_lb : (69 : ℝ) / 100 < Real.log 2 := by
    have h₁ : (69 : ℝ) / 100 < (0.6931471803 : ℝ) := by norm_num
    exact lt_trans h₁ Real.log_two_gt_d9
  have hlog2_pos : 0 < Real.log 2 := lt_trans (by norm_num) hlog2_lb
  have hlog2_le_logN : Real.log 2 ≤ Real.log (N : ℝ) := by
    have h2pos : 0 < (2 : ℝ) := by norm_num
    have hle : (2 : ℝ) ≤ (N : ℝ) := by
      have : (2 : ℕ) ≤ N := le_trans (by decide : (2:ℕ) ≤ X0) hN_ge_X0
      exact_mod_cast this
    exact Real.log_le_log h2pos hle
  have hinv_logN_le : (Real.log (N : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ :=
    inv_le_inv_of_le_real hlog2_pos hlog2_le_logN
  have hlog2_lb' : (69 : ℝ) / 100 ≤ Real.log 2 := le_of_lt hlog2_lb
  have hinv_log2_le : (Real.log 2)⁻¹ ≤ ((69 : ℝ) / 100)⁻¹ :=
    inv_le_inv_of_le_real (by norm_num : (0 : ℝ) < (69 : ℝ) / 100) hlog2_lb'
  have hinv_log2_le_rat : (Real.log 2)⁻¹ ≤ (100 : ℝ) / 69 := by
    have : ((69 : ℝ) / 100)⁻¹ = (100 : ℝ) / 69 := by norm_num
    simpa [this] using hinv_log2_le
  have hinv_logN_le_rat : (Real.log (N : ℝ))⁻¹ ≤ (100 : ℝ) / 69 :=
    le_trans hinv_logN_le hinv_log2_le_rat

  have hNinv_le : (1 / (N : ℝ)) ≤ (1 / (1000000 : ℝ)) := by
    have hle : (1000000 : ℝ) ≤ (N : ℝ) := by
      have : (1000000 : ℕ) ≤ N := by simpa [X0, Goldbach.BankParams.X0] using hN_ge_X0
      exact_mod_cast this
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1000000 : ℝ)) hle

  have hfrac_le :
      (1 / (N : ℝ)) / Real.log (N : ℝ) ≤ (100 : ℝ) / (69 * 1000000) := by
    have hpos_invlog : 0 ≤ (Real.log (N : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hlogNpos)
    have hmul1 : (1 / (N : ℝ)) * (Real.log (N : ℝ))⁻¹
        ≤ (1 / (1000000 : ℝ)) * ((100 : ℝ) / 69) := by
      have := mul_le_mul hNinv_le hinv_logN_le_rat (by positivity) (by positivity : 0 ≤ (1 / (1000000 : ℝ)))
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    -- rewrite both sides into `a / b`
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul1

  have hbase :
      Real.log ((N : ℝ) + 1) / Real.log (N : ℝ)
        ≤ 1 + (100 : ℝ) / (69 * 1000000) := by
    have hfrac_le' : (N : ℝ)⁻¹ / Real.log (N : ℝ) ≤ (100 : ℝ) / (69 * 1000000) := by
      simpa [one_div] using hfrac_le
    have h' : 1 + (N : ℝ)⁻¹ / Real.log (N : ℝ) ≤ 1 + (100 : ℝ) / (69 * 1000000) :=
      add_le_add_left hfrac_le' 1
    exact le_trans hratio_le h'

  have hsq :
      (Real.log ((N : ℝ) + 1) / Real.log (N : ℝ)) ^ 2
        ≤ (1 + (100 : ℝ) / (69 * 1000000)) ^ 2 :=
    pow_le_pow_left₀ hratio_nonneg hbase 2

  have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hsq hconst_nonneg
  have hfinal : (1 / 800 : ℝ) * (1 + (100 : ℝ) / (69 * 1000000)) ^ 2 ≤ (1252 : ℝ) / 10^6 := by
    norm_num
  exact le_trans (by simpa [payload_cap] using hmul) hfinal
