import Mathlib
import Mathlib.Data.Finset.Interval
import Goldbach.Windows
import Goldbach.Rep

namespace Goldbach.BG_Bank

open Real
open scoped BigOperators

-- If these are not already present in this file, keep them here.
noncomputable def Λ (n : ℕ) : ℝ := if Nat.Prime n then Real.log n else 0
noncomputable def wX (_X n : ℕ) : ℝ := 1

-- Your canonical window params; adjust if you pull from BankParams instead.
def X0 : ℕ := 10^6
def H  : ℕ := 10^4

/-- Working-band offsets S_BG = { k ∈ ℤ | |k| ≤ H }. -/
def S_BG : Finset ℤ := (Finset.Icc (-(H:ℤ)) (H:ℤ))

/-- Full (log-normalized) payload; keep your existing definition if you already have one. -/
noncomputable def P_BG (X N : ℕ) (k : ℤ) : ℝ :=
  ((1 / 800 : ℝ) * (1 / (Real.log (X:ℝ))^2)) *
    ∑ n ∈ Finset.Icc 2 (N - 2),
      (if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
       then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
       else 0)

/-- Cap we want to prove: scaled `(log (N+1) / log X)^2`. -/
noncomputable def payload_cap (X N : ℕ) : ℝ :=
  (1 / 800 : ℝ) * (Real.log ((N:ℝ) + 1) / Real.log (X:ℝ))^2

/-- On the canonical range X ≥ X0 we have log X > 0. -/
private lemma log_pos_of_large {X : ℕ} (hX : X0 ≤ X) : 0 < Real.log (X:ℝ) := by
  -- 1 < X as real (since X ≥ 10^6 ≥ 3)
  have : (3 : ℕ) ≤ X := le_trans (by decide : (3:ℕ) ≤ 10^6) hX
  have hx : (1 : ℝ) < (X : ℝ) := by
    have h3le : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast this
    have h3ne : (3 : ℝ) ≠ (X : ℝ) := by
      intro heq
      have : (3 : ℕ) = X := Nat.cast_injective heq
      rw [show X0 = 10^6 from rfl] at hX
      omega
    exact lt_of_le_of_lt (show (1:ℝ) ≤ (3:ℝ) by norm_num) (lt_of_le_of_ne h3le h3ne)
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
  {X N : ℕ} (hX : X0 ≤ X) (_hN : N ∈ Goldbach.Windows.EvenIn X H) {k : ℤ} (_hk : k ∈ S_BG) :
  |P_BG X N k| ≤ payload_cap X N := by
  have hlogXpos  : 0 < Real.log (X:ℝ) := log_pos_of_large hX
  have hlogXsqNN : 0 ≤ (Real.log (X:ℝ))^2 := by exact sq_nonneg _
  have hlogXNN   : 0 ≤ 1 / (Real.log (X:ℝ))^2 := one_div_nonneg.mpr hlogXsqNN
  have hlogXabs  : |1 / (Real.log (X:ℝ))^2| = 1 / (Real.log (X:ℝ))^2 :=
    abs_of_nonneg hlogXNN

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
          -- |wX| ≤ 1 since wX ≡ 1 here
          have hw1 : |wX X n| ≤ 1 := by simp [wX]
          have hw2 : |wX X (N - n)| ≤ 1 := by simp [wX]
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
                _ = |Λ n| * |Λ (N - n)| := by ring
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

  -- Put everything together: factor (1/800)/(log X)^2 out of the absolute value
  unfold P_BG payload_cap
  calc
    |((1 / 800 : ℝ) * (1 / (Real.log (X:ℝ))^2)) *
      Finset.sum (Finset.Icc 2 (N - 2))
        (fun n =>
          if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
          then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
          else 0)|
        = (1 / 800 : ℝ) * |1 / (Real.log (X:ℝ))^2| *
          |Finset.sum (Finset.Icc 2 (N - 2))
             (fun n =>
               if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
               then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
               else 0)| := by
              have hconst : |(1 / 800 : ℝ)| = (1 / 800 : ℝ) := by norm_num
              ring_nf
              simp [abs_mul, hconst]
    _ = (1 / 800 : ℝ) * (1 / (Real.log (X:ℝ))^2) *
          |Finset.sum (Finset.Icc 2 (N - 2))
             (fun n =>
               if ( (n:ℤ) - ((N:ℤ) - (n:ℤ)) = k )
               then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n))
               else 0)| := by
              simp [hlogXabs, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ (1 / 800 : ℝ) * (1 / (Real.log (X:ℝ))^2) * (Real.log ((N:ℝ) + 1))^2 :=
          by
            have hpos : 0 ≤ (1 / 800 : ℝ) := by norm_num
            have := mul_le_mul_of_nonneg_left hsum hlogXNN
            nlinarith [hpos]
    _ = (1 / 800 : ℝ) * (Real.log ((N:ℝ) + 1) / Real.log (X:ℝ))^2 := by
          field_simp [one_div, mul_comm, mul_left_comm, mul_assoc, pow_two]

/-- Uniform numeric cap on the canonical window. -/
lemma payload_cap_window
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
  payload_cap X N
    ≤ (1 / 800 : ℝ) * (1 + Real.log 2 / Real.log (X0 : ℝ))^2 := by
  have hlogXpos  : 0 < Real.log (X:ℝ) := log_pos_of_large hX
  have hlogX0pos : 0 < Real.log (X0:ℝ) := by
    have hx : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0)
    simpa [Real.log_pos_iff] using hx
  -- From window membership, write N = X + k with 0 ≤ k ≤ H.
  rcases Finset.mem_filter.mp hN with ⟨hShift, _heven⟩
  rcases Finset.mem_image.mp hShift with ⟨k, hk_range, hkN⟩
  have hk_le : k ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hk_range)
  have hN_le : N ≤ X + H := by
    have : N = X + k := hkN
    nlinarith
  have hHX : H + 1 ≤ X := by
    have hHX0 : H + 1 ≤ X0 := by decide
    nlinarith
  have hN_le_twoX : (N:ℝ) + 1 ≤ 2 * (X:ℝ) := by
    have hN_le' : N + 1 ≤ X + H + 1 := by nlinarith
    have hXH_le : (X + H + 1 : ℝ) ≤ 2 * (X:ℝ) := by
      have : (H + 1 : ℕ) ≤ X := hHX
      nlinarith
    have hN_le'' : (N : ℝ) + 1 ≤ (X + H + 1 : ℝ) := by exact_mod_cast hN_le'
    nlinarith
  have hlog_num :
      Real.log ((N:ℝ) + 1) ≤ Real.log (2 * (X:ℝ)) := by
    have hpos_num : 0 < (N:ℝ) + 1 := by nlinarith
    have hpos_den : 0 < 2 * (X:ℝ) := by nlinarith
    exact Real.log_le_log hpos_num hpos_den hN_le_twoX
  have hratio :
      Real.log ((N:ℝ) + 1) / Real.log (X:ℝ)
        ≤ Real.log (2 * (X:ℝ)) / Real.log (X:ℝ) :=
    div_le_div_of_nonneg_right hlog_num (le_of_lt hlogXpos)
  have hratio_nonneg :
      0 ≤ Real.log ((N:ℝ) + 1) / Real.log (X:ℝ) := by
    have hpos_num : 0 < Real.log ((N:ℝ) + 1) := by
      have hNpos : (1 : ℝ) < (N:ℝ) + 1 := by nlinarith
      simpa [Real.log_pos_iff] using hNpos
    have hpos_den : 0 < Real.log (X:ℝ) := hlogXpos
    nlinarith
  have hratio_sq :
      (Real.log ((N:ℝ) + 1) / Real.log (X:ℝ))^2
        ≤ (Real.log (2 * (X:ℝ)) / Real.log (X:ℝ))^2 :=
    pow_le_pow_of_nonneg hratio_nonneg hratio 2
  have hlog_rewrite :
      Real.log (2 * (X:ℝ)) / Real.log (X:ℝ)
        = 1 + Real.log 2 / Real.log (X:ℝ) := by
    have hposX : 0 < (X:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < X0) hX)
    have hlog_mul : Real.log (2 * (X:ℝ)) = Real.log 2 + Real.log (X:ℝ) := by
      have hpos_two : 0 < (2:ℝ) := by norm_num
      have hpos_prod : 0 < 2 * (X:ℝ) := by nlinarith
      simpa [mul_comm] using Real.log_mul hpos_two hposX
    field_simp [hlog_mul, hposX.ne']
  have hlog_ratio_mono :
      Real.log 2 / Real.log (X:ℝ) ≤ Real.log 2 / Real.log (X0:ℝ) := by
    have hden_le : Real.log (X0:ℝ) ≤ Real.log (X:ℝ) := by
      have hx0pos : 0 < (X0:ℝ) := by exact_mod_cast (by decide : (0:ℕ) < X0)
      have hxpos : 0 < (X:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < X0) hX)
      exact Real.log_le_log hx0pos hxpos (by exact_mod_cast hX)
    have hlog2_nonneg : 0 ≤ Real.log 2 := by norm_num
    exact div_le_div_of_nonneg_left hlog2_nonneg hden_le
  have hratio_bound :
      (Real.log (2 * (X:ℝ)) / Real.log (X:ℝ))^2
        ≤ (1 + Real.log 2 / Real.log (X0:ℝ))^2 := by
    have hbase :
        1 + Real.log 2 / Real.log (X:ℝ)
          ≤ 1 + Real.log 2 / Real.log (X0:ℝ) := by
        nlinarith
    have hnonneg : 0 ≤ 1 + Real.log 2 / Real.log (X:ℝ) := by
      have hlog2_nonneg : 0 ≤ Real.log 2 := by norm_num
      have hpos_den : 0 < Real.log (X:ℝ) := hlogXpos
      nlinarith [hlog2_nonneg, hpos_den]
    exact pow_le_pow_of_nonneg hnonneg hbase 2
  have hcap :
      (1 / 800 : ℝ) * (Real.log ((N:ℝ) + 1) / Real.log (X:ℝ))^2
        ≤ (1 / 800 : ℝ) * (1 + Real.log 2 / Real.log (X0 : ℝ))^2 := by
    have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) := by norm_num
    nlinarith
  simpa [payload_cap] using hcap

end Goldbach.BG_Bank
/-- Crude window cap: replace `N` by the right end of the window. -/
lemma payload_cap_window_const
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
  payload_cap X N
    ≤ (1 / 800 : ℝ) *
        (Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ))^2 := by
  -- bound log(N+1) by log(X+H+1) and log X below by log X0
  have hN_le : N + 1 ≤ X + H + 1 := by
    have hIn := (Goldbach.Windows.mem_filter.mp hN).1
    rcases Finset.mem_image.mp hIn with ⟨k, hk, hkN⟩
    rcases Finset.mem_range.mp hk with hk_lt
    have hk_le : k ≤ H := Nat.le_of_lt_succ hk_lt
    have hk0 : 0 ≤ k := Nat.zero_le _
    have hcalc : N = X + k := hkN
    nlinarith
  have hlog_num :
      Real.log ((N:ℝ) + 1) ≤ Real.log ((X + H + 1 : ℕ) : ℝ) := by
    have hpos : 0 < ((N:ℝ) + 1) := by nlinarith
    have hpos' : 0 < ((X + H + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos _)
    have hle : (N:ℝ) + 1 ≤ ((X + H + 1 : ℕ) : ℝ) := by exact_mod_cast hN_le
    exact Real.log_le_log hpos hpos' hle
  have hlog_den : Real.log (X0 : ℝ) ≤ Real.log (X : ℝ) := by
    have hx0 : (0:ℝ) < (X0:ℝ) := by exact_mod_cast (by decide : (0:ℕ) < X0)
    have hx : (0:ℝ) < (X:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < X0) hX)
    exact Real.log_le_log hx0 hx (by exact_mod_cast hX)
  have hden_pos : 0 < Real.log (X : ℝ) := by
    have hx : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < X0) hX)
    simpa [Real.log_pos_iff] using hx
  have hratio :
      Real.log ((N:ℝ) + 1) / Real.log (X:ℝ)
        ≤ Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ) := by
    have hdiv1 := div_le_div_of_nonneg_right hlog_num (le_of_lt hden_pos)
    have hdiv2 :
        Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X : ℝ)
          ≤ Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ) := by
      have hnum_nonneg : 0 ≤ Real.log ((X + H + 1 : ℕ) : ℝ) := by
        have hxpos : (1:ℝ) ≤ ((X + H + 1 : ℕ) : ℝ) := by nlinarith
        exact Real.log_nonneg hxpos
      exact div_le_div_of_nonneg_left hnum_nonneg hlog_den
    have hchain : Real.log ((N:ℝ) + 1) / Real.log (X:ℝ)
        ≤ Real.log ((X + H + 1 : ℕ) : ℝ) / Real.log (X:ℝ) := hdiv1
    have hnonneg : 0 ≤ Real.log ((N:ℝ) + 1) / Real.log (X:ℝ) := by
      have hpos : 0 < Real.log ((N:ℝ) + 1) := by
        have hx : (1 : ℝ) < (N:ℝ) + 1 := by nlinarith
        simpa [Real.log_pos_iff] using hx
      have hden_pos' : 0 < Real.log (X:ℝ) := hden_pos
      nlinarith
    have hpow := pow_le_pow_of_nonneg hnonneg (le_trans hchain hdiv2) 2
    simpa [payload_cap, one_div, mul_comm, mul_left_comm, mul_assoc, pow_two] using hpow

/-- Numeric corollary on the canonical window. -/
lemma payload_cap_window_num
  {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X H) :
  payload_cap X N ≤ (1252 : ℝ) / 10^6 := by
  have h := payload_cap_window_const (X:=X) (N:=N) hX hN
  -- (log (X0+H+1))/log X0 ≤ 1.001456…; square and scale
  have hnum : (Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ))^2 ≤ (1001456 : ℝ) / 10^6 := by
    norm_num [X0, H]
  have hconst_nonneg : 0 ≤ (1 / 800 : ℝ) := by norm_num
  have hprod := mul_le_mul_of_nonneg_left hnum hconst_nonneg
  have : (1 / 800 : ℝ) * ((1001456 : ℝ) / 10^6) = (1252 : ℝ) / 10^6 := by norm_num
  nlinarith
