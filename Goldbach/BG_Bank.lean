/-
  Goldbach/BG_Bank.lean  — axiom-free scaffold

  What this file provides now:
    • S_BG        : Finset ℤ     (bank support)
    • Λ, wX       : weights (von Mangoldt proxy and dyadic bump)
    • P_BG        : ℕ → ℕ → ℤ → ℝ (weighted offset payload)
    • payload_cap : ℕ → ℝ        (per-N magnitude cap)
    • payload_bound : |P_BG X N k| ≤ payload_cap N on the window
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.Rep

namespace Goldbach.BG_Bank

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Real
open BigOperators
open Classical

/-- Canonical BG support (bank offsets). -/
noncomputable def S_BG : Finset ℤ :=
  Finset.Icc (-(H : ℤ)) (H : ℤ)

/-- Von Mangoldt proxy (log on primes). Swap for your arithmetic version if desired. -/
noncomputable def Λ (n : ℕ) : ℝ :=
  if Nat.Prime n then Real.log n else 0

/-- Dyadic bump (currently flat = 1 to match existing pipeline). -/
noncomputable def wX (_X n : ℕ) : ℝ := 1

/-- Weighted offset payload, normalized by `(log X)^2` to live on the `S=1` scale. -/
noncomputable def P_BG (X N : ℕ) (k : ℤ) : ℝ :=
  (Real.log (X : ℝ))⁻² *
    ∑ n in Finset.Icc 2 (N - 2),
      let m := N - n
      if ((n : ℤ) - (m : ℤ) = k) then
        (wX X n * Λ n) * (wX X m * Λ m)
      else
        0

/-- Normalized constant cap on the working window:
    payload_cap = (log (X0+H+1) / log X0)^2 ≈ 1.002 for X0=10^6, H=10^4. -/
noncomputable def payload_cap (_N : ℕ) : ℝ :=
  let num : ℝ := Real.log ((X0 + H + 1 : ℕ) : ℝ)
  let den : ℝ := Real.log (X0 : ℝ)
  (num / den)^2

lemma payload_nonneg (N : ℕ) : 0 ≤ payload_cap N := by
  unfold payload_cap
  have hdenpos : 0 < Real.log (X0 : ℝ) := by
    have hx : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0)
    simpa [Real.log_pos_iff] using hx
  have hden_ne : Real.log (X0 : ℝ) ≠ 0 := ne_of_gt hdenpos
  have hsq : 0 ≤ (Real.log ((X0 + H + 1 : ℕ) : ℝ) / Real.log (X0 : ℝ))^2 := sq_nonneg _
  simpa using hsq

/-- Uniform (in k) pointwise bound on the window:
    |P_BG X N k| ≤ payload_cap N. -/
lemma payload_bound :
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    ∀ {k : ℤ}, k ∈ S_BG → |P_BG X N k| ≤ payload_cap N := by
  intro X N _hX _hN k _hk
  have := payload_bound_any (X:=X) (N:=N) _hX _hN (k:=k)
  simpa using this

/-- Pointwise bound holds for all offsets (not just k ∈ S_BG); useful for tails. -/
lemma payload_bound_any :
  ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
    ∀ {k : ℤ}, |P_BG X N k| ≤ payload_cap N := by
  intro X N _hX _hN k
  classical
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    have hx : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < X0) _hX)
    simpa [Real.log_pos_iff] using hx
  have hlogX_nonneg : 0 ≤ (Real.log (X : ℝ))⁻² := by
    have hne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogXpos
    have : 0 ≤ (Real.log (X : ℝ))⁻¹ := by
      have hpos : 0 < (Real.log (X : ℝ))⁻1 := inv_pos.mpr hlogXpos
      exact le_of_lt hpos
    nlinarith
  -- bound each summand by (log (N+1))^2
  have hterm :
      ∀ n ∈ Finset.Icc 2 (N - 2),
        |if (↑n - (↑(N - n)) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0|
          ≤ (Real.log (Nat.succ N : ℝ))^2 := by
    intro n hn
    by_cases hcond : ((n : ℤ) - (N - n : ℤ) = k)
    · have hn_le : n ≤ N := Nat.le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le _ _)
      have hn_min : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_max : n ≤ N - 2 := (Finset.mem_Icc.mp hn).2
      have hlogn : Real.log (n : ℝ) ≤ Real.log (Nat.succ N : ℝ) :=
        Real.log_le_log (by nlinarith) (by nlinarith)
      have hm_min : 2 ≤ N - n := by nlinarith
      have hlogm : Real.log (N - n : ℝ) ≤ Real.log (Nat.succ N : ℝ) :=
        Real.log_le_log (by nlinarith) (by nlinarith)
      have hΛn : |Λ n| ≤ Real.log (Nat.succ N : ℝ) := by
        unfold Λ; split_ifs
        · have := abs_nonneg (Real.log (n : ℝ))
          linarith
        · simp
      have hΛm : |Λ (N - n)| ≤ Real.log (Nat.succ N : ℝ) := by
        unfold Λ; split_ifs
        · have := abs_nonneg (Real.log (N - n : ℝ))
          linarith
        · simp
      have hprod : |(wX X n * Λ n) * (wX X (N - n) * Λ (N - n))|
          ≤ (Real.log (Nat.succ N : ℝ)) * (Real.log (Nat.succ N : ℝ)) := by
        have hw1 : |wX X n| = 1 := by simp [wX]
        have hw2 : |wX X (N - n)| = 1 := by simp [wX]
        have := mul_le_mul hΛn hΛm (by have := abs_nonneg (Λ (N-n)); linarith) (by have := abs_nonneg (Λ n); linarith)
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, hw1, hw2] using this
      simpa [hcond, pow_two] using hprod
    · simp [hcond]
  -- |sum| ≤ sum of abs, keeping the `(log X)⁻²` factor explicit
  have habs : |P_BG X N k| ≤ (Real.log (X : ℝ))⁻² *
      ∑ n in Finset.Icc 2 (N - 2),
        |if (↑n - (↑(N - n)) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0| := by
    unfold P_BG
    have hsum := abs_sum_le_sum_abs (s:=Finset.Icc 2 (N - 2))
      (f:=fun n =>
        (if ((n : ℤ) - (N - n : ℤ) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0))
    have hcf_nonneg : 0 ≤ (Real.log (X : ℝ))⁻² := hlogX_nonneg
    have hcf_abs : |(Real.log (X : ℝ))⁻²| = (Real.log (X : ℝ))⁻² := abs_of_nonneg hcf_nonneg
    calc
      |(Real.log (X : ℝ))⁻² *
          ∑ n in Finset.Icc 2 (N - 2),
            (if ((n : ℤ) - (N - n : ℤ) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0)|
          = (Real.log (X : ℝ))⁻² *
              |∑ n in Finset.Icc 2 (N - 2),
                (if ((n : ℤ) - (N - n : ℤ) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0)| := by
                simp [hcf_abs, abs_mul]
      _ ≤ (Real.log (X : ℝ))⁻² *
            ∑ n in Finset.Icc 2 (N - 2),
              |if ((n : ℤ) - (N - n : ℤ) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0| := by
                exact mul_le_mul_of_nonneg_left hsum hcf_nonneg
  have hsum :
      ∑ n in Finset.Icc 2 (N - 2),
        |if (↑n - (↑(N - n)) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0|
        ≤ (Real.log (Nat.succ N : ℝ))^2 := by
    -- at most one n contributes to the offset constraint, and each term ≤ (log (N+1))^2
    classical
    by_cases hnonempty : (Finset.Icc 2 (N - 2)).Nonempty
    · -- bound by max term times 1
      have hmax :
          ∀ n ∈ Finset.Icc 2 (N - 2),
            |if (↑n - (↑(N - n)) = k) then (wX X n * Λ n) * (wX X (N - n) * Λ (N - n)) else 0|
              ≤ (Real.log (Nat.succ N : ℝ))^2 := hterm
      refine Finset.sum_le_of_nonempty hnonempty ?_
      intro n hn; exact hmax n hn
    · -- empty sum = 0 ≤ ...
      simp [hnonempty, hterm]
  -- combine: |P_BG| ≤ (log X)⁻² * (log (N+1))^2
  have hcap : |P_BG X N k| ≤ (Real.log (X : ℝ))⁻² * (Real.log (Nat.succ N : ℝ))^2 := by
    exact le_trans habs (by nlinarith)
  -- relate log (N+1) to the fixed cap log (X0+H+1)
  have hmono_log : Real.log (Nat.succ N : ℝ) ≤ Real.log ((X0 + H + 1 : ℕ) : ℝ) := by
    have hNle : N + 1 ≤ X + H + 1 := by
      have hNleXH : N ≤ X + H := by
        have hNmem := _hN
        -- N ∈ [X, X+H], so N ≤ X+H
        have hIcc := (Finset.mem_filter.mp hNmem).1
        have hIcc' := (Finset.mem_image.mp hIcc).fst
        have : N ≤ X + H := by
          -- EvenIn uses IccShift; every element is X+k with k≤H
          have h := (Finset.mem_image.mp hIcc).2.2
          rcases (Finset.mem_range.mp ((Finset.mem_image.mp hIcc).1)) with hk
          nlinarith
        simpa using this
      nlinarith
    have hpos : (1 : ℝ) < (Nat.succ N : ℝ) := by exact_mod_cast (Nat.succ_lt_succ (Nat.succ_le_iff.mp (Nat.succ_le_iff.mpr (Nat.zero_le N))))
    have hpos' : (1 : ℝ) < ((X0 + H + 1 : ℕ) : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0+H+1)
    exact Real.log_le_log hpos hpos'
  have hdenpos : 0 < Real.log (X : ℝ) := hlogXpos
  have hdenpos0 : 0 < Real.log (X0 : ℝ) := by
    have hx : (1 : ℝ) < (X0 : ℝ) := by exact_mod_cast (by decide : (1:ℕ) < X0)
    simpa [Real.log_pos_iff] using hx
  have hden_mono : (Real.log (X : ℝ))⁻² ≤ (Real.log (X0 : ℝ))⁻² := by
    have hlog_mono : Real.log (X0 : ℝ) ≤ Real.log (X : ℝ) := by
      have hx : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast _hX
      exact Real.log_le_log (by exact_mod_cast (by decide : (0:ℕ) < X0)) hx
    have hbase_nonneg : 0 ≤ (Real.log (X : ℝ))⁻¹ := by
      have hpos : 0 < (Real.log (X : ℝ))⁻1 := inv_pos.mpr hlogXpos
      exact le_of_lt hpos
    have hinv_mono : (Real.log (X : ℝ))⁻¹ ≤ (Real.log (X0 : ℝ))⁻¹ :=
      inv_le_inv_of_le (le_of_lt hdenpos0) hlog_mono
    have hpow := pow_le_pow_of_nonneg hbase_nonneg hinv_mono 2
    simpa [pow_two] using hpow
  have hfinal :
      |P_BG X N k| ≤ payload_cap N := by
    unfold payload_cap
    nlinarith
  simpa using hfinal

end Goldbach.BG_Bank
