import Goldbach.BG_Bank
import Goldbach.Cert.MajorArcStep2ExpSums
import Goldbach.Cert.SiegelWalfiszAxioms

/-!
Major arcs (Step 19, sigma-agnostic): prime-only vs. von Mangoldt (prime-power disposal).

Steps 2–6 use the von Mangoldt weight `ΛVM` (from `Goldbach.Cert.SiegelWalfisz`).
The Goldbach bank payload uses the prime-only weight

`Goldbach.BG_Bank.Λ(n) = log n` if `n` is prime, else `0`.

The difference is supported on prime powers `p^k` with `k ≥ 2`. For our purposes it is enough to
have a uniform (crude) bound on exponential sums involving the difference, using only:

* `‖gExp β n‖ = 1`, and
* `|ΛVM n - BG_Bank.Λ n|` is `O(log(n+1))`.

This file packages such bounds in a form usable for later triangle-inequality arguments.
-/

namespace Goldbach.Cert
namespace MajorArcStep19PrimePowerDisposal

open scoped BigOperators

open Complex

open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.Cert.SiegelWalfisz

noncomputable section

lemma abs_ΛVM_le_log_succ (n : ℕ) : |ΛVM n| ≤ Real.log ((n : ℝ) + 1) := by
  classical
  cases n with
  | zero =>
      simp [ΛVM]
  | succ n =>
      -- `ΛVM (n+1) = vonMangoldt (n+1)` is nonnegative and ≤ log(n+1) ≤ log(n+2).
      have hnonneg : 0 ≤ ΛVM (n + 1) := by
        -- `vonMangoldt_nonneg` is for `ArithmeticFunction.Λ` (the von Mangoldt function).
        simpa [ΛVM] using (ArithmeticFunction.vonMangoldt_nonneg (n := n + 1))
      have habs : |ΛVM (n + 1)| = ΛVM (n + 1) := abs_of_nonneg hnonneg
      have hle_log : ΛVM (n + 1) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
        simpa [ΛVM] using (ArithmeticFunction.vonMangoldt_le_log (n := n + 1))
      have hlog_mono :
          Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · linarith
      -- Conclude.
      simpa [Nat.succ_eq_add_one, habs, add_assoc] using le_trans hle_log hlog_mono

lemma abs_bankΛ_le_log_succ (n : ℕ) : |Goldbach.BG_Bank.Λ n| ≤ Real.log ((n : ℝ) + 1) := by
  by_cases hp : Nat.Prime n
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have hn2 : (2 : ℕ) ≤ n := Nat.succ_le_of_lt hp.one_lt
      have hn1n : (1 : ℕ) ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn2
      exact_mod_cast hn1n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hlog_mono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
      refine Real.log_le_log ?_ ?_
      · positivity
      · linarith
    simpa [Goldbach.BG_Bank.Λ, hp, abs_of_nonneg hlog_nonneg] using hlog_mono
  · -- `Λ` is zero off primes, so it suffices that `log(n+1) ≥ 0`.
    have hnonneg : 0 ≤ Real.log ((n : ℝ) + 1) := by
      refine Real.log_nonneg ?_
      nlinarith
    simpa [Goldbach.BG_Bank.Λ, hp] using hnonneg

lemma abs_ΛVM_sub_bankΛ_le (n : ℕ) :
    |ΛVM n - Goldbach.BG_Bank.Λ n| ≤ 2 * Real.log ((n : ℝ) + 1) := by
  have htri : |ΛVM n - Goldbach.BG_Bank.Λ n| ≤ |ΛVM n| + |Goldbach.BG_Bank.Λ n| := by
    -- `|x-y| = |x + (-y)| ≤ |x| + |y|`.
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le (ΛVM n) (-Goldbach.BG_Bank.Λ n)
  have h1 := abs_ΛVM_le_log_succ (n := n)
  have h2 := abs_bankΛ_le_log_succ (n := n)
  have : |ΛVM n| + |Goldbach.BG_Bank.Λ n| ≤ 2 * Real.log ((n : ℝ) + 1) := by
    nlinarith
  exact le_trans htri this

/--
Crude bound for the “prime-power contamination” exponential sum on an interval:
the contribution of `ΛVM - BG_Bank.Λ` is `O(card * log(U+2))`.
-/
theorem norm_sum_ΛVM_sub_bankΛ_gExp_le
    {L U : ℕ} (β : ℝ) :
    ‖∑ n ∈ Finset.Ico L (U + 1),
        ((ΛVM n - Goldbach.BG_Bank.Λ n : ℝ) : ℂ) * gExp β n‖
      ≤
    (Finset.Ico L (U + 1)).card * (2 * Real.log ((U : ℝ) + 2)) := by
  classical
  -- `‖∑‖ ≤ ∑ ‖‖`
  have hsum := norm_sum_le (s := Finset.Ico L (U + 1))
    (f := fun n => ((ΛVM n - Goldbach.BG_Bank.Λ n : ℝ) : ℂ) * gExp β n)
  refine le_trans hsum ?_
  -- Bound each summand by a uniform constant.
  have hpoint :
      ∀ n ∈ Finset.Ico L (U + 1),
        ‖((ΛVM n - Goldbach.BG_Bank.Λ n : ℝ) : ℂ) * gExp β n‖
          ≤ 2 * Real.log ((U : ℝ) + 2) := by
    intro n hn
    have hn_le : n ≤ U := Nat.le_of_lt_succ (Finset.mem_Ico.mp hn).2
    have hlog_mono : Real.log ((n : ℝ) + 1) ≤ Real.log ((U : ℝ) + 2) := by
      have hle : (n : ℝ) + 1 ≤ (U : ℝ) + 2 := by
        nlinarith [show (n : ℝ) ≤ (U : ℝ) from Nat.cast_le.2 hn_le]
      exact Real.log_le_log (by positivity) hle
    have habs :
        ‖((ΛVM n - Goldbach.BG_Bank.Λ n : ℝ) : ℂ) * gExp β n‖
          =
        |ΛVM n - Goldbach.BG_Bank.Λ n| := by
      -- Avoid rewriting `(r : ℂ)` into `↑ΛVM n - ↑BG_Bank.Λ n`.
      let r : ℝ := ΛVM n - Goldbach.BG_Bank.Λ n
      calc
        ‖((r : ℂ) * gExp β n)‖ = ‖(r : ℂ)‖ * ‖gExp β n‖ := by
          simpa [norm_mul] using (norm_mul (r : ℂ) (gExp β n))
        _ = |r| := by
          simp [MajorArcStep2ExpSums.gExp, MajorArcExponential.norm_e]
        _ = |ΛVM n - Goldbach.BG_Bank.Λ n| := by
          simp [r]
    have hdiff : |ΛVM n - Goldbach.BG_Bank.Λ n| ≤ 2 * Real.log ((U : ℝ) + 2) := by
      have hbase : |ΛVM n - Goldbach.BG_Bank.Λ n| ≤ 2 * Real.log ((n : ℝ) + 1) :=
        abs_ΛVM_sub_bankΛ_le (n := n)
      nlinarith [hbase, hlog_mono]
    -- Avoid `simp` rewriting the norm into a product of norms; use a direct `calc`.
    calc
      ‖((ΛVM n - Goldbach.BG_Bank.Λ n : ℝ) : ℂ) * gExp β n‖
          = |ΛVM n - Goldbach.BG_Bank.Λ n| := habs
      _ ≤ 2 * Real.log ((U : ℝ) + 2) := hdiff

  have :
      (∑ n ∈ Finset.Ico L (U + 1),
          ‖((ΛVM n - Goldbach.BG_Bank.Λ n : ℝ) : ℂ) * gExp β n‖)
        ≤
      (∑ _n ∈ Finset.Ico L (U + 1), (2 * Real.log ((U : ℝ) + 2) : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact hpoint n hn
  simpa using this.trans_eq (by simp)

end

end MajorArcStep19PrimePowerDisposal
end Goldbach.Cert
