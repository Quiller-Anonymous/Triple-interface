/-
  Major bound for the Hardy–Littlewood main term `M(N) = σ(N) * N / (log N)^2`,
  derived from a window-wise lower bound on the singular series.

  No axioms/sorries: you supply the σ-lower bound for your working window.
-/
import Mathlib

import Goldbach.SingularSeries   -- sigma, C2Const
import Goldbach.MainTerm         -- M
import Goldbach.Windows          -- Windows.EvenIn
import Goldbach.Analytic.MajorBound -- AnalyticAssemble.MajorBound (isolated)

open scoped BigOperators

namespace Goldbach.Analytic

open Singular MainTerm
open Goldbach.AnalyticAssemble

/-- A window-wise lower bound for the singular series σ, parameterized by `C2`. -/
structure SigmaLowerOn (X0 H : ℕ) (C : Singular.C2Const) (σmin : ℝ) : Prop :=
  (σmin_pos : 0 < σmin)
  (bound    : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
                Singular.sigma C N ≥ σmin)

/-- Helper: for even `N ≥ 2`, the factor `N / (log N)^2` is nonnegative. -/
private lemma factor_nonneg (N : ℕ) (hN2 : 2 ≤ N) :
    0 ≤ (N : ℝ) / (Real.log (N : ℝ))^2 := by
  have hlogpos : 0 < Real.log (N : ℝ) := by
    have h1ltN : (1 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hN2
    simpa [Real.log_pos_iff] using h1ltN
  have hdenpos : 0 < (Real.log (N : ℝ))^2 := sq_pos_of_pos hlogpos
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  exact div_nonneg hN0 (le_of_lt hdenpos)

/-- For `N ≥ 2`, the factor `N / (log N)^2` is at least `1`. -/
private lemma one_le_nat_div_log_sq {N : ℕ} (hN2 : 2 ≤ N) :
    (1 : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
  have h1lt : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hN2)
  have hpos : (0 : ℝ) < (N : ℝ) := lt_trans (by norm_num) h1lt

  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos h1lt
  have hlognonneg : 0 ≤ Real.log (N : ℝ) := le_of_lt hlogpos

  have hlog_le_exp_half :
      Real.log (N : ℝ) ≤ Real.exp (Real.log (N : ℝ) / 2) := by
    -- `Real.two_mul_le_exp` at `log N / 2` gives `log N ≤ exp(log N / 2)`
    have h := Real.two_mul_le_exp (x := Real.log (N : ℝ) / 2)
    -- simplify `2 * (log N / 2)` to `log N`
    have : (2 : ℝ) * (Real.log (N : ℝ) / 2) = Real.log (N : ℝ) := by ring
    simpa [this] using h

  have hsq :
      (Real.log (N : ℝ)) ^ 2 ≤ (Real.exp (Real.log (N : ℝ) / 2)) ^ 2 := by
    have hExpNonneg : 0 ≤ Real.exp (Real.log (N : ℝ) / 2) := by
      exact le_of_lt (Real.exp_pos _)
    have hmul : Real.log (N : ℝ) * Real.log (N : ℝ) ≤
        Real.exp (Real.log (N : ℝ) / 2) * Real.exp (Real.log (N : ℝ) / 2) := by
      exact mul_le_mul hlog_le_exp_half hlog_le_exp_half hlognonneg hExpNonneg
    simpa [pow_two] using hmul

  have hsq' : (Real.log (N : ℝ)) ^ 2 ≤ Real.exp (Real.log (N : ℝ)) := by
    -- `(exp (a/2))^2 = exp(a/2 + a/2) = exp a`
    have hadd : Real.log (N : ℝ) / 2 + Real.log (N : ℝ) / 2 = Real.log (N : ℝ) := by ring
    simpa [pow_two, ← Real.exp_add, hadd] using hsq

  have hlog_sq_le : (Real.log (N : ℝ)) ^ 2 ≤ (N : ℝ) := by
    simpa [Real.exp_log hpos] using hsq'

  have hden_pos : 0 < (Real.log (N : ℝ)) ^ 2 := by
    exact pow_pos hlogpos 2

  -- convert `(log N)^2 ≤ N` to `1 ≤ N / (log N)^2`
  have : (1 : ℝ) * (Real.log (N : ℝ)) ^ 2 ≤ (N : ℝ) := by
    simpa [one_mul] using hlog_sq_le
  exact (le_div_iff₀ hden_pos).2 this

/-- Backwards-compatible alias. -/
private lemma one_le_factor (N : ℕ) (hN2 : 2 ≤ N) :
    (1 : ℝ) ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
  simpa using (one_le_nat_div_log_sq (N := N) hN2)

/-- Major bound from a σ-lower bound (scale-aware HL form). -/
lemma major_of_sigma_lower
    {X0 H : ℕ} {S c0 σmin : ℝ} {C : Singular.C2Const}
    (A   : SigmaLowerOn X0 H C σmin)
    (hcs : c0 * S ≤ σmin)
    (two_le_of_mem : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → 2 ≤ N) :
    AnalyticAssemble.MajorBound X0 H S c0 (MainTerm.M C) := by
  intro X N hX hN
  -- positivity of σmin
  have hσmin : 0 < σmin := A.σmin_pos
  -- lower bound on σ
  have hσ : Singular.sigma C N ≥ σmin := A.bound hX hN
  -- define the Hardy–Littlewood factor once
  have hN2 : 2 ≤ N := two_le_of_mem hX hN
  set fac : ℝ := (N : ℝ) / (Real.log (N : ℝ)) ^ 2
  have hfac : 0 ≤ fac := by
    simpa [fac] using factor_nonneg N hN2

  -- M = σ * factor, so M ≥ σmin * factor
  have step1 : σmin * fac ≤ MainTerm.M C N := by
    -- `MainTerm.M C N = sigma C N * fac`
    -- and `σmin ≤ sigma C N`
    have hmul := mul_le_mul_of_nonneg_right hσ hfac
    -- rearrange to match MainTerm.M definition
    simp only [MainTerm.M, fac] at hmul ⊢
    have heq : Singular.sigma C N * (↑N / Real.log ↑N ^ 2) = 
               Singular.sigma C N * ↑N / Real.log ↑N ^ 2 := by ring
    rw [heq] at hmul
    exact hmul

  -- scale `c0*S ≤ σmin` by the nonnegative factor
  have step2 : (c0 * S) * fac ≤ σmin * fac := by
    have hmul := mul_le_mul_of_nonneg_right hcs hfac
    simpa [mul_assoc] using hmul

  have hMfac : (c0 * S) * fac ≤ MainTerm.M C N := le_trans step2 step1

  by_cases hcs0 : c0 * S ≤ 0
  · -- if `c0*S ≤ 0`, it suffices to show `0 ≤ M`
    have hσfac0 : 0 ≤ σmin * fac := mul_nonneg (le_of_lt hσmin) hfac
    have hM0 : 0 ≤ MainTerm.M C N := le_trans hσfac0 step1
    exact le_trans hcs0 hM0
  · -- if `c0*S > 0`, use `1 ≤ fac`
    have hcspos : 0 < c0 * S := lt_of_not_ge hcs0
    have hfac1 : (1 : ℝ) ≤ fac := by
      simpa [fac] using (one_le_nat_div_log_sq (N := N) hN2)
    have hmul : c0 * S ≤ (c0 * S) * fac := by
      have ha0 : 0 ≤ c0 * S := le_of_lt hcspos
      have h' := mul_le_mul_of_nonneg_left hfac1 ha0
      simpa [mul_assoc, one_mul] using h'
    exact le_trans hmul hMfac

/-- Specialization at `S = 1`: it suffices to supply `c0 ≤ σmin`. -/
lemma major_of_sigma_lower_S1
    {X0 H : ℕ} {c0 σmin : ℝ} {C : Singular.C2Const}
    (A   : SigmaLowerOn X0 H C σmin)
    (hc0 : c0 ≤ σmin)
    (two_le_of_mem : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → 2 ≤ N) :
    AnalyticAssemble.MajorBound X0 H (1 : ℝ) c0 (MainTerm.M C) := by
  intro X N hX hN
  have h := major_of_sigma_lower (A:=A) (S:=1) (c0:=c0) (σmin:=σmin)
      (hcs := by simp [mul_one]; exact hc0)
      (two_le_of_mem := two_le_of_mem) hX hN
  simp only [mul_one] at h ⊢
  exact h

end Goldbach.Analytic
