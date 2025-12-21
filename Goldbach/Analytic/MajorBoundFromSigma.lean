/-
  Major bound for the Hardy–Littlewood main term `M(N) = σ(N) * N / (log N)^2`,
  derived from a window-wise lower bound on the singular series.

  No axioms/sorries: you supply the σ-lower bound for your working window.
-/
import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic

import Goldbach.SingularSeries   -- sigma, C2Const
import Goldbach.MainTerm         -- M
import Goldbach.Windows          -- Windows.EvenIn
import Goldbach.AnalyticAssemble -- MajorBound

open scoped BigOperators

namespace Goldbach.Analytic

open Singular MainTerm AnalyticAssemble

/-- A window-wise lower bound for the singular series σ, parameterized by `C2`. -/
structure SigmaLowerOn (X0 H : ℕ) (C : Singular.C2Const) : Prop :=
  (σmin     : ℝ)
  (σmin_pos : 0 < σmin)
  (bound    : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H →
                Singular.sigma C N ≥ σmin)

/-- Helper: for even `N ≥ 2`, the factor `N / (log N)^2` is nonnegative. -/
private lemma factor_nonneg (N : ℕ) (hN2 : 2 ≤ N) :
    0 ≤ (N : ℝ) / (Real.log (N : ℝ))^2 := by
  have hlogpos : 0 < Real.log (N : ℝ) := by
    have h1ltN : (1 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 1 < 2) hN2
    simpa [Real.log_pos_iff] using h1ltN
  have hdenpos : 0 < (Real.log (N : ℝ))^2 := sq_pos_of_ne_zero _ (ne_of_gt hlogpos)
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  exact div_nonneg hN0 (le_of_lt hdenpos)

/-- Major bound from a σ-lower bound (scale-aware HL form). -/
lemma major_of_sigma_lower
    {X0 H : ℕ} {S c0 : ℝ} {C : Singular.C2Const}
    (A   : SigmaLowerOn X0 H C)
    (hcs : c0 * S ≤ A.σmin)
    (two_le_of_mem : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → 2 ≤ N) :
    AnalyticAssemble.MajorBound X0 H S c0 (MainTerm.M C) := by
  intro X N hX hN
  -- lower bound on σ
  have hσ : Singular.sigma C N ≥ A.σmin := A.bound hX hN
  -- nonnegative factor
  have hN2 : 2 ≤ N := two_le_of_mem hX hN
  have hfac : 0 ≤ (N : ℝ) / (Real.log (N : ℝ))^2 := factor_nonneg N hN2
  -- M = σ * factor
  have step1 : MainTerm.M C N ≥ A.σmin * (N : ℝ) / (Real.log (N : ℝ))^2 := by
    simpa [MainTerm.M] using mul_le_mul_of_nonneg_right hσ hfac
  have step2 :
      A.σmin * (N : ℝ) / (Real.log (N : ℝ))^2
        ≥ c0 * S * (N : ℝ) / (Real.log (N : ℝ))^2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_right hcs hfac
  exact ge_trans step1 step2

/-- Specialization at `S = 1`: it suffices to supply `c0 ≤ σmin`. -/
lemma major_of_sigma_lower_S1
    {X0 H : ℕ} {c0 : ℝ} {C : Singular.C2Const}
    (A   : SigmaLowerOn X0 H C)
    (hc0 : c0 ≤ A.σmin)
    (two_le_of_mem : ∀ {X N}, X0 ≤ X → N ∈ Windows.EvenIn X H → 2 ≤ N) :
    AnalyticAssemble.MajorBound X0 H (1 : ℝ) c0 (MainTerm.M C) := by
  simpa [one_mul] using
    major_of_sigma_lower (A:=A) (S:=1) (c0:=c0)
      (hcs := by simpa [one_mul] using hc0)
      (two_le_of_mem := two_le_of_mem)

end Goldbach.Analytic
