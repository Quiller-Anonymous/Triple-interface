import Mathlib
import Goldbach.AO_OffDiag.TailBlock

/-!
One-time numeric certificate component for the S2 σ-lower project:

`TailBlock.sigma_trunc_Q0 2 ≥ 33/25`.

This is *not* the full global σ-lower bound. It is the “value at the coprime/parity locus” that
S2 aims to show is the global minimum.

We prove the inequality by computing a rational version of `sigma_trunc_Q0` at `N = 2` and then
casting to `ℝ`.
-/

namespace Goldbach.Cert.SigmaTruncQ0At2Cert

open scoped BigOperators

open Goldbach.AO_OffDiag

/-- A computable rational version of `TailBlock.sigma_trunc_Q0`. -/
def sigma_trunc_Q0_rat (N : ℕ) : Rat :=
  (Finset.Icc (1 : ℕ) TailBlock.Q0).sum (fun q =>
    if Squarefree q then
      ((TailBlock.ramanujanZ q N : ℤ) : Rat) / ((Nat.totient q : Rat) ^ 2)
    else 0)

lemma sigma_trunc_Q0_eq_rat (N : ℕ) :
    TailBlock.sigma_trunc_Q0 N = (sigma_trunc_Q0_rat N : ℝ) := by
  classical
  -- Unfold both definitions; on squarefree `q` the term is rational and we just cast.
  unfold TailBlock.sigma_trunc_Q0 sigma_trunc_Q0_rat
  -- Move the cast inside the sum.
  simp_rw [Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro q hq
  by_cases hsf : Squarefree q
  · simp [TailBlock.muSq, TailBlock.ramanujanR, hsf, one_div, div_eq_mul_inv, pow_two, mul_assoc,
      mul_left_comm, mul_comm]
  · simp [TailBlock.muSq, TailBlock.ramanujanR, hsf]

private theorem sigma_trunc_Q0_rat_two_ge_33_25 :
    (33 : Rat) / 25 ≤ sigma_trunc_Q0_rat 2 := by
  native_decide

theorem sigma_trunc_Q0_two_ge_33_25 :
    (33 : ℝ) / 25 ≤ TailBlock.sigma_trunc_Q0 2 := by
  have hRat : (33 : Rat) / 25 ≤ sigma_trunc_Q0_rat 2 :=
    sigma_trunc_Q0_rat_two_ge_33_25
  have hReal : ((33 : Rat) / 25 : ℝ) ≤ (sigma_trunc_Q0_rat 2 : ℝ) := by
    exact_mod_cast hRat
  -- Rewrite the RHS to the repo definition.
  simpa [sigma_trunc_Q0_eq_rat (N := 2)] using hReal

end Goldbach.Cert.SigmaTruncQ0At2Cert
