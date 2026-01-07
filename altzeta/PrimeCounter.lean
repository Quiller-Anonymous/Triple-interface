import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
AltZeta/PrimeCounter.lean
=========================

This file introduces the prime-counting objects needed for the B2-style target:
windowed bounds on a smoothed Chebyshev statistic.

Design choice:
* `PsiK` is defined as an infinite sum (`tsum`) on purpose (RH-facing semantics).
* `PsiKTrunc` is the finite truncation used for computation/certification.
* A basic decomposition lemma expresses `PsiK` as truncation + tail under `Summable`.
-/

noncomputable section

open scoped BigOperators Topology
open Real

namespace AltZeta

/-- A real kernel on the log-line. -/
abbrev LogKernel := ℝ → ℝ

/--
The `n`th summand (indexed from `0`) in the smoothed Chebyshev statistic.

We use `n.succ` to avoid `log 0`. For analytic statements one typically assumes `0 < x`.
-/
def psiKernelTerm (K : LogKernel) (x : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n.succ) * K (Real.log (n.succ : ℝ) - Real.log x)

/-- The smoothed Chebyshev statistic `Ψ_K(x)` as an infinite sum (`tsum`). -/
def PsiK (K : LogKernel) (x : ℝ) : ℝ :=
  ∑' n : ℕ, psiKernelTerm K x n

/-- Finite truncation of `Ψ_K(x)` to the first `N` summands. -/
def PsiKTrunc (K : LogKernel) (x : ℝ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) (fun n => psiKernelTerm K x n)

lemma PsiK_eq_trunc_add_tail
    {K : LogKernel} {x : ℝ} {N : ℕ}
    (h : Summable (psiKernelTerm K x)) :
    PsiK K x = PsiKTrunc K x N + ∑' n : ℕ, psiKernelTerm K x (n + N) := by
  simpa [PsiK, PsiKTrunc] using (h.sum_add_tsum_nat_add N).symm

lemma norm_PsiK_sub_trunc_le_tsum_norm_tail
    {K : LogKernel} {x : ℝ} {N : ℕ}
    (hNorm : Summable (fun n : ℕ => ‖psiKernelTerm K x n‖)) :
    ‖PsiK K x - PsiKTrunc K x N‖ ≤ ∑' n : ℕ, ‖psiKernelTerm K x (n + N)‖ := by
  have hTerm : Summable (psiKernelTerm K x) := Summable.of_norm hNorm
  have hTail : PsiK K x - PsiKTrunc K x N = ∑' n : ℕ, psiKernelTerm K x (n + N) := by
    have hEq := PsiK_eq_trunc_add_tail (K := K) (x := x) (N := N) hTerm
    -- rearrange `PsiK = trunc + tail`
    simpa [hEq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (add_sub_cancel_left (PsiKTrunc K x N) (∑' n : ℕ, psiKernelTerm K x (n + N))).symm
  have hNormTail : Summable (fun n : ℕ => ‖psiKernelTerm K x (n + N)‖) := by
    -- shift-invariance of summability on `ℕ`
    simpa using ((_root_.summable_nat_add_iff (f := fun n : ℕ => ‖psiKernelTerm K x n‖) N).2 hNorm)
  -- bound the tail using `‖∑'‖ ≤ ∑'‖ ‖`
  simpa [hTail] using (norm_tsum_le_tsum_norm (f := fun n : ℕ => psiKernelTerm K x (n + N)) hNormTail)

lemma abs_PsiK_sub_trunc_le_tsum_abs_tail
    {K : LogKernel} {x : ℝ} {N : ℕ}
    (hAbs : Summable (fun n : ℕ => |psiKernelTerm K x n|)) :
    |PsiK K x - PsiKTrunc K x N| ≤ ∑' n : ℕ, |psiKernelTerm K x (n + N)| := by
  simpa [Real.norm_eq_abs] using (norm_PsiK_sub_trunc_le_tsum_norm_tail (K := K) (x := x) (N := N) hAbs)

end AltZeta
