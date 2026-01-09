import Mathlib

/-!
Summation by parts (discrete Abel/partial summation), in a form convenient for
major-arc derivations from Siegel–Walfisz bounds.

This file is deliberately sigma-agnostic: it contains only finite-sum algebra.
-/

namespace Goldbach.Cert

open scoped BigOperators

namespace SummationByParts

variable {α : Type} [CommRing α]

/-- Prefix sums `A n := ∑_{m < n+1} a m`. -/
noncomputable def prefixSum (a : ℕ → α) (n : ℕ) : α :=
  (Finset.range (n + 1)).sum a

@[simp] lemma prefixSum_zero (a : ℕ → α) : prefixSum a 0 = a 0 := by
  simp [prefixSum]

@[simp] lemma prefixSum_succ (a : ℕ → α) (n : ℕ) :
    prefixSum a (n + 1) = prefixSum a n + a (n + 1) := by
  simp [prefixSum, Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]

/--
Discrete summation by parts:

`∑_{n=0}^N a(n) f(n) = A(N) f(N) - ∑_{n=0}^{N-1} A(n) (f(n+1) - f(n))`,

where `A(n) := ∑_{m=0}^n a(m)`.
-/
theorem sum_mul_eq_prefixSum_mul_sub_sum_prefixSum_mul_diff
    (a f : ℕ → α) (N : ℕ) :
    (Finset.range (N + 1)).sum (fun n => a n * f n)
      =
      (prefixSum a N) * f N
        - (Finset.range N).sum (fun n => (prefixSum a n) * (f (n + 1) - f n)) := by
  induction N with
  | zero =>
      simp [prefixSum]
  | succ N ih =>
      -- Expand the LHS, then replace the prefix `N`-sum via the IH.
      have hL :
          (Finset.range (N + 2)).sum (fun n => a n * f n)
            =
            (Finset.range (N + 1)).sum (fun n => a n * f n) + a (N + 1) * f (N + 1) := by
        simp [Finset.sum_range_succ]
      -- Expand the RHS `diff` sum.
      have hDiff :
          (Finset.range (N + 1)).sum (fun n => (prefixSum a n) * (f (n + 1) - f n))
            =
            (Finset.range N).sum (fun n => (prefixSum a n) * (f (n + 1) - f n))
              + (prefixSum a N) * (f (N + 1) - f N) := by
        simp [Finset.sum_range_succ]
      -- Now do the standard Abel summation algebra.
      -- (Keep `prefixSum` opaque; only use the one-step recursion.)
      -- Combine and finish by commutative-ring arithmetic.
      -- We avoid unfolding `prefixSum` to keep the goal stable.
      calc
        (Finset.range (N + 2)).sum (fun n => a n * f n)
            =
            (prefixSum a N) * f N
              - (Finset.range N).sum (fun n => (prefixSum a n) * (f (n + 1) - f n))
              + a (N + 1) * f (N + 1) := by
                simp [hL, ih, add_comm]
        _ =
            (prefixSum a (N + 1)) * f (N + 1)
              - (Finset.range (N + 1)).sum (fun n => (prefixSum a n) * (f (n + 1) - f n)) := by
                -- Replace `prefixSum a (N+1)` and the longer `diff` sum, then normalize.
                -- This is the algebraic identity:
                --   A_N f_N + a_{N+1} f_{N+1}
                --     = A_{N+1} f_{N+1} - A_N (f_{N+1} - f_N).
                -- combined with `hDiff`.
                simp [hDiff]
                ring

end SummationByParts

end Goldbach.Cert
