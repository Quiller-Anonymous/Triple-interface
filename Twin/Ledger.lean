/-
  Twin/Ledger.lean
  Type-I ledger: windowed sums over `range`, with clean recurrences.
-/
import Mathlib

open scoped BigOperators

namespace Twin.Ledger

variable {β : Type*} [AddCommMonoid β]

/-- Windowed sum over `N` terms:  ∑_{k=0}^{N-1} f (X + k). -/
def windowSumN (X N : ℕ) (f : ℕ → β) : β :=
  (Finset.range N).sum (fun k => f (X + k))

/-- Windowed sum over a *span* `H`:  ∑_{k=0}^{H} f (X + k). -/
def windowSum (X H : ℕ) (f : ℕ → β) : β :=
  windowSumN X (H+1) f

@[simp] lemma windowSumN_zero (X : ℕ) (f : ℕ → β) :
    windowSumN X 0 f = 0 := by
  simp [windowSumN]

@[simp] lemma windowSum_zero (X : ℕ) (f : ℕ → β) :
    windowSum X 0 f = f X := by
  simp [windowSum, windowSumN]

/-- Recurrence in the *count* `N`. -/
lemma windowSumN_succ (X N : ℕ) (f : ℕ → β) :
    windowSumN X (N+1) f = windowSumN X N f + f (X + N) := by
  classical
  unfold windowSumN
  simpa using Finset.sum_range_succ (fun k => f (X + k)) N

/-- Recurrence in the *span* `H`. -/
lemma windowSum_succ_span (X H : ℕ) (f : ℕ → β) :
    windowSum X (H+1) f = windowSum X H f + f (X + (H+1)) := by
  classical
  unfold windowSum
  simpa using windowSumN_succ X (H+1) f

/-- Additivity over addition of functions. -/
lemma windowSumN_add (X N : ℕ) (f g : ℕ → β) :
    windowSumN X N (fun n => f n + g n)
  = windowSumN X N f + windowSumN X N g := by
  classical
  unfold windowSumN
  simp [Finset.sum_add_distrib]

/-- Specialization to `ℝ`: sum of the constant-one function. -/
@[simp] lemma windowSumN_const_one (X N : ℕ) :
    windowSumN X N (fun _ => (1 : ℝ)) = (N : ℝ) := by
  classical
  induction' N with N ih
  · simp [windowSumN]
  · simp [windowSumN]

@[simp] lemma windowSum_const_one (X H : ℕ) :
    windowSum X H (fun _ => (1 : ℝ)) = (H+1 : ℝ) := by
  classical
  simp [windowSum, windowSumN_const_one]

end Twin.Ledger
