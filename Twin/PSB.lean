/-
  Twin/PSB.lean
  Purely algebraic "PSB assembly" for windowed quantities.

  Core statement:
    If A(n) ≥ c * L(n) − E(n) pointwise, then over any short window [X, X+H]
      windowSum A ≥ c * windowSum L − windowSum E.

  This module is ANALYTIC-FREE: it relies only on finite-sum algebra.
  It depends on Twin.Ledger (windowed sums) and nothing else.
-/
import Mathlib
import Twin.Ledger

open scoped BigOperators

namespace Twin.PSB

/-- A robust `∑ c * f = c * ∑ f` for reals, by induction. -/
lemma sum_const_mul {α} [DecidableEq α] (s : Finset α) (c : ℝ) (f : α → ℝ) :
    s.sum (fun a => c * f a) = c * s.sum f := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    simp [ha, ih, mul_add, add_comm, add_left_comm, add_assoc]

/-- Monotonicity of windowed sums under pointwise inequality. -/
lemma windowSum_mono_of_pointwise
    (X H : ℕ) (a b : ℕ → ℝ)
    (h : ∀ n, a n ≤ b n) :
    Twin.Ledger.windowSum X H a ≤ Twin.Ledger.windowSum X H b := by
  classical
  -- windowSum X H f = ∑_{k=0}^H f (X+k)
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  -- use explicit Finset.sum (no binder macro)
  set S := Finset.range (H+1)
  change S.sum (fun k => a (X + k)) ≤ S.sum (fun k => b (X + k))
  refine Finset.sum_le_sum (fun k hk => ?_)
  exact h (X + k)

/--
**PSB assembly (windowed form).**
If we have a *pointwise* lower bound
`A n ≥ c * L n - E n` for all `n`, then summing over the window `[X, X+H]` yields
`windowSum X H A ≥ c * windowSum X H L - windowSum X H E`.
-/
theorem assemble_lower_bound
    (X H : ℕ) (A L E : ℕ → ℝ) (c : ℝ)
    (hpt : ∀ n, c * L n - E n ≤ A n) :
    Twin.Ledger.windowSum X H A
      ≥ c * Twin.Ledger.windowSum X H L
        -   Twin.Ledger.windowSum X H E := by
  classical
  -- Work with an explicit finite set S = {0,…,H}
  set S := Finset.range (H+1)
  have hsum :
      S.sum (fun k => (c * L (X + k) - E (X + k)))
      ≤ S.sum (fun k => A (X + k)) :=
    Finset.sum_le_sum (by intro k hk; exact hpt (X + k))
  -- Split the left sum and pull out the scalar `c`
  have hleft :
      S.sum (fun k => (c * L (X + k) - E (X + k)))
        = c * S.sum (fun k => L (X + k))
          -   S.sum (fun k => E (X + k)) := by
    have := Finset.sum_sub_distrib
              (s := S) (f := fun k => c * L (X + k)) (g := fun k => E (X + k))
    -- rewrite the first term using `sum_const_mul`
    simpa [this, sum_const_mul S c (fun k => L (X + k))]

  -- Rephrase in terms of `windowSum`
  have hsum' :
      c * Twin.Ledger.windowSum X H L
        -   Twin.Ledger.windowSum X H E
      ≤ Twin.Ledger.windowSum X H A := by
    simpa [Twin.Ledger.windowSum, Twin.Ledger.windowSumN, hleft, S]
      using hsum

  -- flip inequality sides
  exact hsum'

/-- Averaged version: multiply both sides by the nonnegative scalar `1/(H+1)`. -/
theorem assemble_avg_lower_bound
    (X H : ℕ) (A L E : ℕ → ℝ) (c : ℝ)
    (hpt : ∀ n, c * L n - E n ≤ A n) :
    (1 : ℝ) / (H+1) * Twin.Ledger.windowSum X H A
      ≥ (1 : ℝ) / (H+1) * (c * Twin.Ledger.windowSum X H L
                            -     Twin.Ledger.windowSum X H E) := by
  classical
  have base := assemble_lower_bound X H A L E c hpt
  have hden : 0 < (H+1 : ℝ) := by exact_mod_cast (Nat.succ_pos H)
  have hscalar : 0 ≤ (1 : ℝ) / (H+1) := div_nonneg (by norm_num) (le_of_lt hden)
  exact (mul_le_mul_of_nonneg_left base hscalar)

end Twin.PSB
