/-
  Twin/PSB_OnWindow.lean
  PSB assembly using an ON-WINDOW pointwise hypothesis.
-/
import Mathlib
import Twin.Kernel
import Twin.Bridge
import Twin.Ledger

noncomputable section
open scoped BigOperators

namespace Twin.PSB

/-- Pull scalar out of a finite sum (proved by induction to avoid lemma-name drift). -/
lemma sum_const_mul {α} [DecidableEq α] (s : Finset α) (c : ℝ) (f : α → ℝ) :
    s.sum (fun a => c * f a) = c * s.sum f := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha ih
    simp [ha, ih, mul_add]

/-- If the pointwise inequality holds for every `k ≤ H` in the window,
    then the window sum satisfies the assembled lower bound. -/
theorem assemble_lower_bound_onWindow
    (X H : ℕ) {L E : ℕ → ℝ} {c : ℝ}
    (hpt :
      ∀ k : ℕ, k ≤ H →
        c * L (X + k) - E (X + k)
          ≤ Twin.Kernel.J H k * Twin.Bridge.twinIndicator (X + k))
  :
    Twin.Ledger.windowSum X H
        (fun n => Twin.Kernel.J H (n - X) * Twin.Bridge.twinIndicator n)
      ≥ c * Twin.Ledger.windowSum X H L
        -   Twin.Ledger.windowSum X H E := by
  classical
  set S := Finset.range (H+1)
  -- Turn "k ≤ H" into membership in S = {0,…,H}.
  have hptS :
      ∀ k ∈ S,
        c * L (X + k) - E (X + k)
          ≤ Twin.Kernel.J H k * Twin.Bridge.twinIndicator (X + k) := by
    intro k hk; exact hpt k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  -- Sum the pointwise inequality over k = 0..H.
  have hsum := Finset.sum_le_sum (by intro k hk; exact hptS k hk)
  -- Simplify the LHS to c * Σ L - Σ E.
  have lhs_simp :
      S.sum (fun k => c * L (X + k) - E (X + k))
        = c * S.sum (fun k => L (X + k))
          -   S.sum (fun k => E (X + k)) := by
    simp [Finset.sum_sub_distrib, sum_const_mul]
  -- Simplify RHS using (X+k) - X = k.
  have rhs_simp :
      S.sum (fun k => Twin.Kernel.J H ((X + k) - X) * Twin.Bridge.twinIndicator (X + k))
        = S.sum (fun k => Twin.Kernel.J H k * Twin.Bridge.twinIndicator (X + k)) := by
    refine Finset.sum_congr rfl (by intro k hk; simp)
  -- Convert to the exact inequality direction we need:
  -- from  cΣL - ΣE ≤ Σ(J⋅ind)  to  Σ(J⋅ind) ≥ cΣL - ΣE.
  have hmain :
      S.sum (fun k => Twin.Kernel.J H k * Twin.Bridge.twinIndicator (X + k))
        ≥ c * S.sum (fun k => L (X + k))
          -   S.sum (fun k => E (X + k)) := by
    -- start with hsum and rewrite both sides
    have h := hsum
    -- h : (sum (c*L - E)) ≤ (sum (J⋅ind))
    -- rewrite to the target form
    rw [lhs_simp] at h
    exact le_of_lt (lt_of_le_of_lt h (lt_add_one _)) |> fun _ => h
  -- Conclude in window-sum notation.
  unfold Twin.Ledger.windowSum Twin.Ledger.windowSumN
  simpa [S] using hmain

end Twin.PSB
