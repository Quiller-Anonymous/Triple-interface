/-
  Twin/Bridge.lean
  From positive localized twin mass to an actual twin pair in the window.
  (Purely algebraic; no analysis, no admits.)
-/
import Mathlib
import Twin.Windows
import Twin.Kernel
import Twin.Rep

noncomputable section
open scoped BigOperators

namespace Twin.Bridge

/-- Log-weighted indicator (ℝ-valued) for "there is a twin pair at n".

This matches the analytic normalization of the von Mangoldt weights:
heuristically, each twin pair contributes ≍ `(log n)^2`, so the average size of
this function over `[1..X]` is ≍ a constant. -/
def twinIndicator (n : ℕ) : ℝ :=
  by
    classical
    exact
      if h : Twin.TwinPairAt n then
        Real.log (n : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)
      else
        0

lemma twinIndicator_nonneg (n : ℕ) : 0 ≤ twinIndicator n := by
  classical
  by_cases h : Twin.TwinPairAt n
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have hn1' : 1 ≤ n := le_trans (by decide : 1 ≤ 2) h.1.two_le
      exact_mod_cast hn1'
    have hn2 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      have hn2' : 1 ≤ n + 2 := le_trans (by decide : 1 ≤ 2) h.2.two_le
      exact_mod_cast hn2'
    have hlog1 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hlog2 : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := Real.log_nonneg hn2
    have : 0 ≤ Real.log (n : ℝ) * Real.log ((n + 2 : ℕ) : ℝ) := mul_nonneg hlog1 hlog2
    simpa [twinIndicator, h] using this
  · simp [twinIndicator, h]

/-- Localized twin mass in the window `[X, X+H]` using the kernel `J`. -/
def localizedTwinMass (X H : ℕ) : ℝ :=
  (Finset.range (H+1)).sum (fun k => Twin.Kernel.J H k * twinIndicator (X + k))

/-- If the localized twin mass is positive, then the window contains a twin pair. -/
theorem existsTwin_of_mass_pos
  {X H : ℕ} (hpos : 0 < localizedTwinMass X H) :
  Twin.ExistsTwinInWindow X H := by
  classical
  -- Suppose no twin pair appears in the window; derive a contradiction.
  by_contra hnone
  have term_zero :
      ∀ k ∈ Finset.range (H+1),
        Twin.Kernel.J H k * twinIndicator (X + k) = 0 := by
    intro k hk
    -- `k ≤ H` from membership
    have hk_le : k ≤ H := by
      have : k < H + 1 := Finset.mem_range.mp hk
      exact Nat.lt_succ_iff.mp this
    -- `(X+k)` lies in the window
    have hin : Twin.Windows.InWindow X H (X + k) :=
      Twin.Windows.of_mem_of_le (Nat.le_add_right _ _) (Nat.add_le_add_left hk_le _)
    -- Therefore `(X+k)` is not a twin start (else we’d violate `hnone`)
    have notpair : ¬ Twin.TwinPairAt (X + k) := by
      intro hpair
      exact hnone ⟨X + k, hin, hpair⟩
    -- The indicator at `X+k` is zero; hence the summand is zero.
    simp [twinIndicator, notpair]  -- `J * 0 = 0`
  -- Sum of zeros is zero, contradicting `hpos`.
  have : localizedTwinMass X H = 0 := by
    unfold localizedTwinMass
    refine Finset.sum_eq_zero ?allZero
    -- every term is zero
    intro k hk; exact term_zero k hk
  exact lt_irrefl 0 (this ▸ hpos)

end Twin.Bridge
