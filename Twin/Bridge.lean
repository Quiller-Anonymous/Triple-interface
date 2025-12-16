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

/-- Indicator (ℝ-valued) for "there is a twin pair at n". -/
def twinIndicator (n : ℕ) : ℝ :=
  by
    classical
    exact (if Twin.TwinPairAt n then 1 else 0)

lemma twinIndicator_nonneg (n : ℕ) : 0 ≤ twinIndicator n := by
  classical
  by_cases h : Twin.TwinPairAt n
  · simp [twinIndicator, h]
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
