/-
  Twin/AO.lean
  Deterministic occupancy (AO) as windowed averages over short ranges.
-/
import Mathlib
import Twin.Ledger

noncomputable section
open scoped BigOperators

namespace Twin.AO

/-- Windowed average over span `H`:  (1/(H+1)) * ∑_{k=0}^H f (X+k). -/
def windowAvg (X H : ℕ) (f : ℕ → ℝ) : ℝ :=
  (1 : ℝ) / (H+1) * Twin.Ledger.windowSum X H f

@[simp] lemma windowAvg_const_one (X H : ℕ) :
    windowAvg X H (fun _ => (1 : ℝ)) = 1 := by
  classical
  -- Just let `simp` use the nonzero witness to rewrite (H+1)⁻¹ * (H+1) = 1
  have hpos : 0 < (H+1 : ℝ) := by exact_mod_cast (Nat.succ_pos H)
  have hne  : (H+1 : ℝ) ≠ 0 := ne_of_gt hpos
  simp [windowAvg, Twin.Ledger.windowSum_const_one, one_div, hne]

lemma windowAvg_add (X H : ℕ) (f g : ℕ → ℝ) :
    windowAvg X H (fun n => f n + g n)
  = windowAvg X H f + windowAvg X H g := by
  classical
  unfold windowAvg
  simp [Twin.Ledger.windowSum, Twin.Ledger.windowSumN,
        Finset.sum_add_distrib, mul_add]

lemma windowAvg_nonneg
    (X H : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ Finset.range (H+1), 0 ≤ f (X + k)) :
    0 ≤ windowAvg X H f := by
  classical
  unfold windowAvg
  -- Nonnegativity of the sum
  have hsum : 0 ≤ (Finset.range (H+1)).sum (fun k => f (X + k)) :=
    Finset.sum_nonneg (by intro k hk; exact hf k hk)
  -- Nonnegativity of the scalar (1/(H+1))
  have hden0 : 0 < (H+1 : ℝ) := by exact_mod_cast (Nat.succ_pos H)
  have hscalar : 0 ≤ (1 : ℝ) / (H+1) := div_nonneg (by norm_num) (le_of_lt hden0)
  exact mul_nonneg hscalar hsum

end Twin.AO
