/-
  Twin/Kernel.lean
  A simple short-window kernel J_H : ℕ → ℝ with basic facts.
-/
import Mathlib

namespace Twin.Kernel

/-- Short-window kernel: indicator of `[0, H]` (as a function into ℝ). -/
def J (H n : ℕ) : ℝ := if n ≤ H then 1 else 0

@[simp] lemma J_of_le {H n : ℕ} (h : n ≤ H) : J H n = 1 := by
  simp [J, h]

@[simp] lemma J_of_gt {H n : ℕ} (h : H < n) : J H n = 0 := by
  unfold J; simp [Nat.not_le.mpr h]

@[simp] lemma J_zero {H : ℕ} : J H 0 = 1 := J_of_le (Nat.zero_le _)

lemma J_le_one {H n : ℕ} : J H n ≤ 1 := by
  unfold J; by_cases h : n ≤ H <;> simp [h]

lemma J_nonneg {H n : ℕ} : 0 ≤ J H n := by
  unfold J; by_cases h : n ≤ H <;> simp [h]

end Twin.Kernel
