import Mathlib

/-!
# Tail estimate for `∑' m, 1 / m^2`

Mathematically correct statement:
for `t > 0`, the tail of `∑' m, 1 / m^2` beyond `t` is bounded by `2 / t`.

This is **conventional analysis** (p-series tail). We keep it isolated here so all analytic
“literature facts” are in one place.
-/

namespace Goldbach.Utils

open scoped BigOperators

/-- Tail bound for the inverse-square series.

For `t > 0`,
`∑' m : ℕ, if t < (m : ℝ) then ofReal(1/m^2) else 0 ≤ ofReal(2/t)` (in `ℝ≥0∞`).
-/
theorem tsum_tail_inv_sq_le (t : ℝ) (ht : 0 < t) :
    (∑' m : ℕ,
        if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) ≤
      ENNReal.ofReal (2 / t)
  := by
  classical
  -- Work in ℝ first, then push through `ENNReal.ofReal`.
  let f : ℕ → ℝ := fun m => if t < (m : ℝ) then (m ^ 2 : ℝ)⁻¹ else 0
  have hf_nonneg : ∀ m, 0 ≤ f m := by
    intro m
    by_cases h : t < (m : ℝ)
    · simp [f, h]
    · simp [f, h]

  -- Use the standard p-series tail estimate on the range `Ioo ⌊t⌋₊ n`.
  let k : ℕ := ⌊t⌋₊
  have ht_le : (k : ℝ) ≤ t := Nat.floor_le (show 0 ≤ t by linarith [ht])

  have hsum_range_le : ∀ n, (∑ m ∈ Finset.range n, f m) ≤ 2 / (k + 1 : ℝ) := by
    intro n
    let p : ℕ → Prop := fun m => t < (m : ℝ)
    have hsum_filter :
        (∑ m ∈ Finset.range n, f m) =
          ∑ m ∈ (Finset.range n).filter p, (m ^ 2 : ℝ)⁻¹ := by
      -- `sum_filter` rewrites a sum of an `if` into a sum over a filtered finset.
      simpa [f, p] using
        (Finset.sum_filter (s := Finset.range n) (p := p) (f := fun m => (m ^ 2 : ℝ)⁻¹)).symm

    have hsubset : (Finset.range n).filter p ⊆ Finset.Ioo k n := by
      intro m hm
      have hm_range : m ∈ Finset.range n := (Finset.mem_filter.mp hm).1
      have hm_p : p m := (Finset.mem_filter.mp hm).2
      have hm_lt_n : m < n := Finset.mem_range.mp hm_range
      have hk_lt_m : k < m := by
        have : (k : ℝ) < (m : ℝ) := lt_of_le_of_lt ht_le hm_p
        exact_mod_cast this
      simp [Finset.mem_Ioo, hk_lt_m, hm_lt_n]

    calc
      (∑ m ∈ Finset.range n, f m)
          = ∑ m ∈ (Finset.range n).filter p, (m ^ 2 : ℝ)⁻¹ := hsum_filter
      _ ≤ ∑ m ∈ Finset.Ioo k n, (m ^ 2 : ℝ)⁻¹ := by
        -- enlarge the finset: terms are nonnegative
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro m _hm _hm_not
        positivity
      _ ≤ 2 / (k + 1 : ℝ) := by
        simpa using (sum_Ioo_inv_sq_le (α := ℝ) k n)

  have hf_summable : Summable f :=
    summable_of_sum_range_le hf_nonneg (by simpa using hsum_range_le)

  have htsum_le_k : (∑' m, f m) ≤ 2 / (k + 1 : ℝ) :=
    Real.tsum_le_of_sum_range_le hf_nonneg (by simpa using hsum_range_le)

  have hk1_pos : 0 < (k + 1 : ℝ) := by positivity
  have ht_lt_k1 : t < (k + 1 : ℝ) := by
    -- `lt_floor_add_one` gives `t < (⌊t⌋₊ : ℝ) + 1`.
    simpa [k, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Nat.lt_floor_add_one t)
  have ht_le_k1 : t ≤ (k + 1 : ℝ) := le_of_lt ht_lt_k1

  have hk_le_t : (2 : ℝ) / (k + 1 : ℝ) ≤ 2 / t := by
    -- If `t ≤ k+1` and `t > 0`, then `2/(k+1) ≤ 2/t`.
    simpa [div_eq_mul_inv] using
      (div_le_div_of_nonneg_left (a := (2 : ℝ)) (b := (k + 1 : ℝ)) (c := t) (by positivity) ht ht_le_k1)

  have htsum_le : (∑' m, f m) ≤ 2 / t := htsum_le_k.trans hk_le_t

  -- Now convert back to `ℝ≥0∞`.
  have hENN_point :
      (fun m : ℕ => if t < (m : ℝ) then ENNReal.ofReal ((m ^ 2 : ℝ)⁻¹) else 0)
        = fun m => ENNReal.ofReal (f m) := by
    funext m
    by_cases h : t < (m : ℝ)
    · simp [f, h]
    · simp [f, h]

  calc
    (∑' m : ℕ, if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
        = ∑' m : ℕ, if t < (m : ℝ) then ENNReal.ofReal ((m ^ 2 : ℝ)⁻¹) else 0 := by
          refine tsum_congr ?_
          intro m
          by_cases h : t < (m : ℝ) <;> simp [h, one_div]
    _ = ∑' m : ℕ, ENNReal.ofReal (f m) := by
          simpa using congrArg (fun g => ∑' m : ℕ, g m) hENN_point
    _ = ENNReal.ofReal (∑' m : ℕ, f m) := by
          simpa using (ENNReal.ofReal_tsum_of_nonneg hf_nonneg hf_summable).symm
    _ ≤ ENNReal.ofReal (2 / t) := ENNReal.ofReal_le_ofReal htsum_le

end Goldbach.Utils
