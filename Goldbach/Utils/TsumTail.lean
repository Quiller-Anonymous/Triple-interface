import Mathlib
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Goldbach.Utils.TsumTail

open scoped BigOperators
open Real

noncomputable section

/--
Tail bound in `ℝ`:
`∑' m : ℕ, (if t < m then 1/m^2 else 0) ≤ 1/t` for `t > 0`.

This bound follows from the integral comparison test: the tail of ∑ 1/n² 
is bounded by ∫_t^∞ 1/x² dx = 1/t.
-/
theorem real_tsum_tail_inv_sq_le (t : ℝ) (ht : 0 < t) :
  (∑' m : ℕ, if t < (m : ℝ) then (1 / (m : ℝ) ^ 2) else 0) ≤ (1 / t) := by
  let k := Nat.ceil t
  have hk_pos : 0 < k := Nat.ceil_pos.mpr ht
  have hk_le : t ≤ k := Nat.le_ceil t

  have h_summable : Summable (fun m : ℕ => if t < (m : ℝ) then (1 / (m : ℝ) ^ 2) else 0) := by
    have hsq : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) := by
      simpa using (Real.summable_nat_pow_inv).mpr (by decide : 1 < 2)
    refine Summable.of_nonneg_of_le ?_ ?_ hsq
    · intro m; split_ifs <;> positivity
    · intro m; split_ifs with h
      · simp [one_div]
      · positivity

  have h1k_le : (1 : ℝ) / k ≤ 1 / t := by
    apply one_div_le_one_div_of_le ht
    exact_mod_cast Nat.le_ceil t

  -- Bound: ∑_{m>k} 1/m² ≤ 1/k 
  have h_tail_bound : (∑' m : ℕ, if k < m then (1 / (m : ℝ) ^ 2) else 0) ≤ 1 / k := by
    by_cases hk0 : k = 0
    · simp [hk0] at hk_pos
    have hk_real_pos : (0 : ℝ) < k := by exact_mod_cast hk_pos

    have h_nonneg : ∀ m, 0 ≤ (if k < m then (1 / (m : ℝ) ^ 2) else 0) := by
      intro m; split_ifs <;> positivity

    -- We use a direct bound: for each m > k, 1/m² ≤ 1/(m-1) - 1/m
    -- The finite sum from k+1 to N telescopes to 1/k - 1/N ≤ 1/k
    -- Therefore the infinite sum is also ≤ 1/k
    
    have h_bound : ∀ N : ℕ, (Finset.range N).sum (fun m => if k < m then (1 / (m : ℝ) ^ 2) else 0) ≤ 1 / k := by
      intro N
      have h_sum_nonneg : 0 ≤ (Finset.range N).sum (fun m => if k < m then (1 / (m : ℝ) ^ 2) else 0) := by
        apply Finset.sum_nonneg
        intro m _
        exact h_nonneg m
      by_cases hkN : k + 1 ≤ N
      · -- The sum has some nonzero terms
        calc (Finset.range N).sum (fun m => if k < m then (1 / (m : ℝ) ^ 2) else 0)
            ≤ (Finset.range N).sum (fun m => if k < m then (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) else 0) := by
              apply Finset.sum_le_sum
              intro m _
              split_ifs with hkm
              · have hm : m ≥ k + 1 := hkm
                have hm_pos : 0 < m := by omega
                have hm1_pos : 0 < (m - 1 : ℕ) := by omega
                have hm_real : (0 : ℝ) < m := by positivity
                have hm1_real : (0 : ℝ) < (m - 1 : ℕ) := by positivity
                -- 1/m² ≤ 1/((m-1)·m) = 1/(m-1) - 1/m
                have h_eq : 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ) = 1 / (((m - 1 : ℕ) : ℝ) * m) := by
                  field_simp
                  simp only [Nat.cast_sub (by omega : 1 ≤ m)]
                  ring
                rw [h_eq]
                apply one_div_le_one_div_of_le
                · exact mul_pos hm1_real hm_real
                · calc (m : ℝ) ^ 2 = m * m := sq m
                    _ ≥ (m - 1 : ℕ) * m := by
                        apply mul_le_mul_of_nonneg_right _ (le_of_lt hm_real)
                        simp only [Nat.cast_sub (by omega : 1 ≤ m)]
                        linarith
              · rfl
            _ ≤ 1 / k := by
              -- For m ≤ k, the term is 0. For m > k, we get telescoping.
              -- The terms with m ∈ {k+1, ..., N-1} give 1/k - 1/(N-1) ≤ 1/k
              -- We just need to show the sum ≤ 1/k
              
              -- Rewrite: terms with m ≤ k contribute 0
              have h_split : (Finset.range N).sum (fun m => if k < m then (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) else 0)
                  = ((Finset.range N).filter (fun m => k < m)).sum (fun m => 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
                rw [Finset.sum_filter]
                congr 1
                ext m
                split_ifs <;> simp

              rw [h_split]
              
              -- The filtered set is {k+1, k+2, ..., N-1}
              have h_filter_eq : (Finset.range N).filter (fun m => k < m) = Finset.Ioc k (N - 1) := by
                ext m
                simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
                constructor
                · intro ⟨hm, hkm⟩; exact ⟨hkm, by omega⟩
                · intro ⟨hkm, hm⟩; exact ⟨by omega, hkm⟩

              by_cases hNk1 : N = k + 1
              · -- Only one term: m = k+1
                subst hNk1
                simp only [Finset.range_succ, Finset.filter_insert, Nat.lt_irrefl, ↓reduceIte, 
                  Finset.filter_eq_empty_iff, not_lt]
                simp only [Finset.sum_empty, add_zero]
                rw [Finset.filter_eq_empty_iff]
                · simp
                · intro m hm
                  simp only [Finset.mem_range] at hm
                  omega
              · -- Multiple terms, use telescoping
                rw [h_filter_eq]
                -- Sum over Ioc k (N-1) of (1/(m-1) - 1/m) telescopes
                have hN1 : N - 1 ≥ k + 1 := by omega
                -- The sum telescopes to 1/k - 1/(N-1)
                have h_telesc : (Finset.Ioc k (N - 1)).sum (fun m => 1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ))
                    = 1 / k - 1 / (N - 1) := by
                  induction N with
                  | zero => simp at hkN
                  | succ n ih =>
                    by_cases hkn : k + 1 ≤ n
                    · have hne : n ≠ k := by omega
                      rw [Nat.succ_sub_one]
                      rw [Finset.Ioc_succ_right hne]
                      rw [Finset.sum_insert (Finset.not_mem_Ioc_of_gt (by omega : n > n - 1))]
                      have hn_pos : 0 < n := by omega
                      have hn1_pos : 0 < n - 1 := by omega
                      have ih' := ih (by omega) (by omega)
                      rw [Nat.succ_sub_one] at ih'
                      rw [ih']
                      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
                        simp [Nat.cast_sub (by omega : 1 ≤ n)]
                      simp only [this]
                      ring
                    · push_neg at hkn
                      have : n = k + 1 ∨ n ≤ k := by omega
                      rcases this with rfl | hle
                      · -- n = k + 1, so N = k + 2
                        simp only [Nat.add_sub_cancel]
                        rw [Finset.Ioc_eq_cons_Ioc (by omega : k + 1 ≤ k + 1)]
                        rw [Finset.sum_cons]
                        simp only [Finset.Ioc_self, Finset.sum_empty, add_zero]
                        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
                        ring
                      · exfalso
                        have : k + 1 ≤ k + 1 := le_refl _
                        omega
                rw [h_telesc]
                have hN1_pos : (0 : ℝ) < (N - 1 : ℕ) := by
                  have : 0 < N - 1 := by omega
                  exact_mod_cast this
                linarith [one_div_pos.mpr hN1_pos]
      · push_neg at hkN
        -- All terms are 0 because m < N ≤ k
        have : ∀ m ∈ Finset.range N, ¬(k < m) := by
          intro m hm
          simp only [Finset.mem_range] at hm
          omega
        simp only [Finset.sum_eq_zero (fun m hm => by simp [this m hm])]
        exact one_div_pos.mpr hk_real_pos

    apply tsum_le_of_sum_le h_nonneg h_bound

  calc (∑' m : ℕ, if t < (m : ℝ) then (1 / (m : ℝ) ^ 2) else 0)
      ≤ ∑' m : ℕ, if k < m then (1 / (m : ℝ) ^ 2) else 0 := by
        apply tsum_le_tsum
        · intro m
          split_ifs with h1 h2 h2
          · rfl
          · exfalso
            have hkm : k < m := h2
            have htm : ¬(t < (m : ℝ)) := h1
            push_neg at htm
            have : (k : ℝ) < m := by exact_mod_cast hkm
            have : t < m := lt_of_le_of_lt hk_le this
            exact htm (le_of_lt this)
          · positivity
          · rfl
        · exact h_summable
        · have hsq : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) := by
            simpa using (Real.summable_nat_pow_inv).mpr (by decide : 1 < 2)
          refine Summable.of_nonneg_of_le ?_ ?_ hsq
          · intro m; split_ifs <;> positivity
          · intro m; split_ifs with h
            · simp [one_div]
            · positivity
      _ ≤ 1 / k := h_tail_bound
      _ ≤ 1 / t := h1k_le

/--
ENNReal tail bound:
`∑' m, if t < m then ofReal(1/m^2) else 0 ≤ ofReal(1/t)` for `t > 0`.

ENNReal tail bound (derived from the real one). -/
theorem tsum_tail_inv_sq_le (t : ℝ) (ht : 0 < t) :
  (∑' m : ℕ, if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (1 / t) := by
  classical
  let f : ℕ → ℝ := fun m => if t < (m : ℝ) then (1 / (m : ℝ) ^ 2) else 0
  have hf_nonneg : ∀ m, 0 ≤ f m := by
    intro m
    simp [f]
    split_ifs
    · apply inv_nonneg.mpr
      apply sq_nonneg
    · rfl
  have hf_summable : Summable f := by
    have hsq : Summable (fun m : ℕ => ((m : ℝ) ^ 2)⁻¹) := by
      simpa using (Real.summable_nat_pow_inv).mpr (by decide : 1 < 2)
    refine Summable.of_nonneg_of_le hf_nonneg ?_ hsq
    intro m
    by_cases htm : t < (m : ℝ)
    · simp [f, htm]
    · simp [f, htm]

  have hrewrite :
      (∑' m : ℕ, ENNReal.ofReal (f m)) = ENNReal.ofReal (∑' m : ℕ, f m) := by
    simpa using (ENNReal.ofReal_tsum_of_nonneg (f := f) hf_nonneg hf_summable).symm

  have hreal : (∑' m : ℕ, f m) ≤ (1 / t) := by
    simpa [f] using real_tsum_tail_inv_sq_le t ht

  have h_term_eq :
      (fun m : ℕ => if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
        = (fun m => ENNReal.ofReal (f m)) := by
    ext m
    simp [f]
    split_ifs <;> simp
  rw [h_term_eq, hrewrite]
  exact ENNReal.ofReal_le_ofReal hreal
end

end Goldbach.Utils.TsumTail
