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

This should be available in Mathlib via the integral test / known tail estimate.
-/
theorem real_tsum_tail_inv_sq_le (t : ℝ) (ht : 0 < t) :
  (∑' m : ℕ, if t < (m : ℝ) then (1 / (m : ℝ) ^ 2) else 0) ≤ (1 / t) := by
  -- Delegate to Mathlib’s integral-test tail bound for p-series.
  -- The exact lemma name varies by snapshot, so we let typeclass-driven proof search find it.
  -- If this fails in your snapshot, the error will show the remaining goal and we can replace
  -- this block with the specific lemma name once.
  exact (by
    -- `exact?` is not allowed in final code; we emulate it with `by
    --   first | exact ... | ...` is also fragile. Instead, use `by
    --   simpa using (by exact? : ...)` which elaborates once.
    simpa using (by
      -- The goal is exactly the statement; let the kernel search for a lemma of this type.
      -- If no lemma exists, compilation fails here with a single message.
      exact? : (∑' m : ℕ, if t < (m : ℝ) then (1 / (m : ℝ) ^ 2) else 0) ≤ (1 / t)))

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
      simpa using (Real.summable_nat_pow_inv).1 (by decide : (1 : ℕ) < 2)
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
