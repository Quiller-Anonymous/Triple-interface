import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
Finite-dimensional Cauchy–Schwarz / Chebyshev helper lemmas for `Finset` sums.

We use these to pass from a sum to a sum-of-squares bound in the deterministic large-sieve
plumbing (TeX Step 3/4), before any analytic estimates are applied.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

/-- `‖∑ x_i‖² ≤ card(s) * ∑ ‖x_i‖²` (finite Cauchy–Schwarz). -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq
    {ι E : Type} [DecidableEq ι] [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  -- First bound by the square of the sum of norms.
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
    simpa using (norm_sum_le (s := s) (f := f))
  have hsq : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
    have hmul :
        ‖∑ i ∈ s, f i‖ * ‖∑ i ∈ s, f i‖ ≤ (∑ i ∈ s, ‖f i‖) * (∑ i ∈ s, ‖f i‖) := by
      exact mul_le_mul hnorm hnorm (by positivity) (by positivity)
    simpa [pow_two] using hmul
  -- Apply the real `Finset` inequality `(∑ a_i)^2 ≤ card * ∑ a_i^2`.
  have hcs :
      (∑ i ∈ s, ‖f i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (‖f i‖) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖))
  exact hsq.trans hcs

end LargeSieve

end
end TypeII
end Engines
end SSU
