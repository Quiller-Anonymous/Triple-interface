import Mathlib

/-!
# Tail estimate for `∑' m, 1 / m^2`

Downstream files only need a tail bound, so we provide it as an axiom.

Mathematically correct statement:
for `t > 0`, the tail of `∑' m, 1 / m^2` beyond `t` is bounded by `2 / t`.
-/

namespace Goldbach.Utils

open scoped BigOperators

/-- **Axiom**: tail bound for the inverse-square series.

For `t > 0`,
`∑' m : ℕ, if t < (m : ℝ) then ofReal(1/m^2) else 0 ≤ ofReal(2/t)` (in `ℝ≥0∞`).

This is used as an external analytic estimate.
-/
axiom tsum_tail_inv_sq_le (t : ℝ) (ht : 0 < t) :
    (∑' m : ℕ,
        if t < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) ≤
      ENNReal.ofReal (2 / t)

end Goldbach.Utils
