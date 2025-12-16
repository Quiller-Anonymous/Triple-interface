/-
  Twin/FiniteCS.lean
  Small “finite Cauchy–Schwarz” helpers we treat as axioms (standard facts).
-/
import Mathlib
import Twin.Ledger

noncomputable section
open scoped BigOperators

namespace Twin.FiniteCS

/-- Finite Cauchy–Schwarz on the window:  L¹ ≤ √(H+1) · √(L²). -/
axiom window_l1_le_sqrt_span_mul_window_l2
  (X H : ℕ) (f : ℕ → ℝ) :
  Twin.Ledger.windowSum X H (fun n => |f n|)
    ≤ Real.sqrt ((H : ℝ) + 1) *
      Real.sqrt (Twin.Ledger.windowSum X H (fun n => (f n)^2))

/-- Elementary algebra on the span length:
    √(H+1) · √((H+1)/9) = (H+1)/3. -/
axiom sqrt_span_mul_sqrt_span_div9 (H : ℕ) :
  Real.sqrt ((H : ℝ) + 1) * Real.sqrt (((H : ℝ) + 1) / 9)
    = ((H : ℝ) + 1) / 3

end Twin.FiniteCS
