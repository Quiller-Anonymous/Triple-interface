/-
  Twin/WindowCS.lean
  -------------------
  Small wrappers for the windowed Cauchy–Schwarz identities used in the Twin
  pipeline.  These re-export the actual Mathlib-backed lemmas and specialize
  the algebraic identities we formerly treated as axioms.
-/
import Twin.LedgerExtra

noncomputable section
open Real

namespace Twin
namespace WindowCS

export Twin.LedgerExtra
  ( window_l1_le_sqrt_span_mul_window_l2
    sqrt_span_mul_sqrt_span_div9 )

/-- Auxiliary identity: `√((H+1)/9) = √(H+1)/3` for natural spans. -/
lemma sqrt_span_div9 (H : ℕ) :
    Real.sqrt (((↑H : ℝ) + 1) / 9)
      = Real.sqrt ((↑H : ℝ) + 1) / 3 := by
  have hmul := Twin.LedgerExtra.sqrt_span_mul_sqrt_span_div9 H
  have hpos : 0 < (↑H : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (↑H : ℝ) := by exact_mod_cast Nat.zero_le H
    exact add_pos_of_nonneg_of_pos this (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt ((↑H : ℝ) + 1) := Real.sqrt_pos.2 hpos
  have hsqrt_ne : Real.sqrt ((↑H : ℝ) + 1) ≠ 0 := ne_of_gt hsqrt_pos
  have h_div :=
    congrArg (fun t : ℝ => t / Real.sqrt ((↑H : ℝ) + 1)) hmul
  have h_left :
      (Real.sqrt ((↑H : ℝ) + 1) * Real.sqrt (((↑H : ℝ) + 1) / 9))
        / Real.sqrt ((↑H : ℝ) + 1)
        = Real.sqrt (((↑H : ℝ) + 1) / 9) := by
    simpa using
      (mul_div_cancel_left₀
        (Real.sqrt ((↑H : ℝ) + 1))
        (Real.sqrt (((↑H : ℝ) + 1) / 9))
        hsqrt_ne)
  have hN_div :
      ((↑H : ℝ) + 1) / Real.sqrt ((↑H : ℝ) + 1)
        = Real.sqrt ((↑H : ℝ) + 1) := by
    simpa using
      (mul_div_cancel_left₀
        (Real.sqrt ((↑H : ℝ) + 1))
        (Real.sqrt ((↑H : ℝ) + 1))
        hsqrt_ne)
  have h_right :
      ((↑H : ℝ) + 1) / 3 / Real.sqrt ((↑H : ℝ) + 1)
        = Real.sqrt ((↑H : ℝ) + 1) / 3 := by
    have hswap :
        ((↑H : ℝ) + 1) / 3 / Real.sqrt ((↑H : ℝ) + 1)
          = (((↑H : ℝ) + 1) / Real.sqrt ((↑H : ℝ) + 1)) / 3 := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa [hswap, hN_div]
  simpa [h_left, h_right] using h_div

end WindowCS
end Twin
