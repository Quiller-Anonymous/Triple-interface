/-
  Simple monotonicity lemmas for the ledger terms: C2/H and C3 * e^{-B}.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import AltZeta.Core

noncomputable section
open Real AltZeta

namespace AltZeta

lemma inv_le_inv_of_le_pos {a b : ℝ} (ha : 0 < a) (h : a ≤ b) : b ≠ 0 := by
  exact ne_of_gt (lt_of_lt_of_le ha h)

lemma inv_mono_decr {a b : ℝ} (ha : 0 < a) (h : a ≤ b) :
    1 / b ≤ 1 / a := by
  have hbpos : 0 < b := lt_of_lt_of_le ha h
  have := one_div_le_one_div_of_le ha h
  simpa [one_div] using this

/-- If `H₂ ≥ H₁ > 0` then `C2/H₂ ≤ C2/H₁`. -/
lemma C2_over_H_mono {C2 H1 H2 : ℝ}
  (hC2 : 0 ≤ C2) (hH1 : 0 < H1) (hH : H1 ≤ H2) :
  C2 / H2 ≤ C2 / H1 := by
  have h' := inv_mono_decr hH1 hH
  have hC2' : 0 ≤ C2 := hC2
  have : C2 * (1 / H2) ≤ C2 * (1 / H1) := by
    exact mul_le_mul_of_nonneg_left h' hC2'
  simpa [one_div, div_eq_mul_one_div, mul_comm, mul_left_comm, mul_assoc] using this

/-- If `B₂ ≥ B₁` then `e^{-B₂} ≤ e^{-B₁}`. -/
lemma exp_neg_mono {B1 B2 : ℝ} (h : B1 ≤ B2) :
  Real.exp (-B2) ≤ Real.exp (-B1) := by
  have : -B2 ≤ -B1 := by simpa using (neg_le_neg h)
  exact Real.exp_le_exp.mpr this

/-- Monotonicity for the margin when increasing H or B (others fixed). -/
lemma margin_mono_increase_H_B
  (c0 εH : ℝ) (L : Ledger) (Sch1 Sch2 : Schedule)
  (hH : Sch1.H ≤ Sch2.H) (hHpos : 0 < Sch1.H)
  (hB : Sch1.B ≤ Sch2.B) :
  margin c0 εH L Sch2 ≥ margin c0 εH L Sch1 := by
  -- Expand margins
  unfold margin
  -- Compare the `C2/H` term
  have tH : L.C2 / max Sch2.H 1 ≤ L.C2 / max Sch1.H 1 := by
    by_cases h1 : Sch1.H ≤ 1
    · -- then max Sch1.H 1 = 1, and max Sch2.H 1 ≥ 1, so inequality is trivial
      have h2 : 1 ≤ max Sch2.H 1 := by
        have : (1 : ℝ) ≤ 1 := le_rfl
        exact le_max_right _ _
      have : L.C2 / max Sch2.H 1 ≤ L.C2 / 1 := by
        have hc2 : 0 ≤ L.C2 := L.hC2
        have : (max Sch2.H 1) ≥ 1 := h2
        -- use C2/H ≤ C2/1 when H ≥ 1
        have := C2_over_H_mono (C2:=L.C2) (H1:=1) (H2:=max Sch2.H 1) hc2 (by decide : 0< (1:ℝ)) (by simpa using this)
        simpa using this
      simpa [max_eq_right h1, div_one] using this
    · -- Sch1.H > 1 or at least >0; use the previous lemma
      have hH1pos : 0 < max Sch1.H 1 := by
        have : 1 ≤ max Sch1.H 1 := by exact le_max_right _ _
        exact lt_of_le_of_lt this (by decide : (1:ℝ) < 2)
      have hmax : max Sch1.H 1 ≤ max Sch2.H 1 := by
        exact max_le_max hH (le_rfl)
      -- use C2/H monotonicity with H := max H 1
      have hc2 : 0 ≤ L.C2 := L.hC2
      have := C2_over_H_mono (C2:=L.C2) (H1:=max Sch1.H 1) (H2:=max Sch2.H 1) hc2
        (by exact lt_of_le_of_lt (le_max_right _ _) (by decide : (1:ℝ) < 2)) hmax
      simpa using this
  -- Compare the `C3 e^{-B}` term
  have tB : L.C3 * Real.exp (-(Sch2.B)) ≤ L.C3 * Real.exp (-(Sch1.B)) := by
    have hc3 : 0 ≤ L.C3 := L.hC3
    have hexp := exp_neg_mono hB
    exact mul_le_mul_of_nonneg_left hexp hc3
  -- Put it together: subtract both decreases from c0 - (C1 εH + ...)
  have : (L.C2 / max Sch2.H 1 + L.C3 * Real.exp (-(Sch2.B)))
         ≤ (L.C2 / max Sch1.H 1 + L.C3 * Real.exp (-(Sch1.B))) := by
    exact add_le_add tH tB
  -- Flip sign inside the big subtraction
  have := sub_le_sub_left this (c0 - (L.C1 * εH))
  simpa [margin, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

/-- Increasing the pin level `c₀` can only increase the margin (other inputs fixed). -/
lemma margin_mono_increase_c0 {c01 c02 εH : ℝ} (L : Ledger) (Sch : Schedule)
    (hc : c01 ≤ c02) :
    margin c01 εH L Sch ≤ margin c02 εH L Sch := by
  unfold margin
  have := add_le_add_right hc (-(L.C1 * εH + L.C2 / max Sch.H 1 + L.C3 * exp (-(Sch.B))))
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this

/-- Decreasing `ε_H` raises the margin (assuming the ledger constant `C1 ≥ 0`). -/
lemma margin_mono_decrease_eps {c0 ε1 ε2 : ℝ} (L : Ledger) (Sch : Schedule)
    (hε : ε2 ≤ ε1) :
    margin c0 ε2 L Sch ≥ margin c0 ε1 L Sch := by
  unfold margin
  have hprod : L.C1 * ε2 ≤ L.C1 * ε1 :=
    mul_le_mul_of_nonneg_left hε L.hC1
  have hsum :
      L.C1 * ε2 + (L.C2 / max Sch.H 1 + L.C3 * Real.exp (-(Sch.B)))
        ≤ L.C1 * ε1 + (L.C2 / max Sch.H 1 + L.C3 * Real.exp (-(Sch.B))) :=
    add_le_add_right hprod _
  have := sub_le_sub_left hsum c0
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this

end AltZeta
