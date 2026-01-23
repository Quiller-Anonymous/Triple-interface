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
  simpa using div_le_div_of_nonneg_left hC2 hH1 hH

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
  unfold margin
  have hmax : max Sch1.H 1 ≤ max Sch2.H 1 := max_le_max hH le_rfl
  have hmax_pos : 0 < max Sch1.H 1 :=
    lt_of_lt_of_le hHpos (le_max_left _ _)
  have tH : L.C2 / max Sch2.H 1 ≤ L.C2 / max Sch1.H 1 :=
    div_le_div_of_nonneg_left L.hC2 hmax_pos hmax
  have tB : L.C3 * Real.exp (-(Sch2.B)) ≤ L.C3 * Real.exp (-(Sch1.B)) := by
    exact mul_le_mul_of_nonneg_left (exp_neg_mono hB) L.hC3
  have tH' : L.C1 * εH + L.C2 / max Sch2.H 1 ≤ L.C1 * εH + L.C2 / max Sch1.H 1 :=
    add_le_add_left tH (L.C1 * εH)
  have tAll :
      L.C1 * εH + L.C2 / max Sch2.H 1 + L.C3 * Real.exp (-(Sch2.B))
        ≤ L.C1 * εH + L.C2 / max Sch1.H 1 + L.C3 * Real.exp (-(Sch1.B)) :=
    add_le_add tH' tB
  simpa [ge_iff_le] using sub_le_sub_left tAll c0

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
