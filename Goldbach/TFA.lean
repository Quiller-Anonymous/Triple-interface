import «Goldbach».Params
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Set Real

/-! # Time Frequency Analysis (TFA) -/

/--
Section 3.1: The Individual Arcs
"intervals of length ≈ 1/H centered at a/q"
-/
def BankArc (p : GoldbachParams) (X : ℝ) (a q : ℕ) : Set ℝ :=
  let H := H_scale p X
  Ioo ((a : ℝ) / q - 1 / (2 * H)) ((a : ℝ) / q + 1 / (2 * H))

/--
Helper: Disjointness of open intervals
-/
lemma disjoint_Ioo_of_dist_ge {a b r : ℝ} (h : |a - b| ≥ 2 * r) (hr : r > 0) :
    Disjoint (Ioo (a - r) (a + r)) (Ioo (b - r) (b + r)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false, not_and]
  intro h1_l h1_r h2_l
  have dist_x_a : |x - a| < r := abs_lt.mpr ⟨sub_lt_of_sub_lt h1_l, sub_lt_iff_lt_add.mpr h1_r⟩
  have dist_x_b : |x - b| < r := abs_lt.mpr ⟨sub_lt_of_sub_lt h2_l, sub_lt_iff_lt_add.mpr (by assumption)⟩
  linarith [abs_sub_comm a x, abs_add (a-x) (x-b)]

/--
**Verification 1: Bank Arc Disjointness**
This proves that gamma < 1/2 is the correct constraint.
-/
theorem Bank_Arcs_Disjoint_Proof (p : GoldbachParams) (X : ℝ) :
  let Q := Q_scale p X
  let H := H_scale p X
  (hX : 1 < H) →
  ∀ q1 a1 q2 a2,
    (1 ≤ q1 ∧ (q1 : ℝ) ≤ Q) → (1 ≤ q2 ∧ (q2 : ℝ) ≤ Q) →
    (1 ≤ a1 ∧ a1 < q1) → (1 ≤ a2 ∧ a2 < q2) →
    (Nat.Coprime a1 q1) → (Nat.Coprime a2 q2) →
    (a1/q1 ≠ a2/q2) →
    Disjoint (BankArc p X a1 q1) (BankArc p X a2 q2) :=
by
  intros Q H hH q1 a1 q2 a2 hq1 hq2 ha1 ha2 hcop1 hcop2 h_distinct
  let R := 1 / (2 * H)

  -- Farey spacing
  let c1 : ℝ := a1 / q1
  let c2 : ℝ := a2 / q2

  have dist_bound : |c1 - c2| ≥ 1 / (q1 * q2) := by
    rw [div_sub_div]; norm_cast; rw [abs_div, abs_sub_comm]; simp
    have : |(a2:ℤ)*q1 - a1*q2| ≥ 1 := by
      apply Int.abs_pos.mpr; intro z; apply h_distinct
      rw [sub_eq_zero] at z; field_simp; norm_cast at z ⊢; assumption
    gcongr
    norm_cast; linarith [hq1.1]; norm_cast; linarith [hq2.1]

  -- Using q ≤ Q
  have dist_lower_bound : |c1 - c2| ≥ 1 / Q^2 := by
    apply le_trans dist_bound
    apply one_div_le_one_div_of_le
    · apply mul_pos; linarith [p.h_gamma.1]; linarith [p.h_gamma.1]
    · apply mul_le_mul hq1.2 hq2.2; norm_cast; linarith [hq2.1]; linarith [hq1.1]

  -- Geometric Check: 1/Q^2 >= 1/H iff H^(1-2gamma) >= 1
  have gap_condition : 1 / Q^2 ≥ 1 / H := by
    dsimp [Q_scale]; rw [←rpow_nat_cast, ←rpow_mul]
    apply one_div_le_one_div_of_le; linarith
    apply Real.rpow_le_self_of_le_one hH (by linarith)
    linarith [p.h_gamma.2]

  apply disjoint_Ioo_of_dist_ge
  · calc |c1 - c2| ≥ 1 / Q^2 := dist_lower_bound
      _ ≥ 1 / H := gap_condition
      _ = 2 * R := by simp [R]; field_simp; ring
  · apply div_pos one_pos; linarith
