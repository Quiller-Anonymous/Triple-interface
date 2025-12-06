import «Goldbach».Params
import Mathlib.Data.Set.Finite
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

open Set Real

/-! # Bilinear Geometry Definitions -/

/-- The Shearing Map (Section 5.2) -/
def ShearMap (a q : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (q * p.1 - a * p.2, a * p.1 + q * p.2)

/-- The Tube (Section 5.3) -/
def Tube (a q : ℤ) (s : ℤ) (U : ℝ) (D N : Set ℝ) : Set (ℤ × ℤ) :=
  { p | (p.1 : ℝ) ∈ D ∧ (p.2 : ℝ) ∈ N ∧
    abs ((q : ℝ) * p.2 - (a : ℝ) * p.1 - s) ≤ U }

/-! ## Overlap Theorems -/

/--
**Tube Overlap Finiteness**
For any fixed point (d, n), the number of tubes containing it is finite.
We prove this by bounding the parameters (a, q, s) to a finite box.
-/
theorem Tube_Overlap_Finite (p : GoldbachParams) (X : ℝ) (D N : Set ℝ) (U : ℝ) :
  let Q := Q_scale p X
  ∀ d n : ℤ,
  let containing_tubes := { triple : ℤ × ℤ × ℤ |
      let a := triple.1
      let q := triple.2.1
      let s := triple.2.2
      1 ≤ q ∧ (q : ℝ) ≤ Q ∧
      0 ≤ a ∧ a ≤ q ∧
      (d, n) ∈ Tube a q s U D N }
  Set.Finite containing_tubes :=
by
  intro Q d n containing_tubes

  -- Define the bounding box
  -- |s| <= Q|n| + Q|d| + U + 1 is a safe upper bound derived from triangle inequality
  let Bound := Q * |(n:ℝ)| + Q * |(d:ℝ)| + |U| + 1
  let s_min := ⌊-Bound⌋
  let s_max := ⌈Bound⌉

  apply Set.Finite.subset
    (s := (Icc 0 (⌈Q⌉ : ℤ)) ×ˢ (Icc 1 (⌊Q⌋ : ℤ)) ×ˢ (Icc s_min s_max))

  · -- 1. Box is finite
    apply Finite.prod
    · apply Finite.prod
      · exact finite_Icc _ _
      · exact finite_Icc _ _
    · exact finite_Icc _ _

  · -- 2. Subset containment
    intro ⟨a, q, s⟩ h
    simp at h
    rcases h with ⟨h_q_ge, h_q_le, h_a_ge, h_a_le, h_tube⟩
    simp
    constructor
    · constructor
      · -- Bound for a
        constructor
        · exact h_a_ge
        · apply Int.ceil_le.mpr; apply le_trans (Int.le_of_of_nat_le h_a_le); exact h_q_le
      · -- Bound for q
        constructor; exact h_q_ge; apply Int.le_of_of_nat_le; exact h_q_le
    · -- Bound for s
      rw [Tube] at h_tube
      have ineq := h_tube.2.2
      let Val := (q : ℝ) * n - (a : ℝ) * d
      rw [abs_sub_le_iff] at ineq
      rcases ineq with ⟨h_low, h_high⟩

      -- Common bound logic for |Val|
      have h_val_bound : |Val| ≤ Q * |(n:ℝ)| + Q * |(d:ℝ)| := by
        calc |(q:ℝ)*n - (a:ℝ)*d|
          _ ≤ |(q:ℝ)*n| + |(a:ℝ)*d| := abs_sub _ _
          _ = |(q:ℝ)|*|(n:ℝ)| + |(a:ℝ)|*|(d:ℝ)| := by simp [abs_mul]
          _ ≤ Q * |(n:ℝ)| + Q * |(d:ℝ)| := by
              gcongr
              · exact h_q_le
              · exact le_trans (Int.le_of_of_nat_le h_a_le) h_q_le

      -- Prove s is in [s_min, s_max]
      rw [mem_Icc]
      constructor
      · -- s >= s_min
        apply Int.le_floor.mpr
        -- s >= Val - U >= -|Val| - U >= -Bound
        calc (s:ℝ) ≥ Val - U := sub_le_iff_le_add.mp h_low
          _ ≥ -|Val| - |U| := by linarith [neg_abs_le Val, le_abs_self U]
          _ ≥ -(Q * |(n:ℝ)| + Q * |(d:ℝ)|) - |U| := by linarith
          _ = -(Q * |(n:ℝ)| + Q * |(d:ℝ)| + |U|) := by ring
          _ ≥ -Bound := by dsimp [Bound]; linarith

      · -- s <= s_max
        apply Int.ceil_le.mpr
        -- s <= Val + U <= |Val| + |U| <= Bound
        calc (s:ℝ) ≤ Val + U := sub_le_iff_le_add.mp h_high
          _ ≤ |Val| + |U| := by linarith [le_abs_self Val, le_abs_self U]
          _ ≤ (Q * |(n:ℝ)| + Q * |(d:ℝ)|) + |U| := by linarith
          _ ≤ Bound := by dsimp [Bound]; linarith
