import SSU.Torus.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
Torus band-map infrastructure for the TeX normalization `x = ξ / X` (no wrap-around).

This file is project-neutral: it does not depend on any particular SSU instance (Fejér banked,
Goldbach, ...).  It provides:

* the real-frequency band `[-1/H, 1/H]`,
* the evaluation map `ξ ↦ ((ξ/X): AddCircle 1)`,
* the “no wrap-around” injectivity lemma on the band, and
* a small-arc set constructor `arc a b`.
-/

namespace SSU
namespace Torus
namespace BandMap

open MeasureTheory

noncomputable section

abbrev band (H : ℝ) : Set ℝ :=
  Set.Icc (-(1 / H)) (1 / H)

abbrev toUC_div (X : ℝ) : ℝ → UC :=
  fun ξ : ℝ => ((ξ / X : ℝ) : UC)

private theorem mem_Ico_negHalf_addOne_of_abs_lt_half {x : ℝ} (hx : |x| < (1 / 2 : ℝ)) :
    x ∈ Set.Ico (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
  have hx' : -(1 / 2 : ℝ) < x ∧ x < (1 / 2 : ℝ) := abs_lt.mp hx
  refine ⟨le_of_lt hx'.1, ?_⟩
  have hx1 : x < (1 / 2 : ℝ) := hx'.2
  have heq : (1 / 2 : ℝ) = (-(1 / 2 : ℝ)) + (1 : ℝ) := by ring
  exact lt_of_lt_of_eq hx1 heq

/--
No wrap-around on the TeX band: if `(1/H)/X < 1/2`, then the map `ξ ↦ ((ξ/X):𝕋)` is injective on
`band H = [-1/H, 1/H]`.
-/
theorem toUC_div_injOn_band
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H)
    (hsmall : (1 / H) / X < (1 / 2 : ℝ)) :
    Set.InjOn (toUC_div X) (band H) := by
  classical
  intro ξ hξ η hη hcoe
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hξabs : |ξ| ≤ (1 / H) := by
    have hξ' : ξ ∈ Set.Icc (-(1 / H)) (1 / H) := by simpa [band] using hξ
    have hξ'' : (-(1 / H) : ℝ) ≤ ξ ∧ ξ ≤ (1 / H) := by
      simpa [Set.mem_Icc] using hξ'
    exact (abs_le.2 hξ'')
  have hηabs : |η| ≤ (1 / H) := by
    have hη' : η ∈ Set.Icc (-(1 / H)) (1 / H) := by simpa [band] using hη
    have hη'' : (-(1 / H) : ℝ) ≤ η ∧ η ≤ (1 / H) := by
      simpa [Set.mem_Icc] using hη'
    exact (abs_le.2 hη'')
  have hξabs_div : |ξ / X| < (1 / 2 : ℝ) := by
    have : |ξ / X| = |ξ| / X := by
      simp [abs_div, abs_of_pos hX, div_eq_mul_inv, mul_assoc]
    have hle : |ξ| / X ≤ (1 / H) / X := by
      exact (div_le_div_of_nonneg_right hξabs (le_of_lt hX))
    have hlt : |ξ| / X < (1 / 2 : ℝ) := lt_of_le_of_lt hle hsmall
    simpa [this] using hlt
  have hηabs_div : |η / X| < (1 / 2 : ℝ) := by
    have : |η / X| = |η| / X := by
      simp [abs_div, abs_of_pos hX, div_eq_mul_inv, mul_assoc]
    have hle : |η| / X ≤ (1 / H) / X := by
      exact (div_le_div_of_nonneg_right hηabs (le_of_lt hX))
    have hlt : |η| / X < (1 / 2 : ℝ) := lt_of_le_of_lt hle hsmall
    simpa [this] using hlt
  have hξdom : (ξ / X) ∈ Set.Ico (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) :=
    mem_Ico_negHalf_addOne_of_abs_lt_half hξabs_div
  have hηdom : (η / X) ∈ Set.Ico (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) :=
    mem_Ico_negHalf_addOne_of_abs_lt_half hηabs_div
  have hreal :
      (ξ / X : UC) = (η / X : UC) ↔ (ξ / X) = (η / X) := by
    simpa using
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (-(1 / 2 : ℝ)))
        (x := (ξ / X)) (y := (η / X)) hξdom hηdom)
  have hxeq : (ξ / X) = (η / X) := (hreal.mp hcoe)
  have : ξ = η := by
    have := congrArg (fun t : ℝ => t * X) hxeq
    field_simp [hX0] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact this

/-!
### Small arcs inside the fundamental domain

For later bridge steps, it is convenient to name the small arc
`(fun x : ℝ => (x : 𝕋)) '' Icc a b` and characterize membership for representatives in the
fundamental domain `Ico (-1/2) (1/2)`.
-/

abbrev fundDom : Set ℝ := Set.Ico (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))

abbrev arc (a b : ℝ) : Set UC :=
  (fun x : ℝ => (x : UC)) '' (Set.Icc a b)

theorem mem_arc_iff_of_mem_fundDom {a b x : ℝ}
    (ha : a ∈ fundDom) (hb : b ∈ fundDom) (hx : x ∈ fundDom) :
    ((x : UC) ∈ arc a b) ↔ x ∈ Set.Icc a b := by
  constructor
  · intro hxarc
    rcases hxarc with ⟨y, hyIcc, hycoe⟩
    have hy : y ∈ fundDom := by
      refine ⟨le_trans ha.1 hyIcc.1, ?_⟩
      exact lt_of_le_of_lt hyIcc.2 hb.2
    have hxIco : x ∈ Set.Ico (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
      simpa [fundDom] using hx
    have hyIco : y ∈ Set.Ico (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
      simpa [fundDom] using hy
    have hyx : y = x := by
      have : (y : UC) = x ↔ y = x := by
        simpa using (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (-(1 / 2 : ℝ)))
          (x := y) (y := x) hyIco hxIco)
      exact (this.mp (by simpa using hycoe))
    simpa [hyx] using hyIcc
  · intro hxIcc
    exact ⟨x, hxIcc, rfl⟩

end

end BandMap
end Torus
end SSU

