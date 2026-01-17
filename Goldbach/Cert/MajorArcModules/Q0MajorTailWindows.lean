import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Deterministic “smooth window” majorants for the hard `Q0` major arcs.

These are preparation for the option-3 (TT*/mean-zero) ε₂-large tail plan: the SSU/alias-suppression
large-sieve statements in the notes are phrased for *weighted* major-arc windows, while the Lean
pipeline uses a hard indicator `1_{arcSetTextbook}`.

This module introduces an explicit, elementary window `wTextbook` that **dominates** the hard arc
`{ |α - a/q| ≤ 1/(qX) }` on `ℝ` (hence in particular on `[0,1]`), with no number theory.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailWindows

open scoped BigOperators

open Real MeasureTheory

open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

noncomputable def center (q a : ℕ) : ℝ :=
  (a : ℝ) / (q : ℝ)

noncomputable def radius (X q : ℕ) : ℝ :=
  1 / ((q : ℝ) * (X : ℝ))

noncomputable def radius2 (X q : ℕ) : ℝ :=
  2 / ((q : ℝ) * (X : ℝ))

/--
An explicit piecewise-linear window on `ℝ` centered at `a/q`.

It is equal to `1` on the hard textbook arc `|α - a/q| ≤ 1/(qX)`, then decreases linearly to `0`
on the annulus `1/(qX) < |α - a/q| ≤ 2/(qX)`, and vanishes outside `|α - a/q| ≤ 2/(qX)`.
-/
noncomputable def wTextbook (X q a : ℕ) (α : ℝ) : ℝ :=
  let r := radius X q
  let d := |α - center q a|
  if d ≤ r then
    1
  else if d ≤ (2 * r) then
    2 - (d / r)
  else
    0

lemma wTextbook_nonneg (X q a : ℕ) (α : ℝ) : 0 ≤ wTextbook X q a α := by
  classical
  unfold wTextbook
  by_cases h1 : |α - center q a| ≤ radius X q
  · simp [h1]
  by_cases h2 : |α - center q a| ≤ 2 * radius X q
  · simp [h1, h2]
    -- `2 - d/r ≥ 0` since `d ≤ 2r`.
    have hr : 0 ≤ radius X q := by
      unfold radius
      have : 0 ≤ (q : ℝ) * (X : ℝ) := by nlinarith
      exact one_div_nonneg.2 this
    have hpos_or : (0 : ℝ) = radius X q ∨ 0 < radius X q := eq_or_lt_of_le hr
    rcases hpos_or with hr0 | hrpos
    · -- If `r = 0`, the branch condition `d ≤ 2r` forces `d = 0`, so the value is `2`.
      have hr0' : radius X q = 0 := hr0.symm
      have : |α - center q a| = 0 := by
        have : |α - center q a| ≤ 0 := by simpa [hr0'] using h2
        exact le_antisymm this (abs_nonneg _)
      simp [hr0', this]
    · -- Otherwise divide the inequality `d ≤ 2r` by `r`.
      have hdiv : |α - center q a| / radius X q ≤ 2 := by
        have : |α - center q a| ≤ 2 * radius X q := h2
        have := (div_le_iff₀ hrpos).2 (by simpa [mul_assoc] using this)
        simpa [mul_assoc] using this
      linarith
  · simp [h1, h2]

lemma wTextbook_le_one (X q a : ℕ) (α : ℝ) : wTextbook X q a α ≤ 1 := by
  classical
  unfold wTextbook
  by_cases h1 : |α - center q a| ≤ radius X q
  · simp [h1]
  by_cases h2 : |α - center q a| ≤ 2 * radius X q
  · simp [h1, h2]
    -- `2 - d/r ≤ 1` since `d/r ≥ 1` on this branch.
    have hr : 0 ≤ radius X q := by
      unfold radius
      have : 0 ≤ (q : ℝ) * (X : ℝ) := by nlinarith
      exact one_div_nonneg.2 this
    have hpos_or : (0 : ℝ) = radius X q ∨ 0 < radius X q := eq_or_lt_of_le hr
    rcases hpos_or with hr0 | hrpos
    · -- If `r = 0`, this branch is impossible: `d ≤ 0` would have put us in the first branch.
      exfalso
      have hr0' : radius X q = 0 := hr0.symm
      have : |α - center q a| ≤ 0 := by simpa [hr0'] using h2
      exact h1 (by simpa [hr0'] using this)
    · have hdiv : 1 ≤ |α - center q a| / radius X q := by
        have : ¬ |α - center q a| ≤ radius X q := h1
        have : radius X q < |α - center q a| := lt_of_not_ge this
        -- `r < d` implies `1 < d/r`.
        have : 1 < |α - center q a| / radius X q := by
          have := (one_lt_div₀ hrpos).2 this
          simpa using this
        exact this.le
      linarith
  · simp [h1, h2]

lemma radius2_eq_two_mul_radius (X q : ℕ) : radius2 X q = 2 * radius X q := by
  unfold radius2 radius
  ring

lemma abs_sub_center_le_radius2_of_wTextbook_ne_zero
    (X q a : ℕ) (α : ℝ) (h : wTextbook X q a α ≠ 0) :
    |α - center q a| ≤ radius2 X q := by
  classical
  unfold wTextbook at h
  by_cases h1 : |α - center q a| ≤ radius X q
  · have hr : 0 ≤ radius X q := by
      unfold radius
      have : 0 ≤ (q : ℝ) * (X : ℝ) := by nlinarith
      exact one_div_nonneg.2 this
    have : |α - center q a| ≤ 2 * radius X q := by nlinarith
    simpa [radius2_eq_two_mul_radius (X := X) (q := q)] using this
  by_cases h2 : |α - center q a| ≤ 2 * radius X q
  · simpa [h1, h2, radius2_eq_two_mul_radius (X := X) (q := q)] using h2
  · exfalso
    simp [h1, h2] at h

lemma indicator_arcSetTextbook_le_wTextbook
    (X q a : ℕ) (Δ : ℝ) (hΔ : Δ = 1) (α : ℝ) :
    (arcSetTextbook X q a Δ).indicator (fun _ : ℝ => (1 : ℝ)) α ≤ wTextbook X q a α := by
  classical
  subst hΔ
  by_cases hα : α ∈ arcSetTextbook X q a (1 : ℝ)
  · -- On the hard arc, the indicator is `1` and the window is also `1`.
    have : |α - center q a| ≤ radius X q := by
      -- Unfold `arcSetTextbook` and rewrite `Δ = 1`.
      simpa [arcSetTextbook, center, radius, abs_sub_comm, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm] using hα
    simp [wTextbook, Set.indicator_of_mem hα, this]
  · -- Off the hard arc, the indicator is `0`.
    simp [Set.indicator_of_notMem hα, wTextbook_nonneg]

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailWindows
