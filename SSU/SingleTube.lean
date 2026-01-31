import SSU.Kernel

namespace SSU

open scoped BigOperators

noncomputable section

/-!
Single-tube SSU: statement shell.

The notes’ tube inequality is a quadratic form estimate on a finite set of lattice points
`(d,n)` restricted to a tube, involving the determinant-like integer `d' n - d n'`.

This file provides a project-neutral statement format on `ℤ × ℤ`. The eventual SSU project will
specialize the `tube` predicate to the sheared-hyperbola geometry used in the paper.
-/

abbrev TubePoint : Type := ℤ × ℤ

/-! The “short-shift” integer `d' n - d n'`. -/
def shortShift (p q : TubePoint) : ℤ :=
  q.1 * p.2 - p.1 * q.2

/-!
Quadratic form associated to a kernel `K : ℤ → ℝ` over a finite set `T`.

This is the raw bilinear form appearing in the single-tube inequality (up to weights and
normalizations).  We record it as a complex number so later versions can incorporate phases.
-/
def tubeForm (K : ℤ → ℝ) (T : Finset TubePoint) (F : TubePoint → ℂ) : ℂ :=
  Finset.sum T (fun p =>
    Finset.sum T (fun q =>
      F p * (K (shortShift p q)) * (star (F q))))

/-- Energy on a finite set. -/
def tubeEnergy (T : Finset TubePoint) (F : TubePoint → ℂ) : ℝ :=
  Finset.sum T (fun p => ‖F p‖ ^ 2)

/-!
Single-tube SSU statement (Theorem 6.5 / 6.22 in the notes), in a project-neutral shell.

This is *not* the final API: we will later bundle additional geometric hypotheses (shear
coordinates, congruence classes, dyadic windows, etc.) and prove this from those hypotheses.
-/
def SingleTubeSSUStatement (X H : ℝ) (K : ℤ → ℝ) (T : Finset TubePoint) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : TubePoint → ℂ,
      ‖tubeForm K T F‖ ≤ C * Real.sqrt (H / X) * (tubeEnergy T F)

end

end SSU
