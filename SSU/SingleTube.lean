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

theorem tubeEnergy_mul_const (T : Finset TubePoint) (c : ℂ) (F : TubePoint → ℂ) :
    tubeEnergy T (fun p => c * F p) = (‖c‖ ^ 2) * tubeEnergy T F := by
  classical
  unfold tubeEnergy
  -- Rewrite the sum termwise and factor out the constant `‖c‖^2`.
  have hrewrite :
      (∑ p ∈ T, ‖c * F p‖ ^ 2) = ∑ p ∈ T, (‖c‖ ^ 2) * (‖F p‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hn :
        ‖c * F p‖ ^ 2 = (‖c‖ ^ 2) * (‖F p‖ ^ 2) := by
      calc
        ‖c * F p‖ ^ 2 = (‖c‖ * ‖F p‖) ^ 2 := by simp [norm_mul]
        _ = (‖c‖ ^ 2) * (‖F p‖ ^ 2) := by
              simpa using (mul_pow (‖c‖) (‖F p‖) 2)
    simpa [norm_mul] using hn
  -- Now pull out `‖c‖^2`.
  calc
    (∑ p ∈ T, ‖c * F p‖ ^ 2) = ∑ p ∈ T, (‖c‖ ^ 2) * (‖F p‖ ^ 2) := hrewrite
    _ = (‖c‖ ^ 2) * (∑ p ∈ T, ‖F p‖ ^ 2) := by
          -- `Finset.mul_sum` is oriented as `a * ∑ = ∑ a * _`.
          simpa [mul_assoc] using
            (Finset.mul_sum (s := T) (f := fun p => ‖F p‖ ^ 2) (a := (‖c‖ ^ 2))).symm
    _ = (‖c‖ ^ 2) * tubeEnergy T F := rfl

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
