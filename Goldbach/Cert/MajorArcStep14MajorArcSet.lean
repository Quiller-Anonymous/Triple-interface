import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Major arcs (Step 14, sigma-agnostic): a reusable major-arc predicate/set on `[0,1]`.

To actually *use* the exponential-sum approximations from Steps 2–6 inside an integral, we will
eventually split the circle integral into a “major arc” part and a “minor arc” part.

This file provides that splitting infrastructure in a parameterized form:

* `IsMajorArc Q δ α` means `α` lies within `δ/q` of some reduced rational `a/q` with `q ≤ Q`.
* `majorArcSet Q δ` is the corresponding set of reals.
* `measurableSet_majorArcSet` shows this set is measurable (countable union of measurable sets).

We keep this independent of any *specific* choices of `Q` and `δ`; those are project-specific
calibration parameters introduced later.
-/

namespace Goldbach.Cert
namespace MajorArcStep14MajorArcSet

open scoped BigOperators

open MeasureTheory

noncomputable section

/-- Naïve major-arc predicate on reals: near a reduced rational `a/q` with `q ≤ Q`. -/
def IsMajorArc (Q δ : ℝ) (α : ℝ) : Prop :=
  ∃ (q a : ℕ),
    1 ≤ q ∧
    (q : ℝ) ≤ Q ∧
    Nat.Coprime a q ∧
    |α - (a : ℝ) / q| ≤ δ / q

def majorArcSet (Q δ : ℝ) : Set ℝ :=
  {α | IsMajorArc Q δ α}

lemma measurableSet_majorArcSet (Q δ : ℝ) :
    MeasurableSet (majorArcSet Q δ) := by
  classical
  -- Expand the existential definition into a countable union of measurable “boxes”.
  let cond : ℕ → ℕ → Prop :=
    fun q a => 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ Nat.Coprime a q
  let arc : ℕ → ℕ → Set ℝ :=
    fun q a => {α : ℝ | |α - (a : ℝ) / q| ≤ δ / q}

  have hEq :
      majorArcSet Q δ = ⋃ q : ℕ, ⋃ a : ℕ, (if cond q a then arc q a else (∅ : Set ℝ)) := by
    ext α
    constructor
    · intro h
      rcases h with ⟨q, a, hq1, hqQ, hcop, hα⟩
      refine Set.mem_iUnion.2 ⟨q, ?_⟩
      refine Set.mem_iUnion.2 ⟨a, ?_⟩
      have hc : cond q a := ⟨hq1, hqQ, hcop⟩
      simp [majorArcSet, IsMajorArc, hc, arc, hα]
    · intro h
      rcases Set.mem_iUnion.1 h with ⟨q, hq⟩
      rcases Set.mem_iUnion.1 hq with ⟨a, ha⟩
      by_cases hc : cond q a
      · have hα : |α - (a : ℝ) / q| ≤ δ / q := by
          simpa [hc, arc] using ha
        rcases hc with ⟨hq1, hqQ, hcop⟩
        exact ⟨q, a, hq1, hqQ, hcop, hα⟩
      · -- membership in the `if`-branch forces a contradiction
        simpa [hc] using ha

  have hMeas :
      MeasurableSet (⋃ q : ℕ, ⋃ a : ℕ, (if cond q a then arc q a else (∅ : Set ℝ))) := by
    refine MeasurableSet.iUnion ?_
    intro q
    refine MeasurableSet.iUnion ?_
    intro a
    by_cases hc : cond q a
    · have hArc : MeasurableSet (arc q a) := by
        have h1 : Measurable (fun α : ℝ => |α - (a : ℝ) / q|) := by fun_prop
        have h2 : Measurable (fun _ : ℝ => δ / q) := measurable_const
        simpa [arc] using (measurableSet_le h1 h2)
      simpa [hc] using hArc
    · simpa [hc] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))

  simpa [hEq] using hMeas

end

end MajorArcStep14MajorArcSet
end Goldbach.Cert

