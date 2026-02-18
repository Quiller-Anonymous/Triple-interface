import SSU.Torus.Basic

/-!
Measurability helpers for `AddCircle`.

`AddCircle.liftIoc` is defined using the representative map `AddCircle.equivIoc`, which is
continuous everywhere except at the endpoint. This file packages the standard measurability
lemmas used throughout the “torus packet extraction” layer.
-/

namespace SSU
namespace Torus
namespace AddCircleMeasurability

open MeasureTheory AddCircle

noncomputable section

theorem measurable_equivIoc (p a : ℝ) [Fact (0 < p)] :
    Measurable (AddCircle.equivIoc (p := p) a) := by
  classical
  have hcont : ContinuousOn (AddCircle.equivIoc (p := p) a) ({(a : AddCircle p)}ᶜ) := by
    intro x hx
    have hx' : x ≠ (a : AddCircle p) := by
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    exact (AddCircle.continuousAt_equivIoc (p := p) (a := a) (x := x) hx').continuousWithinAt
  simpa using (measurable_of_continuousOn_compl_singleton (a := (a : AddCircle p)) hcont)

theorem measurable_liftIoc {B : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    (p a : ℝ) [Fact (0 < p)] [Archimedean ℝ]
    (f : ℝ → B) (hf : Measurable f) :
    Measurable (AddCircle.liftIoc (p := p) (a := a) f) := by
  classical
  have hrep : Measurable fun y : Set.Ioc a (a + p) => f (y : ℝ) :=
    hf.comp measurable_subtype_coe
  have hEq : AddCircle.liftIoc (p := p) (a := a) f =
      (fun x : AddCircle p => f ((AddCircle.equivIoc (p := p) a x : Set.Ioc a (a + p)) : ℝ)) := by
    rfl
  have he : Measurable (AddCircle.equivIoc (p := p) a) :=
    measurable_equivIoc (p := p) (a := a)
  simpa [hEq] using (hrep.comp he)

end

end AddCircleMeasurability
end Torus
end SSU
