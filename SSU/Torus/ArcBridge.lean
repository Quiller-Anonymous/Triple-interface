import SSU.Torus.BandMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Small-arc bridge on the torus `𝕋 = AddCircle 1`.

This file turns integrals of an indicator-restricted torus function over Haar measure into an
ordinary real integral over the corresponding subinterval of the fundamental domain.

It is the deterministic measure-theoretic justification behind the informal “no wrap-around”
heuristic: on a sufficiently small arc around `0 : 𝕋`, the quotient map `ℝ → 𝕋` is injective and
Haar measure matches Lebesgue measure on the representative interval.
-/

namespace SSU
namespace Torus
namespace ArcBridge

noncomputable section

open MeasureTheory
open SSU.Torus
open SSU.Torus.BandMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/--
Integral over a small arc (as an indicator on `𝕋`) equals the real set-integral over the
corresponding representative interval.

This is stated using `volume` on `𝕋`; for `AddCircle 1`, `volume = haarAddCircle`, so the same
statement applies to `SSU.Torus.μ`.

The endpoint hypotheses `ha hb : _ ∈ fundDom` ensure we are staying inside the fundamental domain.
-/
theorem integral_indicator_arc_eq_integral_Icc
    (a b : ℝ)
    (ha : a ∈ Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)))
    (hb : b ∈ Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)))
    (g : UC → E) :
    (∫ z : UC, (arc a b).indicator g z)
      =
    ∫ x in Set.Icc a b, g (x : UC) := by
  have hpre :
      (∫ z : UC, (arc a b).indicator g z)
        =
      ∫ x in Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)), (arc a b).indicator g (x : UC) := by
    simpa using (AddCircle.integral_preimage (T := (1 : ℝ)) (t := (-(1 / 2 : ℝ)))
      (f := (arc a b).indicator g)).symm
  have hIocIoo :
      (∫ x in Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)),
          (arc a b).indicator g (x : UC))
        =
      ∫ x in Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)),
          (arc a b).indicator g (x : UC) := by
    simpa using
      (MeasureTheory.integral_Ioc_eq_integral_Ioo (μ := (volume : Measure ℝ))
        (f := fun x : ℝ => (arc a b).indicator g (x : UC))
        (x := (-(1 / 2 : ℝ))) (y := ((-(1 / 2 : ℝ)) + (1 : ℝ))))
  have haFD : a ∈ fundDom := ⟨le_of_lt ha.1, ha.2⟩
  have hbFD : b ∈ fundDom := ⟨le_of_lt hb.1, hb.2⟩
  have hcongr :
      (fun x : ℝ => (arc a b).indicator g (x : UC))
        =ᵐ[(volume : Measure ℝ).restrict (Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)))]
      (fun x : ℝ => (Set.Icc a b).indicator (fun t : ℝ => g (t : UC)) x) := by
    have hs : MeasurableSet (Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))) := by
      measurability
    filter_upwards [ae_restrict_mem hs] with x hx
    have hxFund : x ∈ fundDom := by
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hmem : ((x : UC) ∈ arc a b) ↔ x ∈ Set.Icc a b :=
      mem_arc_iff_of_mem_fundDom (a := a) (b := b) (x := x) haFD hbFD hxFund
    by_cases hxab : x ∈ Set.Icc a b <;> simp [Set.indicator, hmem, hxab]
  have hIoo :
      (∫ x in Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)),
          (arc a b).indicator g (x : UC))
        =
      ∫ x in Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)),
          (Set.Icc a b).indicator (fun t : ℝ => g (t : UC)) x := by
    simpa [MeasureTheory.integral] using integral_congr_ae hcongr
  have hsubset :
      Set.Icc a b ⊆ Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
    intro x hxIcc
    have hxlo : (-(1 / 2 : ℝ)) < x := lt_of_lt_of_le ha.1 hxIcc.1
    have hxhi : x < ((-(1 / 2 : ℝ)) + (1 : ℝ)) := lt_of_le_of_lt hxIcc.2 hb.2
    exact ⟨hxlo, hxhi⟩
  have hindicator :
      (∫ x in Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)),
          (Set.Icc a b).indicator (fun t : ℝ => g (t : UC)) x)
        =
      ∫ x in Set.Icc a b, g (x : UC) := by
    have hsIcc : MeasurableSet (Set.Icc a b) := by
      measurability
    have :=
      (MeasureTheory.setIntegral_indicator (μ := (volume : Measure ℝ))
        (s := Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)))
        (t := Set.Icc a b) (f := fun t : ℝ => g (t : UC)) hsIcc)
    have hinter :
        (Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))) ∩ (Set.Icc a b) = Set.Icc a b := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨hsubset hx, hx⟩
    have h' := this
    rw [hinter] at h'
    exact h'
  calc
    (∫ z : UC, (arc a b).indicator g z)
        =
      ∫ x in Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)), (arc a b).indicator g (x : UC) := hpre
    _ =
      ∫ x in Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)), (arc a b).indicator g (x : UC) := hIocIoo
    _ =
      ∫ x in Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)),
        (Set.Icc a b).indicator (fun t : ℝ => g (t : UC)) x := hIoo
    _ =
      ∫ x in Set.Icc a b, g (x : UC) := hindicator

end

end ArcBridge
end Torus
end SSU

