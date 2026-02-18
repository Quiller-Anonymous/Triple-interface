import SSU.Torus.ArcBridge

/-!
Small-arc bridge on the torus `𝕋 = AddCircle 1`.

This file turns integrals of an indicator-restricted torus function over Haar measure into an
ordinary real integral over the corresponding subinterval of the fundamental domain.

It is the deterministic measure-theoretic justification behind the informal “no wrap-around”
heuristic: on a sufficiently small arc around `0 : 𝕋`, the quotient map `ℝ → 𝕋` is injective and
Haar measure matches Lebesgue measure on the representative interval.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzArcBridge

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
  simpa [SSU.Torus.BandMap.arc] using
    (SSU.Torus.ArcBridge.integral_indicator_arc_eq_integral_Icc (a := a) (b := b) ha hb g)

end

end FejerBankedTypeIIToeplitzArcBridge
end Instances
end SSU
