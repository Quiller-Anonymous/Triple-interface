import SSU.Torus.BandToArc

/-!
Band-to-arc bridge for the TeX substitution `x = ξ / X`.

This file packages the deterministic identity

`(1/X) ∫_{|ξ|≤1/H} g((ξ/X):𝕋) dξ = ∫_{𝕋} 1_{arc} g`,

valid under the “no wrap-around” smallness assumption `|(1/H)/X| < 1/2`.

It is the bookkeeping step needed when relating real-frequency ξ-band integrals to torus Haar
integrals on a small arc about `0`.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzBandToArc

noncomputable section

open MeasureTheory
open SSU.Torus
open SSU.Torus.BandMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem one_div_X_smul_integral_band_eval_eq_integral_indicator_arc
    (X H : ℝ)
    (hX : 0 < X)
    (hH : 0 < H)
    (hsmall : (1 / H) / X < (1 / 2 : ℝ))
    (g : UC → E) :
    ((1 / X : ℝ) • ∫ ξ in Set.Icc (-(1 / H)) (1 / H), g ((ξ / X : ℝ) : UC))
      =
    ∫ z : UC, (arc (-(1 / H) / X) ((1 / H) / X)).indicator g z := by
  simpa [SSU.Torus.BandMap.arc] using
    (SSU.Torus.BandToArc.one_div_X_smul_integral_band_eval_eq_integral_indicator_arc
      (X := X) (H := H) (hX := hX) (hH := hH) (hsmall := hsmall) (g := g))

end

end FejerBankedTypeIIToeplitzBandToArc
end Instances
end SSU
