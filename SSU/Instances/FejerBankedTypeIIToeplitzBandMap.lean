import SSU.Torus.BandMap

/-!
Band map infrastructure for the TeX normalization `x = ξ / X` (no wrap-around).

For the TeX `|ξ| ≤ 1/H` band, we frequently evaluate torus multipliers at the point
`x := (ξ / X : ℝ) : AddCircle 1`.

When `(1/H) / X < 1/2`, this evaluation map is injective on the band: there is no wrap-around.
This file records that deterministic fact; later bridge files use it to relate ξ-band integrals
to small-arc torus integrals.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzBandMap

open scoped BigOperators

noncomputable section

open MeasureTheory
open SSU.Torus

abbrev band (H : ℝ) : Set ℝ := SSU.Torus.BandMap.band H

abbrev toUC_div (X : ℝ) : ℝ → UC := SSU.Torus.BandMap.toUC_div X

/--
No wrap-around on the TeX band: if `(1/H)/X < 1/2`, then the map `ξ ↦ ((ξ/X):𝕋)` is injective on
`band H = [-1/H, 1/H]`.
-/
theorem toUC_div_injOn_band
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H)
    (hsmall : (1 / H) / X < (1 / 2 : ℝ)) :
    Set.InjOn (toUC_div X) (band H) := by
  simpa [band, toUC_div] using (SSU.Torus.BandMap.toUC_div_injOn_band (X := X) (H := H) hX hH hsmall)

/-!
### Small arcs inside the fundamental domain

For later bridge steps, it is convenient to name the small arc
`(fun x : ℝ => (x : 𝕋)) '' Icc a b` and characterize membership for representatives in the
fundamental domain `Ico (-1/2) (1/2)`.
-/

abbrev fundDom : Set ℝ := SSU.Torus.BandMap.fundDom

abbrev arc (a b : ℝ) : Set UC := SSU.Torus.BandMap.arc a b

theorem mem_arc_iff_of_mem_fundDom {a b x : ℝ}
    (ha : a ∈ fundDom) (hb : b ∈ fundDom) (hx : x ∈ fundDom) :
    ((x : UC) ∈ arc a b) ↔ x ∈ Set.Icc a b := by
  simpa [fundDom, arc] using
    (SSU.Torus.BandMap.mem_arc_iff_of_mem_fundDom (a := a) (b := b) (x := x) ha hb hx)

end

end FejerBankedTypeIIToeplitzBandMap
end Instances
end SSU
