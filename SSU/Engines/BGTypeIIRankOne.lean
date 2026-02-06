import SSU.Engines.BGToeplitz
import SSU.Engines.BGTubeGeometry
import SSU.Engines.BGTypeIIData
import SSU.Engines.TypeII

/-!
05_BG.tex — TeX-faithful *rank-one Type–II input* (`α ⊗ β`) packaged on the dyadic box.

This file fixes the mathematical convention requested for the “Toeplitz Type–II” block:

* `TubePoint := (d,n) ∈ ℤ×ℤ`,
* product coordinate `k := d*n`,
* rank-one Type–II coefficient array `F(d,n) = α_d β_n` on the dyadic box,
* separable dyadic cutoff `W(d/D,n/N) = W_D(d/D) * W_N(n/N)`,
* aggregated product coefficients `A_k := ∑_{dn=k} α_d β_n W(d/D,n/N)`.

All statements here are deterministic algebraic identities; no analytic bounds and no packet/SSU
heart content.
-/

namespace SSU
namespace Engines
namespace BGTypeIIRankOne

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII.ProductToeplitz

abbrev TubePoint : Type := SSU.TubePoint

/-!
## Rank-one Type–II input
-/

structure Input where
  /-- Type–II coefficient sequence `α_d`. -/
  α : ℤ → ℂ
  /-- Type–II coefficient sequence `β_n`. -/
  β : ℤ → ℂ

namespace Input

variable (I : Input)

/-- The TeX dyadic cutoff pulled back to lattice points: `W(d/D,n/N)`. -/
noncomputable def W_on_point (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (p : TubePoint) : ℂ :=
  SSU.Engines.BGTypeII.Cutoff.W_on_point_separable P W p

/-- The TeX coefficient array on the dyadic box: `F(d,n) = α_d β_n W(d/D,n/N)`. -/
noncomputable def F (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (p : TubePoint) : ℂ :=
  I.α p.1 * I.β p.2 * (Input.W_on_point (P := P) (W := W) p)

/-- Aggregated product coefficients `A_k := ∑_{dn=k} F(d,n)` (TeX Eq. (5.2)). -/
noncomputable def A (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (k : ℤ) : ℂ :=
  coeffByProd P.box (I.F P W) k

/-!
## Toeplitz regrouping (BG “group by product”)
-/

theorem tubeFormProd_eq_sum_A_tex (K : ℤ → ℝ) (hK : ∀ t : ℤ, K (-t) = K t) :
    tubeFormProd K P.box (I.F P W) =
      ∑ k ∈ P.box.image prod, ∑ k' ∈ P.box.image prod,
        (I.A P W k') * star (I.A P W k) * (K (k' - k)) := by
  classical
  -- This is the deterministic regrouping lemma already proved in `SSU.Engines.BGToeplitz`,
  -- specialized to the rank-one coefficient array.
  let CD : SSU.Engines.BGToeplitz.CoeffData :=
    { X := (P.X : ℝ)
      T := P.box
      α := I.α
      β := I.β
      W := fun p => Input.W_on_point (P := P) (W := W) p }
  -- Unfold everything down to the shared `coeffByProd`/`tubeFormProd` primitives.
  simpa [CD, Input.A, Input.F, Input.W_on_point, BGToeplitz.CoeffData.F, BGToeplitz.CoeffData.A] using
    (SSU.Engines.BGToeplitz.CoeffData.tubeFormProd_eq_sum_A_tex (D := CD) (K := K) hK)

end Input

end

end BGTypeIIRankOne
end Engines
end SSU
