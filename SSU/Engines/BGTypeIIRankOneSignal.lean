import SSU.Engines.BGTypeIIRankOne
import SSU.Engines.BGTypeIIArray

/-!
05_BG.tex — the rank-one Type–II signal on the torus (and its real-frequency normalization).

This file packages the user-frozen convention:

`f(x) = ∑_{d∈(D,2D]} ∑_{n∈(N,2N]} α_d β_n W_D(d/D) W_N(n/N) * e(dn * x)` on `𝕋`,

and records the deterministic bridge to the real-frequency form

`f(ξ/X) = ∑_k A_k e(ξ k / X)`,

where `A_k := ∑_{dn=k} α_d β_n W_D(d/D) W_N(n/N)` is defined in
`SSU.Engines.BGTypeIIRankOne.Input.A`.

No analytic bounds and no packet content occurs here.
-/

namespace SSU
namespace Engines
namespace BGTypeIIRankOne

open scoped BigOperators

noncomputable section

open SSU.Torus
open SSU.Engines.TypeII
open SSU.Engines.TypeII.ProductToeplitz

namespace Input

variable (I : Input)

/-- Deterministic bridge: `e(ξ k / X) = fourier k ((ξ/X) : 𝕋)`. -/
theorem e_eq_fourier_coe (X ξ : ℝ) (k : ℤ) :
    e (ξ * (k : ℝ) / X) = (fourier (T := (1 : ℝ)) k ((ξ / X : ℝ) : UC) : ℂ) := by
  -- Copy of `SSU.Engines.BGTypeIIArray.Data.e_eq_fourier_coe`, stated without the `Data` parameter.
  have hfour :
      (fourier (T := (1 : ℝ)) k ((ξ / X : ℝ) : UC) : ℂ)
        =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * (ξ / X)) := by
    simpa [Real.pi, one_div] using
      (AddCircle.fourier_coe_apply (T := (1 : ℝ)) (n := k) (x := (ξ / X)))
  have hmul : ξ * (k : ℝ) / X = (k : ℝ) * (ξ / X) := by ring
  unfold e
  simpa [hmul, mul_assoc, mul_left_comm, mul_comm] using hfour.symm

/-- The torus-side Type–II signal grouped by product: `∑_k A_k * fourier k x`. -/
noncomputable def signalTorusByProd
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (x : UC) : ℂ :=
  ∑ k ∈ P.box.image prod, (I.A P W k) * (fourier (T := (1 : ℝ)) k x)

/-- The real-frequency Type–II signal (TeX normalization): `∑_k A_k e(ξ k / X)`. -/
noncomputable def signalRealByProd
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (X ξ : ℝ) : ℂ :=
  ∑ k ∈ P.box.image prod, (I.A P W k) * e (ξ * (k : ℝ) / X)

theorem signalRealByProd_eq_signalTorusByProd
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (X ξ : ℝ) :
    I.signalRealByProd P W X ξ = I.signalTorusByProd P W ((ξ / X : ℝ) : UC) := by
  classical
  -- Termwise rewrite `e(ξk/X)` into the torus character `fourier k ((ξ/X):𝕋)`.
  unfold Input.signalRealByProd Input.signalTorusByProd
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [Input.e_eq_fourier_coe (X := X) (ξ := ξ) (k := k)]

/-- The TeX rank-one Type–II signal as a **double sum** over the dyadic box points `(d,n)`. -/
noncomputable def signalTorusDN
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (x : UC) : ℂ :=
  ∑ p ∈ P.box, (I.F P W p) * (fourier (T := (1 : ℝ)) (prod p) x)

/-- The TeX rank-one Type–II signal as a real-frequency **double sum** over `(d,n)`. -/
noncomputable def signalRealDN
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (X ξ : ℝ) : ℂ :=
  ∑ p ∈ P.box, (I.F P W p) * e (ξ * (prod p : ℝ) / X)

theorem signalTorusDN_eq_signalTorusByProd
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (x : UC) :
    I.signalTorusDN P W x = I.signalTorusByProd P W x := by
  classical
  -- Group the sum over `P.box` by the map `prod : (d,n) ↦ d*n`.
  let w : TubePoint → ℂ := fun p =>
    (I.F P W p) * (fourier (T := (1 : ℝ)) (prod p) x)
  have hfib :
      (∑ k ∈ P.box.image prod, ∑ p ∈ P.box with prod p = k, w p) = ∑ p ∈ P.box, w p := by
    simpa [w] using
      (Finset.sum_fiberwise_of_maps_to (s := P.box) (t := P.box.image prod) (g := prod)
        (h := fun p hp => Finset.mem_image_of_mem prod hp) (f := w))
  have hfiber (k : ℤ) :
      (∑ p ∈ P.box with prod p = k, w p) =
        (I.A P W k) * (fourier (T := (1 : ℝ)) k x) := by
    -- On the fiber `prod p = k`, the character is constant.
    have hrewrite :
        (∑ p ∈ P.box with prod p = k, w p)
          =
        ∑ p ∈ P.box with prod p = k, (I.F P W p) * (fourier (T := (1 : ℝ)) k x) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hpk : prod p = k := (Finset.mem_filter.mp hp).2
      simp [w, hpk]
    have hpull :
        (∑ p ∈ P.box with prod p = k, (I.F P W p) * (fourier (T := (1 : ℝ)) k x))
          =
        (∑ p ∈ P.box with prod p = k, I.F P W p) * (fourier (T := (1 : ℝ)) k x) := by
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
        (Finset.mul_sum (s := (P.box).filter (fun p => prod p = k))
          (f := fun p => I.F P W p) (a := (fourier (T := (1 : ℝ)) k x : ℂ))).symm
    have hcoeff :
        (∑ p ∈ P.box with prod p = k, I.F P W p) = I.A P W k := by
      -- `coeffByProd_eq_sum_filter`, specialized to `T = P.box` and `F = I.F`.
      simpa [Input.A] using
        (coeffByProd_eq_sum_filter (T := P.box) (F := I.F P W) k).symm
    -- Assemble.
    simpa [hcoeff, mul_assoc] using (hrewrite.trans hpull)
  -- Finish by rewriting both sides into the fiberwise normal form.
  calc
    I.signalTorusDN P W x = ∑ p ∈ P.box, w p := by
      simp [Input.signalTorusDN, w]
    _ = ∑ k ∈ P.box.image prod, ∑ p ∈ P.box with prod p = k, w p := by
      simpa using hfib.symm
    _ = ∑ k ∈ P.box.image prod, (I.A P W k) * (fourier (T := (1 : ℝ)) k x) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simpa using (hfiber (k := k))
    _ = I.signalTorusByProd P W x := by
      simp [Input.signalTorusByProd]

theorem signalRealDN_eq_signalRealByProd
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (X ξ : ℝ) :
    I.signalRealDN P W X ξ = I.signalRealByProd P W X ξ := by
  classical
  -- Same deterministic grouping, but with `e(ξ*prod/X)` in place of the torus character.
  let w : TubePoint → ℂ := fun p => (I.F P W p) * e (ξ * (prod p : ℝ) / X)
  have hfib :
      (∑ k ∈ P.box.image prod, ∑ p ∈ P.box with prod p = k, w p) = ∑ p ∈ P.box, w p := by
    simpa [w] using
      (Finset.sum_fiberwise_of_maps_to (s := P.box) (t := P.box.image prod) (g := prod)
        (h := fun p hp => Finset.mem_image_of_mem prod hp) (f := w))
  have hfiber (k : ℤ) :
      (∑ p ∈ P.box with prod p = k, w p) = (I.A P W k) * e (ξ * (k : ℝ) / X) := by
    have hrewrite :
        (∑ p ∈ P.box with prod p = k, w p)
          =
        ∑ p ∈ P.box with prod p = k, (I.F P W p) * e (ξ * (k : ℝ) / X) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hpk : prod p = k := (Finset.mem_filter.mp hp).2
      -- Use the fiber equation to rewrite `e(ξ*prod/X)`.
      simp [w, hpk]
    have hpull :
        (∑ p ∈ P.box with prod p = k, (I.F P W p) * e (ξ * (k : ℝ) / X))
          =
        (∑ p ∈ P.box with prod p = k, I.F P W p) * e (ξ * (k : ℝ) / X) := by
      simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
        (Finset.mul_sum (s := (P.box).filter (fun p => prod p = k))
          (f := fun p => I.F P W p) (a := (e (ξ * (k : ℝ) / X) : ℂ))).symm
    have hcoeff :
        (∑ p ∈ P.box with prod p = k, I.F P W p) = I.A P W k := by
      simpa [Input.A] using
        (coeffByProd_eq_sum_filter (T := P.box) (F := I.F P W) k).symm
    simpa [hcoeff, mul_assoc] using (hrewrite.trans hpull)
  calc
    I.signalRealDN P W X ξ = ∑ p ∈ P.box, w p := by
      simp [Input.signalRealDN, w]
    _ = ∑ k ∈ P.box.image prod, ∑ p ∈ P.box with prod p = k, w p := by
      simpa using hfib.symm
    _ = ∑ k ∈ P.box.image prod, (I.A P W k) * e (ξ * (k : ℝ) / X) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      simpa using (hfiber (k := k))
    _ = I.signalRealByProd P W X ξ := by
      simp [Input.signalRealByProd]

/-
## Packaging as a `BGTypeIIArray.Data` object (box-first Toeplitz block)

This is a convenience: it allows the rank-one Type–II input `α ⊗ β` to be plugged into the
generic Toeplitz kernel-extraction lemmas that are phrased in terms of `BGTypeIIArray.Data`.
-/

open SSU.Engines.BGTypeIIArray

/-- View the rank-one Type–II input as a `BGTypeIIArray.Data` on the full dyadic box. -/
noncomputable def boxData
    {H0 : Type*}
    (P : SSU.Engines.BGTube.Params) (hU : 2 * P.N ≤ P.U) (W : SSU.Engines.TFA.SeparableWeight) :
    SSU.Engines.BGTypeIIArray.Data H0 :=
  SSU.Engines.BGTypeIIArray.Data.mkBox
    (H := H0)
    P hU W.toWeight
    (α := fun _f _i _j d => I.α d)
    (β := fun _f _i _j n => I.β n)

theorem boxData_tube_eq_box
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (P : SSU.Engines.BGTube.Params) (hU : 2 * P.N ≤ P.U) (W : SSU.Engines.TFA.SeparableWeight) :
    (I.boxData (H0 := H0) (P := P) hU W).tube = P.box := by
  simpa [Input.boxData] using
    (SSU.Engines.BGTypeIIArray.Data.mkBox_tube_eq_box
      (H := H0) (P := P) (hU := hU) (W := W.toWeight)
      (α := fun _f _i _j d => I.α d) (β := fun _f _i _j n => I.β n))

theorem boxData_F_eq_F
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (P : SSU.Engines.BGTube.Params) (hU : 2 * P.N ≤ P.U) (W : SSU.Engines.TFA.SeparableWeight)
    (f : H0) (i j : ℤ) (p : TubePoint) :
    (I.boxData (H0 := H0) (P := P) hU W).F f i j p = I.F P W p := by
  -- Unfold `F(d,n) = α_d β_n W(d/D,n/N)`, and rewrite `W_on_point` into the separable lattice cutoff.
  -- (This is purely definitional; no analytic content.)
  dsimp [Input.boxData, SSU.Engines.BGTypeIIArray.Data.F, SSU.Engines.BGTypeIIArray.Data.C,
    SSU.Engines.BGTypeIIArray.Data.mkBox, SSU.Engines.BGTypeII.TeX.mkCoeffFactorization,
    SSU.Engines.BGToeplitzReduction.TeX.CoeffFactorization.F, SSU.Engines.BGTypeIIRankOne.Input.F,
    SSU.Engines.BGTypeIIRankOne.Input.W_on_point]
  -- `W_on_point P W.toWeight = W_on_point_separable P W` deterministically for separable weights.
  -- First rewrite away the trivial `boxTube` wrapper.
  have hw :
      SSU.Engines.BGTypeII.Cutoff.W_on_point (SSU.Engines.BGTypeII.TubeParams.boxTube P).P W.toWeight p
        =
      SSU.Engines.BGTypeII.Cutoff.W_on_point_separable P W p := by
    simpa [SSU.Engines.BGTypeII.TubeParams.boxTube] using
      (SSU.Engines.BGTypeII.Cutoff.W_on_point_eq_separable (P := P) (W := W) p)
  -- Now the goal is definitional.
  simpa [hw]

theorem boxData_A_eq_A
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (P : SSU.Engines.BGTube.Params) (hU : 2 * P.N ≤ P.U) (W : SSU.Engines.TFA.SeparableWeight)
    (f : H0) (i j k : ℤ) :
    (I.boxData (H0 := H0) (P := P) hU W).A f i j k = I.A P W k := by
  classical
  -- Reduce to equality of coefficient arrays and equality of tube finsets.
  have htube : (I.boxData (H0 := H0) (P := P) hU W).tube = P.box :=
    Input.boxData_tube_eq_box (I := I) (P := P) (hU := hU) (W := W)
  have hF :
      (I.boxData (H0 := H0) (P := P) hU W).F f i j = I.F P W := by
    funext p
    simpa using
      (Input.boxData_F_eq_F (H0 := H0) (I := I) (P := P) (hU := hU) (W := W) (f := f)
        (i := i) (j := j) (p := p))
  -- Rewrite both sides to `coeffByProd` and use the definitional equality of `F`.
  simp [SSU.Engines.BGTypeIIArray.Data.A, SSU.Engines.BGTypeIIRankOne.Input.A, htube, hF]

end Input

end
end BGTypeIIRankOne
end Engines
end SSU
