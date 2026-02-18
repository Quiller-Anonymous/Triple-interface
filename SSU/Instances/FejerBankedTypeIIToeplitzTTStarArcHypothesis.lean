import SSU.Instances.FejerBankedTypeIIToeplitzBandToArc
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis
import SSU.Engines.BGTypeIIArray

/-!
Fejér-banked packets: TT* / kernel-representation step as an *arc* statement on `𝕋`.

The TeX normalization uses the substitution `x = ξ / X`, yielding a Jacobian factor `1/X`.  For
bookkeeping (and to avoid carrying the real variable `ξ` everywhere), it is convenient to package
the TT* step as an identity of the form

`inner(...) = ∫_{𝕋} 1_arc(x) * (K̂_H(X*x) * packetOverlap(x) * |S(x)|²) dx`,

then convert it deterministically into the `ξ`-band integral in
`FejerBankedTypeIIToeplitzTTStarHypothesis`.

This file provides that deterministic conversion.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTTStarArcHypothesis

open scoped BigOperators

noncomputable section

open MeasureTheory
open SSU.Torus

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace Khat

open SSU.Engines.TypeII

abbrev KhatReal (H : ℝ) : ℝ → ℝ := AdmissibleKernel.Khat H

/--
Torus function encoding the TeX factor `K̂_H(ξ)` after the substitution `ξ = X*x`:

`KhatTorus(X,H)(x) = KhatReal(H) (X * xRep)`,

where `xRep` is the representative in the fundamental domain `Ioc (-1/2) (1/2]`.
-/
noncomputable def KhatTorus (X H : ℝ) : UC → ℝ :=
  AddCircle.liftIoc (p := (1 : ℝ)) (a := (-(1 / 2 : ℝ)))
    (fun x : ℝ => KhatReal H (X * x))

theorem KhatTorus_coe_apply
    (X H x : ℝ)
    (hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))) :
    KhatTorus X H (x : UC) = KhatReal H (X * x) := by
  -- `liftIoc` agrees with the original function on `Ioc`.
  simpa [KhatTorus] using
    (AddCircle.liftIoc_coe_apply (p := (1 : ℝ)) (a := (-(1 / 2 : ℝ)))
      (f := fun x : ℝ => KhatReal H (X * x)) (x := x) hx)

/-!
TeX substitution lemma for the kernel weight:

If `|ξ| ≤ 1/H` and `(1/H)/X < 1/2`, then evaluating `KhatTorus(X,H)` at the torus point `x = ξ/X`
recovers `KhatReal(H) ξ` (no wrap-around).

This is the deterministic core of the “`ξ = X*x`” bookkeeping used in the arc-form TT* interface.
-/
theorem KhatTorus_eval_eq_Khat_on_band
    {X H : ℝ} (hX : 0 < X) (hH : 0 < H) (hsmall : (1 / H) / X < (1 / 2 : ℝ))
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1 / H)) (1 / H)) :
    KhatTorus X H ((ξ / X : ℝ) : UC) = KhatReal H ξ := by
  -- Show `ξ/X` lies in the fundamental domain `Ioc (-1/2) (1/2]` (in fact, strict `Ioo`).
  have habs : |ξ / X| ≤ (1 / H) / X := by
    have hξabs : |ξ| ≤ (1 / H) := by
      have : - (1 / H) ≤ ξ ∧ ξ ≤ (1 / H) := by
        simpa [Set.mem_Icc] using hξ
      exact abs_le.2 this
    have hdiv : |ξ| / X ≤ (1 / H) / X :=
      div_le_div_of_nonneg_right hξabs hX.le
    simpa [abs_div, abs_of_pos hX] using hdiv
  have hx_lt : |ξ / X| < (1 / 2 : ℝ) := lt_of_le_of_lt habs hsmall
  have hxIoo : (ξ / X) ∈ Set.Ioo (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
    have hx' : (-(1 / 2 : ℝ)) < (ξ / X) ∧ (ξ / X) < (1 / 2 : ℝ) :=
      (abs_lt.1 hx_lt)
    have : (ξ / X) < ((-(1 / 2 : ℝ)) + (1 : ℝ)) := by
      nlinarith [hx'.2]
    exact ⟨hx'.1, this⟩
  have hxIoc : (ξ / X) ∈ Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ)) :=
    ⟨hxIoo.1, le_of_lt hxIoo.2⟩
  -- Evaluate `KhatTorus` by `liftIoc_coe_apply`.
  have hK := (KhatTorus_coe_apply (X := X) (H := H) (x := (ξ / X)) hxIoc)
  have hmul : X * (ξ / X) = ξ := by
    have hXne : X ≠ 0 := ne_of_gt hX
    -- Avoid `simp` blowups; `field_simp` handles the cancellation cleanly.
    field_simp [hXne]
  simpa [hmul] using hK

end Khat

open Khat

namespace Arc

open SSU.Torus.BandMap

abbrev arcAtBand (X H : ℝ) : Set UC :=
  SSU.Torus.BandMap.arc (-(1 / H) / X) ((1 / H) / X)

end Arc

open Arc

variable {κ : Type*} [DecidableEq κ]

/--
Arc-form TT* hypothesis: the packet Gram is represented as a torus integral over the small arc
`|x| ≤ 1/(H*X)` of the *lifted* weight `K̂_H(X*x)` times the packet overlap and the Type–II signal
evaluated on `𝕋`.

This is equivalent (deterministically) to the `ξ`-band statement in
`FejerBankedTypeIIToeplitzTTStarHypothesis.Hypothesis`, under the “no wrap-around” smallness
assumption `(1/H)/X < 1/2`.
-/
structure Hypothesis where
  Dpacket : SSU.Instances.FejerBankedPartition.Data κ
  Dtype : SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2
  hX : 0 < Dpacket.X
  hH : 0 < Dpacket.H
  hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)
  /-- Arc-form TT* reduction: packet Gram = arc integral. -/
  inner_eq_arcIntegral :
    ∀ f : SSU.Torus.L2, ∀ i ∈ Dpacket.J, ∀ j ∈ Dpacket.J,
      inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
        =
      ∫ z : UC,
        (arcAtBand Dpacket.X Dpacket.H).indicator
          (fun x =>
            (((KhatTorus Dpacket.X Dpacket.H x : ℝ) : ℂ) *
              star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
              (Dtype.prodSumTorusByProd f i j x) *
                star (Dtype.prodSumTorusByProd f i j x))
          z

namespace Hypothesis

variable (h : Hypothesis (κ := κ))

private theorem KhatTorus_eval_eq_Khat_on_band
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H)) :
    KhatTorus h.Dpacket.X h.Dpacket.H ((ξ / h.Dpacket.X : ℝ) : UC)
      =
    SSU.Engines.TypeII.AdmissibleKernel.Khat h.Dpacket.H ξ := by
  -- Delegate to the public deterministic lemma in `namespace Khat`.
  simpa [Khat.KhatReal] using
    (Khat.KhatTorus_eval_eq_Khat_on_band
      (X := h.Dpacket.X) (H := h.Dpacket.H)
      (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall)
      (ξ := ξ) hξ)

/--
Convert an arc-form TT* hypothesis into the `ξ`-band TT* hypothesis.
-/
noncomputable def toBandHypothesis :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.Hypothesis (κ := κ) where
  Dpacket := h.Dpacket
  Dtype := h.Dtype
  hH := h.hH
  hX := (ne_of_gt h.hX)
  inner_eq_weightedIntegral := by
    classical
    intro f i hi j hj
    -- Start from the arc identity.
    have harc := h.inner_eq_arcIntegral (f := f) (i := i) hi (j := j) hj
    -- Rewrite the arc integral as the TeX band integral, with the `1/X` prefactor.
    -- Use the deterministic band→arc bridge with `g :=` the torus integrand.
    let g : UC → ℂ :=
      fun x =>
        (((KhatTorus h.Dpacket.X h.Dpacket.H x : ℝ) : ℂ) *
            star (h.Dpacket.ψ i x) * (h.Dpacket.ψ j x)) *
          (h.Dtype.prodSumTorusByProd f i j x) *
            star (h.Dtype.prodSumTorusByProd f i j x)
    have hbandToArc :
        ((1 / h.Dpacket.X : ℝ) •
            ∫ ξ in Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H), g ((ξ / h.Dpacket.X : ℝ) : UC))
          =
        ∫ z : UC, (arcAtBand h.Dpacket.X h.Dpacket.H).indicator g z := by
      -- `one_div_X_smul_integral_band_eval_eq_integral_indicator_arc`.
      simpa [Arc.arcAtBand, SSU.Torus.BandMap.arc, g, div_eq_mul_inv, mul_assoc] using
        (SSU.Instances.FejerBankedTypeIIToeplitzBandToArc.one_div_X_smul_integral_band_eval_eq_integral_indicator_arc
          (X := h.Dpacket.X) (H := h.Dpacket.H) (hX := h.hX) (hH := h.hH) (hsmall := h.hsmall) g)
    -- So the arc integral equals the band integral.
    have harc' :
        (∫ z : UC, (arcAtBand h.Dpacket.X h.Dpacket.H).indicator g z)
          =
        ((1 / h.Dpacket.X : ℝ) •
            ∫ ξ in Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H), g ((ξ / h.Dpacket.X : ℝ) : UC)) := by
      simpa using hbandToArc.symm
    -- Replace `g((ξ/X):𝕋)` by the TeX integrand with `Khat` and `prodSumRealByProd`.
    -- 1) `KhatTorus((ξ/X):𝕋) = Khat ξ` on the band.
    -- 2) `prodSumTorusByProd((ξ/X):𝕋) = prodSumRealByProd X ξ`.
    have hbridgeProd :
        ∀ ξ : ℝ,
          h.Dtype.prodSumTorusByProd f i j ((ξ / h.Dpacket.X : ℝ) : UC)
            =
          h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j := by
      intro ξ
      -- rewrite using the deterministic bridge lemma in `BGTypeIIArray`.
      simpa using
        (h.Dtype.prodSumRealByProd_eq_prodSumTorusByProd (X := h.Dpacket.X) (ξ := ξ) (f := f) (i := i) (j := j)).symm
    have hcongr :
        (fun ξ : ℝ => g ((ξ / h.Dpacket.X : ℝ) : UC))
          =ᵐ[(volume : Measure ℝ).restrict (Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H))]
        (fun ξ : ℝ =>
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ) *
            (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j) *
              star (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j)) := by
      -- pointwise equality on the restricted set
      have hs : MeasurableSet (Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H)) := by
        measurability
      filter_upwards [ae_restrict_mem hs] with ξ hξ
      have hK : KhatTorus h.Dpacket.X h.Dpacket.H ((ξ / h.Dpacket.X : ℝ) : UC) =
          SSU.Engines.TypeII.AdmissibleKernel.Khat h.Dpacket.H ξ :=
        h.KhatTorus_eval_eq_Khat_on_band (ξ := ξ) (hξ := hξ)
      have hP : h.Dtype.prodSumTorusByProd f i j ((ξ / h.Dpacket.X : ℝ) : UC)
            =
          h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j :=
        hbridgeProd ξ
      -- Unfold only the small definitions needed for the `wLean` normalization.
      have hw :
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ
            =
          (((SSU.Engines.TypeII.AdmissibleKernel.Khat h.Dpacket.H ξ : ℝ) : ℂ) *
              star (h.Dpacket.ψ i ((ξ / h.Dpacket.X : ℝ) : UC)) *
                (h.Dpacket.ψ j ((ξ / h.Dpacket.X : ℝ) : UC))) := by
        -- `wLean = star w`, and `star` flips the packet overlap.
        simp [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean,
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.w, mul_assoc]
      -- Now the integrands match by reassociation.
      -- (Use `hK` to rewrite `KhatTorus` and `hP` to rewrite the Type–II signal.)
      simp [g, hw, hK, hP, mul_assoc]
    -- Convert scalar smul into multiplication by `(1/X : ℝ)` in `ℂ` for the final statement.
    -- Start from `harc`, rewrite RHS using `harc'`, then rewrite the integral by `hcongr`.
    calc
      inner ℂ (((h.Dpacket.toMultiplierModel).packetOpUnnormalized i) f)
          (((h.Dpacket.toMultiplierModel).packetOpUnnormalized j) f)
          =
        ∫ z : UC, (arcAtBand h.Dpacket.X h.Dpacket.H).indicator g z := harc
      _ =
        ((1 / h.Dpacket.X : ℝ) •
            ∫ ξ in Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H), g ((ξ / h.Dpacket.X : ℝ) : UC)) := harc'
      _ =
        ((1 / h.Dpacket.X : ℝ) •
            ∫ ξ in Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H),
              (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                    (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ) *
                (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j) *
                  star (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j)) := by
          -- replace the integrand a.e.
          refine congrArg (fun z : ℂ => ((1 / h.Dpacket.X : ℝ) • z)) ?_
          -- `integral_congr_ae` on the restricted measure
          simpa [MeasureTheory.integral] using integral_congr_ae hcongr
      _ =
        (1 / h.Dpacket.X) *
          ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band h.Dpacket.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := h.Dpacket) h.Dpacket.X h.Dpacket.H i j ξ) *
              (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j) *
                star (h.Dtype.prodSumRealByProd h.Dpacket.X ξ f i j) := by
          -- `band H` is definitionally the same closed interval.
          -- Also turn `smul` by a real into multiplication in `ℂ`.
          have hband :
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band h.Dpacket.H
                =
              Set.Icc (-(1 / h.Dpacket.H)) (1 / h.Dpacket.H) := by
            simp [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band,
              SSU.Engines.BGTypeIIWeightedToeplitz.band, one_div]
          -- `((r:ℝ) • z) = ((r:ℝ):ℂ) * z` for `ℂ`.
          simp [hband, Complex.real_smul, mul_assoc]

end Hypothesis

end

end FejerBankedTypeIIToeplitzTTStarArcHypothesis
end Instances
end SSU
