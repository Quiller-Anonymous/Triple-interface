import SSU.Instances.FejerBankedPartition
import SSU.Engines.BGTypeIIArrayWeightedToeplitz
import SSU.Engines.TypeII
import SSU.Engines.TypeIIProductToeplitzComplex

/-!
Fejér-banked packets: Toeplitz kernel with packet overlap factor.

This file defines the TeX-faithful weight

`w_{i,j}(ξ) := K̂_H(ξ) * ψ_i(ξ/X) * conj(ψ_j(ξ/X))`

and the induced Toeplitz kernel

`K_{i,j}(h) := ∫_{|ξ|≤1/H} w_{i,j}(ξ) e(ξ h / X) dξ`.

It then specializes the deterministic Toeplitzization lemma so that the *weighted* product
exponential sum `prodSumRealByProd` (built from `A_k`) yields the `k,k'` Toeplitz form with this
pair-dependent complex kernel.

This is purely bookkeeping: it does not prove that any particular packet Gram equals such an
integral; that extraction is the application-specific “ReductionToTubeForm” step.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzKernel

open scoped BigOperators

noncomputable section

open MeasureTheory
open SSU.Engines.TypeII

namespace Weight

open SSU.Torus

variable {κ : Type*} [DecidableEq κ]

abbrev band (H : ℝ) : Set ℝ :=
  SSU.Engines.BGTypeIIWeightedToeplitz.band H

/-- Measurability of the truncated Fejér density `K̂_H`. -/
theorem measurable_Khat (H : ℝ) : Measurable (SSU.Engines.TypeII.AdmissibleKernel.Khat H) := by
  classical
  -- `Khat H ξ := if |ξ| ≤ H⁻¹ then H * |ξ| else 0`.
  refine Measurable.ite ?_ ?_ measurable_const
  · -- `{ξ | |ξ| ≤ H⁻¹}` is measurable.
    simpa using (measurableSet_le measurable_abs measurable_const)
  · simpa [SSU.Engines.TypeII.AdmissibleKernel.Khat] using (measurable_const.mul measurable_abs)

/-- The “torus point” map `ξ ↦ (ξ/X : UC)` is measurable. -/
theorem measurable_toUC_div (X : ℝ) : Measurable fun ξ : ℝ => ((ξ / X : ℝ) : UC) := by
  -- Use continuity of `AddCircle.mk` and of multiplication by a constant.
  have hcont_div : Continuous fun ξ : ℝ => ξ / X := by
    simpa [div_eq_mul_inv] using (continuous_id.mul continuous_const)
  -- `AddCircle.mk` is continuous.
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ))).measurable.comp hcont_div.measurable

/-- TeX weight with packet overlap: `w_{i,j}(ξ) := K̂_H(ξ) * ψ_i(ξ/X) * conj(ψ_j(ξ/X))`. -/
noncomputable def w
    (D : SSU.Instances.FejerBankedPartition.Data κ)
    (X H : ℝ) (i j : ℤ) (ξ : ℝ) : ℂ :=
  ((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) *
    (D.ψ i ((ξ / X : ℝ) : UC)) * star (D.ψ j ((ξ / X : ℝ) : UC))

/--
Lean-facing packet-overlap weight.

Mathlib’s `inner` is conjugate-linear in the first argument, so the Gram integrand for multiplier
packets naturally involves `conj(ψ_i) * ψ_j`, i.e. `star (w_{i,j}) / K̂_H`.

We keep `w` as the TeX-facing weight and use `wLean := star w` when connecting to Lean’s `inner`.
-/
noncomputable def wLean
    (D : SSU.Instances.FejerBankedPartition.Data κ)
    (X H : ℝ) (i j : ℤ) (ξ : ℝ) : ℂ :=
  star (w (D := D) X H i j ξ)

/-- Induced complex Toeplitz kernel `K_{i,j}(h)` from the packet-overlap weight. -/
noncomputable abbrev K
    (D : SSU.Instances.FejerBankedPartition.Data κ)
    (X H : ℝ) (i j : ℤ) (h : ℤ) : ℂ :=
  SSU.Engines.BGTypeIIWeightedToeplitz.K X H (fun ξ => w (D := D) X H i j ξ) h

/-- Induced complex Toeplitz kernel from the Lean-facing weight `wLean`. -/
noncomputable abbrev KLean
    (D : SSU.Instances.FejerBankedPartition.Data κ)
    (X H : ℝ) (i j : ℤ) (h : ℤ) : ℂ :=
  SSU.Engines.BGTypeIIWeightedToeplitz.K X H (fun ξ => wLean (D := D) X H i j ξ) h

  theorem norm_w_le
      (D : SSU.Instances.FejerBankedPartition.Data κ)
      (X H : ℝ)
      (hH : 0 < H)
      (i j : ℤ)
      (ξ : ℝ) :
      ‖w (D := D) X H i j ξ‖ ≤
        (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) * (D.M * D.Φmax) ^ 2 := by
    -- Use `‖abc‖ ≤ ‖a‖‖b‖‖c‖`, and the pointwise bound `‖ψ‖ ≤ M*Φmax`.
    have hψi : ‖D.ψ i ((ξ / X : ℝ) : UC)‖ ≤ D.M * D.Φmax := D.norm_ψ_le (j := i) _
    have hψj : ‖D.ψ j ((ξ / X : ℝ) : UC)‖ ≤ D.M * D.Φmax := D.norm_ψ_le (j := j) _
    have hKhat_nonneg : 0 ≤ SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ :=
      SSU.Engines.TypeII.AdmissibleKernel.Khat_nonneg (H := H) hH ξ
    -- `Khat ≥ 0`, so `‖(Khat : ℂ)‖ = Khat`.
    have hKhat :
        ‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ)‖ =
          SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ := by
      simpa [Complex.norm_real, abs_of_nonneg hKhat_nonneg]
    have hMΦ_nonneg : 0 ≤ D.M * D.Φmax := mul_nonneg D.M_nonneg D.Φmax_nonneg
    calc
      ‖w (D := D) X H i j ξ‖
          = ‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) *
              (D.ψ i ((ξ / X : ℝ) : UC)) * star (D.ψ j ((ξ / X : ℝ) : UC))‖ := by
                rfl
      _ ≤ ‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ)‖ *
            ‖D.ψ i ((ξ / X : ℝ) : UC)‖ * ‖star (D.ψ j ((ξ / X : ℝ) : UC))‖ := by
            -- `‖a*b*c‖ ≤ ‖a‖‖b‖‖c‖`
            simpa [mul_assoc] using
              (calc
                ‖(((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) *
                    (D.ψ i ((ξ / X : ℝ) : UC))) * star (D.ψ j ((ξ / X : ℝ) : UC))‖
                    ≤
                    ‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) *
                        (D.ψ i ((ξ / X : ℝ) : UC))‖ *
                      ‖star (D.ψ j ((ξ / X : ℝ) : UC))‖ := by
                      simpa using
                        (norm_mul_le
                          (((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) *
                            (D.ψ i ((ξ / X : ℝ) : UC)))
                          (star (D.ψ j ((ξ / X : ℝ) : UC))))
                _ ≤ (‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ)‖ *
                      ‖D.ψ i ((ξ / X : ℝ) : UC)‖) * ‖star (D.ψ j ((ξ / X : ℝ) : UC))‖ := by
                      exact
                        mul_le_mul_of_nonneg_right
                          (norm_mul_le
                            ((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ)
                            (D.ψ i ((ξ / X : ℝ) : UC)))
                          (norm_nonneg _)
                _ = ‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ)‖ *
                      ‖D.ψ i ((ξ / X : ℝ) : UC)‖ *
                      ‖star (D.ψ j ((ξ / X : ℝ) : UC))‖ := by
                      ring)
      _ = (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) *
            ‖D.ψ i ((ξ / X : ℝ) : UC)‖ * ‖D.ψ j ((ξ / X : ℝ) : UC)‖ := by
            have hstar :
                ‖star (D.ψ j ((ξ / X : ℝ) : UC))‖ = ‖D.ψ j ((ξ / X : ℝ) : UC)‖ := by
              simpa using (norm_star (D.ψ j ((ξ / X : ℝ) : UC)))
            calc
              ‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ)‖ *
                    ‖D.ψ i ((ξ / X : ℝ) : UC)‖ * ‖star (D.ψ j ((ξ / X : ℝ) : UC))‖
                  =
                  ‖((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ)‖ *
                    ‖D.ψ i ((ξ / X : ℝ) : UC)‖ * ‖D.ψ j ((ξ / X : ℝ) : UC)‖ := by
                    rw [hstar]
              _ = (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) *
                    ‖D.ψ i ((ξ / X : ℝ) : UC)‖ * ‖D.ψ j ((ξ / X : ℝ) : UC)‖ := by
                    rw [hKhat]
      _ ≤ (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) * (D.M * D.Φmax) * (D.M * D.Φmax) := by
            have hprod :
                ‖D.ψ i ((ξ / X : ℝ) : UC)‖ * ‖D.ψ j ((ξ / X : ℝ) : UC)‖ ≤
                  (D.M * D.Φmax) * (D.M * D.Φmax) :=
              mul_le_mul hψi hψj (norm_nonneg _) hMΦ_nonneg
            have := mul_le_mul_of_nonneg_left hprod hKhat_nonneg
            simpa [mul_assoc] using this
      _ = (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) * (D.M * D.Φmax) ^ 2 := by
            ring_nf

  /-- The overlap-weight `w_{i,j}` is integrable on the ξ-band. -/
  theorem integrableOn_w
      (D : SSU.Instances.FejerBankedPartition.Data κ)
      (X H : ℝ)
      (hH : 0 < H)
      (i j : ℤ) :
      IntegrableOn (fun ξ => w (D := D) X H i j ξ) (band H) := by
    classical
    -- Dominating integrable real function.
    have hKhat_int :
        IntegrableOn (SSU.Engines.TypeII.AdmissibleKernel.Khat H) (band H) := by
      -- `band H = [-1/H, 1/H] = [-H⁻¹, H⁻¹]`.
      have hband : band H = Set.Icc (-H⁻¹) H⁻¹ := by
        simp [band, SSU.Engines.BGTypeIIWeightedToeplitz.band, one_div]
      simpa [hband] using (SSU.Engines.TypeII.AdmissibleKernel.Khat_integrableOn (H := H) hH)
    have hdom_int :
        IntegrableOn
          (fun ξ => (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) * (D.M * D.Φmax) ^ 2)
          (band H) := by
      -- multiply by a constant
      simpa [mul_assoc] using hKhat_int.mul_const ((D.M * D.Φmax) ^ 2)
    -- Measurability of `w`.
    have hmeasKhatC :
        Measurable fun ξ : ℝ =>
          ((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.measurable.comp (measurable_Khat (H := H)))
    have hmeas_toUC : Measurable fun ξ : ℝ => ((ξ / X : ℝ) : UC) := measurable_toUC_div X
    have hmeas_ψi :
        Measurable fun ξ : ℝ => D.ψ i (((ξ / X : ℝ) : UC)) :=
      (D.measurable_ψ i).comp hmeas_toUC
    have hmeas_ψj :
        Measurable fun ξ : ℝ => D.ψ j (((ξ / X : ℝ) : UC)) :=
      (D.measurable_ψ j).comp hmeas_toUC
    have hw_mble :
        AEStronglyMeasurable (fun ξ => w (D := D) X H i j ξ)
          ((volume : Measure ℝ).restrict (band H)) := by
      -- `Measurable` implies `AEStronglyMeasurable` for any measure.
      have hw_meas : Measurable (fun ξ => w (D := D) X H i j ξ) := by
        have hψj_star : Measurable fun ξ : ℝ => star (D.ψ j (((ξ / X : ℝ) : UC))) :=
          continuous_star.measurable.comp hmeas_ψj
        -- `w = (KhatC * ψi) * star(ψj)`
        simpa [w, mul_assoc] using (hmeasKhatC.mul hmeas_ψi).mul hψj_star
      exact hw_meas.aestronglyMeasurable
    -- Apply the dominated integrability lemma on the restricted measure.
    -- Convert everything to `Integrable` on the restricted measure and use `Integrable.mono'`.
    have hdom_int' :
        Integrable
          (fun ξ => (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) * (D.M * D.Φmax) ^ 2)
          ((volume : Measure ℝ).restrict (band H)) := by
      simpa [MeasureTheory.IntegrableOn] using hdom_int
    have hw_int :
        Integrable (fun ξ => w (D := D) X H i j ξ) ((volume : Measure ℝ).restrict (band H)) :=
      MeasureTheory.Integrable.mono' hdom_int' hw_mble <|
        (Filter.Eventually.of_forall fun ξ =>
          norm_w_le (D := D) (X := X) (H := H) hH (i := i) (j := j) ξ)
    simpa [MeasureTheory.IntegrableOn] using hw_int

  theorem integrableOn_wLean
      (D : SSU.Instances.FejerBankedPartition.Data κ)
      (X H : ℝ)
      (hH : 0 < H)
      (i j : ℤ) :
      IntegrableOn (fun ξ => wLean (D := D) X H i j ξ) (band H) := by
    have hw : IntegrableOn (fun ξ => w (D := D) X H i j ξ) (band H) :=
      integrableOn_w (D := D) (X := X) (H := H) hH i j
    have hw' :
        Integrable (fun ξ => w (D := D) X H i j ξ) ((volume : Measure ℝ).restrict (band H)) := by
      simpa [MeasureTheory.IntegrableOn] using hw
    have hwStar :
        Integrable (fun ξ => star (w (D := D) X H i j ξ))
          ((volume : Measure ℝ).restrict (band H)) := by
      refine ⟨(MeasureTheory.AEStronglyMeasurable.star hw'.1), ?_⟩
      -- `‖star z‖ = ‖z‖`, hence the same finite-integral bound.
      simpa [MeasureTheory.HasFiniteIntegral, norm_star] using hw'.2
    simpa [MeasureTheory.IntegrableOn, wLean] using hwStar

end Weight

open SSU.Engines.TypeII.ProductToeplitz

theorem integral_weight_mul_prodSumRealByProd_mul_star
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    {κ : Type*} [DecidableEq κ]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (D : SSU.Engines.BGTypeIIArray.Data H0)
    (X H : ℝ) (f : H0) (i j : ℤ)
    (hH : 0 < H)
    (hw : IntegrableOn (fun ξ => Weight.wLean (D := Dpacket) X H i j ξ) (Weight.band H))
    (hX : X ≠ 0) :
    (∫ ξ in Weight.band H,
        (Weight.wLean (D := Dpacket) X H i j ξ) *
          (D.prodSumRealByProd X ξ f i j) * star (D.prodSumRealByProd X ξ f i j))
      =
    ∑ k ∈ (D.tube).image prod, ∑ k' ∈ (D.tube).image prod,
      (D.A f i j k') * star (D.A f i j k) *
        (Weight.KLean (D := Dpacket) X H i j (k' - k)) := by
  classical
  -- This is the deterministic Toeplitzization lemma, specialized to the TeX product sum.
  simpa [Weight.KLean, Weight.wLean, Weight.K, Weight.w, Weight.band] using
    (SSU.Engines.BGTypeIIArrayWeightedToeplitz.integral_weight_mul_prodSumRealByProd_mul_star
      (D := D) (X := X) (H := H) (w := fun ξ => Weight.wLean (D := Dpacket) X H i j ξ)
      (f := f) (i := i) (j := j) (hH := hH) (hw := hw) (hX := hX))

theorem integral_weight_mul_prodSumRealByProd_mul_star_auto
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    {κ : Type*} [DecidableEq κ]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (D : SSU.Engines.BGTypeIIArray.Data H0)
    (X H : ℝ) (f : H0) (i j : ℤ)
    (hH : 0 < H)
    (hX : X ≠ 0) :
    (∫ ξ in Weight.band H,
        (Weight.wLean (D := Dpacket) X H i j ξ) *
          (D.prodSumRealByProd X ξ f i j) * star (D.prodSumRealByProd X ξ f i j))
      =
    ∑ k ∈ (D.tube).image prod, ∑ k' ∈ (D.tube).image prod,
      (D.A f i j k') * star (D.A f i j k) *
        (Weight.KLean (D := Dpacket) X H i j (k' - k)) := by
  have hw :
      IntegrableOn (fun ξ => Weight.wLean (D := Dpacket) X H i j ξ) (Weight.band H) :=
    Weight.integrableOn_wLean (D := Dpacket) (X := X) (H := H) hH i j
  exact integral_weight_mul_prodSumRealByProd_mul_star
    (Dpacket := Dpacket) (D := D) (X := X) (H := H) (f := f) (i := i) (j := j)
    (hH := hH) (hw := hw) (hX := hX)

/--
Same as `integral_weight_mul_prodSumRealByProd_mul_star`, but with the RHS packaged as the
`ProductToeplitz.toeplitzFormTeXC` normalization for the underlying tube array `D.F f i j`.
-/
theorem integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    {κ : Type*} [DecidableEq κ]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (D : SSU.Engines.BGTypeIIArray.Data H0)
    (X H : ℝ) (f : H0) (i j : ℤ)
    (hH : 0 < H)
    (hw : IntegrableOn (fun ξ => Weight.wLean (D := Dpacket) X H i j ξ) (Weight.band H))
    (hX : X ≠ 0) :
    (∫ ξ in Weight.band H,
        (Weight.wLean (D := Dpacket) X H i j ξ) *
          (D.prodSumRealByProd X ξ f i j) * star (D.prodSumRealByProd X ξ f i j))
      =
    SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
      (K := fun h => Weight.KLean (D := Dpacket) X H i j h)
      (T := D.tube)
      (F := D.F f i j) := by
  classical
  -- Expand the `toeplitzFormTeXC` definition and rewrite `D.A` in terms of `coeffByProd`.
  -- The resulting double sum is exactly the RHS of `integral_weight_mul_prodSumRealByProd_mul_star`.
  simpa [SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC, SSU.Engines.BGTypeIIArray.Data.A]
    using (integral_weight_mul_prodSumRealByProd_mul_star
      (Dpacket := Dpacket) (D := D) (X := X) (H := H) (f := f) (i := i) (j := j)
      (hH := hH) (hw := hw) (hX := hX))

theorem integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
    {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    {κ : Type*} [DecidableEq κ]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (D : SSU.Engines.BGTypeIIArray.Data H0)
    (X H : ℝ) (f : H0) (i j : ℤ)
    (hH : 0 < H)
    (hX : X ≠ 0) :
    (∫ ξ in Weight.band H,
        (Weight.wLean (D := Dpacket) X H i j ξ) *
          (D.prodSumRealByProd X ξ f i j) * star (D.prodSumRealByProd X ξ f i j))
      =
    SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
      (K := fun h => Weight.KLean (D := Dpacket) X H i j h)
      (T := D.tube)
      (F := D.F f i j) := by
  have hw :
      IntegrableOn (fun ξ => Weight.wLean (D := Dpacket) X H i j ξ) (Weight.band H) :=
    Weight.integrableOn_wLean (D := Dpacket) (X := X) (H := H) hH i j
  exact integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC
    (Dpacket := Dpacket) (D := D) (X := X) (H := H) (f := f) (i := i) (j := j)
    (hH := hH) (hw := hw) (hX := hX)

end

end FejerBankedTypeIIToeplitzKernel
end Instances
end SSU
