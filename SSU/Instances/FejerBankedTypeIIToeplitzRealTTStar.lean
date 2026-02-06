import SSU.Engines.L2Multipliers
import SSU.Instances.FejerBankedPartition
import SSU.Instances.FejerBankedTypeIIToeplitzKernel

/-!
Real-frequency TT* model for Fejér-banked packets (TeX normalization with the `1/X` prefactor).

This file provides a *proved* instance of the TT*/kernel-representation step in a canonical
real-frequency Hilbert space:

* Ambient space: `L²` on the ξ-band `[-1/H, 1/H]` with measure `(1/X) dξ`.
* Packets: multiplier operators by `√K̂_H(ξ) * ψ_j(ξ/X)`.

Then the Gram entry is exactly the weighted band integral with the Lean-facing overlap weight
`wLean(ξ) = K̂_H(ξ) * conj(ψ_i(ξ/X)) * ψ_j(ξ/X)`.

This is the “TT* identity” as an abstract analytic tool; later files relate this real-frequency
model to concrete torus-side packet operators.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzRealTTStar

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus

variable {κ : Type*} [DecidableEq κ]

namespace Model

open SSU.Instances.FejerBankedTypeIIToeplitzKernel

/-- The ξ-band `|ξ| ≤ 1/H` (reusing the deterministic definition). -/
abbrev band (H : ℝ) : Set ℝ :=
  Weight.band H

/--
The TeX-normalized ξ-band measure: `(1/X) dξ` restricted to `band H`.

We package it as a scaled restricted measure so the `1/X` factor is automatic in `L²` inner
products.
-/
noncomputable def μBand (X H : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (1 / X)) • ((volume : Measure ℝ).restrict (band H))

/-- `L²` on the ξ-band, with TeX `1/X` normalization. -/
abbrev L2Band (X H : ℝ) : Type :=
  SSU.Measure.L2 (μ := μBand X H)

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable {X H : ℝ}

-- Convenience lemmas about the scaling factor.
theorem ofReal_one_div_pos (hX : 0 < X) : 0 < (ENNReal.ofReal (1 / X)) := by
  simpa [ENNReal.ofReal_pos, one_div] using (div_pos (show (0 : ℝ) < 1 by norm_num) hX)

/--
Packet multiplier on the ξ-band:

`φ_j(ξ) := √K̂_H(ξ) * ψ_j((ξ/X):𝕋)`.
-/
noncomputable def φ (X H : ℝ) (j : ℤ) (ξ : ℝ) : ℂ :=
  ((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ) *
    D.ψ j ((ξ / X : ℝ) : UC)

theorem measurable_φ (X H : ℝ) (j : ℤ) : Measurable (φ (D := D) X H j) := by
  -- `ξ ↦ √Khat(H,ξ)` is measurable and `ξ ↦ ψ_j((ξ/X):𝕋)` is measurable; multiply.
  have hKhat : Measurable fun ξ : ℝ => SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ :=
    Weight.measurable_Khat H
  have hsqrt : Measurable fun ξ : ℝ => Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) :=
    (Real.continuous_sqrt.measurable.comp hKhat)
  have hsqrtC : Measurable fun ξ : ℝ =>
      ((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.measurable.comp hsqrt)
  have htoUC : Measurable fun ξ : ℝ => ((ξ / X : ℝ) : UC) :=
    Weight.measurable_toUC_div X
  have hψ : Measurable fun ξ : ℝ => D.ψ j (((ξ / X : ℝ) : UC)) :=
    (D.measurable_ψ j).comp htoUC
  simpa [φ, mul_assoc] using hsqrtC.mul hψ

theorem norm_φ_le (hH : 0 < H) (j : ℤ) (ξ : ℝ) :
    ‖φ (D := D) X H j ξ‖ ≤ D.M * D.Φmax := by
  -- `‖√Khat‖ ≤ 1` and `‖ψ‖ ≤ M*Φmax`.
  have hKhat0 :
      0 ≤ SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ :=
    SSU.Engines.TypeII.AdmissibleKernel.Khat_nonneg (H := H) hH ξ
  have hKhat1 :
      SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ ≤ 1 :=
    SSU.Engines.TypeII.AdmissibleKernel.Khat_le_one (H := H) hH ξ
  have hsqrt1 : Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) ≤ 1 := by
    -- `√x ≤ 1 ↔ x ≤ 1`.
    exact (Real.sqrt_le_one).2 hKhat1
  have hsqrt_norm :
      ‖((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ)‖ ≤ 1 := by
    -- For nonnegative reals, `‖(r:ℂ)‖ = r`.
    have hnonneg : 0 ≤ Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) :=
      Real.sqrt_nonneg _
    simpa [Complex.norm_real, abs_of_nonneg hnonneg] using hsqrt1
  have hψ := D.norm_ψ_le (j := j) ((ξ / X : ℝ) : UC)
  calc
    ‖φ (D := D) X H j ξ‖
        = ‖((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ) *
            D.ψ j ((ξ / X : ℝ) : UC)‖ := by
              rfl
    _ = ‖((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ)‖ *
          ‖D.ψ j ((ξ / X : ℝ) : UC)‖ := by
          simpa [norm_mul]
    _ ≤ 1 * (D.M * D.Φmax) := by
          have h0 : 0 ≤ ‖D.ψ j ((ξ / X : ℝ) : UC)‖ := by positivity
          have h1 :
              ‖((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ)‖ *
                  ‖D.ψ j ((ξ / X : ℝ) : UC)‖
                ≤
              1 * ‖D.ψ j ((ξ / X : ℝ) : UC)‖ :=
            mul_le_mul_of_nonneg_right hsqrt_norm h0
          have h2 :
              1 * ‖D.ψ j ((ξ / X : ℝ) : UC)‖ ≤ 1 * (D.M * D.Φmax) :=
            mul_le_mul_of_nonneg_left hψ (by norm_num)
          exact le_trans h1 h2
    _ = D.M * D.Φmax := by simp

theorem memLp_φ (hH : 0 < H) (hX : 0 < X) (j : ℤ) :
    MemLp (φ (D := D) X H j) (∞ : ℝ≥0∞) (μBand X H) := by
  -- Use `memLp_top_of_bound` with a constant bound.
  refine MeasureTheory.memLp_top_of_bound ?_ (D.M * D.Φmax) ?_
  · -- `AEStronglyMeasurable` under the scaled restricted measure.
    have hmeas : Measurable (φ (D := D) X H j) := measurable_φ (D := D) (X := X) (H := H) j
    exact hmeas.aestronglyMeasurable
  · -- Pointwise bound a.e.
    refine Filter.Eventually.of_forall ?_
    intro ξ
    exact norm_φ_le (D := D) (X := X) (H := H) hH (j := j) ξ

/-- Packet operator on the ξ-band: multiplication by `φ_j`. -/
noncomputable def packetOp (hH : 0 < H) (hX : 0 < X) (j : ℤ) :
    L2Band X H →L[ℂ] L2Band X H :=
  SSU.Measure.mulL2Op (μ := μBand X H) (φ (D := D) X H j)
    (memLp_φ (D := D) (X := X) (H := H) hH hX j)

theorem inner_packetOp_eq_weightedIntegral
    (hH : 0 < H) (hX : 0 < X)
    (S : L2Band X H) (i j : ℤ) :
    inner ℂ (packetOp (D := D) (X := X) (H := H) hH hX i S)
        (packetOp (D := D) (X := X) (H := H) hH hX j S)
      =
    (1 / X) *
      ∫ ξ in band H,
        (Weight.wLean (D := D) X H i j ξ) * (S ξ) * star (S ξ) := by
  -- Expand the Gram entry using the generic multiplier lemma on the scaled restricted measure.
  have hinner :=
    (SSU.Measure.inner_mulL2Op_eq_integral (μ := μBand X H)
      (φ := φ (D := D) X H i) (ψ := φ (D := D) X H j)
      (hφ := memLp_φ (D := D) (X := X) (H := H) hH hX i)
      (hψ := memLp_φ (D := D) (X := X) (H := H) hH hX j)
      (f := S) (g := S))
  -- Rewrite the measure scaling into an explicit `1/X` prefactor.
  have hscale :
      (∫ ξ : ℝ,
          (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μBand X H)
        =
      ((1 / X : ℝ) : ℂ) *
        ∫ ξ in band H,
          (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) := by
    -- Use `integral_smul_measure` on the scaled restricted measure.
    let μ0 : Measure ℝ := (volume : Measure ℝ).restrict (band H)
    have htoReal :
        (ENNReal.ofReal (1 / X)).toReal = (1 / X) := by
      have hX0 : 0 ≤ X := le_of_lt hX
      have hnonneg : 0 ≤ (1 / X : ℝ) := one_div_nonneg.mpr hX0
      simpa [ENNReal.toReal_ofReal hnonneg]
    have hsmul :
        (∫ ξ : ℝ,
              (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μBand X H)
          =
        (ENNReal.ofReal (1 / X)).toReal •
          ∫ ξ : ℝ,
              (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μ0 := by
      -- Unfold `μBand` and apply the Bochner integral scaling lemma.
      -- (`μ0` is definitionally `volume.restrict (band H)`.)
      simpa [Model.μBand, μ0] using
        (integral_smul_measure
          (μ := μ0)
          (f := fun ξ : ℝ =>
            (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ))
          (c := ENNReal.ofReal (1 / X))).symm
    calc
      (∫ ξ : ℝ,
            (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μBand X H)
          =
        (ENNReal.ofReal (1 / X)).toReal •
          ∫ ξ : ℝ,
              (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μ0 := hsmul
      _ =
        ((1 / X : ℝ) : ℂ) *
          ∫ ξ : ℝ,
              (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μ0 := by
        -- Convert real scalar multiplication on `ℂ` into multiplication by the coerced real.
          -- Avoid `simp` lemmas that cancel the common right factor and introduce `∨` goals.
          have :
              (ENNReal.ofReal (1 / X)).toReal •
                  (∫ ξ : ℝ,
                      (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μ0)
                =
              (((ENNReal.ofReal (1 / X)).toReal : ℝ) : ℂ) *
                  (∫ ξ : ℝ,
                      (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μ0) := by
            simp [Complex.real_smul, mul_assoc]
          -- Now rewrite the scalar.
          have hscalar :
              (((ENNReal.ofReal (1 / X)).toReal : ℝ) : ℂ) = ((1 / X : ℝ) : ℂ) := by
            simpa using congrArg (fun r : ℝ => (r : ℂ)) htoReal
          -- Rewrite only the scalar; avoid `simp`-cancellation lemmas on products.
          -- After rewriting, the goal is definitional.
          rw [this, hscalar]
      _ =
        ((1 / X : ℝ) : ℂ) *
          ∫ ξ in band H,
            (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) := by
          rfl
  -- Simplify `star φ_i * φ_j` into the Lean-facing weight `wLean`.
  have hweight :
      (fun ξ : ℝ => (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ)) =
        fun ξ : ℝ =>
          Weight.wLean (D := D) X H i j ξ := by
    funext ξ
    -- Unfold `φ` and `wLean` and use `sqrt * sqrt = Khat` (in `ℂ`).
    have hKhat0 :
        0 ≤ SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ :=
      SSU.Engines.TypeII.AdmissibleKernel.Khat_nonneg (H := H) hH ξ
    have hsqrt_sq :
        Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) *
            Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ)
          =
        SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ := by
      simpa [pow_two] using (Real.mul_self_sqrt hKhat0)
    have hsqrtC_sq :
        (((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ) *
              ((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ))
          =
        ((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) := by
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hsqrt_sq
    -- Expand and reassociate to expose the `a*a` factor.
    set a : ℂ := ((Real.sqrt (SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ) : ℝ) : ℂ)
    have ha_star : star a = a := by simp [a]
    have ha_sq : a * a = ((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) := by
      simpa [a] using hsqrtC_sq
    -- Write everything at the evaluation point `((ξ/X):𝕋)`.
    set ψi : ℂ := D.ψ i ((ξ / X : ℝ) : UC)
    set ψj : ℂ := D.ψ j ((ξ / X : ℝ) : UC)
    -- Now: `star (a*ψi) * (a*ψj) = (a*a) * (star ψi * ψj)`.
    calc
      star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ
          =
        star (a * ψi) * (a * ψj) := by
          simp [Model.φ, a, ψi, ψj]
      _ =
        (a * a) * (star ψi * ψj) := by
          -- Expand stars and reassociate; `ℂ` is commutative.
          simp [star_mul, ha_star, mul_assoc, mul_left_comm, mul_comm]
      _ =
        ((SSU.Engines.TypeII.AdmissibleKernel.Khat H ξ : ℝ) : ℂ) * (star ψi * ψj) := by
          simp [ha_sq]
      _ = Weight.wLean (D := D) X H i j ξ := by
          -- `wLean = KhatC * conj(ψ_i) * ψ_j` (up to commuting factors).
          simp [Weight.wLean, Weight.w, ψi, ψj, mul_assoc, mul_left_comm, mul_comm]
  -- Finish: rewrite the integral, and commute `star(S)*S` into `S*star(S)`.
  -- (We keep the explicit `1/X` outside to match TeX.)
  have hcomm : ∀ ξ : ℝ, (star (S ξ) * S ξ) = (S ξ) * star (S ξ) := by
    intro ξ
    simpa [mul_comm] using (mul_comm (star (S ξ)) (S ξ))
  -- Assemble.
  calc
    inner ℂ (packetOp (D := D) (X := X) (H := H) hH hX i S)
        (packetOp (D := D) (X := X) (H := H) hH hX j S)
        =
      ∫ ξ : ℝ,
        (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) ∂μBand X H := by
          simpa [packetOp, SSU.Measure.mulL2Op] using hinner
    _ =
      ((1 / X : ℝ) : ℂ) *
        ∫ ξ in band H,
          (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ) := hscale
    _ =
      ((1 / X : ℝ) : ℂ) *
        ∫ ξ in band H,
          (Weight.wLean (D := D) X H i j ξ) * ((S ξ) * star (S ξ)) := by
          -- Rewrite the weight and commute `star(S)*S`.
          refine congrArg (fun z : ℂ => ((1 / X : ℝ) : ℂ) * z) ?_
          refine integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro ξ
          have hw : star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ =
              Weight.wLean (D := D) X H i j ξ := by
            simpa using congrArg (fun f => f ξ) hweight
          have hc : star (S ξ) * S ξ = (S ξ) * star (S ξ) := hcomm ξ
          calc
            (star (φ (D := D) X H i ξ) * φ (D := D) X H j ξ) * (star (S ξ) * S ξ)
                =
              (Weight.wLean (D := D) X H i j ξ) * (star (S ξ) * S ξ) := by
                -- Multiply the pointwise identity `hw` by the common right factor.
                simpa using congrArg (fun t : ℂ => t * (star (S ξ) * S ξ)) hw
            _ =
              (Weight.wLean (D := D) X H i j ξ) * ((S ξ) * star (S ξ)) := by
                -- Multiply the pointwise identity `hc` by the common left factor.
                simpa [mul_assoc] using congrArg (fun t : ℂ => (Weight.wLean (D := D) X H i j ξ) * t) hc
    _ = (1 / X) *
        ∫ ξ in band H,
          (Weight.wLean (D := D) X H i j ξ) * (S ξ) * star (S ξ) := by
          -- Reassociate, and drop the explicit `((1/X):ℂ)` cast.
          simp [mul_assoc]

end Model

end

end FejerBankedTypeIIToeplitzRealTTStar
end Instances
end SSU
