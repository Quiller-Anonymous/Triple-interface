import SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar
import SSU.Engines.BGTypeIIRankOne
import SSU.Engines.BGTypeIIRankOneSignal
import SSU.Engines.BGTypeIIWeightedToeplitz
import SSU.Engines.TypeIIProductToeplitzComplex
import SSU.Instances.FejerBankedTypeIIToeplitzBandToArc
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
First non-toy proved Toeplitz Type–II reduction in the real-frequency TT* model.

This file is a “platinum milestone” for the SSU Toeplitz pipeline:

* packets live on the ξ-band `[-1/H,1/H]` with TeX-normalized measure `(1/X)dξ`, and
  are multipliers by `√K̂_H(ξ) * ψ_j((ξ/X):𝕋)` (proved TT* identity);
* the input signal is the TeX rank-one Type–II product exponential sum
    `S(ξ) = ∑_{k} A_k e(ξ k / X)`
  coming from a dyadic box coefficient array `F(d,n) = α_d β_n W(d/D,n/N)`; and
* we Toeplitzize the weighted band integral to get the TeX `k,k'` Toeplitz quadratic form with
  induced kernel `K_{i,j}`.

This does *not* yet connect torus-side packet operators to the ξ-band model; that bridge is a later
step in the end-to-end SSU project plan.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzRankOneReal

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus
open SSU.Engines.TypeII

variable {κ : Type*} [DecidableEq κ]

namespace RankOne

open SSU.Engines.BGTypeIIRankOne
open SSU.Engines.BGTypeIIRankOne.Input
open SSU.Engines.TypeII.ProductToeplitz
open SSU.Instances.FejerBankedTypeIIToeplitzKernel

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : Input)

abbrev Sset : Finset ℤ :=
  P.box.image prod

noncomputable def A (k : ℤ) : ℂ :=
  I.A (P := P) (W := W) k

/-- The TeX real-frequency product exponential sum `S(ξ) = ∑_k A_k e(ξ k / X)`. -/
noncomputable def Sfun (ξ : ℝ) : ℂ :=
  ∑ k ∈ Sset (P := P), (A (I := I) (P := P) (W := W) k) * e (ξ * (k : ℝ) / D.X)

theorem Sfun_eq_signalRealByProd (ξ : ℝ) :
    Sfun (D := D) (I := I) (P := P) (W := W) ξ = I.signalRealByProd P W D.X ξ := by
  classical
  simp [Sfun, Input.signalRealByProd, Sset, A]

theorem measurable_Sfun : Measurable (Sfun (D := D) (I := I) (P := P) (W := W)) := by
  classical
  -- Finite sum of continuous functions.
  have hterm (k : ℤ) (_hk : k ∈ Sset (P := P)) :
      Measurable fun ξ : ℝ => (A (I := I) (P := P) (W := W) k) * e (ξ * (k : ℝ) / D.X) := by
    have hcont : Continuous fun ξ : ℝ => e (ξ * (k : ℝ) / D.X) := by
      have : Continuous fun ξ : ℝ => ξ * (k : ℝ) / D.X := by
        simpa [div_eq_mul_inv, mul_assoc] using (continuous_id.mul continuous_const)
      exact continuous_e.comp this
    simpa using (measurable_const.mul hcont.measurable)
  simpa [Sfun] using (Finset.measurable_sum (s := Sset (P := P)) (f := fun k ξ =>
    (A (I := I) (P := P) (W := W) k) * e (ξ * (k : ℝ) / D.X)) hterm)

theorem norm_Sfun_le (ξ : ℝ) :
    ‖Sfun (D := D) (I := I) (P := P) (W := W) ξ‖ ≤
      ∑ k ∈ Sset (P := P), ‖A (I := I) (P := P) (W := W) k‖ := by
  classical
  -- Triangle inequality, and `‖e(·)‖ = 1`.
  have h1 :
      ‖Sfun (D := D) (I := I) (P := P) (W := W) ξ‖
        ≤
      ∑ k ∈ Sset (P := P), ‖(A (I := I) (P := P) (W := W) k) * e (ξ * (k : ℝ) / D.X)‖ := by
    simpa [Sfun] using
      (norm_sum_le (s := Sset (P := P))
        (f := fun k => (A (I := I) (P := P) (W := W) k) * e (ξ * (k : ℝ) / D.X)))
  have h2 :
      (∑ k ∈ Sset (P := P), ‖(A (I := I) (P := P) (W := W) k) * e (ξ * (k : ℝ) / D.X)‖)
        =
      ∑ k ∈ Sset (P := P), ‖A (I := I) (P := P) (W := W) k‖ := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have he : ‖e (ξ * (k : ℝ) / D.X)‖ = 1 := by
      simpa using (norm_e (ξ * (k : ℝ) / D.X))
    simp [norm_mul, he]
  exact h2 ▸ h1

theorem memLp_Sfun_top (X H : ℝ) :
    MemLp (Sfun (D := D) (I := I) (P := P) (W := W)) (∞ : ℝ≥0∞)
      (FejerBankedTypeIIToeplitzRealTTStar.Model.μBand X H) := by
  classical
  -- Use `memLp_top_of_bound` with the global bound `∑ ‖A_k‖`.
  refine MeasureTheory.memLp_top_of_bound ?_ (∑ k ∈ Sset (P := P), ‖A (I := I) (P := P) (W := W) k‖) ?_
  · exact (measurable_Sfun (D := D) (I := I) (P := P) (W := W)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro ξ
    exact norm_Sfun_le (D := D) (I := I) (P := P) (W := W) ξ

theorem memLp_Sfun_two (X H : ℝ) :
    MemLp (Sfun (D := D) (I := I) (P := P) (W := W)) (2 : ℝ≥0∞)
      (FejerBankedTypeIIToeplitzRealTTStar.Model.μBand X H) := by
  classical
  -- Finite-measure monotonicity: `L^∞ ⊆ L^2`.
  have htop : MemLp (Sfun (D := D) (I := I) (P := P) (W := W)) (∞ : ℝ≥0∞)
      (FejerBankedTypeIIToeplitzRealTTStar.Model.μBand X H) :=
    memLp_Sfun_top (D := D) (I := I) (P := P) (W := W) X H
  -- The ξ-band restricted measure is finite, and scaling preserves finiteness.
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (FejerBankedTypeIIToeplitzRealTTStar.Model.band H)) := by
    -- `band H` is an `Icc`, hence has finite Lebesgue measure.
    dsimp [FejerBankedTypeIIToeplitzRealTTStar.Model.band, Weight.band,
      SSU.Engines.BGTypeIIWeightedToeplitz.band]
    infer_instance
  haveI : IsFiniteMeasure (FejerBankedTypeIIToeplitzRealTTStar.Model.μBand X H) := by
    -- `μBand X H = c • (volume.restrict (band H))`, with `c ≠ ∞`.
    refine MeasureTheory.Measure.smul_finite _ (c := ENNReal.ofReal (1 / X)) (by simp)
  exact MeasureTheory.MemLp.mono_exponent htop (by simp)

noncomputable def S (X H : ℝ) :
    FejerBankedTypeIIToeplitzRealTTStar.Model.L2Band X H :=
  (memLp_Sfun_two (D := D) (I := I) (P := P) (W := W) X H).toLp
    (Sfun (D := D) (I := I) (P := P) (W := W))

theorem S_coeFn_eq (X H : ℝ) :
    (fun ξ : ℝ => (S (D := D) (I := I) (P := P) (W := W) X H) ξ)
      =ᵐ[FejerBankedTypeIIToeplitzRealTTStar.Model.μBand X H]
    (Sfun (D := D) (I := I) (P := P) (W := W)) := by
  classical
  -- `toLp` agrees a.e. with the original function.
  simpa [S] using
    (memLp_Sfun_two (D := D) (I := I) (P := P) (W := W) X H).coeFn_toLp
      (f := Sfun (D := D) (I := I) (P := P) (W := W))

theorem S_coeFn_eq_restrictVolume (X H : ℝ) (hX : 0 < X) :
    (fun ξ : ℝ => (S (D := D) (I := I) (P := P) (W := W) X H) ξ)
      =ᵐ[(volume : Measure ℝ).restrict (Weight.band H)]
    (Sfun (D := D) (I := I) (P := P) (W := W)) := by
  -- `μBand X H` is a scalar multiple of the restricted volume measure, so `ae` agrees on null sets.
  have hμ :
      (fun ξ : ℝ => (S (D := D) (I := I) (P := P) (W := W) X H) ξ)
        =ᵐ[FejerBankedTypeIIToeplitzRealTTStar.Model.μBand X H]
      (Sfun (D := D) (I := I) (P := P) (W := W)) := by
    simpa using (S_coeFn_eq (D := D) (I := I) (P := P) (W := W) X H)
  let μ0 : Measure ℝ := (volume : Measure ℝ).restrict (Weight.band H)
  let c : ℝ≥0∞ := ENNReal.ofReal (1 / X)
  have hc0 : c ≠ 0 := by
    have : ¬ (1 / X : ℝ) ≤ 0 := (one_div_pos.2 hX).not_le
    simpa [c, ENNReal.ofReal_eq_zero] using this
  have hμ' :
      (fun ξ : ℝ => (S (D := D) (I := I) (P := P) (W := W) X H) ξ)
        =ᵐ[c • μ0]
      (Sfun (D := D) (I := I) (P := P) (W := W)) := by
    simpa [FejerBankedTypeIIToeplitzRealTTStar.Model.μBand, FejerBankedTypeIIToeplitzRealTTStar.Model.band,
      Weight.band, μ0, c] using hμ
  -- Convert the a.e. equality to a measure-zero statement about the disagreement set.
  have hzero :
      (c • μ0) {ξ : ℝ |
          (S (D := D) (I := I) (P := P) (W := W) X H) ξ
            ≠
          (Sfun (D := D) (I := I) (P := P) (W := W)) ξ} = 0 := by
    have h' :
        (c • μ0) {ξ : ℝ |
            ¬ ((S (D := D) (I := I) (P := P) (W := W) X H) ξ
                =
              (Sfun (D := D) (I := I) (P := P) (W := W)) ξ)} = 0 :=
      (MeasureTheory.ae_iff.1 hμ')
    simpa using h'
  have hmul :
      c * μ0 {ξ : ℝ |
          (S (D := D) (I := I) (P := P) (W := W) X H) ξ
            ≠
          (Sfun (D := D) (I := I) (P := P) (W := W)) ξ} = 0 := by
    simpa [Measure.smul_apply, μ0, c] using hzero
  have hμ0zero :
      μ0 {ξ : ℝ |
          (S (D := D) (I := I) (P := P) (W := W) X H) ξ
            ≠
          (Sfun (D := D) (I := I) (P := P) (W := W)) ξ} = 0 := by
    have : c = 0 ∨ μ0 {ξ : ℝ |
          (S (D := D) (I := I) (P := P) (W := W) X H) ξ
            ≠
          (Sfun (D := D) (I := I) (P := P) (W := W)) ξ} = 0 := by
      simpa using (mul_eq_zero.mp hmul)
    exact this.resolve_left hc0
  have :
      ∀ᵐ ξ ∂μ0,
        (S (D := D) (I := I) (P := P) (W := W) X H) ξ
          =
        (Sfun (D := D) (I := I) (P := P) (W := W)) ξ := by
    refine (MeasureTheory.ae_iff.2 ?_)
    simpa using hμ0zero
  simpa [μ0] using this

end RankOne

open RankOne
open SSU.Engines.TypeII.ProductToeplitz
open SSU.Engines.TypeII.ProductToeplitz (toeplitzFormTeXC)
open FejerBankedTypeIIToeplitzRealTTStar
open FejerBankedTypeIIToeplitzRealTTStar.Model
open SSU.Instances.FejerBankedTypeIIToeplitzKernel

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

set_option maxHeartbeats 1000000

theorem inner_eq_toeplitzFormTeXC_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H)
    (i j : ℤ) :
    inner ℂ
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := (fun p => I.F (P := P) (W := W) p)) := by
  classical
  -- Start from the proved TT* identity in the ξ-band model.
  have hTT :
      inner ℂ
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      (1 / D.X) *
        ∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star (((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)) := by
    simpa [Model.band, Weight.band] using
      (Model.inner_packetOp_eq_weightedIntegral (D := D) (X := D.X) (H := D.H) hH hX
        (S := RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) (i := i) (j := j))
  -- Replace `S` by the explicit finite sum `Sfun` inside the band integral.
  have hSae :
      (fun ξ : ℝ => (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)
        =ᵐ[(volume : Measure ℝ).restrict (Weight.band D.H)]
      RankOne.Sfun (D := D) (I := I) (P := P) (W := W) := by
    -- `μBand` is a scalar multiple of the restricted volume measure, so `ae` agrees on null sets.
    -- We simply reuse the `toLp` a.e. equality and change the measure.
    have hμ :
        (fun ξ : ℝ => (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)
          =ᵐ[Model.μBand D.X D.H]
        RankOne.Sfun (D := D) (I := I) (P := P) (W := W) := by
      simpa using (RankOne.S_coeFn_eq (D := D) (I := I) (P := P) (W := W) D.X D.H)
    -- Transport the a.e. statement from `μBand = c • μ0` to `μ0` directly (without relying on
    -- `ae_smul_measure_iff`, which is absent in this toolchain snapshot).
    let μ0 : Measure ℝ := (volume : Measure ℝ).restrict (Weight.band D.H)
    let c : ℝ≥0∞ := ENNReal.ofReal (1 / D.X)
    have hc0 : c ≠ 0 := by
      have : (0 : ℝ) < (1 / D.X) := by simpa using (one_div_pos.2 hX)
      -- `ofReal x = 0 ↔ x ≤ 0`.
      exact by
        have : ¬ (1 / D.X) ≤ 0 := not_le_of_gt this
        simpa [c, ENNReal.ofReal_eq_zero] using this
    have hμ' :
        (fun ξ : ℝ => (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)
          =ᵐ[c • μ0]
        RankOne.Sfun (D := D) (I := I) (P := P) (W := W) := by
      simpa [Model.μBand, Model.band, μ0, c] using hμ
    -- Convert the a.e. equality to a measure-zero statement about the disagreement set.
    have hzero : (c • μ0) {ξ : ℝ | (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ
        ≠ RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ} = 0 := by
      -- `ae_iff`: `∀ᵐ ξ, S ξ = Sfun ξ` iff the disagreement set has measure `0`.
      have h' :
          (c • μ0) {ξ : ℝ |
              ¬ ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ
                  = RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ)} = 0 :=
        (MeasureTheory.ae_iff.1 hμ')
      simpa using h'
    have hmul :
        c * μ0 {ξ : ℝ | (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ
          ≠ RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ} = 0 := by
      -- `smul_apply` for measures is multiplication by the scalar.
      simpa [Measure.smul_apply, μ0, c] using hzero
    have hμ0zero :
        μ0 {ξ : ℝ | (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ
          ≠ RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ} = 0 := by
      -- Cancel `c` from `c * μ0 N = 0` using `hc0`.
      have : c = 0 ∨ μ0 {ξ : ℝ | (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ
          ≠ RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ} = 0 := by
        simpa using (mul_eq_zero.mp hmul)
      exact this.resolve_left hc0
    -- Return the desired a.e. equality on the unscaled restricted measure.
    have : ∀ᵐ ξ ∂ μ0,
        (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ
          = RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ := by
      -- `ae_iff` in reverse direction.
      refine (MeasureTheory.ae_iff.2 ?_)
      simpa using hμ0zero
    simpa [μ0] using this

  have hTT' :
      inner ℂ
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      ((1 / D.X : ℝ) : ℂ) *
        ∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
              star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) := by
    -- Use `hTT` and rewrite the integrand a.e. using `hSae`.
    -- Note: `hTT` already has the prefactor `(1/D.X)` as a real scalar.
    have hcongr :
        (fun ξ : ℝ =>
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star (((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)))
          =ᵐ[(volume : Measure ℝ).restrict (Weight.band D.H)]
        (fun ξ : ℝ =>
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
                star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ)) := by
      filter_upwards [hSae] with ξ hξ
      simp [hξ]
    -- Apply the a.e. congruence inside the restricted integral.
    have hint :
        (∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star (((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)))
          =
        ∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
                star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) := by
      simpa [MeasureTheory.integral] using integral_congr_ae hcongr
    -- Finish: rewrite the integral on the RHS of `hTT`.
    have hmul :
        ((1 / D.X : ℝ) : ℂ) *
            (∫ ξ in Weight.band D.H,
              (Weight.wLean (D := D) D.X D.H i j ξ) *
                ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                  star (((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)))
          =
        ((1 / D.X : ℝ) : ℂ) *
            (∫ ξ in Weight.band D.H,
              (Weight.wLean (D := D) D.X D.H i j ξ) *
                (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
                  star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ)) := by
      simpa using congrArg (fun z : ℂ => ((1 / D.X : ℝ) : ℂ) * z) hint
    exact hTT.trans (by simpa [mul_assoc] using hmul)

  -- Toeplitzize the weighted band integral deterministically.
  have hw :
      IntegrableOn (fun ξ => Weight.wLean (D := D) D.X D.H i j ξ) (Weight.band D.H) :=
    Weight.integrableOn_wLean (D := D) (X := D.X) (H := D.H) hH i j
  have hXne : D.X ≠ 0 := ne_of_gt hX
  have hToeplitz :
      (∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
              star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ))
        =
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t => Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
    -- Apply Toeplitzization to `Ssum`, then rewrite in terms of `toeplitzFormTeXC`.
    have hdet :
        (∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              (SSU.Engines.BGTypeIIWeightedToeplitz.Ssum D.X ξ (RankOne.Sset (P := P))
                  (RankOne.A (I := I) (P := P) (W := W))) *
                star (SSU.Engines.BGTypeIIWeightedToeplitz.Ssum D.X ξ (RankOne.Sset (P := P))
                  (RankOne.A (I := I) (P := P) (W := W))))
          =
        ∑ k ∈ RankOne.Sset (P := P), ∑ k' ∈ RankOne.Sset (P := P),
          (RankOne.A (I := I) (P := P) (W := W) k') *
            star (RankOne.A (I := I) (P := P) (W := W) k) *
              (SSU.Engines.BGTypeIIWeightedToeplitz.K D.X D.H
                  (fun ξ => Weight.wLean (D := D) D.X D.H i j ξ) (k' - k)) := by
      simpa [SSU.Engines.BGTypeIIWeightedToeplitz.K] using
        (SSU.Engines.BGTypeIIWeightedToeplitz.integral_weight_mul_Ssum_mul_star_Ssum
          (X := D.X) (H := D.H)
          (w := fun ξ => Weight.wLean (D := D) D.X D.H i j ξ)
          (S := RankOne.Sset (P := P))
          (A := RankOne.A (I := I) (P := P) (W := W))
          hH hw hXne)
    -- Rewrite `Sfun` as `Ssum` (definitional).
    have hSfun :
        (fun ξ : ℝ => RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ)
          =
        fun ξ : ℝ =>
          SSU.Engines.BGTypeIIWeightedToeplitz.Ssum D.X ξ (RankOne.Sset (P := P))
            (RankOne.A (I := I) (P := P) (W := W)) := by
      funext ξ
      simp [RankOne.Sfun, SSU.Engines.BGTypeIIWeightedToeplitz.Ssum, RankOne.Sset, RankOne.A]
    -- Rewrite the LHS of `hdet` via `hSfun`, then rewrite the RHS sum as `toeplitzFormTeXC`.
    -- `toeplitzFormTeXC` uses the same index set and coefficients by definition.
    -- The induced kernel is `Weight.KLean`, which matches `BGTypeIIWeightedToeplitz.K` with `wLean`.
    have hkernel :
        (fun t : ℤ => Weight.KLean (D := D) D.X D.H i j t)
          =
        fun t : ℤ =>
          SSU.Engines.BGTypeIIWeightedToeplitz.K D.X D.H
            (fun ξ => Weight.wLean (D := D) D.X D.H i j ξ) t := by
      rfl
    -- Now finish by unfolding `toeplitzFormTeXC`.
    -- This is definitional: `coeffByProd` for `I.F` equals `I.A`.
    -- Use `simp` only for the `coeffByProd`/`I.A` normalization.
    classical
    -- Convert the `k,k'` sum into the `toeplitzFormTeXC` definition.
    -- `toeplitzFormTeXC` is already a `k,k'` sum over `T.image prod`.
    -- Here `T = P.box`, so `T.image prod = RankOne.Sset`.
    have himage : (P.box.image prod) = RankOne.Sset (P := P) := rfl
    -- Put it together.
    -- (We rewrite in a `calc` to keep definitional equalities stable.)
    calc
      (∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
              star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ))
          =
        ∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (SSU.Engines.BGTypeIIWeightedToeplitz.Ssum D.X ξ (RankOne.Sset (P := P))
              (RankOne.A (I := I) (P := P) (W := W))) *
              star (SSU.Engines.BGTypeIIWeightedToeplitz.Ssum D.X ξ (RankOne.Sset (P := P))
                (RankOne.A (I := I) (P := P) (W := W))) := by
              simp [hSfun]
      _ =
        ∑ k ∈ RankOne.Sset (P := P), ∑ k' ∈ RankOne.Sset (P := P),
          (RankOne.A (I := I) (P := P) (W := W) k') *
            star (RankOne.A (I := I) (P := P) (W := W) k) *
              (SSU.Engines.BGTypeIIWeightedToeplitz.K D.X D.H
                  (fun ξ => Weight.wLean (D := D) D.X D.H i j ξ) (k' - k)) := hdet
      _ =
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t => Weight.KLean (D := D) D.X D.H i j t)
          (T := P.box)
          (F := fun p => I.F (P := P) (W := W) p) := by
          -- Unfold `toeplitzFormTeXC`; the coefficient array is already grouped by products.
          -- Keep the coefficient array opaque (do not unfold `I.F`) to avoid blowups.
          simp [SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC, RankOne.Sset, RankOne.A,
            SSU.Engines.BGTypeIIRankOne.Input.A, hkernel]

  -- Combine the pieces.
  calc
    inner ℂ
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      ((1 / D.X : ℝ) : ℂ) *
        ∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
              star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) := hTT'
    _ =
      ((1 / D.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t => Weight.KLean (D := D) D.X D.H i j t)
          (T := P.box)
          (F := fun p => I.F (P := P) (W := W) p) := by
          -- Rewrite the band integral using `hToeplitz`.
          -- (Avoid `simp`, which can unfold `1 / D.X` and create spurious `D.X = 0` branches.)
          simpa [mul_assoc] using congrArg (fun z : ℂ => ((1 / D.X : ℝ) : ℂ) * z) hToeplitz

theorem inner_eq_toeplitzFormTeXC_rankOne_boxData
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H)
    (i j : ℤ) :
    inner ℂ
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := (I.boxData (H0 := SSU.Torus.L2) (P := P) hU W).tube)
        (F := (I.boxData (H0 := SSU.Torus.L2) (P := P) hU W).F (0 : SSU.Torus.L2) i j) := by
  classical
  have hmain :=
    inner_eq_toeplitzFormTeXC_rankOne (D := D) (P := P) (W := W) (I := I) hX hH i j
  have htube : (I.boxData (H0 := SSU.Torus.L2) (P := P) hU W).tube = P.box :=
    I.boxData_tube_eq_box (H0 := SSU.Torus.L2) (P := P) (hU := hU) (W := W)
  have hF :
      (I.boxData (H0 := SSU.Torus.L2) (P := P) hU W).F (0 : SSU.Torus.L2) i j =
        fun p => I.F (P := P) (W := W) p := by
    funext p
    simpa using
      (I.boxData_F_eq_F (H0 := SSU.Torus.L2) (P := P) (hU := hU) (W := W)
        (f := (0 : SSU.Torus.L2)) (i := i) (j := j) (p := p))
  simpa [htube, hF] using hmain

theorem inner_eq_toeplitzFormTeXC_rankOne_mkBoxData
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H)
    (i j : ℤ) :
    let Dtype :
        SSU.Engines.BGTypeIIArray.Data
          (FejerBankedTypeIIToeplitzRealTTStar.Model.L2Band D.X D.H) :=
      SSU.Engines.BGTypeIIArray.Data.mkBox
        (H := FejerBankedTypeIIToeplitzRealTTStar.Model.L2Band D.X D.H)
        P hU W.toWeight
        (α := fun _f _i _j d => I.α d)
        (β := fun _f _i _j n => I.β n)
    inner ℂ
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := Dtype.tube)
        (F := Dtype.F (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) i j) := by
  classical
  intro Dtype
  -- Start from the already proved box identity.
  have hmain :=
    inner_eq_toeplitzFormTeXC_rankOne (D := D) (P := P) (W := W) (I := I) hX hH i j
  -- Rewrite the RHS into the `mkBox` data package.
  have htube : Dtype.tube = P.box := by
    simpa [Dtype] using
      (I.boxData_tube_eq_box
        (H0 := FejerBankedTypeIIToeplitzRealTTStar.Model.L2Band D.X D.H)
        (P := P) (hU := hU) (W := W))
  have hF :
      Dtype.F (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) i j
        =
      fun p => I.F (P := P) (W := W) p := by
    funext p
    simpa [Dtype] using
      (I.boxData_F_eq_F
        (H0 := FejerBankedTypeIIToeplitzRealTTStar.Model.L2Band D.X D.H)
        (P := P) (hU := hU) (W := W)
        (f := RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H)
        (i := i) (j := j) (p := p))
  simpa [htube, hF] using hmain

theorem inner_eq_arcIntegral_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    inner ℂ
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
      =
    ∫ z : UC,
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator
        (fun x =>
          (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus D.X D.H x : ℝ) : ℂ) *
              star (D.ψ i x) * (D.ψ j x)) *
            (I.signalTorusByProd P W x) *
              star (I.signalTorusByProd P W x))
        z := by
  classical
  -- 1) Start from the proved TT* identity in the ξ-band model.
  have hTT :
      inner ℂ
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      ((1 / D.X : ℝ) : ℂ) *
        ∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) := by
    simpa [Model.band, Weight.band] using
      (Model.inner_packetOp_eq_weightedIntegral (D := D) (X := D.X) (H := D.H) hH hX
        (S := RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) (i := i) (j := j))
  -- 2) Replace `S` by the explicit sum `Sfun` a.e. on the restricted volume measure.
  have hSae :
      (fun ξ : ℝ => (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)
        =ᵐ[(volume : Measure ℝ).restrict (Weight.band D.H)]
      RankOne.Sfun (D := D) (I := I) (P := P) (W := W) := by
    simpa using
      (RankOne.S_coeFn_eq_restrictVolume (D := D) (I := I) (P := P) (W := W) D.X D.H hX)
  have hTT' :
      inner ℂ
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      ((1 / D.X : ℝ) : ℂ) *
        ∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
              star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) := by
    have hcongr :
        (fun ξ : ℝ =>
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ))
          =ᵐ[(volume : Measure ℝ).restrict (Weight.band D.H)]
        (fun ξ : ℝ =>
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
                star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ)) := by
      filter_upwards [hSae] with ξ hξ
      simp [hξ]
    have hint :
        (∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ))
          =
        ∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
                star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) := by
      simpa [MeasureTheory.integral] using integral_congr_ae hcongr
    have := congrArg (fun z : ℂ => ((1 / D.X : ℝ) : ℂ) * z) hint
    exact hTT.trans (by simpa [mul_assoc] using this)
  -- 3) Rewrite the integrand into an arc-evaluated torus function `g((ξ/X):𝕋)`.
  let g : UC → ℂ :=
    fun x =>
      (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus D.X D.H x : ℝ) : ℂ) *
          star (D.ψ i x) * (D.ψ j x)) *
        (I.signalTorusByProd P W x) *
          star (I.signalTorusByProd P W x)
  have hcongr2 :
      (fun ξ : ℝ =>
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
              star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ))
        =ᵐ[(volume : Measure ℝ).restrict (Weight.band D.H)]
      (fun ξ : ℝ => g ((ξ / D.X : ℝ) : UC)) := by
    have hs : MeasurableSet (Weight.band D.H) := by
      dsimp [Weight.band, SSU.Engines.BGTypeIIWeightedToeplitz.band]
      measurability
    filter_upwards [ae_restrict_mem hs] with ξ hξ
    have hK :
        SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus D.X D.H
            ((ξ / D.X : ℝ) : UC)
          =
        SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal D.H ξ := by
      simpa [SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal] using
        (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus_eval_eq_Khat_on_band
          (X := D.X) (H := D.H) (hX := hX) (hH := hH) (hsmall := hsmall) (ξ := ξ) hξ)
    have hS :
        RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ
          =
        I.signalTorusByProd P W ((ξ / D.X : ℝ) : UC) := by
      calc
        RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ
            =
          I.signalRealByProd P W D.X ξ := by
            simpa using (RankOne.Sfun_eq_signalRealByProd (D := D) (I := I) (P := P) (W := W) (ξ := ξ))
        _ =
          I.signalTorusByProd P W ((ξ / D.X : ℝ) : UC) := by
            simpa using (I.signalRealByProd_eq_signalTorusByProd (P := P) (W := W) (X := D.X) (ξ := ξ))
    -- Unfold `wLean`/`g` and rewrite `KhatTorus` and `Sfun`.
    -- (Keep rewriting deterministic; avoid simp-cancellation lemmas.)
    simpa [g, Weight.wLean, Weight.w, hK, hS]
  -- 4) Apply the deterministic band→arc bridge with the TeX `1/X` prefactor.
  have hbandToArc :
      ((1 / D.X : ℝ) • ∫ ξ in Set.Icc (-(1 / D.H)) (1 / D.H), g ((ξ / D.X : ℝ) : UC))
        =
      ∫ z : UC,
        (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator g z := by
    simpa [SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand,
      SSU.Torus.BandMap.arc, g, div_eq_mul_inv, mul_assoc] using
      (SSU.Instances.FejerBankedTypeIIToeplitzBandToArc.one_div_X_smul_integral_band_eval_eq_integral_indicator_arc
        (X := D.X) (H := D.H) (hX := hX) (hH := hH) (hsmall := hsmall) g)
  have hbandToArcC :
      ((1 / D.X : ℝ) : ℂ) * (∫ ξ in Weight.band D.H, g ((ξ / D.X : ℝ) : UC))
        =
      ∫ z : UC,
        (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator g z := by
    -- `Weight.band` is definitionally the `Icc` used in the bridge.
    have hb : Weight.band D.H = Set.Icc (-(1 / D.H)) (1 / D.H) := rfl
    -- Convert real scalar multiplication to complex multiplication.
    simpa [hb, Complex.real_smul, mul_assoc] using hbandToArc
  -- 5) Assemble: rewrite the band integral using `hcongr2`, then apply the bridge.
  have hrewrite :
      ((1 / D.X : ℝ) : ℂ) *
          ∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
                star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ)
        =
      ((1 / D.X : ℝ) : ℂ) * (∫ ξ in Weight.band D.H, g ((ξ / D.X : ℝ) : UC)) := by
    have :=
      (integral_congr_ae hcongr2 : (∫ ξ in Weight.band D.H,
          (fun ξ : ℝ =>
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
                star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ)) ξ)
          =
        ∫ ξ in Weight.band D.H, (fun ξ : ℝ => g ((ξ / D.X : ℝ) : UC)) ξ)
    -- Multiply both sides by the common scalar.
    simpa [mul_assoc] using congrArg (fun z : ℂ => ((1 / D.X : ℝ) : ℂ) * z) this
  -- Finish.
  calc
    inner ℂ
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      ((1 / D.X : ℝ) : ℂ) *
        ∫ ξ in Weight.band D.H,
          (Weight.wLean (D := D) D.X D.H i j ξ) *
            (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) *
              star (RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ) := hTT'
    _ =
      ((1 / D.X : ℝ) : ℂ) * (∫ ξ in Weight.band D.H, g ((ξ / D.X : ℝ) : UC)) := hrewrite
    _ =
      ∫ z : UC,
        (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator g z := by
          simpa using hbandToArcC
    _ =
      ∫ z : UC,
        (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand D.X D.H).indicator
          (fun x =>
            (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus D.X D.H x : ℝ) : ℂ) *
                star (D.ψ i x) * (D.ψ j x)) *
              (I.signalTorusByProd P W x) *
                star (I.signalTorusByProd P W x))
          z := by
          simp [g]

end

end FejerBankedTypeIIToeplitzRankOneReal
end Instances
end SSU
