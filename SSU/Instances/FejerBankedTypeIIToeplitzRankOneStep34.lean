import SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar
import SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal
import SSU.Instances.FejerBankedTypeIIToeplitzKernel
import SSU.Engines.TypeIIToeplitz
import SSU.Engines.BGTypeIIRankOneSignal

/-!
Rank-one Type–II signal: Step 3–4 (large sieve) ⇒ TT* Gram bounds (TeX-faithful, rank-one only).

This file is the first place where the **Type–II analytic input** (packaged as `Step34ProdSum`)
actually improves a bound for the Fejér-banked TT* packet operators.

We work in the **real-frequency TT*** band model (as in `05b_SSU.tex`), where packets are
multipliers by `√K̂_H(ξ) * ψ_j((ξ/X):𝕋)` and the Gram is a weighted band integral.

The input signal is the TeX rank-one Type–II signal on the dyadic box, expressed as
`prodSum X ξ box F`.

This is still *not* the SSU heart (no interzone decay in `distZ` yet); it provides a uniform
bound on Gram entries in terms of `tubeEnergy`, with the expected `√(H/X)` scaling coming from the
large sieve estimate.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzRankOneStep34

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus
open SSU.Engines.TypeII
open SSU.Engines.TypeIIToeplitz

set_option maxHeartbeats 1000000

variable {κ : Type*} [DecidableEq κ]

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

open SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar
open SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal
open SSU.Instances.FejerBankedTypeIIToeplitzKernel
open SSU.Engines.BGTypeIIRankOne

namespace RankOne

private noncomputable def FDN (p : SSU.TubePoint) : ℂ :=
  I.F P W p

private theorem prodSum_eq_signalRealDN (ξ : ℝ) :
    SSU.Engines.TypeII.ProductToeplitz.prodSum D.X ξ P.box (FDN (P := P) (W := W) (I := I))
      =
    I.signalRealDN P W D.X ξ := by
  classical
  -- Both are definitional `∑_{p∈box} F(p) e(ξ*prod(p)/X)`.
  simp [SSU.Engines.TypeII.ProductToeplitz.prodSum, Input.signalRealDN, FDN]

/--
Pointwise large sieve bound for the explicit rank-one signal `Sfun(ξ)` on the ξ-band, expressed in
terms of the dyadic box coefficient array `F(d,n)`.
-/
theorem norm_Sfun_sq_le_of_step34
    (hX : 0 < D.X) (hH : 0 < D.H)
    (step34 : Step34ProdSum D.X D.H P.box)
    (ξ : ℝ) (hξ : ξ ∈ Weight.band D.H) :
    ‖RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ‖ ^ 2
      ≤
    step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p) := by
  classical
  -- Convert `Sfun` into `signalRealDN`, then into `prodSum`, then apply Step 3–4.
  have hAbs : |ξ| ≤ (1 / D.H) := by
    have hle : -(1 / D.H) ≤ ξ ∧ ξ ≤ (1 / D.H) := by
      simpa [Weight.band, Set.mem_Icc] using hξ
    exact abs_le.2 hle
  have hSfun :
      RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ = I.signalRealDN P W D.X ξ := by
    calc
      RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ
          =
        I.signalRealByProd P W D.X ξ := by
          simpa using (RankOne.Sfun_eq_signalRealByProd (D := D) (I := I) (P := P) (W := W) (ξ := ξ))
      _ = I.signalRealDN P W D.X ξ := by
          simpa using (Input.signalRealDN_eq_signalRealByProd (I := I) (P := P) (W := W) (X := D.X) (ξ := ξ)).symm
  have hprod :
      I.signalRealDN P W D.X ξ =
        SSU.Engines.TypeII.ProductToeplitz.prodSum D.X ξ P.box (fun p => I.F P W p) := by
    simp [Input.signalRealDN, SSU.Engines.TypeII.ProductToeplitz.prodSum]
  -- Apply Step 3–4 to `prodSum`.
  have h34 :
      ‖SSU.Engines.TypeII.ProductToeplitz.prodSum D.X ξ P.box (fun p => I.F P W p)‖ ^ 2
        ≤
      step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p) := by
    simpa [Step34ProdSum] using (step34.bound ξ hAbs (fun p => I.F P W p))
  -- Finish.
  -- Rewrite the LHS into `prodSum` using `hSfun` and `hprod`.
  simpa [hSfun, hprod] using h34

end RankOne

namespace Gram

/--
Uniform bound on the TT* packet Gram entry for the rank-one Type–II signal, assuming a Step 3–4
bound on the underlying product sum.

This is the “replace Cauchy–Schwarz with large sieve” milestone: the constant depends on the
packet overlap only through the crude `‖ψ‖_∞ ≤ M * Φmax` bound.
-/
theorem norm_inner_packetOp_rankOne_le
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H)
    (step34 : Step34ProdSum D.X D.H P.box)
    (i j : ℤ) :
    ‖inner ℂ
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
          (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))‖
      ≤
    ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
        (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
      (2 * (D.H)⁻¹) := by
  classical
  -- Start from the TT* band integral identity.
  have hTT :=
    Model.inner_packetOp_eq_weightedIntegral (D := D) (X := D.X) (H := D.H) hH hX
      (S := RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) (i := i) (j := j)
  -- Take norms and bound by the integral of norms.
  have hnorm :
      ‖inner ℂ
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))‖
        =
      ‖(1 / D.X) *
          ∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖ := by
    simpa [hTT]
  -- Now bound the RHS.
  have hle1 :
      ‖(1 / D.X) *
          ∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
        ≤
      (1 / D.X) *
        ∫ ξ in Weight.band D.H,
          ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖ := by
    -- `‖c * z‖ = |c| * ‖z‖` and `|1/X| = 1/X` for `X>0`, then `‖∫‖ ≤ ∫‖·‖`.
    have hX0 : 0 ≤ (1 / D.X : ℝ) := one_div_nonneg.mpr (le_of_lt hX)
    -- Use the general Bochner inequality on the restricted measure.
    -- (No integrability assumptions are needed here.)
    have := (norm_integral_le_integral_norm
      (μ := (volume : Measure ℝ).restrict (Weight.band D.H))
      (f := fun ξ : ℝ =>
        (Weight.wLean (D := D) D.X D.H i j ξ) *
          ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
            star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)))
    -- Combine with scalar multiplication.
    -- `simp` keeps the expression readable.
    -- The scalar is `(1 / (D.X : ℂ))`, so its norm is `|1 / D.X| = 1 / D.X` since `D.X > 0`.
    have habs : |(D.X : ℝ)| = D.X := abs_of_pos hX
    simpa [mul_assoc, hX0, Real.norm_eq_abs, abs_of_nonneg hX0, habs] using
      mul_le_mul_of_nonneg_left this hX0
  -- Pointwise bound the integrand by `Khat * (MΦmax)^2 * (Step34 RHS)`.
  have hs : MeasurableSet (Weight.band D.H) := by
    dsimp [Weight.band, Model.band, SSU.Engines.BGTypeIIWeightedToeplitz.band]
    measurability
  have hSae :
      (fun ξ : ℝ => (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)
        =ᵐ[(volume : Measure ℝ).restrict (Weight.band D.H)]
      RankOne.Sfun (D := D) (I := I) (P := P) (W := W) := by
    simpa using
      (RankOne.S_coeFn_eq_restrictVolume (D := D) (I := I) (P := P) (W := W) D.X D.H hX)
  have hpoint :
      (fun ξ : ℝ =>
          ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖)
        ≤ᵐ[(volume : Measure ℝ).restrict (Weight.band D.H)]
      (fun ξ : ℝ =>
        (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * ((D.M * D.Φmax) ^ 2) *
          (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) := by
    filter_upwards [ae_restrict_mem hs, hSae] with ξ hξ hS
    -- Bound `‖wLean‖` by `Khat * (MΦmax)^2`.
    have hw : ‖Weight.wLean (D := D) D.X D.H i j ξ‖
        ≤ (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * (D.M * D.Φmax) ^ 2 := by
      -- `‖wLean‖ = ‖w‖` and use the proved `norm_w_le`.
      simpa [Weight.wLean, Weight.w] using
        (Weight.norm_w_le (D := D) (X := D.X) (H := D.H) hH i j ξ)
    -- Bound `‖S ξ‖^2` by Step34.
    have hSsq :
        ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ ^ 2
          ≤ step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p) := by
      have hSfun :
          ‖RankOne.Sfun (D := D) (I := I) (P := P) (W := W) ξ‖ ^ 2
            ≤ step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p) :=
        RankOne.norm_Sfun_sq_le_of_step34 (D := D) (P := P) (W := W) (I := I) hX hH step34 ξ hξ
      simpa [hS] using hSfun
    -- Rewrite the LHS norm.
    -- `‖w * S * star S‖ ≤ ‖w‖ * ‖S‖ * ‖star S‖ = ‖w‖ * ‖S‖^2`.
    have hstar : ‖star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
        = ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ := by
      simpa using norm_star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)
    have hmul :
        ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
            ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
          ≤
        ‖Weight.wLean (D := D) D.X D.H i j ξ‖ *
          (‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ ^ 2) := by
      -- two applications of `‖a*b‖ ≤ ‖a‖‖b‖`.
      have := norm_mul_le
        (Weight.wLean (D := D) D.X D.H i j ξ)
        (((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
          star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ))
      have h2 := norm_mul_le
        ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)
        (star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ))
      -- Combine and simplify.
      -- `‖S * star S‖ ≤ ‖S‖ * ‖star S‖ = ‖S‖^2`.
      have hSS :
          ‖((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
            ≤ ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ ^ 2 := by
        calc
          ‖((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
              ≤
            ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ *
              ‖star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖ := by
                simpa using h2
          _ = ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ *
              ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ := by
                simp [hstar]
          _ = ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ ^ 2 := by
                simp [pow_two]
      calc
        ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
            ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
            =
          ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
            (((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ))‖ := by
              simp [mul_assoc]
        _ ≤ ‖Weight.wLean (D := D) D.X D.H i j ξ‖ *
              ‖((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖ := by
              simpa using this
        _ ≤ ‖Weight.wLean (D := D) D.X D.H i j ξ‖ *
              (‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ ^ 2) := by
              exact mul_le_mul_of_nonneg_left hSS (norm_nonneg _)
    -- Combine the pointwise bounds.
    have hKhat_nonneg : 0 ≤ SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ :=
      SSU.Engines.TypeII.AdmissibleKernel.Khat_nonneg (H := D.H) hH ξ
    calc
      ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
            ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
              star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
          ≤
        ‖Weight.wLean (D := D) D.X D.H i j ξ‖ *
          (‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ ^ 2) := hmul
      _ ≤ ((SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * (D.M * D.Φmax) ^ 2) *
            (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p)) := by
            have hS' :
                ‖(RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ‖ ^ 2
                  ≤
                step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p) := hSsq
            have hnonneg : 0 ≤ (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * (D.M * D.Φmax) ^ 2 := by
              exact mul_nonneg hKhat_nonneg (sq_nonneg _)
            exact mul_le_mul hw hS' (by positivity) hnonneg
      _ = (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * ((D.M * D.Φmax) ^ 2) *
            (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p)) := by
            ring
  -- Integrate the pointwise bound.
  have hle2 :
      (1 / D.X) *
          ∫ ξ in Weight.band D.H,
            ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
                ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                  star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖
        ≤
      (1 / D.X) *
        ∫ ξ in Weight.band D.H,
          (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * ((D.M * D.Φmax) ^ 2) *
            (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p)) := by
    let μ : Measure ℝ := (volume : Measure ℝ).restrict (Weight.band D.H)
    have hnonneg :
        0 ≤ᵐ[μ] fun ξ : ℝ =>
          ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖ := by
      exact ae_of_all _ (fun _ => by positivity)
    -- RHS integrability comes from `Khat_integrableOn` on the band.
    have hKhat_int :
        Integrable (fun ξ : ℝ => SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) μ := by
      have hband : Weight.band D.H = Set.Icc (-D.H⁻¹) D.H⁻¹ := by
        simp [Weight.band, SSU.Engines.BGTypeIIWeightedToeplitz.band, one_div]
      -- `IntegrableOn` is definitionally `Integrable` on the restricted measure.
      simpa [μ, hband, MeasureTheory.IntegrableOn] using
        (SSU.Engines.TypeII.AdmissibleKernel.Khat_integrableOn (H := D.H) hH)
    set C0 : ℝ :=
        ((D.M * D.Φmax) ^ 2) *
          (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))
    have hgi :
        Integrable (fun ξ : ℝ => (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0) μ := by
      simpa [mul_assoc, C0] using hKhat_int.mul_const C0
    have hpoint' :
        (fun ξ : ℝ =>
            ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
                ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                  star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖)
          ≤ᵐ[μ]
        (fun ξ : ℝ => (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0) := by
      -- `hpoint` already has the same inequality; only reassociate constants.
      simpa [μ, C0, mul_assoc, mul_left_comm, mul_comm] using hpoint
    -- Apply integral monotonicity on the restricted measure.
    have hinter :
        (∫ ξ, (fun ξ : ℝ =>
            ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
                ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                  star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖) ξ ∂μ)
          ≤
        ∫ ξ, (fun ξ : ℝ => (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0) ξ ∂μ :=
      MeasureTheory.integral_mono_of_nonneg (μ := μ) hnonneg hgi hpoint'
    have hX0 : 0 ≤ (1 / D.X : ℝ) := one_div_nonneg.mpr (le_of_lt hX)
    -- Convert `μ`-integrals back to restricted integrals.
    simpa [μ, C0, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hinter hX0
  -- Evaluate the remaining integral using the crude kernel moment bound.
  have hKhatInt :
      (∫ ξ in Weight.band D.H, SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ)
        ≤ 2 * (D.H)⁻¹ := by
    -- `Weight.band D.H` is definitionally `Icc (-(1/D.H)) (1/D.H)`, and `Khat` uses `H⁻¹`.
    simpa [Weight.band, SSU.Engines.BGTypeIIWeightedToeplitz.band, one_div] using
      (SSU.Engines.TypeII.AdmissibleKernel.integral_Khat_le (H := D.H) hH)
  -- Pull constants out and apply `hKhatInt`.
  have hle3 :
      (1 / D.X) *
        ∫ ξ in Weight.band D.H,
          (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * ((D.M * D.Φmax) ^ 2) *
            (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))
        ≤
      ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
        (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
        (2 * (D.H)⁻¹) := by
    have hX0 : 0 ≤ (1 / D.X : ℝ) := one_div_nonneg.mpr (le_of_lt hX)
    set C0 : ℝ :=
        ((D.M * D.Φmax) ^ 2) *
          (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))
    have hC0 : 0 ≤ C0 := by
      have h1 : 0 ≤ ((D.M * D.Φmax) ^ 2 : ℝ) := by positivity
      have h2 : 0 ≤ step34.C := step34.C_nonneg
      have h3 : 0 ≤ Real.sqrt (D.H / D.X) := by positivity
      have h4 : 0 ≤ tubeEnergy P.box (fun p => I.F P W p) := by
        classical
        unfold SSU.tubeEnergy
        refine Finset.sum_nonneg ?_
        intro p hp
        positivity
      -- `C0` is a product of nonnegative factors.
      simpa [C0, mul_assoc, mul_left_comm, mul_comm] using
        mul_nonneg h1 (mul_nonneg h2 (mul_nonneg h3 h4))
    have hpull :
        (∫ ξ in Weight.band D.H, (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0)
          =
        (∫ ξ in Weight.band D.H, SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0 := by
      simpa using
        (MeasureTheory.integral_mul_const (μ := (volume : Measure ℝ).restrict (Weight.band D.H))
          C0 (fun ξ : ℝ => SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ))
    have hmul :
        (∫ ξ in Weight.band D.H, SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0
          ≤ (2 * (D.H)⁻¹) * C0 := by
      exact mul_le_mul_of_nonneg_right hKhatInt hC0
    calc
      (1 / D.X) *
          ∫ ξ in Weight.band D.H,
            (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * ((D.M * D.Φmax) ^ 2) *
              (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))
          =
        (1 / D.X) * ∫ ξ in Weight.band D.H, (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0 := by
          simp [C0, mul_assoc, mul_left_comm, mul_comm]
      _ = (1 / D.X) * ((∫ ξ in Weight.band D.H, SSU.Engines.TypeII.AdmissibleKernel.Khat D.H ξ) * C0) := by
          simp [hpull]
      _ ≤ (1 / D.X) * ((2 * (D.H)⁻¹) * C0) := by
          -- `hmul : (∫ Khat) * C0 ≤ (2 * H⁻¹) * C0`.
          exact mul_le_mul_of_nonneg_left (by simpa using hmul) hX0
      _ = ((1 / D.X) * C0) * (2 * (D.H)⁻¹) := by ring
      _ = ((1 / D.X) * ((D.M * D.Φmax) ^ 2) *
          (step34.C * Real.sqrt (D.H / D.X) * tubeEnergy P.box (fun p => I.F P W p))) *
          (2 * (D.H)⁻¹) := by
          -- Expand `C0` once; avoid heavy commutative `simp`.
          simp [C0, mul_assoc]
  -- Combine the chain.
  -- Combine the chain starting from `‖inner‖` (via `hnorm`) and then applying `hle1`, `hle2`, `hle3`.
  have habsX : |(D.X : ℝ)| = D.X := abs_of_pos hX
  have hstart :
      ‖inner ℂ
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))‖
        ≤
      (1 / D.X) *
        ∫ ξ in Weight.band D.H,
          ‖(Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖ := by
    -- Rewrite the LHS using `hnorm` and then apply `hle1`.
    have : ‖inner ℂ
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX i
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (Model.packetOp (D := D) (X := D.X) (H := D.H) hH hX j
            (RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))‖
        =
      ‖(1 / D.X) *
          ∫ ξ in Weight.band D.H,
            (Weight.wLean (D := D) D.X D.H i j ξ) *
              ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ) *
                star ((RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H) ξ)‖ := by
      simpa [hnorm]
    -- Apply `hle1` after rewriting.
    simpa [this] using hle1

  have hfinal := le_trans hstart (le_trans hle2 hle3)
  simpa [habsX] using hfinal

end Gram

end

end FejerBankedTypeIIToeplitzRankOneStep34
end Instances
end SSU
