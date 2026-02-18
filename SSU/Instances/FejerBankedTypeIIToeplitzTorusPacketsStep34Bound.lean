import SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets
import SSU.Engines.TypeIIToeplitz

/-!
Fejér-banked packets (torus-side): Step 3–4 bound ⇒ torus packet Gram bound.

This is the final “plumbing” wrapper in the Toeplitz Type–II reduction pipeline:

* use the proved identity (general Type–II array) from
  `FejerBankedTypeIIToeplitzTorusPackets.lean`:
    `inner(packetOpUnnormalized i fTT, packetOpUnnormalized j fTT)
      = (1/X) * toeplitzFormTeXC (K_{i,j}) (tube) (F f i j)`,
* rewrite `toeplitzFormTeXC` as the `wLean`-weighted ξ-band integral (deterministic), and
* bound that integral using:
  - the crude packet multiplier bound `‖ψ_j‖∞ ≤ M*Φmax`,
  - the Step 3–4 hypothesis `Step34ProdSum X H tube` on the product exponential sum,
  - the moment bound `∫ Khat ≤ 2/H`.

No SSU-heart analytic number theory occurs here; all analytic difficulty is encapsulated in the
`Step34ProdSum` hypothesis.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTorusPacketsStep34Bound

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus

open SSU.Engines.TypeII
open SSU.Engines.TypeIIToeplitz

variable {κ : Type*} [DecidableEq κ]

variable (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)

variable {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
variable (D : SSU.Engines.BGTypeIIArray.Data H0)

set_option maxHeartbeats 800000 in
theorem norm_inner_packetOpUnnormalized_le
    (f : H0) (i j : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (step34 : Step34ProdSum Dpacket.X Dpacket.H D.tube) :
    ‖inner ℂ
        (((Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := D) f i j hH))‖
      ≤
    ((1 / Dpacket.X) * ((Dpacket.M * Dpacket.Φmax) ^ 2) *
        (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j))) *
      (2 * (Dpacket.H)⁻¹) := by
  classical
  -- 1) Rewrite the inner product as `(1/X) * toeplitzFormTeXC`.
  have hToe :
      inner ℂ
          (((Dpacket.toMultiplierModel).packetOpUnnormalized i)
            (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
              (Dpacket := Dpacket) (D := D) f i j hH))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j)
            (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
              (Dpacket := Dpacket) (D := D) f i j hH))
        =
      ((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube)
          (F := D.F f i j) := by
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.inner_packetOpUnnormalized_eq_toeplitzFormTeXC
        (Dpacket := Dpacket) (D := D) (f := f) (i := i) (j := j)
        (hX := hX) (hH := hH) (hsmall := hsmall))

  -- 2) Bound the RHS by turning `toeplitzFormTeXC` into the weighted band integral.
  have hX0 : (Dpacket.X : ℝ) ≠ 0 := ne_of_gt hX
  have htoepInt :
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube)
          (F := D.F f i j)
        =
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)) := by
    -- Use the deterministic Toeplitzization lemma and rewrite.
    -- (We use the lemma in the direction “integral = toeplitzFormTeXC”, then symm.)
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
        (Dpacket := Dpacket) (D := D) (X := Dpacket.X) (H := Dpacket.H) (f := f) (i := i) (j := j)
        (hH := hH) (hX := hX0)).symm

  -- 3) Take norms and use `‖∫‖ ≤ ∫‖·‖`.
  have hnorm1 :
      ‖((1 / Dpacket.X : ℝ) : ℂ) *
          SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube)
            (F := D.F f i j)‖
        =
      (1 / Dpacket.X) *
        ‖SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube)
            (F := D.F f i j)‖ := by
    have hscalarNorm : ‖((1 / Dpacket.X : ℝ) : ℂ)‖ = (1 / Dpacket.X) := by
      have hnonneg : 0 ≤ (1 / Dpacket.X : ℝ) := one_div_nonneg.2 (le_of_lt hX)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      ‖((1 / Dpacket.X : ℝ) : ℂ) *
          SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube)
            (F := D.F f i j)‖
          =
        ‖((1 / Dpacket.X : ℝ) : ℂ)‖ *
          ‖SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube)
            (F := D.F f i j)‖ := by simpa using
              (norm_mul
                (((1 / Dpacket.X : ℝ) : ℂ))
                (SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
                  (K := fun t =>
                    SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                      (D := Dpacket) Dpacket.X Dpacket.H i j t)
                  (T := D.tube)
                  (F := D.F f i j)))
      _ =
        (1 / Dpacket.X) *
          ‖SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube)
            (F := D.F f i j)‖ := by rw [hscalarNorm]

  have hnormToInt :
      ‖SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube)
            (F := D.F f i j)‖
        =
      ‖∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ := by
    simpa [htoepInt]

  have hleInt :
      ‖∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)‖
        ≤
      ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
        ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ := by
    -- Bochner inequality on the restricted measure.
    simpa [MeasureTheory.integral] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := (volume : Measure ℝ).restrict (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H))
        (f := fun ξ : ℝ =>
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)))

  -- 4) Pointwise bound of the integrand:
  -- `‖wLean‖ ≤ Khat * (M*Φmax)^2` and `‖S‖^2 ≤ step34.C * sqrt(H/X) * tubeEnergy`.
  have hpoint :
      (fun ξ : ℝ =>
        ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)‖)
        ≤ᵐ[(volume : Measure ℝ).restrict (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H)]
      fun ξ : ℝ =>
        (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) *
          ((Dpacket.M * Dpacket.Φmax) ^ 2) *
            (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j)) := by
    have hs : MeasurableSet (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H) := by
      -- `band` is a closed interval.
      dsimp [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band]
      measurability
    filter_upwards [ae_restrict_mem hs] with ξ hξ
    -- Band membership gives `|ξ| ≤ 1/H`.
    have hξabs : |ξ| ≤ (1 / Dpacket.H) := by
      have hle : (-(1 / Dpacket.H) : ℝ) ≤ ξ ∧ ξ ≤ (1 / Dpacket.H) := by
        simpa [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band, Set.mem_Icc] using hξ
      exact abs_le.2 hle
    -- Step34 bound on the (ungrouped) product sum.
    have hprod :
        D.prodSumRealByProd Dpacket.X ξ f i j
          = SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ D.tube (D.F f i j) := by
      simpa [SSU.Engines.BGTypeIIArray.Data.prodSumReal] using
        (D.prodSumReal_eq_prodSumRealByProd (X := Dpacket.X) (ξ := ξ) (f := f) (i := i) (j := j)).symm
    have hS0 :
        ‖D.prodSumRealByProd Dpacket.X ξ f i j‖ ^ 2
          ≤
        step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j) := by
      have h34 :
          ‖SSU.Engines.TypeII.ProductToeplitz.prodSum Dpacket.X ξ D.tube (D.F f i j)‖ ^ 2
            ≤
          step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j) := by
        have hAbs : |ξ| ≤ (1 / Dpacket.H) := hξabs
        simpa using (step34.bound ξ hAbs (D.F f i j))
      simpa [hprod] using h34
    -- Bound `‖wLean‖` using `‖ψ‖ ≤ M*Φmax` and `KhatTorus_eval_eq_Khat_on_band`.
    have hKhat :
        SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H ((ξ / Dpacket.X : ℝ) : UC)
          = SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal Dpacket.H ξ := by
      -- Use the deterministic no-wrap lemma.
      simpa [SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal] using
        (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus_eval_eq_Khat_on_band
          (X := Dpacket.X) (H := Dpacket.H) (hX := hX) (hH := hH) (hsmall := hsmall) ξ
          (by simpa [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band] using hξ))
    have hψi : ‖Dpacket.ψ i ((ξ / Dpacket.X : ℝ) : UC)‖ ≤ Dpacket.M * Dpacket.Φmax :=
      Dpacket.norm_ψ_le i ((ξ / Dpacket.X : ℝ) : UC)
    have hψj : ‖Dpacket.ψ j ((ξ / Dpacket.X : ℝ) : UC)‖ ≤ Dpacket.M * Dpacket.Φmax :=
      Dpacket.norm_ψ_le j ((ξ / Dpacket.X : ℝ) : UC)
    have hw :
        ‖SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) Dpacket.X Dpacket.H i j ξ‖
          ≤
        (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * ((Dpacket.M * Dpacket.Φmax) ^ 2) := by
      have hw0 :=
        SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.norm_w_le
          (D := Dpacket) (X := Dpacket.X) (H := Dpacket.H) (hH := hH) (i := i) (j := j) (ξ := ξ)
      simpa [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean] using hw0
    -- Combine: `‖wLean * S * star S‖ = ‖wLean‖ * ‖S‖^2`.
    have hSS : ‖(D.prodSumRealByProd Dpacket.X ξ f i j) * star (D.prodSumRealByProd Dpacket.X ξ f i j)‖
        = ‖D.prodSumRealByProd Dpacket.X ξ f i j‖ ^ 2 := by
      simpa [pow_two, mul_assoc] using
        (norm_mul (D.prodSumRealByProd Dpacket.X ξ f i j) (star (D.prodSumRealByProd Dpacket.X ξ f i j)))
    -- Finish the pointwise inequality.
    calc
      ‖SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) Dpacket.X Dpacket.H i j ξ *
          (D.prodSumRealByProd Dpacket.X ξ f i j) *
            star (D.prodSumRealByProd Dpacket.X ξ f i j)‖
          =
        ‖SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) Dpacket.X Dpacket.H i j ξ‖ *
          ‖(D.prodSumRealByProd Dpacket.X ξ f i j) * star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ := by
            simp [norm_mul, mul_assoc]
      _ =
        ‖SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) Dpacket.X Dpacket.H i j ξ‖ *
          (‖D.prodSumRealByProd Dpacket.X ξ f i j‖ ^ 2) := by
            rw [hSS]
      _ ≤
        ((SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * ((Dpacket.M * Dpacket.Φmax) ^ 2)) *
          (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j)) := by
            have h1 :=
              mul_le_mul_of_nonneg_right hw (by positivity : 0 ≤ ‖D.prodSumRealByProd Dpacket.X ξ f i j‖ ^ 2)
            have hKfac :
                0 ≤ (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * ((Dpacket.M * Dpacket.Φmax) ^ 2) := by
              exact mul_nonneg
                (SSU.Engines.TypeII.AdmissibleKernel.Khat_nonneg (H := Dpacket.H) (hH := hH) ξ)
                (by positivity)
            have h2 := mul_le_mul_of_nonneg_left hS0 hKfac
            exact le_trans h1 (by simpa [mul_assoc, mul_left_comm, mul_comm] using h2)
      _ = (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * ((Dpacket.M * Dpacket.Φmax) ^ 2) *
            (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j)) := by
            ring

  -- 5) Integrate the pointwise bound, then bound `∫ Khat ≤ 2/H`.
  have hInt :
      ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
        ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)‖
        ≤
      ((Dpacket.M * Dpacket.Φmax) ^ 2) *
        (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j)) *
          (2 * (Dpacket.H)⁻¹) := by
    -- First use `integral_mono_of_nonneg` on the restricted measure.
    let μ : Measure ℝ :=
      (volume : Measure ℝ).restrict (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H)
    set Cfac : ℝ :=
      ((Dpacket.M * Dpacket.Φmax) ^ 2) *
        (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j))
    have hnonneg :
        0 ≤ᵐ[μ] fun ξ =>
          ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
              (D.prodSumRealByProd Dpacket.X ξ f i j) *
                star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ := by
      exact Filter.Eventually.of_forall (fun ξ => norm_nonneg _)
    have hKhat_int_on :
        IntegrableOn (fun ξ => SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ)
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H) := by
      have hband :
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H =
            Set.Icc (-(Dpacket.H)⁻¹) (Dpacket.H)⁻¹ := by
        simp [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band,
          SSU.Engines.BGTypeIIWeightedToeplitz.band]
      simpa [hband] using
        (SSU.Engines.TypeII.AdmissibleKernel.Khat_integrableOn (H := Dpacket.H) hH)
    have hKhat_int :
        Integrable (fun ξ => SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) μ := by
      simpa [μ, MeasureTheory.IntegrableOn] using hKhat_int_on
    have hgi :
        Integrable
          (fun ξ => (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * Cfac) μ := by
      simpa [Cfac, mul_assoc] using hKhat_int.mul_const Cfac
    have hpoint' :
        (fun ξ =>
            ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                  (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
                (D.prodSumRealByProd Dpacket.X ξ f i j) *
                  star (D.prodSumRealByProd Dpacket.X ξ f i j)‖)
          ≤ᵐ[μ]
          (fun ξ => (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * Cfac) := by
      simpa [μ, Cfac, mul_assoc, mul_left_comm, mul_comm] using hpoint
    have hmono :
        (∫ ξ, ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                    (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
                  (D.prodSumRealByProd Dpacket.X ξ f i j) *
                    star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ ∂ μ)
          ≤
        (∫ ξ, (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * Cfac ∂ μ) := by
      exact MeasureTheory.integral_mono_of_nonneg (μ := μ) hnonneg hgi hpoint'
    -- Pull out constants and apply `∫ Khat ≤ 2/H`.
    have hpull :
        (∫ ξ, (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * Cfac ∂ μ)
          =
        (∫ ξ, SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ ∂ μ) * Cfac := by
      simpa using
        (MeasureTheory.integral_mul_const
          (μ := μ)
          (f := fun ξ => SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ)
          Cfac)
    have hKhat :
        (∫ ξ, SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ ∂ μ)
          ≤ 2 * (Dpacket.H)⁻¹ := by
      have hband :
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H =
            Set.Icc (-(Dpacket.H)⁻¹) (Dpacket.H)⁻¹ := by
        simp [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band,
          SSU.Engines.BGTypeIIWeightedToeplitz.band]
      simpa [μ, hband] using
        (SSU.Engines.TypeII.AdmissibleKernel.integral_Khat_le (H := Dpacket.H) hH)
    have hE0 : 0 ≤ tubeEnergy D.tube (D.F f i j) := by
      unfold SSU.tubeEnergy
      refine Finset.sum_nonneg ?_
      intro p hp
      positivity
    have hCfac0 : 0 ≤ Cfac := by
      have hM0 : 0 ≤ (Dpacket.M * Dpacket.Φmax) ^ 2 := by positivity
      have hsqrt0 : 0 ≤ Real.sqrt (Dpacket.H / Dpacket.X) := Real.sqrt_nonneg _
      have htail0 :
          0 ≤ step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j) := by
        exact mul_nonneg (mul_nonneg step34.C_nonneg hsqrt0) hE0
      exact mul_nonneg hM0 htail0
    have hbound :
        (∫ ξ, ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                    (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
                  (D.prodSumRealByProd Dpacket.X ξ f i j) *
                    star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ ∂ μ)
          ≤ (2 * (Dpacket.H)⁻¹) * Cfac := by
      calc
        (∫ ξ, ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                    (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
                  (D.prodSumRealByProd Dpacket.X ξ f i j) *
                    star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ ∂ μ)
            ≤ (∫ ξ, (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ) * Cfac ∂ μ) := hmono
        _ = (∫ ξ, SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H ξ ∂ μ) * Cfac := hpull
        _ ≤ (2 * (Dpacket.H)⁻¹) * Cfac := by
          exact mul_le_mul_of_nonneg_right hKhat hCfac0
    -- Return to set-integral notation.
    have hboundSet :
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
              (D.prodSumRealByProd Dpacket.X ξ f i j) *
                star (D.prodSumRealByProd Dpacket.X ξ f i j)‖
          ≤ (2 * (Dpacket.H)⁻¹) * Cfac := by
      simpa [μ] using hbound
    calc
      ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
              (D.prodSumRealByProd Dpacket.X ξ f i j) *
                star (D.prodSumRealByProd Dpacket.X ξ f i j)‖
          ≤ (2 * (Dpacket.H)⁻¹) * Cfac := hboundSet
      _ = ((Dpacket.M * Dpacket.Φmax) ^ 2) *
            (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j)) *
              (2 * (Dpacket.H)⁻¹) := by
            simp [Cfac, mul_assoc, mul_left_comm, mul_comm]

  -- 6) Combine all pieces.
  have hnormInner :
      ‖inner ℂ
          (((Dpacket.toMultiplierModel).packetOpUnnormalized i)
            (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
              (Dpacket := Dpacket) (D := D) f i j hH))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j)
            (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
              (Dpacket := Dpacket) (D := D) f i j hH))‖
        =
      ‖((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube)
          (F := D.F f i j)‖ := by
    simpa using congrArg norm hToe
  -- Use `hnormInner`, `hnorm1`, `hnormToInt`, `hleInt`, and `hInt`.
  -- Keep everything on the `ℝ` side; cast/`simp` is handled earlier.
  calc
    ‖inner ℂ
        (((Dpacket.toMultiplierModel).packetOpUnnormalized i)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j)
          (SSU.Instances.FejerBankedTypeIIToeplitzTorusPackets.General.fTT
            (Dpacket := Dpacket) (D := D) f i j hH))‖
        =
      (1 / Dpacket.X) *
        ‖SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
                (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube)
            (F := D.F f i j)‖ := by
          -- Combine `hnormInner` and `hnorm1`.
          simpa [hnormInner] using hnorm1
    _ =
      (1 / Dpacket.X) *
        ‖∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ := by
          simp [hnormToInt]
    _ ≤
      (1 / Dpacket.X) *
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          ‖(SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)‖ := by
          have hnonneg : 0 ≤ (1 / Dpacket.X : ℝ) := one_div_nonneg.2 (le_of_lt hX)
          exact mul_le_mul_of_nonneg_left hleInt hnonneg
    _ ≤
      (1 / Dpacket.X) *
        (((Dpacket.M * Dpacket.Φmax) ^ 2) *
          (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j)) *
            (2 * (Dpacket.H)⁻¹)) := by
          have hnonneg : 0 ≤ (1 / Dpacket.X : ℝ) := one_div_nonneg.2 (le_of_lt hX)
          exact mul_le_mul_of_nonneg_left hInt hnonneg
    _ = ((1 / Dpacket.X) * ((Dpacket.M * Dpacket.Φmax) ^ 2) *
          (step34.C * Real.sqrt (Dpacket.H / Dpacket.X) * tubeEnergy D.tube (D.F f i j))) *
          (2 * (Dpacket.H)⁻¹) := by
          ring

end

end FejerBankedTypeIIToeplitzTorusPacketsStep34Bound
end Instances
end SSU
