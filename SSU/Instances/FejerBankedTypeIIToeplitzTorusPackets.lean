import SSU.Instances.FejerBankedPartition
import SSU.Instances.FejerBankedTypeIIToeplitzBandToArc
import SSU.Instances.FejerBankedTypeIIToeplitzKernel
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis
import SSU.Engines.BGTypeIIArray
import SSU.Torus.AddCircleMeasurability

/-!
Fejér-banked packets (torus-side): deterministic extraction bridge to a Toeplitz Type–II form.

This generalizes `FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean` by replacing the fixed
rank-one Type–II signal with a *general* BG Type–II coefficient array package
`SSU.Engines.BGTypeIIArray.Data`.

It proves, for each pair `(i,j)`, that the torus packet Gram entry for the TT*-weighted input

`fTT(x) := 1_arc(x) * sqrt(KhatTorus(X,H)(x)) * S_{i,j}(x)`

with `S_{i,j}(x) := D.prodSumTorusByProd f i j x`,
is exactly the TeX-normalized grouped-by-product Toeplitz quadratic form
`(1/X) * toeplitzFormTeXC (K_{i,j}) (tube) (F f i j)`.

This is an **algebraic/bookkeeping** lemma: it uses only multiplier Gram expansion, the
band→arc substitution, and deterministic weighted-Toeplitzization.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTorusPackets

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace Helpers

open AddCircle

/-!
`KhatTorus` is defined using `AddCircle.liftIoc`, which involves the representative map
`equivIoc`. That map is continuous everywhere except at the endpoint, hence measurable by the
generic lemma `measurable_of_continuousOn_compl_singleton`.

This mirrors the measurability helpers used in the rank-one bridge file, but is public here so
other “torus packet extraction” files can reuse it.
-/

theorem measurable_equivIoc (p a : ℝ) [Fact (0 < p)] :
    Measurable (AddCircle.equivIoc (p := p) a) := by
  simpa using SSU.Torus.AddCircleMeasurability.measurable_equivIoc (p := p) (a := a)

theorem measurable_liftIoc {B : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    (p a : ℝ) [Fact (0 < p)] [Archimedean ℝ]
    (f : ℝ → B) (hf : Measurable f) :
    Measurable (AddCircle.liftIoc (p := p) (a := a) f) := by
  simpa using
    SSU.Torus.AddCircleMeasurability.measurable_liftIoc (p := p) (a := a) (f := f) hf

end Helpers

namespace General

variable {κ : Type*} [DecidableEq κ]

variable (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)

variable {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
variable (D : SSU.Engines.BGTypeIIArray.Data H0)

open SSU.Engines.TypeII.ProductToeplitz

abbrev X : ℝ := Dpacket.X
abbrev H : ℝ := Dpacket.H

abbrev arc : Set UC :=
  SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand (X := Dpacket.X) (H := Dpacket.H)

noncomputable def fTT_fun (f : H0) (i j : ℤ) : UC → ℂ :=
  (arc (Dpacket := Dpacket)).indicator (fun x =>
    ((Real.sqrt (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)
      * D.prodSumTorusByProd f i j x)

private theorem measurable_arc : MeasurableSet (arc (Dpacket := Dpacket)) := by
  classical
  -- `arcAtBand` is a compact image of `Icc`, hence closed, hence measurable.
  -- This matches the proof pattern in the rank-one bridge.
  dsimp [arc, SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand,
    SSU.Torus.BandMap.arc]
  have hcont : Continuous (fun x : ℝ => (x : UC)) := by
    simpa using (continuous_quotient_mk' : Continuous fun x : ℝ => (x : UC))
  have hcompact : IsCompact (Set.Icc (-(1 / Dpacket.H) / Dpacket.X) ((1 / Dpacket.H) / Dpacket.X)) :=
    isCompact_Icc
  have hclosed :
      IsClosed ((fun x : ℝ => (x : UC)) '' Set.Icc (-(1 / Dpacket.H) / Dpacket.X) ((1 / Dpacket.H) / Dpacket.X)) :=
    (hcompact.image hcont).isClosed
  simpa using hclosed.measurableSet

private theorem measurable_prodSumTorusByProd (f : H0) (i j : ℤ) :
    Measurable (D.prodSumTorusByProd f i j) := by
  classical
  -- Finite sum of measurable characters.
  unfold SSU.Engines.BGTypeIIArray.Data.prodSumTorusByProd
  refine Finset.measurable_sum (s := (D.tube).image prod) ?_
  intro k hk
  have hfour : Measurable fun x : UC => (fourier (T := (1 : ℝ)) k x : ℂ) :=
    (fourier (T := (1 : ℝ)) k).continuous.measurable
  simpa [mul_assoc] using (measurable_const.mul hfour)

private theorem measurable_KhatTorus : Measurable
    (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H) := by
  classical
  -- `KhatTorus` is `liftIoc` of a measurable function.
  unfold SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal
  have hmeas : Measurable (fun x : ℝ =>
      SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H (Dpacket.X * x)) := by
    have hK : Measurable (SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H) := by
      classical
      refine Measurable.ite ?_ (measurable_const.mul measurable_abs) measurable_const
      exact measurableSet_le measurable_abs measurable_const
    simpa [Function.comp, mul_assoc] using (hK.comp (measurable_const.mul measurable_id))
  simpa using (Helpers.measurable_liftIoc (p := (1 : ℝ)) (a := (-(1 / 2 : ℝ)))
    (f := fun x : ℝ => SSU.Engines.TypeII.AdmissibleKernel.Khat Dpacket.H (Dpacket.X * x)) hmeas)

private theorem measurable_fTT_fun (f : H0) (i j : ℤ) :
    Measurable (fTT_fun (Dpacket := Dpacket) (D := D) f i j) := by
  classical
  -- Combine measurability of the arc indicator with measurability of the product.
  have hsqrt : Measurable fun x : UC =>
      Real.sqrt (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) :=
    (Real.continuous_sqrt.measurable.comp (measurable_KhatTorus (Dpacket := Dpacket)))
  have hsqrtC : Measurable fun x : UC =>
      ((Real.sqrt (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.measurable.comp hsqrt)
  have hsig : Measurable (D.prodSumTorusByProd f i j) :=
    measurable_prodSumTorusByProd (D := D) f i j
  have hmul : Measurable fun x : UC =>
      ((Real.sqrt (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)
        * D.prodSumTorusByProd f i j x :=
    hsqrtC.mul hsig
  simpa [fTT_fun, arc] using hmul.indicator (measurable_arc (Dpacket := Dpacket))

private theorem norm_prodSumTorusByProd_le (f : H0) (i j : ℤ) (x : UC) :
    ‖D.prodSumTorusByProd f i j x‖
      ≤
    ∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖ := by
  classical
  unfold SSU.Engines.BGTypeIIArray.Data.prodSumTorusByProd
  have h1 :
      ‖∑ k ∈ (D.tube).image prod, (D.A f i j k) * (fourier (T := (1 : ℝ)) k x : ℂ)‖
        ≤
      ∑ k ∈ (D.tube).image prod, ‖(D.A f i j k) * (fourier (T := (1 : ℝ)) k x : ℂ)‖ := by
    simpa using (norm_sum_le (s := (D.tube).image prod)
      (f := fun k => (D.A f i j k) * (fourier (T := (1 : ℝ)) k x : ℂ)))
  have h2 :
      (∑ k ∈ (D.tube).image prod, ‖(D.A f i j k) * (fourier (T := (1 : ℝ)) k x : ℂ)‖)
        =
      ∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖ := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hchar : ‖(fourier (T := (1 : ℝ)) k x : ℂ)‖ = 1 := by
      simpa [fourier_apply] using (Circle.norm_coe (AddCircle.toCircle ((k : ℤ) • x)))
    simp [norm_mul, hchar]
  exact h2 ▸ h1

private theorem KhatTorus_nonneg (hH : 0 < Dpacket.H) (x : UC) :
    0 ≤ SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x := by
  classical
  unfold SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal
  simpa [AddCircle.liftIoc, Function.comp] using
    (SSU.Engines.TypeII.AdmissibleKernel.Khat_nonneg (H := Dpacket.H) (hH := hH)
      (Dpacket.X *
        ((AddCircle.equivIoc (p := (1 : ℝ)) (-(1 / 2 : ℝ)) x :
          Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))) : ℝ)))

private theorem KhatTorus_le_one (hH : 0 < Dpacket.H) (x : UC) :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x ≤ 1 := by
  classical
  unfold SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal
  simpa [AddCircle.liftIoc, Function.comp] using
    (SSU.Engines.TypeII.AdmissibleKernel.Khat_le_one (H := Dpacket.H) hH
      (Dpacket.X *
        ((AddCircle.equivIoc (p := (1 : ℝ)) (-(1 / 2 : ℝ)) x :
          Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))) : ℝ)))

private theorem norm_fTT_fun_le (f : H0) (i j : ℤ) (hH : 0 < Dpacket.H) (x : UC) :
    ‖fTT_fun (Dpacket := Dpacket) (D := D) f i j x‖
      ≤
    ∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖ := by
  classical
  by_cases hx : x ∈ arc (Dpacket := Dpacket)
  · have hK1 :
        SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x ≤ 1 :=
      KhatTorus_le_one (Dpacket := Dpacket) hH x
    have hsqrt1 :
        Real.sqrt (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) ≤ 1 :=
      (Real.sqrt_le_one).2 hK1
    have hsqrt_norm :
        ‖((Real.sqrt
            (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)‖
          ≤ 1 := by
      have hnonneg : 0 ≤ Real.sqrt
          (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) :=
        Real.sqrt_nonneg _
      simpa [Complex.norm_real, abs_of_nonneg hnonneg] using hsqrt1
    have hsig := norm_prodSumTorusByProd_le (D := D) f i j x
    have : ‖((Real.sqrt
          (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)
        * D.prodSumTorusByProd f i j x‖
          ≤ ∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖ := by
      have h0 : 0 ≤ ‖D.prodSumTorusByProd f i j x‖ := by positivity
      have hmul1 :
          ‖((Real.sqrt
            (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)‖
            * ‖D.prodSumTorusByProd f i j x‖
            ≤ 1 * ‖D.prodSumTorusByProd f i j x‖ :=
        mul_le_mul_of_nonneg_right hsqrt_norm h0
      have hmul2 :
          1 * ‖D.prodSumTorusByProd f i j x‖ ≤ ∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖ := by
        simpa using hsig
      calc
        ‖((Real.sqrt
              (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)
            * D.prodSumTorusByProd f i j x‖
            = ‖((Real.sqrt
                (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)‖
              * ‖D.prodSumTorusByProd f i j x‖ := by simpa [norm_mul]
        _ ≤ 1 * ‖D.prodSumTorusByProd f i j x‖ := hmul1
        _ ≤ ∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖ := hmul2
    simpa [fTT_fun, arc, hx] using this
  · have : 0 ≤ ∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖ :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    simpa [fTT_fun, arc, hx] using this

theorem memLp_fTT_fun_top (f : H0) (i j : ℤ) (hH : 0 < Dpacket.H) :
    MemLp (fTT_fun (Dpacket := Dpacket) (D := D) f i j) (∞ : ℝ≥0∞) μ := by
  classical
  refine MeasureTheory.memLp_top_of_bound
      (measurable_fTT_fun (Dpacket := Dpacket) (D := D) f i j).aestronglyMeasurable
      (∑ k ∈ (D.tube).image prod, ‖D.A f i j k‖) ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact norm_fTT_fun_le (Dpacket := Dpacket) (D := D) f i j hH x

theorem memLp_fTT_fun_two (f : H0) (i j : ℤ) (hH : 0 < Dpacket.H) :
    MemLp (fTT_fun (Dpacket := Dpacket) (D := D) f i j) (2 : ℝ≥0∞) μ := by
  classical
  have htop :
      MemLp (fTT_fun (Dpacket := Dpacket) (D := D) f i j) (∞ : ℝ≥0∞) μ :=
    memLp_fTT_fun_top (Dpacket := Dpacket) (D := D) f i j hH
  haveI : IsFiniteMeasure (μ := μ) := by infer_instance
  exact MeasureTheory.MemLp.mono_exponent htop (by simp)

noncomputable def fTT (f : H0) (i j : ℤ) (hH : 0 < Dpacket.H) : SSU.Torus.L2 :=
  (memLp_fTT_fun_two (Dpacket := Dpacket) (D := D) f i j hH).toLp
    (fTT_fun (Dpacket := Dpacket) (D := D) f i j)

theorem fTT_coeFn_eq (f : H0) (i j : ℤ) (hH : 0 < Dpacket.H) :
    (fun x : UC => (fTT (Dpacket := Dpacket) (D := D) f i j hH) x)
      =ᵐ[μ]
    (fTT_fun (Dpacket := Dpacket) (D := D) f i j) := by
  classical
  simpa [fTT] using
    (memLp_fTT_fun_two (Dpacket := Dpacket) (D := D) f i j hH).coeFn_toLp
      (f := fTT_fun (Dpacket := Dpacket) (D := D) f i j)

theorem inner_packetOpUnnormalized_eq_arcIntegral
    (f : H0) (i j : ℤ) (hH : 0 < Dpacket.H) :
    inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
      =
    ∫ z : UC,
      (arc (Dpacket := Dpacket)).indicator
        (fun x =>
          (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x : ℝ) : ℂ) *
                star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
              (D.prodSumTorusByProd f i j x) * star (D.prodSumTorusByProd f i j x))
        z ∂μ := by
  classical
  -- Start from the deterministic Gram expansion for multiplier packets.
  have hGram :=
    (Dpacket.toMultiplierModel).inner_packetOpUnnormalized_eq_integral (i := i) (j := j)
      (f := fTT (Dpacket := Dpacket) (D := D) f i j hH)
      (g := fTT (Dpacket := Dpacket) (D := D) f i j hH)
  -- Replace the `L²` representative by the explicit `fTT_fun` a.e.
  have hEq :
      (fun x : UC =>
          (star (Dpacket.ψ i x) * Dpacket.ψ j x) *
            (star ((fTT (Dpacket := Dpacket) (D := D) f i j hH) x) *
              (fTT (Dpacket := Dpacket) (D := D) f i j hH) x))
        =ᵐ[μ]
      (fun x : UC =>
          (star (Dpacket.ψ i x) * Dpacket.ψ j x) *
            (star (fTT_fun (Dpacket := Dpacket) (D := D) f i j x) *
              fTT_fun (Dpacket := Dpacket) (D := D) f i j x)) := by
    filter_upwards [fTT_coeFn_eq (Dpacket := Dpacket) (D := D) f i j hH] with x hx
    simp [hx]
  have hint :
      (∫ x : UC,
          (star (Dpacket.ψ i x) * Dpacket.ψ j x) *
            (star ((fTT (Dpacket := Dpacket) (D := D) f i j hH) x) *
              (fTT (Dpacket := Dpacket) (D := D) f i j hH) x) ∂μ)
        =
      ∫ x : UC,
        (star (Dpacket.ψ i x) * Dpacket.ψ j x) *
          (star (fTT_fun (Dpacket := Dpacket) (D := D) f i j x) *
            fTT_fun (Dpacket := Dpacket) (D := D) f i j x) ∂μ :=
    integral_congr_ae hEq
  -- Now simplify `star fTT_fun * fTT_fun` into the arc indicator form.
  have hpoint :
      (fun x : UC =>
          (star (Dpacket.ψ i x) * Dpacket.ψ j x) *
            (star (fTT_fun (Dpacket := Dpacket) (D := D) f i j x) *
              fTT_fun (Dpacket := Dpacket) (D := D) f i j x))
        =
      (fun x : UC =>
        (arc (Dpacket := Dpacket)).indicator
          (fun x =>
            (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x : ℝ) : ℂ) *
              star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
                (D.prodSumTorusByProd f i j x) * star (D.prodSumTorusByProd f i j x))
          x) := by
    funext x
    by_cases hx : x ∈ arc (Dpacket := Dpacket)
    · -- On-arc: compute directly.
      have hK0 :
          0 ≤ SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x :=
        KhatTorus_nonneg (Dpacket := Dpacket) hH x
      have hsqrt_mul :
          ((Real.sqrt
              (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ) *
              ((Real.sqrt
                (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) : ℝ) : ℂ)
            =
          ((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x : ℝ) : ℂ) := by
        have :
            Real.sqrt
                (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x) *
              Real.sqrt
                (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x)
              =
            SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x := by
          simpa [pow_two] using (Real.sq_sqrt hK0)
        simpa [Complex.ofReal_mul] using congrArg (fun t : ℝ => (t : ℂ)) this
      set r : ℝ :=
        SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x
      set a : ℂ := ((Real.sqrt r : ℝ) : ℂ)
      set s : ℂ := D.prodSumTorusByProd f i j x
      have hfTT : fTT_fun (Dpacket := Dpacket) (D := D) f i j x = a * s := by
        simp [fTT_fun, arc, hx, a, s, r]
      have hRHS :
          (arc (Dpacket := Dpacket)).indicator
              (fun x =>
                (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x : ℝ) : ℂ) *
                  star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
                    (D.prodSumTorusByProd f i j x) * star (D.prodSumTorusByProd f i j x))
              x
            =
          (((r : ℝ) : ℂ) * star (Dpacket.ψ i x) * (Dpacket.ψ j x)) * s * star s := by
        simp [Set.indicator, hx, r, s, mul_assoc, mul_left_comm, mul_comm]
      have hstar_a : star a = a := by simp [a]
      rw [hRHS]
      have haa : a * a = ((r : ℝ) : ℂ) := by
        simpa [a, r] using hsqrt_mul
      have hstar_as : star (a * s) = star s * a := by
        simpa [star_mul, hstar_a, mul_assoc] using (rfl : star (a * s) = star (a * s))
      calc
        (star (Dpacket.ψ i x) * Dpacket.ψ j x) *
            (star (fTT_fun (Dpacket := Dpacket) (D := D) f i j x) *
              fTT_fun (Dpacket := Dpacket) (D := D) f i j x)
            =
          (star (Dpacket.ψ i x) * Dpacket.ψ j x) * ((star s * a) * (a * s)) := by
            simp [hfTT, hstar_as, mul_assoc]
        _ = (star (Dpacket.ψ i x) * Dpacket.ψ j x) * (((r : ℝ) : ℂ) * (s * star s)) := by
            ring_nf
            simp [pow_two] at *
            rw [haa]
            ring_nf
        _ = (((r : ℝ) : ℂ) * star (Dpacket.ψ i x) * (Dpacket.ψ j x)) * s * star s := by
            ring_nf
    · -- Off-arc: everything is zero by the indicator.
      simp [fTT_fun, arc, hx]
  -- Assemble.
  calc
    inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        =
      ∫ x : UC, (star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
          (star ((fTT (Dpacket := Dpacket) (D := D) f i j hH) x) *
            (fTT (Dpacket := Dpacket) (D := D) f i j hH) x) ∂μ := by
            simpa [SSU.Instances.TorusDyadicShell.MultiplierModel.packetOpUnnormalized] using hGram
    _ =
      ∫ x : UC, (star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
          (star (fTT_fun (Dpacket := Dpacket) (D := D) f i j x) *
            fTT_fun (Dpacket := Dpacket) (D := D) f i j x) ∂μ := hint
    _ =
      ∫ z : UC,
        (arc (Dpacket := Dpacket)).indicator
          (fun x =>
            (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x : ℝ) : ℂ) *
              star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
                (D.prodSumTorusByProd f i j x) * star (D.prodSumTorusByProd f i j x))
          z ∂μ := by
            simpa using congrArg (fun F : UC → ℂ => ∫ z : UC, F z ∂μ) hpoint

theorem inner_packetOpUnnormalized_eq_toeplitzFormTeXC
    (f : H0) (i j : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)) :
    inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
      =
    ((1 / Dpacket.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := Dpacket) Dpacket.X Dpacket.H i j t)
        (T := D.tube)
        (F := D.F f i j) := by
  classical
  -- Start from the arc-integral form of the Gram entry.
  have hArc := inner_packetOpUnnormalized_eq_arcIntegral (Dpacket := Dpacket) (D := D) (f := f) (i := i) (j := j) hH
  -- Convert arc integral to a band integral with the `1/X` Jacobian.
  -- We apply the generic band→arc lemma with `g` the arc integrand.
  let g : UC → ℂ :=
    fun x =>
      (((SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H x : ℝ) : ℂ) *
            star (Dpacket.ψ i x) * (Dpacket.ψ j x)) *
          (D.prodSumTorusByProd f i j x) * star (D.prodSumTorusByProd f i j x)
  have hband :
      (∫ z : UC, (arc (Dpacket := Dpacket)).indicator g z ∂μ)
        =
      ((1 / Dpacket.X : ℝ) •
        ∫ ξ in Set.Icc (-(1 / Dpacket.H)) (1 / Dpacket.H), g ((ξ / Dpacket.X : ℝ) : UC)) := by
    -- The band→arc lemma is stated w.r.t. the default `volume` measure; convert to `∂μ`.
    have hvol : (volume : Measure UC) = μ := by
      simp [SSU.Torus.μ, SSU.Torus.UC, AddCircle.volume_eq_smul_haarAddCircle]
    have h :=
      (SSU.Instances.FejerBankedTypeIIToeplitzBandToArc.one_div_X_smul_integral_band_eval_eq_integral_indicator_arc
        (X := Dpacket.X) (H := Dpacket.H) (hX := hX) (hH := hH) (hsmall := hsmall) (g := g))
    -- Flip and simplify `arcAtBand` vs `bandMap.arc`, and rewrite `volume` as `μ`.
    -- `arcAtBand X H` is definitionally `bandMap.arc (-(1/H)/X) ((1/H)/X)`.
    simpa [arc, SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Arc.arcAtBand, hvol] using h.symm
  -- Rewrite the band integrand using `KhatTorus_eval_eq_Khat_on_band`, so it matches `wLean`.
  have hKhat :
      ∀ ξ : ℝ, ξ ∈ Set.Icc (-(1 / Dpacket.H)) (1 / Dpacket.H) →
        (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus Dpacket.X Dpacket.H ((ξ / Dpacket.X : ℝ) : UC))
          =
        SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal Dpacket.H ξ := by
    intro ξ hξ
    simpa [SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatReal]
      using (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis.Khat.KhatTorus_eval_eq_Khat_on_band
        (X := Dpacket.X) (H := Dpacket.H) (hX := hX) (hH := hH) (hsmall := hsmall) ξ hξ)
  -- Now express the band integral as the `wLean`-weighted band integral of `prodSumRealByProd`.
  have hbridge :
      (∫ ξ in Set.Icc (-(1 / Dpacket.H)) (1 / Dpacket.H), g ((ξ / Dpacket.X : ℝ) : UC))
        =
      ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
        (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
          (D.prodSumRealByProd Dpacket.X ξ f i j) * star (D.prodSumRealByProd Dpacket.X ξ f i j) := by
    classical
    -- `band H` is definitional `Icc`.
    -- Rewrite `g((ξ/X):𝕋)` into `wLean * prodSumTorusByProd * star`.
    -- Then rewrite `prodSumTorusByProd` into `prodSumRealByProd` (deterministic bridge).
    have hprod :
        ∀ ξ : ℝ, D.prodSumRealByProd Dpacket.X ξ f i j =
          D.prodSumTorusByProd f i j ((ξ / Dpacket.X : ℝ) : UC) := by
      intro ξ
      simpa using (D.prodSumRealByProd_eq_prodSumTorusByProd (X := Dpacket.X) (ξ := ξ) (f := f) (i := i) (j := j))
    -- Apply integral congruence.
    refine integral_congr_ae ?_
    -- Pointwise on the band, unfold and simplify.
    filter_upwards
      [ae_restrict_mem (μ := (volume : Measure ℝ)) (s := Set.Icc (-(1 / Dpacket.H)) (1 / Dpacket.H))
        measurableSet_Icc] with ξ hξ
    have hK := hKhat ξ hξ
    -- `wLean` uses `KhatReal H ξ`.
    -- Move factors into the `wLean` definition.
    simp [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean,
      SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.w,
      SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band,
      g, hK, hprod ξ, mul_assoc, mul_left_comm, mul_comm]
  -- Toeplitzize the weighted band integral.
  have htoe :
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) * star (D.prodSumRealByProd Dpacket.X ξ f i j))
        =
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := Dpacket) Dpacket.X Dpacket.H i j t)
        (T := D.tube)
        (F := D.F f i j) := by
    -- Use the existing deterministic Toeplitzization lemma in the kernel file.
    have hX0 : (Dpacket.X : ℝ) ≠ 0 := ne_of_gt hX
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
        (Dpacket := Dpacket) (D := D) (X := Dpacket.X) (H := Dpacket.H) (f := f) (i := i) (j := j)
        (hH := hH) (hX := hX0))
  -- Put everything together and convert `•` into `((1/X):ℂ) * _`.
  have hscalar :
      ((1 / Dpacket.X : ℝ) •
          SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
            (K := fun t =>
              SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := Dpacket) Dpacket.X Dpacket.H i j t)
            (T := D.tube) (F := D.F f i j))
        =
      ((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube) (F := D.F f i j) := by
    -- Scalar multiplication by `ℝ` on `ℂ` is multiplication by `((r:ℂ))`.
    simp
  -- Final chain.
  calc
    inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        =
      ∫ z : UC, (arc (Dpacket := Dpacket)).indicator g z ∂μ := by
        simpa [g] using hArc
    _ =
      ((1 / Dpacket.X : ℝ) •
        ∫ ξ in Set.Icc (-(1 / Dpacket.H)) (1 / Dpacket.H), g ((ξ / Dpacket.X : ℝ) : UC)) := hband
    _ =
      ((1 / Dpacket.X : ℝ) •
        ∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) * star (D.prodSumRealByProd Dpacket.X ξ f i j)) := by
        -- Replace the integrand by `hbridge`.
        simpa [SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band] using congrArg (fun z => ((1 / Dpacket.X : ℝ) • z)) hbridge
    _ =
      ((1 / Dpacket.X : ℝ) •
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube)
          (F := D.F f i j)) := by
        -- Avoid `simp`-driven cancellations; just push `htoe` through the scalar factor.
        simpa using congrArg (fun z => ((1 / Dpacket.X : ℝ) • z)) htoe
    _ =
      ((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube)
          (F := D.F f i j) := by
        simpa [hscalar]

/--
Same extraction step as `inner_packetOpUnnormalized_eq_toeplitzFormTeXC`, but kept in the
weighted-band-integral form (the exact TT*/Step-2 shape used by bridge hypotheses).
-/
theorem inner_packetOpUnnormalized_eq_weightedIntegral
    (f : H0) (i j : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)) :
    inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
      =
    ((1 / Dpacket.X : ℝ) : ℂ) *
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)) := by
  have hToe :
      inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
          (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        =
      ((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube)
          (F := D.F f i j) :=
    inner_packetOpUnnormalized_eq_toeplitzFormTeXC
      (Dpacket := Dpacket) (D := D) (f := f) (i := i) (j := j)
      (hX := hX) (hH := hH) (hsmall := hsmall)
  have hX0 : (Dpacket.X : ℝ) ≠ 0 := ne_of_gt hX
  have hDet :
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j))
        =
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
            (D := Dpacket) Dpacket.X Dpacket.H i j t)
        (T := D.tube)
        (F := D.F f i j) := by
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzKernel.integral_weight_mul_prodSumRealByProd_mul_star_eq_toeplitzFormTeXC_auto
        (Dpacket := Dpacket) (D := D) (X := Dpacket.X) (H := Dpacket.H)
        (f := f) (i := i) (j := j) (hH := hH) (hX := hX0))
  calc
    inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        =
      ((1 / Dpacket.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean
              (D := Dpacket) Dpacket.X Dpacket.H i j t)
          (T := D.tube)
          (F := D.F f i j) := hToe
    _ =
      ((1 / Dpacket.X : ℝ) : ℂ) *
        (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
              (D.prodSumRealByProd Dpacket.X ξ f i j) *
                star (D.prodSumRealByProd Dpacket.X ξ f i j)) := by
      rw [← hDet]

/-- `J`-indexed wrapper of `inner_packetOpUnnormalized_eq_weightedIntegral` for heart-facing APIs. -/
theorem inner_packetOpUnnormalized_eq_weightedIntegral_onJ
    (f : H0)
    (i : ℤ) (_hi : i ∈ Dpacket.J)
    (j : ℤ) (_hj : j ∈ Dpacket.J)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ)) :
    inner ℂ (((Dpacket.toMultiplierModel).packetOpUnnormalized i) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
        (((Dpacket.toMultiplierModel).packetOpUnnormalized j) (fTT (Dpacket := Dpacket) (D := D) f i j hH))
      =
    ((1 / Dpacket.X : ℝ) : ℂ) *
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band Dpacket.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := Dpacket) Dpacket.X Dpacket.H i j ξ) *
            (D.prodSumRealByProd Dpacket.X ξ f i j) *
              star (D.prodSumRealByProd Dpacket.X ξ f i j)) := by
  simpa using
    inner_packetOpUnnormalized_eq_weightedIntegral
      (Dpacket := Dpacket) (D := D) (f := f) (i := i) (j := j)
      (hX := hX) (hH := hH) (hsmall := hsmall)

end General

end

end FejerBankedTypeIIToeplitzTorusPackets
end Instances
end SSU
