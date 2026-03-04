import SSU.Instances.FejerBankedPartition
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof
import SSU.Instances.FejerBankedTypeIIToeplitzTorusRankOneTTStar
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis
import SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis
import SSU.Engines.BGTypeIIRankOneSignal
import SSU.Torus.AddCircleMeasurability

/-!
Fejér-banked packets: **torus-side** TT* bridge for rank-one Type–II input.

This file finally constructs the weighted torus signal

`g(x) := 1_arc(x) * √(KhatTorus(X,H)(x)) * S(x)`

and proves that the **actual torus packet Gram entry**

`⟪(ψ_i•g),(ψ_j•g)⟫_{L²(𝕋)}`

equals the TeX small-arc integral, and hence (by the already proved deterministic Toeplitzization)
equals the TeX `k,k'` Toeplitz quadratic form.

We keep this *rank-one only*: the general Type–II extraction from arbitrary inputs is the later
`ReductionToTubeFormProd` milestone.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIToeplitzTorusPacketsRankOne

open scoped BigOperators ENNReal

noncomputable section

open MeasureTheory
open SSU.Torus

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {κ : Type*} [DecidableEq κ]

variable (D : SSU.Instances.FejerBankedPartition.Data κ)
variable (P : SSU.Engines.BGTube.Params)
variable (W : SSU.Engines.TFA.SeparableWeight)
variable (I : SSU.Engines.BGTypeIIRankOne.Input)

namespace Helpers

open AddCircle

/-!
`KhatTorus` is defined using `AddCircle.liftIoc`, which involves the representative map
`equivIoc`. That map is continuous everywhere except at the endpoint, hence measurable by the
generic lemma `measurable_of_continuousOn_compl_singleton`.
-/

private theorem measurable_equivIoc (p a : ℝ) [Fact (0 < p)] :
    Measurable (AddCircle.equivIoc (p := p) a) := by
  simpa using SSU.Torus.AddCircleMeasurability.measurable_equivIoc (p := p) (a := a)

private theorem measurable_liftIoc {B : Type*} [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    (p a : ℝ) [Fact (0 < p)] [Archimedean ℝ]
    (f : ℝ → B) (hf : Measurable f) :
    Measurable (AddCircle.liftIoc (p := p) (a := a) f) := by
  simpa using
    SSU.Torus.AddCircleMeasurability.measurable_liftIoc (p := p) (a := a) (f := f) hf

end Helpers

namespace RankOne

open SSU.Engines.BGTypeIIRankOne
open SSU.Engines.TypeII.ProductToeplitz
open SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcHypothesis

abbrev arc : Set UC :=
  Arc.arcAtBand D.X D.H

noncomputable def fTT_fun : UC → ℂ :=
  (arc (D := D)).indicator (fun x =>
    ((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ) * I.signalTorusByProd P W x)

private theorem measurable_signalTorusByProd : Measurable (I.signalTorusByProd P W) := by
  classical
  -- Finite sum of measurable characters.
  unfold Input.signalTorusByProd
  refine Finset.measurable_sum (s := P.box.image prod) ?_
  intro k hk
  have hfour : Measurable fun x : UC => (fourier (T := (1 : ℝ)) k x : ℂ) :=
    (fourier (T := (1 : ℝ)) k).continuous.measurable
  simpa [mul_assoc] using (measurable_const.mul hfour)

private theorem measurable_KhatTorus : Measurable (Khat.KhatTorus D.X D.H) := by
  -- `KhatTorus` is `liftIoc` of a measurable function.
  classical
  unfold Khat.KhatTorus Khat.KhatReal
  -- Use `Helpers.measurable_liftIoc`.
  have hmeas : Measurable (fun x : ℝ =>
      SSU.Engines.TypeII.AdmissibleKernel.Khat D.H (D.X * x)) := by
    -- `Khat` is measurable; multiply by a constant.
    have hK : Measurable (SSU.Engines.TypeII.AdmissibleKernel.Khat D.H) := by
      classical
      -- copy of the measurability lemma used in `TypeII.Khat_integrableOn`
      refine Measurable.ite ?_ (measurable_const.mul measurable_abs) measurable_const
      exact measurableSet_le measurable_abs measurable_const
    simpa [Function.comp, mul_assoc] using (hK.comp (measurable_const.mul measurable_id))
  simpa using
    (Helpers.measurable_liftIoc (p := (1 : ℝ)) (a := (-(1 / 2 : ℝ))) (f := fun x : ℝ =>
        SSU.Engines.TypeII.AdmissibleKernel.Khat D.H (D.X * x)) hmeas)

private theorem measurable_arc : MeasurableSet (arc (D := D)) := by
  classical
  -- `arcAtBand` is a compact image of `Icc`, hence closed, hence measurable.
  dsimp [arc, Arc.arcAtBand, SSU.Torus.BandMap.arc]
  have hcont : Continuous (fun x : ℝ => (x : UC)) := by
    simpa using (continuous_quotient_mk' : Continuous fun x : ℝ => (x : UC))
  have hcomp :
      IsCompact ((fun x : ℝ => (x : UC)) '' Set.Icc (-(1 / D.H) / D.X) ((1 / D.H) / D.X)) :=
    (isCompact_Icc.image hcont)
  exact hcomp.isClosed.measurableSet

private theorem measurable_fTT_fun : Measurable (fTT_fun (D := D) (P := P) (W := W) (I := I)) := by
  classical
  -- Measurable indicator of a measurable set.
  have hsqrt : Measurable fun x : UC => Real.sqrt (Khat.KhatTorus D.X D.H x) :=
    (Real.continuous_sqrt.measurable.comp (measurable_KhatTorus (D := D)))
  have hsqrtC : Measurable fun x : UC => ((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.measurable.comp hsqrt)
  have hsig : Measurable (I.signalTorusByProd P W) := measurable_signalTorusByProd (I := I) (P := P) (W := W)
  have hmul : Measurable fun x : UC =>
      ((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ) * I.signalTorusByProd P W x :=
    hsqrtC.mul hsig
  simpa [fTT_fun, arc] using hmul.indicator (measurable_arc (D := D))

private theorem norm_signalTorusByProd_le (x : UC) :
    ‖I.signalTorusByProd P W x‖
      ≤
    ∑ k ∈ P.box.image prod, ‖I.A P W k‖ := by
  classical
  -- Same bound as in the real-frequency model, but with `fourier` in place of `e`.
  unfold Input.signalTorusByProd
  have h1 :
      ‖∑ k ∈ P.box.image prod, (I.A P W k) * (fourier (T := (1 : ℝ)) k x : ℂ)‖
        ≤
      ∑ k ∈ P.box.image prod, ‖(I.A P W k) * (fourier (T := (1 : ℝ)) k x : ℂ)‖ := by
    simpa using (norm_sum_le (s := P.box.image prod)
      (f := fun k => (I.A P W k) * (fourier (T := (1 : ℝ)) k x : ℂ)))
  have h2 :
      (∑ k ∈ P.box.image prod, ‖(I.A P W k) * (fourier (T := (1 : ℝ)) k x : ℂ)‖)
        =
      ∑ k ∈ P.box.image prod, ‖I.A P W k‖ := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hchar : ‖(fourier (T := (1 : ℝ)) k x : ℂ)‖ = 1 := by
      -- `fourier k x ∈ unit circle`.
      simpa [fourier_apply] using (Circle.norm_coe (AddCircle.toCircle ((k : ℤ) • x)))
    simp [norm_mul, hchar]
  exact h2 ▸ h1

private theorem KhatTorus_nonneg (hH : 0 < D.H) (x : UC) : 0 ≤ Khat.KhatTorus D.X D.H x := by
  classical
  -- Expand to the real representative and use `Khat_nonneg`.
  unfold Khat.KhatTorus Khat.KhatReal
  -- `liftIoc` evaluates `f` at the representative in `Ioc`.
  -- We prove a pointwise inequality, so unfold the definition and reduce to `Khat_nonneg`.
  simpa [AddCircle.liftIoc, Function.comp] using
    (SSU.Engines.TypeII.AdmissibleKernel.Khat_nonneg (H := D.H) (hH := hH)
      (D.X * ((AddCircle.equivIoc (p := (1 : ℝ)) (-(1 / 2 : ℝ)) x :
        Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))) : ℝ)))

private theorem KhatTorus_le_one (hH : 0 < D.H) (x : UC) : Khat.KhatTorus D.X D.H x ≤ 1 := by
  classical
  -- Same reduction to the representative.
  unfold Khat.KhatTorus Khat.KhatReal
  simpa [AddCircle.liftIoc, Function.comp] using
    (SSU.Engines.TypeII.AdmissibleKernel.Khat_le_one (H := D.H) hH
      (D.X * ((AddCircle.equivIoc (p := (1 : ℝ)) (-(1 / 2 : ℝ)) x : Set.Ioc (-(1 / 2 : ℝ)) ((-(1 / 2 : ℝ)) + (1 : ℝ))) : ℝ)))

private theorem norm_fTT_fun_le (hH : 0 < D.H) (x : UC) :
    ‖fTT_fun (D := D) (P := P) (W := W) (I := I) x‖
      ≤
    ∑ k ∈ P.box.image prod, ‖I.A P W k‖ := by
  classical
  by_cases hx : x ∈ arc (D := D)
  · -- On the arc, `‖√Khat‖ ≤ 1`.
    have hK0 : 0 ≤ Khat.KhatTorus D.X D.H x := KhatTorus_nonneg (D := D) (hH := hH) x
    have hK1 : Khat.KhatTorus D.X D.H x ≤ 1 := KhatTorus_le_one (D := D) (hH := hH) x
    have hsqrt1 : Real.sqrt (Khat.KhatTorus D.X D.H x) ≤ 1 := by
      exact (Real.sqrt_le_one).2 hK1
    have hsqrt_norm :
        ‖((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ)‖ ≤ 1 := by
      have hnonneg : 0 ≤ Real.sqrt (Khat.KhatTorus D.X D.H x) := Real.sqrt_nonneg _
      simpa [Complex.norm_real, abs_of_nonneg hnonneg] using hsqrt1
    have hsig := norm_signalTorusByProd_le (I := I) (P := P) (W := W) x
    -- Expand `fTT_fun` and bound.
    have : ‖((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ) * I.signalTorusByProd P W x‖
          ≤ ∑ k ∈ P.box.image prod, ‖I.A P W k‖ := by
      have h0 : 0 ≤ ‖I.signalTorusByProd P W x‖ := by positivity
      have hmul1 :
          ‖((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ)‖ * ‖I.signalTorusByProd P W x‖
            ≤ 1 * ‖I.signalTorusByProd P W x‖ :=
        mul_le_mul_of_nonneg_right hsqrt_norm h0
      have hmul2 :
          1 * ‖I.signalTorusByProd P W x‖ ≤ ∑ k ∈ P.box.image prod, ‖I.A P W k‖ := by
        simpa using hsig
      calc
        ‖((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ) * I.signalTorusByProd P W x‖
            = ‖((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ)‖ *
                ‖I.signalTorusByProd P W x‖ := by simpa [norm_mul]
        _ ≤ 1 * ‖I.signalTorusByProd P W x‖ := hmul1
        _ ≤ ∑ k ∈ P.box.image prod, ‖I.A P W k‖ := hmul2
    simpa [fTT_fun, arc, hx] using this
  · -- Off the arc, the indicator is `0`.
    have : 0 ≤ ∑ k ∈ P.box.image prod, ‖I.A P W k‖ := by
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    simpa [fTT_fun, arc, hx] using this

theorem memLp_fTT_fun_top (hH : 0 < D.H) :
    MemLp (fTT_fun (D := D) (P := P) (W := W) (I := I)) (∞ : ℝ≥0∞) μ := by
  classical
  -- Use `memLp_top_of_bound` with the global bound `∑ ‖A_k‖`.
  refine MeasureTheory.memLp_top_of_bound (measurable_fTT_fun (D := D) (P := P) (W := W) (I := I)).aestronglyMeasurable
    (∑ k ∈ P.box.image prod, ‖I.A P W k‖) ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  exact norm_fTT_fun_le (D := D) (P := P) (W := W) (I := I) hH x

theorem memLp_fTT_fun_two (hH : 0 < D.H) :
    MemLp (fTT_fun (D := D) (P := P) (W := W) (I := I)) (2 : ℝ≥0∞) μ := by
  classical
  have htop : MemLp (fTT_fun (D := D) (P := P) (W := W) (I := I)) (∞ : ℝ≥0∞) μ :=
    memLp_fTT_fun_top (D := D) (P := P) (W := W) (I := I) hH
  -- Haar measure on `𝕋` is finite.
  haveI : IsFiniteMeasure (μ := μ) := by
    -- `μ univ = 1`.
    infer_instance
  exact MeasureTheory.MemLp.mono_exponent htop (by simp)

noncomputable def fTT (hH : 0 < D.H) : SSU.Torus.L2 :=
  (memLp_fTT_fun_two (D := D) (P := P) (W := W) (I := I) hH).toLp
    (fTT_fun (D := D) (P := P) (W := W) (I := I))

theorem fTT_coeFn_eq (hH : 0 < D.H) :
    (fun x : UC => (fTT (D := D) (P := P) (W := W) (I := I) hH) x)
      =ᵐ[μ]
    (fTT_fun (D := D) (P := P) (W := W) (I := I)) := by
  classical
  simpa [fTT] using
    (memLp_fTT_fun_two (D := D) (P := P) (W := W) (I := I) hH).coeFn_toLp
      (f := fTT_fun (D := D) (P := P) (W := W) (I := I))

/-!
## Torus packet Gram = arc integral (rank-one TT* input)
-/

theorem inner_packetOpUnnormalized_eq_arcIntegral_rankOne
    (hH : 0 < D.H) (i j : ℤ) :
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ∫ z : UC,
      (Arc.arcAtBand D.X D.H).indicator
        (fun x =>
          (((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) *
            (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x))
        z ∂μ := by
  classical
  -- Start from the deterministic Gram expansion for multiplier packets.
  have hGram :=
    (D.toMultiplierModel).inner_packetOpUnnormalized_eq_integral (i := i) (j := j)
      (f := fTT (D := D) (P := P) (W := W) (I := I) hH)
      (g := fTT (D := D) (P := P) (W := W) (I := I) hH)
  -- Replace the `L²` representative by the explicit `fTT_fun` a.e.
  have hEq :
      (fun x : UC =>
          (star (D.ψ i x) * D.ψ j x) *
            (star ((fTT (D := D) (P := P) (W := W) (I := I) hH) x) *
              (fTT (D := D) (P := P) (W := W) (I := I) hH) x))
        =ᵐ[μ]
      (fun x : UC =>
          (star (D.ψ i x) * D.ψ j x) *
            (star (fTT_fun (D := D) (P := P) (W := W) (I := I) x) *
              fTT_fun (D := D) (P := P) (W := W) (I := I) x)) := by
    filter_upwards [fTT_coeFn_eq (D := D) (P := P) (W := W) (I := I) hH] with x hx
    simp [hx]
  have hint :
      (∫ x : UC,
          (star (D.ψ i x) * D.ψ j x) *
            (star ((fTT (D := D) (P := P) (W := W) (I := I) hH) x) *
              (fTT (D := D) (P := P) (W := W) (I := I) hH) x) ∂μ)
        =
      ∫ x : UC,
        (star (D.ψ i x) * D.ψ j x) *
          (star (fTT_fun (D := D) (P := P) (W := W) (I := I) x) *
            fTT_fun (D := D) (P := P) (W := W) (I := I) x) ∂μ := by
    exact integral_congr_ae hEq
  -- Now simplify `star fTT_fun * fTT_fun` into the arc indicator form.
  have hpoint :
      (fun x : UC =>
          (star (D.ψ i x) * D.ψ j x) *
            (star (fTT_fun (D := D) (P := P) (W := W) (I := I) x) *
              fTT_fun (D := D) (P := P) (W := W) (I := I) x))
        =
      (fun x : UC =>
        (Arc.arcAtBand D.X D.H).indicator
          (fun x =>
            (((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) *
              (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x))
          x) := by
    funext x
    by_cases hx : x ∈ Arc.arcAtBand D.X D.H
    · -- On-arc: compute directly.
      have hK0 : 0 ≤ Khat.KhatTorus D.X D.H x := KhatTorus_nonneg (D := D) (hH := hH) x
      have hsqrt_mul :
          ((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ) *
              ((Real.sqrt (Khat.KhatTorus D.X D.H x) : ℝ) : ℂ)
            =
          ((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) := by
        -- `sqrt r * sqrt r = r` for `0 ≤ r`.
        have : Real.sqrt (Khat.KhatTorus D.X D.H x) * Real.sqrt (Khat.KhatTorus D.X D.H x)
              = Khat.KhatTorus D.X D.H x := by
          simpa [pow_two] using (Real.sq_sqrt hK0)
        -- Cast to `ℂ`.
        simpa [Complex.ofReal_mul] using congrArg (fun t : ℝ => (t : ℂ)) this
      -- Avoid `simp`-cancellation lemmas (`mul_eq_mul_left_iff`) by rewriting each side first.
      set r : ℝ := Khat.KhatTorus D.X D.H x
      set a : ℂ := ((Real.sqrt r : ℝ) : ℂ)
      set s : ℂ := I.signalTorusByProd P W x
      have hfTT : fTT_fun (D := D) (P := P) (W := W) (I := I) x = a * s := by
        simp [fTT_fun, RankOne.arc, hx, a, s, r]
      have hRHS :
          (Arc.arcAtBand D.X D.H).indicator
              (fun x =>
                (((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) *
                  (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x))
              x
            =
          (((r : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) * s * star s := by
        -- Only use `hx` to evaluate the indicator; do not unfold the arc set.
        simp [Set.indicator, hx, r, s, mul_assoc, mul_left_comm, mul_comm]
      -- Now compute the LHS from `hfTT` and simplify algebraically.
      -- (`ℂ` is commutative, so we finish with `ring_nf` after rewriting the sqrt product.)
      have hstar_a : star a = a := by simp [a]
      -- Switch to the rewritten RHS.
      rw [hRHS]
      -- Replace `a*a` by `r` in a controlled way.
      have haa : a * a = ((r : ℝ) : ℂ) := by
        simpa [a, r] using hsqrt_mul
      have hstar_as : star (a * s) = star s * a := by
        -- `star (a*s) = star s * star a = star s * a`.
        simpa [star_mul, hstar_a, mul_assoc] using (rfl : star (a * s) = star (a * s))
      -- Now finish by commutative-ring normalization.
      -- (Everything lives in `ℂ`, so `ring_nf` is safe and avoids `mul_eq_mul_left_iff`.)
      -- The target is `(↑r * star ψi * ψj) * s * star s`.
      -- We also use commutativity to swap `star s * s` into `s * star s`.
      calc
        (star (D.ψ i x) * D.ψ j x) *
            (star (fTT_fun (D := D) (P := P) (W := W) (I := I) x) *
              fTT_fun (D := D) (P := P) (W := W) (I := I) x)
            =
          (star (D.ψ i x) * D.ψ j x) * ((star s * a) * (a * s)) := by
            -- Rewrite `fTT_fun x` and expand the `star`.
            -- (Do not use `simp` on the whole goal; keep the multiplication order explicit.)
            simp [hfTT, hstar_as, mul_assoc]
        _ = (star (D.ψ i x) * D.ψ j x) * (((r : ℝ) : ℂ) * (s * star s)) := by
            -- Normalize the middle product and rewrite `a*a`.
            -- `ring_nf` turns `((star s * a) * (a * s))` into `(a*a) * (s*star s)`.
            -- Then `haa` replaces `a*a` by `r`.
            ring_nf
            -- Rewrite `a^2` into `a*a`, then `rw [haa]`, then normalize.
            simp [pow_two] at *
            rw [haa]
            ring_nf
        _ = (((r : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) * s * star s := by
            ring_nf
    · -- Off-arc: everything is zero by the indicator.
      simp [fTT_fun, RankOne.arc, hx]
  -- Assemble.
  -- `inner_packetOpUnnormalized_eq_integral` already gives the integral form, so rewrite it.
  calc
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        =
      ∫ x : UC, (star (D.ψ i x) * (D.ψ j x)) *
          (star ((fTT (D := D) (P := P) (W := W) (I := I) hH) x) *
            (fTT (D := D) (P := P) (W := W) (I := I) hH) x) ∂μ := by
            simpa [TorusDyadicShell.MultiplierModel.packetOpUnnormalized] using hGram
    _ =
      ∫ x : UC, (star (D.ψ i x) * (D.ψ j x)) *
          (star (fTT_fun (D := D) (P := P) (W := W) (I := I) x) *
            fTT_fun (D := D) (P := P) (W := W) (I := I) x) ∂μ := hint
    _ =
      ∫ z : UC,
        (Arc.arcAtBand D.X D.H).indicator
          (fun x =>
            (((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) *
              (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x))
          z ∂μ := by
            -- Push the pointwise identity through the integral.
            simpa using congrArg (fun F : UC → ℂ => ∫ z : UC, F z ∂μ) hpoint

  -- Drop the explicit `∂μ` on the RHS (notation only).
  -- (We keep it explicit above to make the `congrArg` step definitional.)


/-!
## Arc integral = Toeplitz form (rank-one), and final combined statement
-/

theorem arcIntegral_eq_toeplitzFormTeXC_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    (∫ z : UC,
        (Arc.arcAtBand D.X D.H).indicator
          (fun x =>
            (((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) *
              (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x))
          z ∂μ)
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
  -- Both sides equal the same TT* band-model Gram entry (proved earlier).
  have hToep :
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      ((1 / D.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
          (T := P.box)
          (F := fun p => I.F (P := P) (W := W) p) := by
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof.inner_eq_toeplitzFormTeXC_rankOne
        (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (i := i) (j := j))
  have hArc :
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      (∫ z : UC,
        (Arc.arcAtBand D.X D.H).indicator
          (fun x =>
            (((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) *
              (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x))
          z) := by
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTTStarArcProof.inner_eq_arcIntegral_rankOne
        (D := D) (P := P) (W := W) (I := I) (hX := hX) (hH := hH) (hsmall := hsmall) (i := i) (j := j))
  -- Transitivity.
  -- Rewrite the `volume`-based integral in `hArc` into `∂μ`. (For `AddCircle 1`, `volume = μ`.)
  have hvol : (volume : Measure UC) = μ := by
    -- `volume = ofReal 1 • haarAddCircle = haarAddCircle`.
    simp [SSU.Torus.μ, SSU.Torus.UC, AddCircle.volume_eq_smul_haarAddCircle]
  have hArcμ :
      inner ℂ
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX i
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
          (SSU.Instances.FejerBankedTypeIIToeplitzRealTTStar.Model.packetOp
            (D := D) (X := D.X) (H := D.H) hH hX j
            (SSU.Instances.FejerBankedTypeIIToeplitzRankOneReal.RankOne.S (D := D) (I := I) (P := P) (W := W) D.X D.H))
        =
      (∫ z : UC,
        (Arc.arcAtBand D.X D.H).indicator
          (fun x =>
            (((Khat.KhatTorus D.X D.H x : ℝ) : ℂ) * star (D.ψ i x) * (D.ψ j x)) *
              (I.signalTorusByProd P W x) * star (I.signalTorusByProd P W x))
          z ∂μ) := by
    -- Change the measure on the RHS.
    simpa [MeasureTheory.integral, hvol] using hArc
  simpa [hArcμ] using hToep

theorem inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
  -- Inner = arc integral by direct Gram expansion on torus, then use the already-proved arc⇒Toeplitz step.
  have hArc :=
    inner_packetOpUnnormalized_eq_arcIntegral_rankOne (D := D) (P := P) (W := W) (I := I) (hH := hH) i j
  have hArcToToep :=
    arcIntegral_eq_toeplitzFormTeXC_rankOne (D := D) (P := P) (W := W) (I := I)
      (hX := hX) (hH := hH) (hsmall := hsmall) i j
  simpa [hArc] using hArcToToep

/-- `J`-indexed wrapper of `inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne`. -/
theorem inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne_onJ
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i : ℤ) (_hi : i ∈ D.J) (j : ℤ) (_hj : j ∈ D.J) :
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
  simpa using
    inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne
      (D := D) (P := P) (W := W) (I := I)
      (hX := hX) (hH := hH) (hsmall := hsmall) i j

/--
Weighted-band-integral form of the rank-one TT* identity (torus packet operators).

This rewrites the Toeplitz quadratic form via the deterministic Toeplitzization lemma in
`FejerBankedTypeIIToeplitzTorusRankOneTTStar`.
-/
theorem inner_packetOpUnnormalized_eq_weightedIntegral_rankOne
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := D) D.X D.H i j ξ) *
            (I.signalRealByProd P W D.X ξ) *
              star (I.signalRealByProd P W D.X ξ)) := by
  have hToep :=
    inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne
      (D := D) (P := P) (W := W) (I := I)
      (hX := hX) (hH := hH) (hsmall := hsmall) i j
  have hDet :
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := D) D.X D.H i j ξ) *
            (I.signalRealByProd P W D.X ξ) *
              star (I.signalRealByProd P W D.X ξ))
        =
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := P.box)
        (F := fun p => I.F (P := P) (W := W) p) := by
    have hX0 : (D.X : ℝ) ≠ 0 := ne_of_gt hX
    simpa using
      (SSU.Instances.FejerBankedTypeIIToeplitzTorusRankOneTTStar.RankOne.bandIntegral_eq_toeplitzFormTeXC_rankOne
        (D := D) (P := P) (W := W) (I := I) (hH := hH) (hX := hX0) (i := i) (j := j))
  calc
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        =
      ((1 / D.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
          (T := P.box)
          (F := fun p => I.F (P := P) (W := W) p) := hToep
    _ =
      ((1 / D.X : ℝ) : ℂ) *
        (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := D) D.X D.H i j ξ) *
              (I.signalRealByProd P W D.X ξ) *
                star (I.signalRealByProd P W D.X ξ)) := by
      rw [← hDet]

/-- `J`-indexed wrapper of `inner_packetOpUnnormalized_eq_weightedIntegral_rankOne`. -/
theorem inner_packetOpUnnormalized_eq_weightedIntegral_rankOne_onJ
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i : ℤ) (_hi : i ∈ D.J) (j : ℤ) (_hj : j ∈ D.J) :
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := D) D.X D.H i j ξ) *
            (I.signalRealByProd P W D.X ξ) *
              star (I.signalRealByProd P W D.X ξ)) := by
  simpa using
    inner_packetOpUnnormalized_eq_weightedIntegral_rankOne
      (D := D) (P := P) (W := W) (I := I)
      (hX := hX) (hH := hH) (hsmall := hsmall) i j

/-!
## Box-data rephrasing (rank-one)

For the rank-one input, the coefficient array is independent of `(f,i,j)`. We record a
box-data variant that rewrites the product sum in terms of `BGTypeIIArray.Data.prodSumRealByProd`.
-/

theorem inner_packetOpUnnormalized_eq_weightedIntegral_rankOne_boxData
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    let Dtype :
        SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2 :=
      I.boxData (H0 := SSU.Torus.L2) (P := P) hU W
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := D) D.X D.H i j ξ) *
            (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j) *
              star (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j)) := by
  classical
  -- Start from the rank-one weighted-integral identity.
  have hbase :=
    inner_packetOpUnnormalized_eq_weightedIntegral_rankOne
      (D := D) (P := P) (W := W) (I := I)
      (hX := hX) (hH := hH) (hsmall := hsmall) i j
  -- Rewrite the product sum using the `boxData` coefficients.
  let Dtype :
      SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2 :=
    I.boxData (H0 := SSU.Torus.L2) (P := P) hU W
  have htube : Dtype.tube = P.box :=
    I.boxData_tube_eq_box (H0 := SSU.Torus.L2) (P := P) (hU := hU) (W := W)
  have hA :
      ∀ k : ℤ,
        Dtype.A (0 : SSU.Torus.L2) i j k = I.A P W k := by
    intro k
    simpa using
      (I.boxData_A_eq_A (H0 := SSU.Torus.L2) (P := P) (hU := hU) (W := W)
        (f := (0 : SSU.Torus.L2)) (i := i) (j := j) (k := k))
  have hsum :
      ∀ ξ : ℝ,
        I.signalRealByProd P W D.X ξ =
          Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j := by
    intro ξ
    -- Expand both sums and rewrite `tube`/`A`.
    simp [SSU.Engines.BGTypeIIArray.Data.prodSumRealByProd,
      SSU.Engines.BGTypeIIRankOne.Input.signalRealByProd, htube, hA]
  -- Replace the integrand using `hsum`.
  have hrew :
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := D) D.X D.H i j ξ) *
            (I.signalRealByProd P W D.X ξ) *
              star (I.signalRealByProd P W D.X ξ))
        =
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := D) D.X D.H i j ξ) *
            (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j) *
              star (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j)) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine ae_of_all _ (fun ξ => ?_)
    simp [hsum ξ]
  -- Finish.
  calc
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        =
      ((1 / D.X : ℝ) : ℂ) *
        (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := D) D.X D.H i j ξ) *
              (I.signalRealByProd P W D.X ξ) *
                star (I.signalRealByProd P W D.X ξ)) := hbase
    _ =
      ((1 / D.X : ℝ) : ℂ) *
        (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := D) D.X D.H i j ξ) *
              (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j) *
                star (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j)) := by
      rw [hrew]

theorem inner_packetOpUnnormalized_eq_weightedIntegral_rankOne_boxData_onJ
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i : ℤ) (_hi : i ∈ D.J) (j : ℤ) (_hj : j ∈ D.J) :
    let Dtype :
        SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2 :=
      I.boxData (H0 := SSU.Torus.L2) (P := P) hU W
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
          (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
              (D := D) D.X D.H i j ξ) *
            (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j) *
              star (Dtype.prodSumRealByProd D.X ξ (0 : SSU.Torus.L2) i j)) := by
  simpa using
    inner_packetOpUnnormalized_eq_weightedIntegral_rankOne_boxData
      (D := D) (P := P) (W := W) (I := I)
      (hU := hU) (hX := hX) (hH := hH) (hsmall := hsmall) i j

theorem inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne_boxData
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i j : ℤ) :
    let Dtype :
        SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2 :=
      I.boxData (H0 := SSU.Torus.L2) (P := P) hU W
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := Dtype.tube)
        (F := Dtype.F (0 : SSU.Torus.L2) i j) := by
  classical
  -- Start from the weighted-integral identity and rewrite the integral using the box-data Toeplitzization.
  have hbase :=
    inner_packetOpUnnormalized_eq_weightedIntegral_rankOne
      (D := D) (P := P) (W := W) (I := I)
      (hX := hX) (hH := hH) (hsmall := hsmall) i j
  have hX0 : (D.X : ℝ) ≠ 0 := ne_of_gt hX
  -- Deterministic Toeplitzization with `boxData`.
  have hdet :=
    (SSU.Instances.FejerBankedTypeIIToeplitzTorusRankOneTTStar.RankOne.bandIntegral_eq_toeplitzFormTeXC_rankOne_boxData
      (D := D) (P := P) (W := W) (I := I)
      (hU := hU) (hH := hH) (hX := hX0) i j)
  -- Finish by rewriting the integral.
  calc
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        =
      ((1 / D.X : ℝ) : ℂ) *
        (∫ ξ in SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.band D.H,
            (SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.wLean
                (D := D) D.X D.H i j ξ) *
              (I.signalRealByProd P W D.X ξ) *
                star (I.signalRealByProd P W D.X ξ)) := hbase
    _ =
      ((1 / D.X : ℝ) : ℂ) *
        SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
          (K := fun t =>
            SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
          (T := (I.boxData (H0 := SSU.Torus.L2) (P := P) hU W).tube)
          (F := (I.boxData (H0 := SSU.Torus.L2) (P := P) hU W).F (0 : SSU.Torus.L2) i j) := by
      -- Apply the deterministic box-data Toeplitzization.
      rw [hdet]

theorem inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne_boxData_onJ
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ))
    (i : ℤ) (_hi : i ∈ D.J) (j : ℤ) (_hj : j ∈ D.J) :
    let Dtype :
        SSU.Engines.BGTypeIIArray.Data SSU.Torus.L2 :=
      I.boxData (H0 := SSU.Torus.L2) (P := P) hU W
    inner ℂ (((D.toMultiplierModel).packetOpUnnormalized i) (fTT (D := D) (P := P) (W := W) (I := I) hH))
        (((D.toMultiplierModel).packetOpUnnormalized j) (fTT (D := D) (P := P) (W := W) (I := I) hH))
      =
    ((1 / D.X : ℝ) : ℂ) *
      SSU.Engines.TypeII.ProductToeplitz.toeplitzFormTeXC
        (K := fun t =>
          SSU.Instances.FejerBankedTypeIIToeplitzKernel.Weight.KLean (D := D) D.X D.H i j t)
        (T := Dtype.tube)
        (F := Dtype.F (0 : SSU.Torus.L2) i j) := by
  simpa using
    inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne_boxData
      (D := D) (P := P) (W := W) (I := I)
      (hU := hU) (hX := hX) (hH := hH) (hsmall := hsmall) i j

/-!
## Fixed-signal TT* hypotheses (rank-one, box-data)

This packages the proved rank-one TT* identity into the fixed-signal hypothesis interfaces. The
weighted-band form is taken as the primitive production extraction endpoint; the Toeplitz-form
interface is then obtained by the deterministic ξ-band → Toeplitz conversion.
-/

noncomputable def ttStarBandHypothesisFor_rankOne_boxData
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ)) :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.HypothesisFor (κ := κ) where
  Dpacket := D
  Dtype := I.boxData (H0 := SSU.Torus.L2) (P := P) hU W
  f := fTT (D := D) (P := P) (W := W) (I := I) hH
  hH := hH
  hX := ne_of_gt hX
  inner_eq_weightedIntegral := by
    intro i hi j hj
    simpa using
      inner_packetOpUnnormalized_eq_weightedIntegral_rankOne_boxData_onJ
        (D := D) (P := P) (W := W) (I := I)
        (hU := hU) (hX := hX) (hH := hH) (hsmall := hsmall)
        (i := i) (j := j) hi hj

noncomputable def ttStarToeplitzHypothesisFor_rankOne_boxData
    (hU : 2 * P.N ≤ P.U)
    (hX : 0 < D.X) (hH : 0 < D.H) (hsmall : (1 / D.H) / D.X < (1 / 2 : ℝ)) :
    SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.HypothesisFor (κ := κ) := by
  let hBand :=
    ttStarBandHypothesisFor_rankOne_boxData
      (D := D) (P := P) (W := W) (I := I)
      (hU := hU) (hX := hX) (hH := hH) (hsmall := hsmall)
  exact
    { Dpacket := hBand.Dpacket
      Dtype := hBand.Dtype
      f := hBand.f
      hH := hBand.hH
      hX := hBand.hX
      inner_eq_toeplitzFormTeXC := by
        intro i hi j hj
        simpa using hBand.inner_eq_toeplitzFormTeXC (i := i) hi (j := j) hj }

end RankOne

end

end FejerBankedTypeIIToeplitzTorusPacketsRankOne
end Instances
end SSU
