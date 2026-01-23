import Goldbach.Cert.MajorArcModules.Q0MajorSmallExtraction
import Goldbach.Cert.MajorArcModules.ExpSumTrivialBound
import Mathlib.MeasureTheory.Integral.Prod

/-!
β-integrability resource for ε₂-small extraction.

`Q0MajorSmallExtraction.corr_integral_major_Q0_small_eq_sum` requires, for each `(q,a)`, an
`IntervalIntegrable` hypothesis in `β` for the single-arc β-integrand. This file supplies a
deterministic proof of that hypothesis from:

- the trivial triangle-inequality bound `ExpSumTrivialBound.norm_expSum_le`, and
- elementary measurability facts about parameter-dependent integrals.

No analytic number theory is used.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorSmallOuterIntegrable

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.BetaInterval
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.ExpSumTrivialBound
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_expSum (X N : ℕ) : Continuous (fun γ : UC => expSum X N γ) := by
  classical
  unfold Goldbach.Cert.MajorArcStep12ShiftedExpSums.expSum
  refine continuous_finset_sum (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.s N) ?_
  intro n _hn
  exact continuous_const.mul ((fourier (T := (1 : ℝ)) (n : ℤ)).continuous)

private lemma continuous_innerIntegrand_uncurry (X N : ℕ) :
    Continuous (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) := by
  -- `innerIntegrand` is a product of continuous functions in `(β,α)`.
  have hfour :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.2 : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp (continuous_coe_UC.comp continuous_snd)
  have hsub :
      Continuous fun p : ℝ × ℝ => expSum X N ((p.2 : UC) - (p.1 : UC)) :=
    (continuous_expSum X N).comp ((continuous_coe_UC.comp continuous_snd).sub
      (continuous_coe_UC.comp continuous_fst))
  have hadd :
      Continuous fun p : ℝ × ℝ => expSum X N ((p.2 : UC) + (p.1 : UC)) :=
    (continuous_expSum X N).comp ((continuous_coe_UC.comp continuous_snd).add
      (continuous_coe_UC.comp continuous_fst))
  simpa [Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand, mul_assoc] using
    (hfour.mul (hsub.mul hadd))

private lemma measurable_uncurry_arcIndicator (X N : ℕ) (q a : ℕ) (Δ : ℝ) :
    Measurable fun p : ℝ × ℝ =>
      (arcSetTextbook X q a Δ).indicator (fun α : ℝ => innerIntegrand X N p.1 α) p.2 := by
  classical
  -- Package the α-side indicator as an indicator on the product via the `snd` preimage set.
  have hs : MeasurableSet (arcSetTextbook X q a Δ) :=
    measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ)
  let S : Set (ℝ × ℝ) := (fun p : ℝ × ℝ => p.2) ⁻¹' arcSetTextbook X q a Δ
  have hS : MeasurableSet S := by
    simpa [S] using hs.preimage (measurable_snd : Measurable fun p : ℝ × ℝ => p.2)
  have hinter :
      Measurable fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2 :=
    (continuous_innerIntegrand_uncurry (X := X) (N := N)).measurable
  have hmeas : Measurable (S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2)) :=
    hinter.indicator hS
  have hEq :
      (fun p : ℝ × ℝ =>
          (arcSetTextbook X q a Δ).indicator (fun α : ℝ => innerIntegrand X N p.1 α) p.2)
        =
      fun p : ℝ × ℝ =>
        S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) p := by
    funext p
    by_cases hp : p.2 ∈ arcSetTextbook X q a Δ
    · simp [S, hp, Set.indicator_of_mem]
    · simp [S, hp, Set.indicator_of_notMem]
  simpa [hEq] using hmeas

private lemma stronglyMeasurable_arcIntegral (X N : ℕ) (q a : ℕ) (Δ : ℝ) :
    StronglyMeasurable (fun β : ℝ =>
      ∫ α in (0 : ℝ)..(1 : ℝ),
        (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α) := by
  classical
  -- Rewrite the interval integral as a set integral over `Ioc 0 1`.
  have hI :
      (fun β : ℝ =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)
        =
      fun β : ℝ =>
        ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ),
          (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α := by
    funext β
    simpa using
      (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
        (f := fun α : ℝ =>
          (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num))
  -- Apply the general measurability lemma for parameter integrals on a product.
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ))
  have huncurry : StronglyMeasurable (fun p : ℝ × ℝ =>
      (arcSetTextbook X q a Δ).indicator (fun α : ℝ => innerIntegrand X N p.1 α) p.2) := by
    exact (measurable_uncurry_arcIndicator (X := X) (N := N) (q := q) (a := a) (Δ := Δ)).stronglyMeasurable
  have hSM :
      StronglyMeasurable (fun β : ℝ =>
        ∫ α, (arcSetTextbook X q a Δ).indicator (fun α : ℝ => innerIntegrand X N β α) α ∂ν) := by
    simpa [ν] using
      (MeasureTheory.StronglyMeasurable.integral_prod_right (E := ℂ) (ν := ν)
        (f := fun β α => (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)
        huncurry)
  -- Convert the restricted-measure integral back to set integral.
  have hSM' :
      StronglyMeasurable (fun β : ℝ =>
        ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ),
          (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α) := by
    simpa [ν] using hSM
  simpa [hI] using hSM'

private lemma norm_innerIntegrand_le (X N : ℕ) (hN2 : 2 ≤ N) (β α : ℝ) :
    ‖innerIntegrand X N β α‖ ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  set C : ℝ := ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)
  have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 := by
    simp [fourier_apply]
  have hfour_le : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ ≤ (1 : ℝ) := by
    simpa [hfour]
  have h1 : ‖expSum X N ((α : UC) - (β : UC))‖ ≤ C := by
    simpa [C] using norm_expSum_le (X := X) (N := N) hN2 ((α : UC) - (β : UC))
  have h2 : ‖expSum X N ((α : UC) + (β : UC))‖ ≤ C := by
    simpa [C] using norm_expSum_le (X := X) (N := N) hN2 ((α : UC) + (β : UC))
  have hC0 : 0 ≤ C := by
    have hlog0 : 0 ≤ Real.log (N : ℝ) := by
      have h1N : (1 : ℝ) < (N : ℝ) := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
      exact (Real.log_pos h1N).le
    have hN0 : 0 ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact mul_nonneg hN0 hlog0
  have hprod :
      ‖innerIntegrand X N β α‖ =
          ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
            * ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
    simp [Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand, norm_mul, mul_assoc]
  calc
    ‖innerIntegrand X N β α‖
        = ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
            * ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := hprod
    _ ≤ (1 : ℝ) * C * C := by
      have h01 : 0 ≤ (1 : ℝ) := by norm_num
      have hA : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
          * ‖expSum X N ((α : UC) - (β : UC))‖ ≤ (1 : ℝ) * C := by
        exact mul_le_mul hfour_le h1 (norm_nonneg (expSum X N ((α : UC) - (β : UC)))) h01
      have hB : (‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
          * ‖expSum X N ((α : UC) - (β : UC))‖) * ‖expSum X N ((α : UC) + (β : UC))‖
          ≤ ((1 : ℝ) * C) * C := by
        have hBC0 : 0 ≤ (1 : ℝ) * C := mul_nonneg h01 hC0
        exact mul_le_mul hA h2 (norm_nonneg (expSum X N ((α : UC) + (β : UC)))) hBC0
      simpa [mul_assoc] using hB
    _ = C ^ 2 := by
      simp [pow_two, mul_assoc, C]
    _ = (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
      simp [C]

private lemma norm_arcIntegral_le (X N : ℕ) (hN2 : 2 ≤ N) (q a : ℕ) (Δ : ℝ) (β : ℝ) :
    ‖∫ α in (0 : ℝ)..(1 : ℝ),
        (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖
      ≤
    (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  have houter :
      ∀ α ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖(arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖
          ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
    intro α _hα
    by_cases hαarc : α ∈ arcSetTextbook X q a Δ
    · simpa [Set.indicator_of_mem hαarc] using norm_innerIntegrand_le (X := X) (N := N) hN2 (β := β) (α := α)
    · have : ‖(0 : ℂ)‖ ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
        have : 0 ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by nlinarith
        simpa using this
      simpa [Set.indicator_of_notMem hαarc] using this
  -- Interval length is `1`.
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (C := (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2)
      (f := fun α : ℝ =>
        (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)
      houter
  have habs : |((1 : ℝ) - (0 : ℝ))| = (1 : ℝ) := by norm_num
  simpa [habs] using h

private lemma intervalIntegrable_betaArcIntegrand
    (X N : ℕ) (hN2 : 2 ≤ N) (q a : ℕ) (Δ : ℝ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
      (volume : Measure ℝ) aβ bβ := by
  -- Use `IntegrableOn.of_bound` with a deterministic constant bound.
  have hab : aβ ≤ bβ := BetaInterval.hle
  have hMeas :
      AEStronglyMeasurable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
        ((volume : Measure ℝ).restrict (Set.Ioc aβ bβ)) := by
    -- The β-integrand is strongly measurable on `ℝ`, hence AE-strongly measurable on the restriction.
    have hK : StronglyMeasurable (fun β : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)) := by
      classical
      -- `kernelPolyC` is a finite Fourier polynomial, hence continuous (and thus strongly measurable).
      have hcont : Continuous fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
        dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC]
        have :
            Continuous fun β : ℝ =>
              ∑ k ∈ Goldbach.BG_Identity.S_BG,
                (Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k (β : UC) := by
          refine continuous_finset_sum _ ?_
          intro k _hk
          exact continuous_const.mul (((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC)
        simpa [Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly_eq] using this
      exact hcont.stronglyMeasurable
    have hI :
        StronglyMeasurable (fun β : ℝ =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α) :=
      stronglyMeasurable_arcIntegral (X := X) (N := N) (q := q) (a := a) (Δ := Δ)
    have h := hK.mul hI
    exact (h.aestronglyMeasurable).restrict
  have hBound :
      ∀ᵐ (β : ℝ) ∂(volume : Measure ℝ).restrict (Set.Ioc aβ bβ),
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)‖
          ≤ kernelCap * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro (β : ℝ)
    have hK : ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelCap :=
      norm_kernelPolyC_le_kernelCap (x := (β : UC))
    have hI :
        ‖∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖
          ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 :=
      norm_arcIntegral_le (X := X) (N := N) hN2 (q := q) (a := a) (Δ := Δ) (β := β)
    calc
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)‖
          =
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ *
          ‖∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α‖ := by
            simp [norm_mul]
      _ ≤ kernelCap * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
            exact mul_le_mul hK hI (norm_nonneg _) kernelCap_nonneg
  have hs : (volume : Measure ℝ) (Set.Ioc aβ bβ) < ⊤ := by
    simpa using (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := aβ) (b := bβ))
  have hInt :
      IntegrableOn
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
        (Set.Ioc aβ bβ) (volume : Measure ℝ) :=
    IntegrableOn.of_bound (μ := (volume : Measure ℝ))
      (s := Set.Ioc aβ bβ) hs hMeas
      (kernelCap * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2) hBound
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := (volume : Measure ℝ))
      (f := fun β : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
      hab).2 hInt

/--
The `hOuter` hypothesis required by `Q0MajorSmallExtraction.corr_integral_major_Q0_small_eq_sum`.

This is a deterministic integrability lemma in `β` for each single arc `(q,a)`.
-/
theorem intervalIntegrable_betaSmall_indicator_singleArc
    (X N : ℕ) (Δ : ℝ) (hN2 : 2 ≤ N) :
    ∀ q ∈ Finset.Icc (1 : ℕ) (Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ),
      ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α)) β)
          volume aβ bβ := by
  intro q hq a ha
  have hbase :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ),
              (arcSetTextbook X q a Δ).indicator (fun α => innerIntegrand X N β α) α))
        volume aβ bβ :=
    intervalIntegrable_betaArcIntegrand (X := X) (N := N) hN2 (q := q) (a := a) (Δ := Δ)
  -- Add the β-small indicator.
  exact
    intervalIntegrable_indicator_of_intervalIntegrable
      (a := aβ) (b := bβ) (s := betaSmallSet) measurableSet_betaSmallSet hbase

end

end Goldbach.Cert.MajorArcModules.Q0MajorSmallOuterIntegrable
