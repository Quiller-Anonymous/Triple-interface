import Goldbach.Cert.MajorArcModules.ExpSumTrivialBound
import Goldbach.Cert.MajorArcModules.Q0MajorSmallExtractionResource
import Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels
import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Goldbach.Cert.MajorArcStep25MinorArcBound
import Mathlib.MeasureTheory.Integral.Prod

/-!
Deterministic β-integrability resources for the ε₁ / interzone route.

This file supplies the `IntervalIntegrable` hypotheses in `β` needed by the dyadic-zone
decomposition (`zoneSet`) and by the `Q0` major/minor split for the minor-energy ledger.

No analytic number theory is used: we only prove measurability and a crude uniform bound on the
integrand on compact intervals.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource

open scoped BigOperators Interval

open Set Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.ExpSumTrivialBound
open Goldbach.Cert.MajorArcModules.Q0MajorSmallExtractionResource
open Goldbach.Cert.MajorArcModules.Q0MinorInterzoneDyadicLevels

open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcStep25MinorArcBound

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma two_le_of_mem_EvenIn {X N : ℕ} (hX0 : X0 ≤ X) (hN : N ∈ EvenIn X H) : 2 ≤ N := by
  classical
  rcases Finset.mem_filter.mp hN with ⟨hIn, _hEven⟩
  rcases Finset.mem_image.mp hIn with ⟨k, hk, rfl⟩
  have h2X0 : 2 ≤ X0 := by
    dsimp [X0]
    norm_num
  have h2X : 2 ≤ X := le_trans h2X0 hX0
  exact le_trans h2X (Nat.le_add_right _ _)

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_expSum (X N : ℕ) : Continuous (fun γ : UC => expSum X N γ) := by
  classical
  unfold Goldbach.Cert.MajorArcStep12ShiftedExpSums.expSum
  refine continuous_finset_sum (s N) ?_
  intro n _hn
  exact continuous_const.mul ((fourier (T := (1 : ℝ)) (n : ℤ)).continuous)

private lemma continuous_innerIntegrand_uncurry (X N : ℕ) :
    Continuous (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) := by
  have hfour :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.2 : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp
      (continuous_coe_UC.comp continuous_snd)
  have hsub :
      Continuous fun p : ℝ × ℝ => expSum X N ((p.2 : UC) - (p.1 : UC)) :=
    (continuous_expSum X N).comp
      ((continuous_coe_UC.comp continuous_snd).sub (continuous_coe_UC.comp continuous_fst))
  have hadd :
      Continuous fun p : ℝ × ℝ => expSum X N ((p.2 : UC) + (p.1 : UC)) :=
    (continuous_expSum X N).comp
      ((continuous_coe_UC.comp continuous_snd).add (continuous_coe_UC.comp continuous_fst))
  simpa [Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand, mul_assoc] using
    (hfour.mul (hsub.mul hadd))

private lemma stronglyMeasurable_indicator_integral
    (X N : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    StronglyMeasurable (fun β : ℝ =>
      ∫ α in (0 : ℝ)..(1 : ℝ),
        s.indicator (fun α : ℝ => innerIntegrand X N β α) α) := by
  classical
  -- Rewrite the interval integral as a set integral over `Ioc 0 1`.
  have hI :
      (fun β : ℝ =>
          ∫ α in (0 : ℝ)..(1 : ℝ),
            s.indicator (fun α : ℝ => innerIntegrand X N β α) α)
        =
      fun β : ℝ =>
        ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ),
          s.indicator (fun α : ℝ => innerIntegrand X N β α) α := by
    funext β
    simpa using
      (intervalIntegral.integral_of_le (μ := (volume : Measure ℝ))
        (f := fun α : ℝ => s.indicator (fun α : ℝ => innerIntegrand X N β α) α)
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num))

  -- Measurability of the `(β,α)`-uncurried indicator integrand.
  let S : Set (ℝ × ℝ) := (fun p : ℝ × ℝ => p.2) ⁻¹' s
  have hS : MeasurableSet S := by
    simpa [S] using hs.preimage (measurable_snd : Measurable fun p : ℝ × ℝ => p.2)
  have hinter :
      Measurable fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2 :=
    (continuous_innerIntegrand_uncurry (X := X) (N := N)).measurable
  have hmeas : Measurable (S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2)) :=
    hinter.indicator hS
  have hEq :
      (fun p : ℝ × ℝ => s.indicator (fun α : ℝ => innerIntegrand X N p.1 α) p.2)
        =
      fun p : ℝ × ℝ => S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) p := by
    funext p
    by_cases hp : p.2 ∈ s
    · simp [S, hp, Set.indicator_of_mem]
    · simp [S, hp, Set.indicator_of_notMem]
  have huncurry : StronglyMeasurable (fun p : ℝ × ℝ =>
      s.indicator (fun α : ℝ => innerIntegrand X N p.1 α) p.2) := by
    simpa [hEq] using hmeas.stronglyMeasurable

  -- Apply the general measurability lemma for parameter integrals on a product.
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ))
  have hSM :
      StronglyMeasurable (fun β : ℝ =>
        ∫ α, s.indicator (fun α : ℝ => innerIntegrand X N β α) α ∂ν) := by
    simpa [ν] using
      (MeasureTheory.StronglyMeasurable.integral_prod_right (E := ℂ) (ν := ν)
        (f := fun β α => s.indicator (fun α : ℝ => innerIntegrand X N β α) α)
        huncurry)
  have hSM' :
      StronglyMeasurable (fun β : ℝ =>
        ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ),
          s.indicator (fun α : ℝ => innerIntegrand X N β α) α) := by
    simpa [ν] using hSM
  simpa [hI] using hSM'

private lemma norm_innerIntegrand_le (X N : ℕ) (hN2 : 2 ≤ N) (β α : ℝ) :
    ‖innerIntegrand X N β α‖ ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  set C : ℝ := ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)
  have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 := by
    simp [fourier_apply]
  have h1 : ‖expSum X N ((α : UC) - (β : UC))‖ ≤ C := by
    simpa [C] using ExpSumTrivialBound.norm_expSum_le (X := X) (N := N) hN2 ((α : UC) - (β : UC))
  have h2 : ‖expSum X N ((α : UC) + (β : UC))‖ ≤ C := by
    simpa [C] using ExpSumTrivialBound.norm_expSum_le (X := X) (N := N) hN2 ((α : UC) + (β : UC))
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
        =
      ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
        * ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := hprod
    _ ≤ (1 : ℝ) * C * C := by
      have hfour_le : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ ≤ (1 : ℝ) := by
        simpa [hfour]
      have h12 : ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ ≤ C * C :=
        mul_le_mul h1 h2 (norm_nonneg _) hC0
      nlinarith [hfour_le, h12]
    _ = C ^ 2 := by ring
    _ = (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by simp [C]

private lemma norm_innerIndicatorIntegral_le (X N : ℕ) (hN2 : 2 ≤ N) {s : Set ℝ} (β : ℝ) :
    ‖∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α‖
      ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  set C : ℝ := (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2
  have houter :
      ∀ α ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖s.indicator (fun α : ℝ => innerIntegrand X N β α) α‖ ≤ C := by
    intro α _hα
    by_cases hαs : α ∈ s
    · simpa [Set.indicator_of_mem hαs, C] using norm_innerIntegrand_le (X := X) (N := N) hN2 (β := β) (α := α)
    · have : ‖(0 : ℂ)‖ ≤ C := by
        have : 0 ≤ C := by
          dsimp [C]
          simpa [pow_two] using (sq_nonneg (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)))
        simpa using this
      simpa [Set.indicator_of_notMem hαs] using this
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := C)
      (f := fun α : ℝ => s.indicator (fun α : ℝ => innerIntegrand X N β α) α)
      houter
  have habs : |((1 : ℝ) - (0 : ℝ))| = (1 : ℝ) := by norm_num
  simpa [habs, C] using h

/--
Generic β-integrability lemma for the interzone/zone-set and major/minor indicator integrands.

This is the deterministic input needed by the dyadic Gram-decay → lever-bundle → ledger-engine
bridge.
-/
theorem intervalIntegrable_beta_kernel_mul_innerIndicatorIntegral
    (X N : ℕ) (hN2 : 2 ≤ N) {s : Set ℝ} (hs : MeasurableSet s) :
    IntervalIntegrable
      (fun β : ℝ =>
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α))
      volume (0 : ℝ) (1 : ℝ) := by
  have hab : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
  have hMeas :
      AEStronglyMeasurable
        (fun β : ℝ =>
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α))
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ))) := by
    have hK : StronglyMeasurable (fun β : ℝ => kernelPolyC (β : UC)) := by
      classical
      have hcont : Continuous fun β : ℝ => kernelPolyC (β : UC) := by
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
    have hI : StronglyMeasurable (fun β : ℝ =>
        ∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α) :=
      stronglyMeasurable_indicator_integral (X := X) (N := N) hs
    exact (hK.mul hI).aestronglyMeasurable.restrict
  have hBound :
      ∀ᵐ (β : ℝ) ∂(volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) (1 : ℝ)),
        ‖kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α)‖
          ≤ kernelCap * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro β
    have hK : ‖kernelPolyC (β : UC)‖ ≤ kernelCap :=
      norm_kernelPolyC_le_kernelCap (x := (β : UC))
    have hI :
        ‖∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α‖
          ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 :=
      norm_innerIndicatorIntegral_le (X := X) (N := N) hN2 (s := s) (β := β)
    calc
      ‖kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α)‖
          =
        ‖kernelPolyC (β : UC)‖ *
          ‖∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α‖ := by
            simp [norm_mul]
      _ ≤ kernelCap * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
            exact mul_le_mul hK hI (norm_nonneg _) kernelCap_nonneg
  have hs' : (volume : Measure ℝ) (Set.Ioc (0 : ℝ) (1 : ℝ)) < ⊤ := by
    simpa using (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := (1 : ℝ)))
  have hInt :
      IntegrableOn
        (fun β : ℝ =>
          kernelPolyC (β : UC) *
            (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α))
        (Set.Ioc (0 : ℝ) (1 : ℝ)) volume :=
    IntegrableOn.of_bound (μ := (volume : Measure ℝ))
      (s := Set.Ioc (0 : ℝ) (1 : ℝ)) hs' hMeas
      (kernelCap * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2) hBound
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := (volume : Measure ℝ))
      (f := fun β : ℝ =>
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ), s.indicator (fun α : ℝ => innerIntegrand X N β α) α))
      hab).2 hInt

/-!
## Concrete `hInner/hOuter` instantiations used by the dyadic lever-bundle route
-/

theorem hInner
    {X N : ℕ} (hX : X0 ≤ X) (_hN : N ∈ EvenIn X H) :
    ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ) :=
  fun β => innerIntegrand_intervalIntegrable (X := X) (N := N) (β := β)

theorem hOuterMaj
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) (Δ : ℝ) :
    IntervalIntegrable
      (fun β : ℝ =>
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (majorArcSetQ0 X Δ).indicator (fun α : ℝ => innerIntegrand X N β α) α))
      volume (0 : ℝ) (1 : ℝ) := by
  have hN2 : 2 ≤ N := two_le_of_mem_EvenIn (X := X) (N := N) hX hN
  exact intervalIntegrable_beta_kernel_mul_innerIndicatorIntegral
    (X := X) (N := N) hN2 (s := majorArcSetQ0 X Δ) (majorArcSetQ0_measurableSet X Δ)

theorem hOuterMin
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) (Δ : ℝ) :
    IntervalIntegrable
      (fun β : ℝ =>
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (majorArcSetQ0 X Δ)ᶜ.indicator (fun α : ℝ => innerIntegrand X N β α) α))
      volume (0 : ℝ) (1 : ℝ) := by
  have hN2 : 2 ≤ N := two_le_of_mem_EvenIn (X := X) (N := N) hX hN
  exact intervalIntegrable_beta_kernel_mul_innerIndicatorIntegral
    (X := X) (N := N) hN2 (s := (majorArcSetQ0 X Δ)ᶜ) (majorArcSetQ0_measurableSet X Δ).compl

theorem hOuterZone
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) (Δ : ℝ) (j : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        kernelPolyC (β : UC) *
          (∫ α in (0 : ℝ)..(1 : ℝ),
            (zoneSet X Δ j).indicator (fun α : ℝ => innerIntegrand X N β α) α))
      volume (0 : ℝ) (1 : ℝ) := by
  have hN2 : 2 ≤ N := two_le_of_mem_EvenIn (X := X) (N := N) hX hN
  exact intervalIntegrable_beta_kernel_mul_innerIndicatorIntegral
    (X := X) (N := N) hN2 (s := zoneSet X Δ j) (measurableSet_zoneSet X Δ j)

end

end Goldbach.Cert.MajorArcModules.Q0MinorOuterIntegrableResource
