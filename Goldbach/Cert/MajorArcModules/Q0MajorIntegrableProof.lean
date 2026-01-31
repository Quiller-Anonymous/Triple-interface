import Goldbach.Cert.MajorArcModules.Q0MajorRoute
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Goldbach.Cert.MajorArcModules.BetaInterval
import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
β-integrability for the turnkey `Q0` major-arc route.

This is intended to be “easy plumbing”: show that the β-integrand

`β ↦ kernelPolyC(β) * innerMajorQ0(β)`

is interval integrable on `[-1/2, 1/2]` (for fixed `X,N,Δ`).
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof

open scoped Interval

open Set Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.Q0MajorRoute
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral
open Goldbach.Cert.MajorArcStep12ShiftedExpSums
open Goldbach.Cert.MajorArcStep17MajorMinorSplit
open Goldbach.Cert.MajorArcStep7FourierOrthogonality
open Goldbach.Cert.MajorArcStep24IntegralExtraction

open Goldbach.Cert.MajorArcModules.BetaInterval

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)))

private lemma continuous_expSum (X N : ℕ) : Continuous (fun γ : UC => expSum X N γ) := by
  classical
  unfold Goldbach.Cert.MajorArcStep12ShiftedExpSums.expSum
  simpa using
    (continuous_finset_sum (s N) (fun n _hn =>
      (continuous_const.mul ((fourier (T := (1 : ℝ)) (n : ℤ)).continuous))))

private lemma expSum_bound {X N : ℕ} (hN2 : 2 ≤ N) (γ : UC) :
    ‖expSum X N γ‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
  classical
  -- Triangle inequality for the finite sum.
  have htri :
      ‖expSum X N γ‖ ≤
        ∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := by
    simpa [Goldbach.Cert.MajorArcStep12ShiftedExpSums.expSum] using
      (norm_sum_le (s := s N)
        (f := fun n =>
          aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)))

  have hlog0 : 0 ≤ Real.log (N : ℝ) := by
    have h1N : (1 : ℝ) < (N : ℝ) := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) this
    exact (Real.log_pos h1N).le

  have hterm :
      ∀ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ ≤ Real.log (N : ℝ) := by
    intro n hn
    have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) this

    have hfour : ‖(fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ = 1 := by
      simp [fourier_apply]

    have haTerm : ‖aTerm X n‖ ≤ Real.log (N : ℝ) := by
      -- `aTerm X n` is the complex cast of `wX X n * Λ n`.
      unfold Goldbach.Cert.MajorArcStep10RLSmoothIntegral.aTerm
      have hw : |Goldbach.BG_Bank.wX X n| ≤ 1 := Goldbach.BG_Bank.abs_wX_le_one X n
      have hΛ : |Goldbach.BG_Bank.Λ n| ≤ Real.log (N : ℝ) := by
        by_cases hprime : Nat.Prime n
        · have hn_le' : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn_le
          have hlog_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
            Real.log_le_log (by simpa using hnpos) hn_le'
          have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := (Real.log_pos (by
            have : (1 : ℝ) < (n : ℝ) := by
              have : (2 : ℝ) ≤ (n : ℝ) := by
                have : 2 ≤ n := (Finset.mem_Icc.mp hn).1
                exact_mod_cast this
              exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) this
            exact this)).le
          simpa [Goldbach.BG_Bank.Λ, hprime, abs_of_nonneg hlog_nonneg] using hlog_le
        · -- not prime: `Λ n = 0`
          simpa [Goldbach.BG_Bank.Λ, hprime, hlog0]
      have hmul : |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| ≤ |Goldbach.BG_Bank.Λ n| := by
        have h0 : 0 ≤ |Goldbach.BG_Bank.Λ n| := abs_nonneg _
        calc
          |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n|
              = |Goldbach.BG_Bank.wX X n| * |Goldbach.BG_Bank.Λ n| := by
                  simp [abs_mul]
          _ ≤ 1 * |Goldbach.BG_Bank.Λ n| := by
                  exact mul_le_mul_of_nonneg_right hw h0
          _ = |Goldbach.BG_Bank.Λ n| := by simp
      -- Convert the `ℂ` norm into an `ℝ` absolute value, then use `|wX*Λ| ≤ |Λ| ≤ log N`.
      have hnorm : ‖((Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n : ℝ) : ℂ)‖
          = |Goldbach.BG_Bank.wX X n * Goldbach.BG_Bank.Λ n| := by
        simp [RCLike.norm_ofReal]
      -- Finish.
      simpa [hnorm] using le_trans hmul hΛ

    calc
      ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖
          = ‖aTerm X n‖ * ‖(fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖ := by
              simpa using norm_mul (aTerm X n) (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)
      _ = ‖aTerm X n‖ := by simp [hfour]
      _ ≤ Real.log (N : ℝ) := haTerm

  have hsum :
      (∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
        ≤
      ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
    have hle :
        (∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
          ≤
        ∑ _n ∈ s N, Real.log (N : ℝ) :=
      Finset.sum_le_sum (fun n hn => hterm n hn)
    have hsubset : s N ⊆ Finset.range (N + 1) := by
      intro n hn
      have hn_le : n ≤ N := le_trans (Finset.mem_Icc.mp hn).2 (Nat.sub_le N 2)
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hn_le)
    have hcard : ((s N).card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      have : (s N).card ≤ (Finset.range (N + 1)).card := Finset.card_le_card hsubset
      simpa using (Nat.cast_le.2 this)
    calc
      (∑ n ∈ s N, ‖aTerm X n * (fourier (T := (1 : ℝ)) (n : ℤ) γ : ℂ)‖)
          ≤ (∑ _n ∈ s N, Real.log (N : ℝ)) := hle
      _ = ((s N).card : ℝ) * Real.log (N : ℝ) := by simp
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
            exact mul_le_mul_of_nonneg_right hcard hlog0

  exact le_trans htri hsum

private lemma innerMajorQ0_bound {X N : ℕ} (hN2 : 2 ≤ N) (Δ : ℝ) (β : ℝ) :
    ‖innerMajorQ0 X N Δ β‖ ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  classical
  have hconst :
      ∀ α ∈ (Ι (0 : ℝ) (1 : ℝ)),
        ‖(majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α‖
          ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
    intro α _hαI
    by_cases hα : α ∈ majorArcSetQ0 X Δ
    · have hsub :
        ‖expSum X N ((α : UC) - (β : UC))‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) :=
        expSum_bound (X := X) (N := N) hN2 ((α : UC) - (β : UC))
      have hadd :
        ‖expSum X N ((α : UC) + (β : UC))‖ ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) :=
        expSum_bound (X := X) (N := N) hN2 ((α : UC) + (β : UC))
      have hfour : ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖ = 1 := by
        simp [fourier_apply]
      have hmul :
          ‖innerIntegrand X N β α‖ ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
        have hR : 0 ≤ ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) := by
          have hN0 : 0 ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (N + 1))
          have hlog0 : 0 ≤ Real.log (N : ℝ) := by
            have h1N : (1 : ℝ) < (N : ℝ) := by
              have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
              exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) this
            exact (Real.log_pos h1N).le
          exact mul_nonneg hN0 hlog0
        have hprod1 :
            ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖
              ≤
            (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * ‖expSum X N ((α : UC) + (β : UC))‖ :=
          mul_le_mul_of_nonneg_right hsub (norm_nonneg _)
        have hprod2 :
            (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * ‖expSum X N ((α : UC) + (β : UC))‖
              ≤
            (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hadd hR
        have hprod :
            ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖
              ≤
            (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) :=
          le_trans hprod1 hprod2
        calc
          ‖innerIntegrand X N β α‖
              =
            ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)
                * expSum X N ((α : UC) - (β : UC))
                * expSum X N ((α : UC) + (β : UC))‖ := by
                  rfl
          _ =
            ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (α : UC) : ℂ)‖
              * ‖expSum X N ((α : UC) - (β : UC))‖
              * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp [mul_assoc]
          _ =
            1 * ‖expSum X N ((α : UC) - (β : UC))‖ * ‖expSum X N ((α : UC) + (β : UC))‖ := by
                simp [hfour]
          _ ≤ 1 * ((((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) * (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ))) := by
                simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1))
          _ = (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
                simp [pow_two, mul_assoc]
      simpa [Set.indicator_of_mem hα] using hmul
    · have : (0 : ℝ) ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := sq_nonneg _
      simpa [Set.indicator_of_notMem hα] using this

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ)) (C := (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2)
      (f := fun α : ℝ =>
        (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α)
      hconst
  simpa [Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.innerMajorQ0] using
    (by simpa using h)

private lemma aestronglyMeasurable_innerMajorQ0 (X N : ℕ) (Δ : ℝ) :
    AEStronglyMeasurable (fun β : ℝ => innerMajorQ0 X N Δ β)
      (volume.restrict (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))) := by
  -- Use `integral_prod_right'` on the product space `β × α`.
  let μβ : Measure ℝ := volume.restrict (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
  let να : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (1 : ℝ))
  let S : Set (ℝ × ℝ) := (fun p : ℝ × ℝ => p.2) ⁻¹' majorArcSetQ0 X Δ

  have hS : MeasurableSet S := by
    have hmaj : MeasurableSet (majorArcSetQ0 X Δ) := majorArcSetQ0_measurableSet (X := X) (Δ := Δ)
    simpa [S] using hmaj.preimage (measurable_snd : Measurable fun p : ℝ × ℝ => p.2)

  have hcontInner :
      Continuous (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) := by
    -- Build continuity from continuity of the coefficient map and of `expSum`.
    let coeUC : ℝ → UC := fun x => (x : UC)
    have hcoe : Continuous coeUC := continuous_coe_UC
    have hcoe1 : Continuous fun p : ℝ × ℝ => coeUC p.1 := hcoe.comp continuous_fst
    have hcoe2 : Continuous fun p : ℝ × ℝ => coeUC p.2 := hcoe.comp continuous_snd
    have hexp : Continuous (fun γ : UC => expSum X N γ) := continuous_expSum (X := X) (N := N)
    let subArg : ℝ × ℝ → UC := fun p => (coeUC p.2) - (coeUC p.1)
    let addArg : ℝ × ℝ → UC := fun p => (coeUC p.2) + (coeUC p.1)
    have hsub : Continuous subArg := hcoe2.sub hcoe1
    have hadd : Continuous addArg := hcoe2.add hcoe1
    have hEsub : Continuous fun p : ℝ × ℝ => expSum X N (subArg p) := hexp.comp hsub
    have hEadd : Continuous fun p : ℝ × ℝ => expSum X N (addArg p) := hexp.comp hadd
    have hfour : Continuous fun p : ℝ × ℝ => (fourier (T := (1 : ℝ)) (-(N : ℤ)) (coeUC p.2) : ℂ) :=
      ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous.comp hcoe2)
    -- `innerIntegrand` is a product of continuous functions.
    have : Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (coeUC p.2) : ℂ) * expSum X N (subArg p) * expSum X N (addArg p) := by
      -- `Continuous.mul` produces `a * (b * c)`; reassociate.
      simpa [mul_assoc] using (hfour.mul (hEsub.mul hEadd))
    simpa [Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand, UC, coeUC, subArg, addArg, sub_eq_add_neg, mul_assoc]
      using this

  have hf :
      AEStronglyMeasurable (S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2)) (μβ.prod να) :=
    (hcontInner.measurable.indicator hS).aestronglyMeasurable

  have hInt :
      AEStronglyMeasurable
        (fun β : ℝ => ∫ α, (S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) (β, α)) ∂να)
        μβ :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' (μ := μβ) (ν := να) hf

  have hEq :
      (fun β : ℝ => innerMajorQ0 X N Δ β)
        =
      (fun β : ℝ => ∫ α, (S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) (β, α)) ∂να) := by
    funext β
    have h01 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
    -- First rewrite the RHS indicator as the α-side indicator.
    have hpoint :
        (fun α : ℝ =>
            S.indicator (fun p : ℝ × ℝ => innerIntegrand X N p.1 p.2) (β, α))
          =
        fun α : ℝ => (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α := by
      funext α
      by_cases hα : α ∈ majorArcSetQ0 X Δ <;> simp [S, hα]
    -- Now rewrite `innerMajorQ0` to a set integral on `Ioc 0 1`, and compare with the RHS.
    have hL :
        innerMajorQ0 X N Δ β
          =
        ∫ α, (majorArcSetQ0 X Δ).indicator (fun α => innerIntegrand X N β α) α ∂να := by
      unfold Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.innerMajorQ0
      -- interval integral `0..1` is the set integral on `Ioc 0 1`
      simp [να, intervalIntegral.integral_of_le h01]
    -- conclude
    simpa [hpoint, hL]

  simpa [hEq] using hInt

theorem q0Major_integrable (Δ : ℝ) : Q0MajorIntegrable Δ := by
  refine ⟨?_⟩
  intro X N hX hN
  have hN2 : 2 ≤ N := by
    -- `N ∈ EvenIn X H` and `X ≥ X0 = 10^6`.
    have hNX : X ≤ N := by
      -- Unpack `N ∈ EvenIn X H` to obtain `N = X + k` for some `k`.
      have hIn : N ∈ IccShift X H := (Finset.mem_filter.mp hN).1
      rcases (Finset.mem_image.mp hIn) with ⟨k, hk, rfl⟩
      exact Nat.le_add_right X k
    have h2X0 : (2 : ℕ) ≤ X0 := by
      -- `X0 = 10^6`.
      simpa [Goldbach.BankParams.X0] using (by decide : (2 : ℕ) ≤ 10 ^ (6 : ℕ))
    exact le_trans h2X0 (le_trans hX hNX)

  have hab : (-( (2 : ℝ)⁻¹) : ℝ) ≤ ((2 : ℝ)⁻¹ : ℝ) := by nlinarith
  have hs : volume (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) < ⊤ := by
    simpa using (measure_Ioc_lt_top :
      volume (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) < ⊤)

  have hMeasK :
      AEStronglyMeasurable
        (fun β : ℝ => Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        (volume.restrict (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))) := by
    classical
    -- `kernelPolyC` is a finite Fourier polynomial, hence continuous in `β`.
    have hcont : Continuous fun β : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
      -- Use the Step 9 expansion and continuity of finite sums.
      dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC]
      have :
          Continuous fun β : ℝ =>
            ∑ k ∈ Goldbach.BG_Identity.S_BG,
              (Goldbach.BG_Identity.K_full k : ℂ) * fourier (T := (1 : ℝ)) k (β : UC) := by
        refine continuous_finset_sum _ ?_
        intro k _hk
        exact continuous_const.mul (((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC)
      simpa [Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly_eq] using this
    exact hcont.aestronglyMeasurable

  have hMeasI :
      AEStronglyMeasurable (fun β : ℝ => innerMajorQ0 X N Δ β)
        (volume.restrict (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))) :=
    aestronglyMeasurable_innerMajorQ0 (X := X) (N := N) (Δ := Δ)

  have hMeas :
      AEStronglyMeasurable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β)
        (volume.restrict (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))) :=
    hMeasK.mul hMeasI

  have hbound :
      ∀ᵐ (β : ℝ) ∂volume.restrict (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)),
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β‖
          ≤
        kernelCap * ((((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2) := by
    refine Filter.Eventually.of_forall ?_
    intro (β : ℝ)
    have hK : ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelCap :=
      norm_kernelPolyC_le_kernelCap (x := (β : UC))
    have hI : ‖innerMajorQ0 X N Δ β‖ ≤ ((((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2) :=
      innerMajorQ0_bound (X := X) (N := N) hN2 (Δ := Δ) (β := β)
    have h0 : 0 ≤ kernelCap := kernelCap_nonneg
    calc
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β‖
          =
        ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
          * ‖innerMajorQ0 X N Δ β‖ := by
            simpa using (norm_mul (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
              (innerMajorQ0 X N Δ β))
      _ ≤ kernelCap * ‖innerMajorQ0 X N Δ β‖ := by
            exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ kernelCap * ((((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hI h0

  have hInt :
      IntegrableOn
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β)
        (Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) volume :=
    IntegrableOn.of_bound (μ := volume)
      (s := Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))
      hs hMeas (kernelCap * ((((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2)) hbound

  -- Convert to `IntervalIntegrable`.
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := volume)
      (f := fun β : ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β)
      hab).2 hInt

end

end Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof

namespace Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof

open scoped Interval

open Complex MeasureTheory

open Goldbach.Cert.MajorArcModules.BetaInterval

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline

noncomputable section

/-!
Reusable measurability / `MemLp` facts for TT*/Parseval certificate work.

The TT* interfaces (`Q0MajorTailTTStar`) assume `MemLp (β ↦ innerMajorQ0 ...) 2` on
`Iβ = (-1/2, 1/2]`.  The proofs in this file already establish the needed measurability and a
uniform pointwise bound; we package them here as non-private lemmas.
-/

theorem aestronglyMeasurable_innerMajorQ0_Iβ (X N : ℕ) (Δ : ℝ) :
    AEStronglyMeasurable (fun β : ℝ => innerMajorQ0 X N Δ β) (volume.restrict Iβ) := by
  -- This is exactly the private lemma in this file; `Iβ` is the shared β-interval from
  -- `MajorArcModules/BetaInterval`.
  simpa [Iβ, aβ, bβ] using
    (aestronglyMeasurable_innerMajorQ0 (X := X) (N := N) (Δ := Δ) :
      AEStronglyMeasurable (fun β : ℝ => innerMajorQ0 X N Δ β)
        (volume.restrict (Set.Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ))))

theorem norm_innerMajorQ0_le (X N : ℕ) (Δ : ℝ) (β : ℝ) (hN2 : 2 ≤ N) :
    ‖innerMajorQ0 X N Δ β‖ ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
  -- This is the private lemma `innerMajorQ0_bound`.
  simpa using (innerMajorQ0_bound (X := X) (N := N) (Δ := Δ) (β := β) hN2)

theorem memLp_innerMajorQ0_Iβ (X N : ℕ) (Δ : ℝ) (hN2 : 2 ≤ N) :
    MemLp (fun β : ℝ => innerMajorQ0 X N Δ β) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ) := by
  classical
  have hmeas :
      AEStronglyMeasurable (fun β : ℝ => innerMajorQ0 X N Δ β) (volume.restrict Iβ) :=
    aestronglyMeasurable_innerMajorQ0_Iβ (X := X) (N := N) (Δ := Δ)
  have hbound :
      ∀ᵐ β : ℝ ∂volume.restrict Iβ,
        ‖innerMajorQ0 X N Δ β‖ ≤ (((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ)) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro β
    exact norm_innerMajorQ0_le (X := X) (N := N) (Δ := Δ) (β := β) hN2
  -- Bounded + AE-strongly measurable on a finite-measure space implies `MemLp`.
  classical
  -- Provide the instance explicitly to keep elaboration stable.
  letI : IsFiniteMeasure (volume.restrict Iβ) := by infer_instance
  exact MeasureTheory.MemLp.of_bound (μ := volume.restrict Iβ) (p := ENNReal.ofReal (2 : ℝ))
    hmeas _ hbound

private lemma two_le_of_mem_EvenIn {X N : ℕ} (hX0 : X0 ≤ X) (hN : N ∈ EvenIn X H) : 2 ≤ N := by
  classical
  have hIn : N ∈ Goldbach.Windows.IccShift X H := (Finset.mem_filter.mp hN).1
  rcases Finset.mem_image.mp hIn with ⟨k, _hk, rfl⟩
  have h2X0 : 2 ≤ X0 := by
    -- `X0 = 10^6`.
    simpa [Goldbach.BankParams.X0] using (by decide : 2 ≤ 10 ^ (6 : ℕ))
  have h2X : 2 ≤ X := le_trans h2X0 hX0
  exact le_trans h2X (Nat.le_add_right X k)

theorem memLp_innerMajorQ0_Iβ_of_mem_EvenIn {X N : ℕ} (Δ : ℝ) (hX0 : X0 ≤ X)
    (hN : N ∈ EvenIn X H) :
    MemLp (fun β : ℝ => innerMajorQ0 X N Δ β) (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ) := by
  have hN2 : 2 ≤ N := two_le_of_mem_EvenIn (X := X) (N := N) hX0 hN
  exact memLp_innerMajorQ0_Iβ (X := X) (N := N) (Δ := Δ) hN2

end

end Goldbach.Cert.MajorArcModules.Q0MajorIntegrableProof
