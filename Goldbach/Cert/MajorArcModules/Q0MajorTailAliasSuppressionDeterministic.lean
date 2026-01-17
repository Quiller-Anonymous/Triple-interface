import Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionSpec
import Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeightBounds
import Goldbach.Cert.MajorArcStep16CircleToInterval
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Star.BigOperators

/-!
Deterministic discharge of `Q0AliasSuppressedHybridLargeSieve` under the `wTextbook` design.

For `X ≥ X0`, the smooth major-arc weight satisfies `0 ≤ W ≤ 1` pointwise, hence its constant mode
`c = ∫_0^1 W` lies in `[0,1]` and the balanced weight `W∘ = W - c` satisfies `|W∘| ≤ 1`.

Combining this with Parseval for the Fourier polynomial `trigSumShift` yields the interface
`Q0AliasSuppressedHybridLargeSieve (1 / X0)`.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionDeterministic

open scoped BigOperators Interval
open scoped ComplexConjugate
open scoped InnerProductSpace

open Complex MeasureTheory AddCircle

open Goldbach.BankParams

open Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionSpec
open Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeight
open Goldbach.Cert.MajorArcModules.Q0MajorTailSmoothWeightBounds
open Goldbach.Cert.MajorArcStep16CircleToInterval

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-!
Local aliases for the spec interface.

We avoid opening `Q0MajorTailAliasSuppressionSpec` directly to keep `UC` unambiguous.
-/
-- We keep `UC` and `μ` from the spec namespace; the Haar measure is `Goldbach.Cert.MajorArcStep7FourierOrthogonality.μ`.

private abbrev μ : Measure UC := Goldbach.Cert.MajorArcStep7FourierOrthogonality.μ

private lemma majorArcConstModeSmooth_nonneg {X : ℕ} :
    0 ≤ majorArcConstModeSmooth X := by
  classical
  unfold majorArcConstModeSmooth
  have hW : ∀ α : ℝ, 0 ≤ majorArcWeightSmooth X α := fun α =>
    majorArcWeightSmooth_nonneg (X := X) α
  simpa using
    (intervalIntegral.integral_nonneg_of_forall (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
      (by nlinarith) hW)

private lemma majorArcConstModeSmooth_le_one {X : ℕ} (hX : X0 ≤ X) :
    majorArcConstModeSmooth X ≤ 1 := by
  classical
  have hc0 : 0 ≤ majorArcConstModeSmooth X := majorArcConstModeSmooth_nonneg (X := X)

  have hbound :
      ∀ α : ℝ,
        α ∈ Ι (0 : ℝ) (1 : ℝ) → ‖majorArcWeightSmooth X α‖ ≤ (1 : ℝ) := by
    intro α _hα
    have h0 : 0 ≤ majorArcWeightSmooth X α := majorArcWeightSmooth_nonneg (X := X) α
    have h1 : majorArcWeightSmooth X α ≤ 1 := majorArcWeightSmooth_le_one (X := X) hX α
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1

  have habs :
      |majorArcConstModeSmooth X| ≤ 1 := by
    unfold majorArcConstModeSmooth
    have hnorm :
        ‖∫ α in (0 : ℝ)..(1 : ℝ), majorArcWeightSmooth X α‖ ≤ (1 : ℝ) * |(1 : ℝ) - (0 : ℝ)| := by
      -- This is the `volume` interval integral, so we use the `volume` version of the bound.
      simpa using
        (intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun α : ℝ => majorArcWeightSmooth X α) (C := (1 : ℝ))
          (h := hbound))
    simpa [Real.norm_eq_abs] using (le_trans hnorm (by simp))

  simpa [abs_of_nonneg hc0] using habs

private lemma abs_majorArcWeightSmoothBalanced_le_one {X : ℕ} (hX : X0 ≤ X) (α : ℝ) :
    |majorArcWeightSmoothBalanced X α| ≤ 1 := by
  classical
  have hW0 : 0 ≤ majorArcWeightSmooth X α := majorArcWeightSmooth_nonneg (X := X) α
  have hW1 : majorArcWeightSmooth X α ≤ 1 := majorArcWeightSmooth_le_one (X := X) hX α
  have hc0 : 0 ≤ majorArcConstModeSmooth X := majorArcConstModeSmooth_nonneg (X := X)
  have hc1 : majorArcConstModeSmooth X ≤ 1 := majorArcConstModeSmooth_le_one (X := X) hX
  have hupper : majorArcWeightSmoothBalanced X α ≤ 1 := by
    dsimp [majorArcWeightSmoothBalanced]
    have : majorArcWeightSmooth X α - majorArcConstModeSmooth X ≤ majorArcWeightSmooth X α :=
      sub_le_self _ hc0
    exact le_trans this hW1
  have hlower : (-1 : ℝ) ≤ majorArcWeightSmoothBalanced X α := by
    dsimp [majorArcWeightSmoothBalanced]
    have hneg : (-1 : ℝ) ≤ -majorArcConstModeSmooth X := by
      have := neg_le_neg hc1
      simpa using this
    have hle : -majorArcConstModeSmooth X ≤ majorArcWeightSmooth X α - majorArcConstModeSmooth X := by
      have := add_le_add_right hW0 (-majorArcConstModeSmooth X)
      simpa [sub_eq_add_neg, add_assoc] using this
    exact le_trans hneg hle
  exact abs_le.2 ⟨hlower, hupper⟩

private lemma fourier_add_arg (n : ℤ) (x y : UC) :
    (fourier (T := (1 : ℝ)) n (x + y) : ℂ)
      =
    (fourier (T := (1 : ℝ)) n x : ℂ) * (fourier (T := (1 : ℝ)) n y : ℂ) := by
  simp [fourier_apply, zsmul_add, toCircle_add]

private lemma trigSumShift_l2_sq_eq_sum_norm_sq {X : ℕ} (coeff : ℕ → ℂ) (β : ℝ) :
    (∫ α in (0 : ℝ)..(1 : ℝ), ‖trigSumShift X coeff β α‖ ^ 2)
      =
    ∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2 := by
  classical
  let βUC : UC := (β : UC)
  let c : ℕ → ℂ := fun n => coeff n * (fourier (T := (1 : ℝ)) (n : ℤ) βUC : ℂ)
  let f : C(UC, ℂ) :=
    ∑ n ∈ coeffRange X, (c n) • (fourier (T := (1 : ℝ)) (n : ℤ))

  have hf : ∀ α : ℝ, f (α : UC) = trigSumShift X coeff β α := by
    intro α
    -- Expand `f` and `trigSumShift` and compare termwise.
    -- Expand both sides as sums over `coeffRange X` and compare termwise.
    have hL :
        f (α : UC)
          =
        ∑ n ∈ coeffRange X,
          (coeff n * (fourier (T := (1 : ℝ)) (n : ℤ) βUC : ℂ))
            * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ) := by
      simp [f, c, smul_eq_mul, mul_assoc, -fourier_apply]
    have hR :
        trigSumShift X coeff β α
          =
        ∑ n ∈ coeffRange X,
          coeff n * (fourier (T := (1 : ℝ)) (n : ℤ) ((α + β : ℝ) : UC) : ℂ) := by
      simp [trigSumShift, trigSum, -fourier_apply]
    rw [hL, hR]
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hcoe : ((α : UC) + βUC) = ((α + β : ℝ) : UC) := by
      simp [βUC, add_assoc]
    have hadd :
        (fourier (T := (1 : ℝ)) (n : ℤ) ((α + β : ℝ) : UC) : ℂ)
          =
        (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
          * (fourier (T := (1 : ℝ)) (n : ℤ) βUC : ℂ) := by
      -- Avoid `simp` recursion by rewriting directly.
      have h := fourier_add_arg (n := (n : ℤ)) (x := (α : UC)) (y := βUC)
      -- `h : fourier n ((α : UC) + βUC) = ...`; rewrite the LHS into `((α + β) : UC)`.
      -- Note `← hcoe : ((α + β : ℝ) : UC) = (α : UC) + βUC`.
      simpa [hcoe] using h
    -- Rearrange commutatively.
    calc
      (coeff n * (fourier (T := (1 : ℝ)) (n : ℤ) βUC : ℂ))
          * (fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
          =
        coeff n * ((fourier (T := (1 : ℝ)) (n : ℤ) (α : UC) : ℂ)
          * (fourier (T := (1 : ℝ)) (n : ℤ) βUC : ℂ)) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ = coeff n * (fourier (T := (1 : ℝ)) (n : ℤ) ((α + β : ℝ) : UC) : ℂ) := by
            -- Use `hadd` (with symmetry) and avoid heavy `simp`.
            have := congrArg (fun z : ℂ => coeff n * z) hadd.symm
            simpa [mul_assoc] using this

  have hv : Orthonormal ℂ (fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal))) := by
    simpa using (orthonormal_fourier (T := (1 : ℝ)))
  have hv' :
      Orthonormal ℂ fun n : ℕ =>
        fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ) :=
    hv.comp (fun n : ℕ => (n : ℤ)) (fun _ _ h => Int.ofNat.inj h)

  have hparseval_uc :
      (∫ θ : UC, ‖f θ‖ ^ 2 ∂μ) = ∑ n ∈ coeffRange X, ‖c n‖ ^ 2 := by
    have hinner_int :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∫ θ : UC, ((‖f θ‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      simpa [RCLike.mul_conj] using (ContinuousMap.inner_toLp (μ := μ) (𝕜 := ℂ) f f)

    have hinner_sum :
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
          =
        ∑ n ∈ coeffRange X, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
      have htoLp :
          ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f
            =
          ∑ n ∈ coeffRange X,
            (c n) • (fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ)) := by
        simp [f, fourierLp, map_sum, map_smul]
      calc
        ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
            ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ
            =
          ⟪∑ n ∈ coeffRange X,
              (c n) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ),
              ∑ n ∈ coeffRange X,
                (c n) • fourierLp (T := (1 : ℝ)) (p := (2 : ENNReal)) (n : ℤ)⟫_ℂ := by
              simp [htoLp]
        _ = ∑ n ∈ coeffRange X, conj (c n) * c n := by
              simpa using (hv'.inner_sum (l₁ := c) (l₂ := c) (s := coeffRange X))
        _ = ∑ n ∈ coeffRange X, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simpa using (RCLike.conj_mul (c n))

    have hcast_int :
        ((∫ θ : UC, ‖f θ‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        (∫ θ : UC, ((‖f θ‖ ^ 2 : ℝ) : ℂ) ∂μ) := by
      have h :
          (∫ θ : UC, ((‖f θ‖ ^ 2 : ℝ) : ℂ) ∂μ)
            =
          ((∫ θ : UC, ‖f θ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
        exact
          (integral_ofReal (μ := μ) (f := fun θ : UC => ‖f θ‖ ^ 2) :
            (∫ θ : UC, ((‖f θ‖ ^ 2 : ℝ) : ℂ) ∂μ) = ((∫ θ : UC, ‖f θ‖ ^ 2 ∂μ : ℝ) : ℂ))
      exact h.symm

    have hcast_sum :
        ((∑ n ∈ coeffRange X, ‖c n‖ ^ 2 : ℝ) : ℂ)
          =
        ∑ n ∈ coeffRange X, ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
      simpa using (map_sum Complex.ofRealHom (fun n : ℕ => ‖c n‖ ^ 2) (coeffRange X))

    have hEqC :
        ((∫ θ : UC, ‖f θ‖ ^ 2 ∂μ : ℝ) : ℂ)
          =
        ((∑ n ∈ coeffRange X, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
      calc
        ((∫ θ : UC, ‖f θ‖ ^ 2 ∂μ : ℝ) : ℂ)
            = (∫ θ : UC, ((‖f θ‖ ^ 2 : ℝ) : ℂ) ∂μ) := hcast_int
        _ = ⟪ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f,
              ContinuousMap.toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℂ) f⟫_ℂ := by
              symm
              exact hinner_int
        _ = ∑ n ∈ coeffRange X, ((‖c n‖ ^ 2 : ℝ) : ℂ) := hinner_sum
        _ = ((∑ n ∈ coeffRange X, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
              simpa [hcast_sum] using (hcast_sum.symm)

    have hEqR : (∫ θ : UC, ‖f θ‖ ^ 2 ∂μ) = ∑ n ∈ coeffRange X, ‖c n‖ ^ 2 := by
      have h := congrArg (fun z : ℂ => RCLike.re z) hEqC
      simpa only [RCLike.ofReal_re] using h

    exact hEqR

  have hcn : ∀ n ∈ coeffRange X, ‖c n‖ ^ 2 = ‖coeff n‖ ^ 2 := by
    intro n _hn
    have hnorm : ‖(fourier (T := (1 : ℝ)) (n : ℤ) βUC : ℂ)‖ = 1 := by
      simpa [fourier_apply] using (Circle.norm_coe (toCircle ((n : ℤ) • βUC :)))
    simp [c, norm_mul, hnorm, mul_assoc]

  calc
    (∫ α in (0 : ℝ)..(1 : ℝ), ‖trigSumShift X coeff β α‖ ^ 2)
        =
      ∫ α in (0 : ℝ)..(1 : ℝ), ‖f (α : UC)‖ ^ 2 := by
          refine intervalIntegral.integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro α
          simpa [hf α]
    _ = (∫ θ : UC, ‖f θ‖ ^ 2 ∂μ) := by
          simpa using (integral_μ_eq_intervalIntegral (f := fun θ : UC => (‖f θ‖ ^ 2 : ℝ))).symm
    _ = ∑ n ∈ coeffRange X, ‖c n‖ ^ 2 := hparseval_uc
    _ = ∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          simpa [hcn n hn]

theorem q0AliasSuppressedHybridLargeSieve :
    Q0AliasSuppressedHybridLargeSieve (1 / (X0 : ℝ)) := by
  classical
  refine ⟨by positivity, ?_⟩
  intro X hX coeff β
  have hW : ∀ α : ℝ, |majorArcWeightSmoothBalanced X α| ≤ 1 :=
    abs_majorArcWeightSmoothBalanced_le_one (X := X) hX

  have hab01 : (0 : ℝ) ≤ (1 : ℝ) := by norm_num

  have hInt :
      IntervalIntegrable (fun α : ℝ => ‖trigSumShift X coeff β α‖ ^ 2) volume (0 : ℝ) (1 : ℝ) := by
    have hcont : Continuous fun α : ℝ => trigSumShift X coeff β α := by
      -- Use the explicit finite Fourier polynomial definition.
      simp [trigSumShift, trigSum, -fourier_apply]
      refine continuous_finset_sum (s := coeffRange X) ?_
      intro n hn
      have hreal : Continuous fun α : ℝ => (α + β : ℝ) := continuous_id.add continuous_const
      have hcoe : Continuous fun t : ℝ => (t : UC) := by
        simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))
      have hmap : Continuous fun α : ℝ => ((α + β : ℝ) : UC) := hcoe.comp hreal
      have hfour :
          Continuous fun α : ℝ => (fourier (T := (1 : ℝ)) (n : ℤ) (((α + β : ℝ) : UC)) : ℂ) :=
        (fourier (T := (1 : ℝ)) (n : ℤ)).continuous.comp hmap
      exact continuous_const.mul hfour
    have hcont2 : Continuous fun α : ℝ => ‖trigSumShift X coeff β α‖ ^ 2 := by
      simpa [pow_two] using (hcont.norm.pow 2)
    exact hcont2.intervalIntegrable (0 : ℝ) (1 : ℝ)

  have hab :
      |∫ α in (0 : ℝ)..(1 : ℝ),
          majorArcWeightSmoothBalanced X α * ‖trigSumShift X coeff β α‖ ^ 2|
        ≤
      ∫ α in (0 : ℝ)..(1 : ℝ), ‖trigSumShift X coeff β α‖ ^ 2 := by
    have hpoint :
        ∀ α : ℝ,
          α ∈ Set.Ioc (0 : ℝ) (1 : ℝ) →
            ‖majorArcWeightSmoothBalanced X α * ‖trigSumShift X coeff β α‖ ^ 2‖
              ≤
            ‖trigSumShift X coeff β α‖ ^ 2 := by
      intro α _hα
      have hWα : |majorArcWeightSmoothBalanced X α| ≤ 1 := hW α
      have hnonneg : 0 ≤ ‖trigSumShift X coeff β α‖ ^ 2 := by nlinarith
      calc
        ‖majorArcWeightSmoothBalanced X α * ‖trigSumShift X coeff β α‖ ^ 2‖
            = |majorArcWeightSmoothBalanced X α| * (‖trigSumShift X coeff β α‖ ^ 2) := by
                simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
        _ ≤ 1 * (‖trigSumShift X coeff β α‖ ^ 2) := by
                exact mul_le_mul_of_nonneg_right hWα hnonneg
        _ = ‖trigSumShift X coeff β α‖ ^ 2 := by ring
    have hnorm :=
      intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun α : ℝ => majorArcWeightSmoothBalanced X α * ‖trigSumShift X coeff β α‖ ^ 2)
        (g := fun α : ℝ => ‖trigSumShift X coeff β α‖ ^ 2)
        hab01 (by
          refine Filter.Eventually.of_forall ?_
          intro α
          intro hα
          simpa using hpoint α hα) hInt
    simpa [Real.norm_eq_abs] using hnorm

  have hparseval := trigSumShift_l2_sq_eq_sum_norm_sq (X := X) coeff β

  have hscale :
      (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2)
        ≤
      (1 / (X0 : ℝ)) * (X : ℝ) * (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2) := by
    have hnonneg : 0 ≤ (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2) := by
      refine Finset.sum_nonneg ?_
      intro n hn
      exact sq_nonneg _
    have hratio : 1 ≤ (1 / (X0 : ℝ)) * (X : ℝ) := by
      have hX0pos : 0 < (X0 : ℝ) := by
        have : 0 < X0 := by decide
        exact_mod_cast this
      have hX0_le : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have := (one_le_div₀ hX0pos).2 hX0_le
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
    have hmul :
        (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2)
          ≤
        ((1 / (X0 : ℝ)) * (X : ℝ)) * (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2) := by
      simpa [one_mul] using (mul_le_mul_of_nonneg_right hratio hnonneg)
    simpa [mul_assoc] using hmul

  calc
    |∫ α in (0 : ℝ)..(1 : ℝ),
          majorArcWeightSmoothBalanced X α * ‖trigSumShift X coeff β α‖ ^ 2|
        ≤
      ∫ α in (0 : ℝ)..(1 : ℝ), ‖trigSumShift X coeff β α‖ ^ 2 := hab
    _ = ∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2 := hparseval
    _ ≤ (1 / (X0 : ℝ)) * (X : ℝ) * (∑ n ∈ coeffRange X, ‖coeff n‖ ^ 2) := hscale

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailAliasSuppressionDeterministic
