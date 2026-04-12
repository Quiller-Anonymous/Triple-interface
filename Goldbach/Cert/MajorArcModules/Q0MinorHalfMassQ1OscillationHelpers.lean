import Goldbach.Cert.MajorArcStep5ExpSumApprox
import Goldbach.Cert.MajorArcStep2MajorArcDecomp
import Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval
import Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation
import Goldbach.Cert.MajorArcModules.BetaInterval
import Mathlib.Algebra.Field.GeomSum

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers

open scoped BigOperators

open MeasureTheory
open Complex
open Goldbach
open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep2ExpSums
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarShape
open Goldbach.BankPieces.Cert.RawScaleFrozenScalarParseval
open Goldbach.Cert.MajorArcModules.BetaInterval

noncomputable section

/--
Canonical one-dimensional exponential sum on the Step-21 interval `Ico 4 ((L - 2) + 1)`.

This is the reusable one-variable oscillatory core behind the positive/negative `q = 1` common
branch.
-/
noncomputable def finiteGExpIco (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((L - 2) + 1), gExp θ n

/--
Exact adjacent/frequency-shift difference of the canonical one-dimensional exponential sum.
-/
noncomputable def finiteGExpIcoShiftDiff (L : ℕ) (θ δ : ℝ) : ℂ :=
  finiteGExpIco L (θ + δ) - finiteGExpIco L θ

/--
Termwise `shift_minus_one` expansion of the frequency-shift difference.
-/
theorem finiteGExpIcoShiftDiff_eq_sum_base_mul_shift_sub_one
    (L : ℕ) (θ δ : ℝ) :
    finiteGExpIcoShiftDiff L θ δ
      =
    ∑ n ∈ Finset.Ico 4 ((L - 2) + 1),
      gExp θ n * (gExp δ n - 1) := by
  unfold finiteGExpIcoShiftDiff finiteGExpIco
  calc
    (∑ n ∈ Finset.Ico 4 ((L - 2) + 1), gExp (θ + δ) n)
        - (∑ n ∈ Finset.Ico 4 ((L - 2) + 1), gExp θ n)
      =
    ∑ n ∈ Finset.Ico 4 ((L - 2) + 1), (gExp (θ + δ) n - gExp θ n) := by
        rw [Finset.sum_sub_distrib]
    _ =
    ∑ n ∈ Finset.Ico 4 ((L - 2) + 1), gExp θ n * (gExp δ n - 1) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add]
        ring

/--
Equivalent exact re-expression as a difference of two finite geometric sums.
-/
theorem finiteGExpIcoShiftDiff_eq_sum_add_sub_sum
    (L : ℕ) (θ δ : ℝ) :
    finiteGExpIcoShiftDiff L θ δ
      =
    (∑ n ∈ Finset.Ico 4 ((L - 2) + 1), gExp (θ + δ) n)
      - (∑ n ∈ Finset.Ico 4 ((L - 2) + 1), gExp θ n) := by
  rfl

/--
Theorem-facing target for a sharp one-dimensional shift-difference bound.

This is intentionally abstract: the live question is no longer algebraic, but whether the finite
geometric sum difference beats the trivial `L^2 |δ|` scale in the oscillatory regime.
-/
structure FiniteGExpIcoShiftDiffBound
    (bound : ℕ → ℝ → ℝ → ℝ) : Prop where
  nonneg :
    ∀ L θ δ, 0 ≤ bound L θ δ
  le_bound :
    ∀ L θ δ,
      ‖finiteGExpIcoShiftDiff L θ δ‖ ≤ bound L θ δ

/--
Quadratic `β`-energy of the canonical shift-difference on the small-`β` interval.

This is the live oscillatory object for the new q=1 energy branch: control in `L²_β`, not
pointwise absolute value.
-/
noncomputable def finiteGExpIcoShiftDiffBetaEnergy
    (L : ℕ) (δ : ℝ) : ℝ :=
  ∫ β in aβ..bβ, ‖finiteGExpIcoShiftDiff L β δ‖ ^ 2

/--
Quadratic `β`-energy of the reflected canonical shift-difference on the small-`β` interval.
-/
noncomputable def finiteGExpIcoShiftDiffNegBetaEnergy
    (L : ℕ) (δ : ℝ) : ℝ :=
  ∫ β in aβ..bβ, ‖finiteGExpIcoShiftDiff L (-β) δ‖ ^ 2

/--
Abstract theorem surface for the `L²_β` bound actually needed by the q=1 positive branch.

The same route constant is used for the `β` and `-β` phases so the negative companion can be
handled by symmetry or duplication later.
-/
structure FiniteGExpIcoShiftDiffBetaEnergyTarget
    (bound : ℕ → ℝ → ℝ) : Prop where
  nonneg :
    ∀ L δ, 0 ≤ bound L δ
  le_pos :
    ∀ L δ, finiteGExpIcoShiftDiffBetaEnergy L δ ≤ bound L δ
  le_neg :
    ∀ L δ, finiteGExpIcoShiftDiffNegBetaEnergy L δ ≤ bound L δ

/--
Quadratic `β`-energy of the plain plus/minus product of one-dimensional finite exponential sums.

The positive q=1 common β-energy branch factors into a harmless Fourier-in-`u / X` difference
times this product, so this is the actual oscillatory helper target for that branch.
-/
noncomputable def finiteGExpIcoPlusMinusProductBetaEnergy
    (L : ℕ) (δ : ℝ) : ℝ :=
  ∫ β in aβ..bβ,
    ‖finiteGExpIco L (δ + β) * finiteGExpIco L (δ - β)‖ ^ 2

/--
Theorem-facing `L²_β` target for the plain plus/minus product.
-/
structure FiniteGExpIcoPlusMinusProductBetaEnergyTarget
    (bound : ℕ → ℝ → ℝ) : Prop where
  nonneg :
    ∀ L δ, 0 ≤ bound L δ
  le_bound :
    ∀ L δ, finiteGExpIcoPlusMinusProductBetaEnergy L δ ≤ bound L δ

/-- Cubic Parseval-scale bound for the plus/minus product energy. -/
noncomputable def finiteGExpIcoPlusMinusProductBetaEnergyCubicBound
    (L : ℕ) (_δ : ℝ) : ℝ :=
  ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ) ^ 3

/--
Abstract theorem surface for a one-variable bound on the canonical finite exponential sum.
-/
structure FiniteGExpIcoBound
    (bound : ℕ → ℝ → ℝ) : Prop where
  nonneg :
    ∀ L θ, 0 ≤ bound L θ
  le_bound :
    ∀ L θ, ‖finiteGExpIco L θ‖ ≤ bound L θ

private lemma norm_gExp_eq_one_local (θ : ℝ) (n : ℕ) :
    ‖gExp θ n‖ = 1 := by
  simpa using Goldbach.Cert.MajorArcStep2ExpSums.norm_gExp θ n

private lemma gExp_nat_add_local (θ : ℝ) (m n : ℕ) :
    gExp θ (m + n) = gExp θ m * gExp θ n := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp
  have hphase : θ * ((m + n : ℕ) : ℝ) = θ * (m : ℝ) + θ * (n : ℝ) := by
    norm_num
    ring
  rw [hphase, Goldbach.Cert.MajorArcStep5ExpSumApprox.e_add]

private lemma gExp_one_pow_local (θ : ℝ) :
    ∀ n : ℕ, (gExp θ 1) ^ n = gExp θ n
  | 0 => by
      unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp
      simp [Goldbach.Cert.MajorArcExponential.e]
  | n + 1 => by
      calc
        (gExp θ 1) ^ (n + 1)
            = (gExp θ 1) ^ n * gExp θ 1 := by simp [pow_succ]
        _ = gExp θ n * gExp θ 1 := by rw [gExp_one_pow_local θ n]
        _ = gExp θ (n + 1) := by
            simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
              (gExp_nat_add_local θ n 1).symm

private lemma finiteGExpIco_eq_sum_powers
    (L : ℕ) (θ : ℝ) :
    finiteGExpIco L θ
      =
    ∑ n ∈ Finset.Ico 4 ((L - 2) + 1), (gExp θ 1) ^ n := by
  unfold finiteGExpIco
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [gExp_one_pow_local]

/--
If the step phase is trivial, the canonical finite exponential sum is exactly its cardinality.
-/
theorem finiteGExpIco_eq_card_of_phase_eq_one
    (L : ℕ) (θ : ℝ) (hphase : gExp θ 1 = 1) :
    finiteGExpIco L θ = ((Finset.Ico 4 ((L - 2) + 1)).card : ℂ) := by
  rw [finiteGExpIco_eq_sum_powers]
  calc
    ∑ n ∈ Finset.Ico 4 ((L - 2) + 1), (gExp θ 1) ^ n
        = ∑ n ∈ Finset.Ico 4 ((L - 2) + 1), (1 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [hphase]
    _ = ((Finset.Ico 4 ((L - 2) + 1)).card : ℂ) := by simp

/--
Geometric-series formula for the canonical finite exponential sum on `Ico 4 ((L - 2) + 1)`.
-/
theorem finiteGExpIco_eq_geom_div_of_phase_ne_one
    (L : ℕ) (θ : ℝ)
    (hphase : gExp θ 1 ≠ 1)
    (hIco : 4 ≤ (L - 2) + 1) :
    finiteGExpIco L θ
      =
    (((gExp θ 1) ^ 4 - (gExp θ 1) ^ (((L - 2) + 1))) / (1 - gExp θ 1)) := by
  rw [finiteGExpIco_eq_sum_powers]
  simpa using geom_sum_Ico' (x := gExp θ 1) hphase hIco

/--
Oscillatory geometric-series bound for the canonical finite exponential sum.

This is the theorem that replaces the dead `card^2` route: once the one-step phase is nontrivial,
the sum is bounded by `2 / ‖1 - z‖` with `z = gExp θ 1`.
-/
theorem norm_finiteGExpIco_le_two_div_norm_one_sub
    (L : ℕ) (θ : ℝ) (hphase : gExp θ 1 ≠ 1) :
    ‖finiteGExpIco L θ‖ ≤ 2 / ‖1 - gExp θ 1‖ := by
  by_cases hIco : 4 ≤ (L - 2) + 1
  · rw [finiteGExpIco_eq_geom_div_of_phase_ne_one L θ hphase hIco, norm_div]
    have hnum :
        ‖(gExp θ 1) ^ 4 - (gExp θ 1) ^ (((L - 2) + 1))‖ ≤ 2 := by
      calc
        ‖(gExp θ 1) ^ 4 - (gExp θ 1) ^ (((L - 2) + 1))‖
            ≤ ‖(gExp θ 1) ^ 4‖ + ‖(gExp θ 1) ^ (((L - 2) + 1))‖ := by
                exact norm_sub_le _ _
        _ = 2 := by
              simp [norm_gExp_eq_one_local]
              norm_num
    have hden_nonneg : 0 ≤ ‖1 - gExp θ 1‖ := norm_nonneg _
    exact (div_le_div_of_nonneg_right hnum hden_nonneg)
  · have hEmpty : Finset.Ico 4 ((L - 2) + 1) = ∅ := by
      exact Finset.Ico_eq_empty_of_le (le_of_not_ge hIco)
    rw [finiteGExpIco, hEmpty, Finset.sum_empty, norm_zero]
    positivity

/--
Trivial cardinality bound for the canonical finite exponential sum.
-/
theorem norm_finiteGExpIco_le_card
    (L : ℕ) (θ : ℝ) :
    ‖finiteGExpIco L θ‖
      ≤ ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ) := by
  unfold finiteGExpIco
  calc
    ‖∑ n ∈ Finset.Ico 4 ((L - 2) + 1), gExp θ n‖
      ≤ ∑ n ∈ Finset.Ico 4 ((L - 2) + 1), ‖gExp θ n‖ := by
          exact norm_sum_le _ _
    _ = ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ) := by
          simp [norm_gExp_eq_one_local]

private lemma continuous_gExp_real_local (n : ℕ) :
    Continuous fun β : ℝ => gExp β n := by
  unfold gExp Goldbach.Cert.MajorArcExponential.e
  have hmul : Continuous fun β : ℝ => ((β : ℂ) * (n : ℂ)) :=
    continuous_ofReal.mul continuous_const
  have hscale : Continuous fun β : ℝ => ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hmul
  have hexpArg :
      Continuous fun β : ℝ => (Complex.I : ℂ) * ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hscale
  simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.continuous_exp.comp hexpArg

private lemma continuous_finiteGExpIco_local (L : ℕ) :
    Continuous fun β : ℝ => finiteGExpIco L β := by
  unfold finiteGExpIco
  refine continuous_finset_sum _ ?_
  intro n hn
  exact continuous_gExp_real_local n

private lemma gExp_add_one_arg_local (θ β : ℝ) (n : ℕ) :
    gExp (θ + (β + 1)) n = gExp (θ + β) n := by
  unfold gExp
  have harg :
      (θ + (β + 1)) * (n : ℝ)
        =
      (θ + β) * (n : ℝ) + (n : ℝ) := by
    ring
  rw [harg]
  exact Goldbach.Cert.MajorArcStep2MajorArcDecomp.e_add_nat
    (x := (θ + β) * (n : ℝ)) (m := n)

private lemma e_sub_nat_local (x : ℝ) (m : ℕ) :
    Goldbach.Cert.MajorArcExponential.e (x - (m : ℝ))
      =
    Goldbach.Cert.MajorArcExponential.e x := by
  have h :=
    Goldbach.Cert.MajorArcStep2MajorArcDecomp.e_add_nat
      (x := x - (m : ℝ)) (m := m)
  simpa using h.symm

private lemma gExp_sub_one_arg_local (θ β : ℝ) (n : ℕ) :
    gExp (θ - (β + 1)) n = gExp (θ - β) n := by
  unfold gExp
  have harg :
      (θ - (β + 1)) * (n : ℝ)
        =
      (θ - β) * (n : ℝ) - (n : ℝ) := by
    ring
  rw [harg]
  exact e_sub_nat_local ((θ - β) * (n : ℝ)) n

private lemma periodic_normSq_finiteGExpIco_add (L : ℕ) (θ : ℝ) :
    Function.Periodic (fun β : ℝ => ‖finiteGExpIco L (θ + β)‖ ^ 2) (1 : ℝ) := by
  intro β
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
  unfold finiteGExpIco
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact gExp_add_one_arg_local θ β n

private lemma periodic_normSq_finiteGExpIco_sub (L : ℕ) (θ : ℝ) :
    Function.Periodic (fun β : ℝ => ‖finiteGExpIco L (θ - β)‖ ^ 2) (1 : ℝ) := by
  intro β
  refine congrArg (fun z : ℂ => ‖z‖ ^ 2) ?_
  unfold finiteGExpIco
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact gExp_sub_one_arg_local θ β n

private lemma finiteGExpIco_empty_of_not_five_le
    (L : ℕ) (hL : ¬ 5 ≤ L) :
    Finset.Ico 4 ((L - 2) + 1) = ∅ := by
  exact Finset.Ico_eq_empty_of_le (by omega)

private lemma finiteGExpIco_card_eq_sub_five
    (L : ℕ) (hL : 5 ≤ L) :
    (Finset.Ico 4 ((L - 2) + 1)).card = L - 5 := by
  rw [Nat.card_Ico]
  omega

private theorem integral_normSq_finiteGExpIco_sub_aβ_bβ_eq_card
    (L : ℕ) (θ : ℝ) :
    (∫ β in aβ..bβ, ‖finiteGExpIco L (θ - β)‖ ^ 2)
      =
    ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ) := by
  by_cases hL : 5 ≤ L
  · let g : ℝ → ℝ := fun β => ‖finiteGExpIco L (θ - β)‖ ^ 2
    have hgper : Function.Periodic g (1 : ℝ) := periodic_normSq_finiteGExpIco_sub L θ
    have hbaseper : Function.Periodic (fun β : ℝ => ‖finiteGExpIco L β‖ ^ 2) (1 : ℝ) := by
      simpa using periodic_normSq_finiteGExpIco_add L 0
    have hparse :
        (∫ β in (0 : ℝ)..(1 : ℝ), ‖finiteGExpIco L β‖ ^ 2) = (L - 5 : ℝ) := by
      simpa [finiteGExpIco, frozenExpSumC] using
        integral_normSq_frozenExpSumC_zero_one L hL
    have hcard :
        ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ) = (L - 5 : ℝ) := by
      exact_mod_cast finiteGExpIco_card_eq_sub_five L hL
    calc
      (∫ β in aβ..bβ, ‖finiteGExpIco L (θ - β)‖ ^ 2)
          = ∫ β in (0 : ℝ)..(1 : ℝ), g β := by
              simpa [g, bβ_eq_aβ_add_one] using
                (hgper.intervalIntegral_add_eq aβ (0 : ℝ))
      _ = ∫ β in (θ - 1)..θ, ‖finiteGExpIco L β‖ ^ 2 := by
              simpa [g, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                (intervalIntegral.integral_comp_sub_left
                  (f := fun β : ℝ => ‖finiteGExpIco L β‖ ^ 2)
                  (a := (0 : ℝ)) (b := (1 : ℝ)) (d := θ))
      _ = ∫ β in (0 : ℝ)..(1 : ℝ), ‖finiteGExpIco L β‖ ^ 2 := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (hbaseper.intervalIntegral_add_eq (θ - 1 : ℝ) (0 : ℝ))
      _ = (L - 5 : ℝ) := hparse
      _ = ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ) := hcard.symm
  · have hEmpty := finiteGExpIco_empty_of_not_five_le L hL
    simp [finiteGExpIco, hEmpty]

private lemma intervalIntegrable_normSq_finiteGExpIco_product
    (L : ℕ) (δ : ℝ) :
    IntervalIntegrable
      (fun β : ℝ =>
        ‖finiteGExpIco L (δ + β) * finiteGExpIco L (δ - β)‖ ^ 2)
      volume aβ bβ := by
  have hplus :
      Continuous fun β : ℝ => finiteGExpIco L (δ + β) :=
    (continuous_finiteGExpIco_local L).comp
      ((continuous_const : Continuous fun _ : ℝ => δ).add continuous_id)
  have hminus :
      Continuous fun β : ℝ => finiteGExpIco L (δ - β) :=
    (continuous_finiteGExpIco_local L).comp
      ((continuous_const : Continuous fun _ : ℝ => δ).sub continuous_id)
  exact ((hplus.mul hminus).norm.pow 2).intervalIntegrable _ _

private lemma intervalIntegrable_normSq_finiteGExpIco_sub
    (L : ℕ) (δ : ℝ) :
    IntervalIntegrable (fun β : ℝ => ‖finiteGExpIco L (δ - β)‖ ^ 2)
      volume aβ bβ := by
  have hminus :
      Continuous fun β : ℝ => finiteGExpIco L (δ - β) :=
    (continuous_finiteGExpIco_local L).comp
      ((continuous_const : Continuous fun _ : ℝ => δ).sub continuous_id)
  exact (hminus.norm.pow 2).intervalIntegrable _ _

theorem finiteGExpIcoPlusMinusProductBetaEnergy_le_cubicBound
    (L : ℕ) (δ : ℝ) :
    finiteGExpIcoPlusMinusProductBetaEnergy L δ
      ≤
    finiteGExpIcoPlusMinusProductBetaEnergyCubicBound L δ := by
  let cardR : ℝ := ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ)
  have hpoint :
      ∀ β ∈ Set.Icc aβ bβ,
        ‖finiteGExpIco L (δ + β) * finiteGExpIco L (δ - β)‖ ^ 2
          ≤
        cardR ^ 2 * ‖finiteGExpIco L (δ - β)‖ ^ 2 := by
    intro β hβ
    have hplus := norm_finiteGExpIco_le_card L (δ + β)
    have hplus' : ‖finiteGExpIco L (δ + β)‖ ≤ cardR := by
      simpa [cardR] using hplus
    have hcard_nonneg : 0 ≤ cardR := by positivity
    have hplus_nonneg : 0 ≤ ‖finiteGExpIco L (δ + β)‖ := norm_nonneg _
    have hminus_nonneg : 0 ≤ ‖finiteGExpIco L (δ - β)‖ := norm_nonneg _
    have hmul :
        ‖finiteGExpIco L (δ + β)‖ * ‖finiteGExpIco L (δ - β)‖
          ≤
        cardR * ‖finiteGExpIco L (δ - β)‖ := by
      exact mul_le_mul_of_nonneg_right hplus' hminus_nonneg
    have hmul_left_nonneg :
        0 ≤ ‖finiteGExpIco L (δ + β)‖ * ‖finiteGExpIco L (δ - β)‖ := by
      exact mul_nonneg hplus_nonneg hminus_nonneg
    have hmul_right_nonneg :
        0 ≤ cardR * ‖finiteGExpIco L (δ - β)‖ := by
      exact mul_nonneg hcard_nonneg hminus_nonneg
    rw [norm_mul]
    nlinarith
  have hmono :=
    intervalIntegral.integral_mono_on (μ := volume) (a := aβ) (b := bβ)
      (f := fun β : ℝ =>
        ‖finiteGExpIco L (δ + β) * finiteGExpIco L (δ - β)‖ ^ 2)
      (g := fun β : ℝ =>
        cardR ^ 2 * ‖finiteGExpIco L (δ - β)‖ ^ 2)
      hle
      (intervalIntegrable_normSq_finiteGExpIco_product L δ)
      ((intervalIntegrable_normSq_finiteGExpIco_sub L δ).const_mul (cardR ^ 2))
      hpoint
  have hsub := integral_normSq_finiteGExpIco_sub_aβ_bβ_eq_card L δ
  unfold finiteGExpIcoPlusMinusProductBetaEnergy finiteGExpIcoPlusMinusProductBetaEnergyCubicBound
  calc
    ∫ β in aβ..bβ,
        ‖finiteGExpIco L (δ + β) * finiteGExpIco L (δ - β)‖ ^ 2
        ≤
      ∫ β in aβ..bβ,
        cardR ^ 2 * ‖finiteGExpIco L (δ - β)‖ ^ 2 := hmono
    _ = cardR ^ 2
        * (∫ β in aβ..bβ, ‖finiteGExpIco L (δ - β)‖ ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
    _ = cardR ^ 2 * cardR := by
          rw [hsub]
    _ = cardR ^ 3 := by ring

theorem finiteGExpIcoPlusMinusProductBetaEnergyTarget_cubic :
    FiniteGExpIcoPlusMinusProductBetaEnergyTarget
      finiteGExpIcoPlusMinusProductBetaEnergyCubicBound where
  nonneg := by
    intro L δ
    unfold finiteGExpIcoPlusMinusProductBetaEnergyCubicBound
    positivity
  le_bound := finiteGExpIcoPlusMinusProductBetaEnergy_le_cubicBound

/--
Concrete theorem-facing bound combining the trivial cardinality regime and the geometric
oscillatory regime.
-/
noncomputable def finiteGExpIcoGeomBound (L : ℕ) (θ : ℝ) : ℝ :=
  min ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ)
    (if _hphase : gExp θ 1 = 1 then
      ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ)
    else
      2 / ‖1 - gExp θ 1‖)

/--
The canonical finite exponential sum satisfies the expected geometric two-regime bound.
-/
theorem finiteGExpIcoBound_of_geom :
    FiniteGExpIcoBound finiteGExpIcoGeomBound where
  nonneg := by
    intro L θ
    unfold finiteGExpIcoGeomBound
    refine le_min ?_ ?_
    · positivity
    · split
      · positivity
      · positivity
  le_bound := by
    intro L θ
    have hcard := norm_finiteGExpIco_le_card L θ
    have hgeom :
        ‖finiteGExpIco L θ‖
          ≤
        if _hphase : gExp θ 1 = 1 then
          ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ)
        else
          2 / ‖1 - gExp θ 1‖ := by
      by_cases hphase : gExp θ 1 = 1
      · simpa [hphase] using hcard
      · simpa [hphase] using norm_finiteGExpIco_le_two_div_norm_one_sub L θ hphase
    exact le_min hcard hgeom

/--
Canonical soft small-shift bound for the frequency difference.

This is the `L^2 |δ|` regime coming directly from the exact shift identity and the existing
`norm_gExp_sum_Ico_add_shift_sub_le` lemma.
-/
noncomputable def finiteGExpIcoSoftShiftBound
    (L : ℕ) (δ : ℝ) : ℝ :=
  ((Finset.Ico 4 ((L - 2) + 1)).card : ℝ)
    * ((L - 2 : ℕ) : ℝ)
    * (4 * Real.pi * |δ|)

theorem finiteGExpIcoSoftShiftBound_nonneg
    (L : ℕ) (δ : ℝ) :
    0 ≤ finiteGExpIcoSoftShiftBound L δ := by
  unfold finiteGExpIcoSoftShiftBound
  positivity

/--
Soft small-shift bound specialized to the canonical finite exponential sum.
-/
theorem norm_finiteGExpIcoShiftDiff_le_soft
    (L : ℕ) (θ δ : ℝ) (hδ : |2 * Real.pi * δ| ≤ 1) :
    ‖finiteGExpIcoShiftDiff L θ δ‖ ≤ finiteGExpIcoSoftShiftBound L δ := by
  unfold finiteGExpIcoShiftDiff finiteGExpIco finiteGExpIcoSoftShiftBound
  simpa using
    Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation.norm_gExp_sum_Ico_add_shift_sub_le
      θ δ L hδ

/--
Oscillatory triangle bound: any one-variable bound for `finiteGExpIco` immediately yields a
shift-difference bound by the triangle inequality.
-/
theorem norm_finiteGExpIcoShiftDiff_le_oscillatory
    {bound : ℕ → ℝ → ℝ}
    (hbound : FiniteGExpIcoBound bound)
    (L : ℕ) (θ δ : ℝ) :
    ‖finiteGExpIcoShiftDiff L θ δ‖ ≤ bound L (θ + δ) + bound L θ := by
  unfold finiteGExpIcoShiftDiff
  calc
    ‖finiteGExpIco L (θ + δ) - finiteGExpIco L θ‖
      ≤ ‖finiteGExpIco L (θ + δ)‖ + ‖finiteGExpIco L θ‖ := by
          simpa using norm_sub_le (finiteGExpIco L (θ + δ)) (finiteGExpIco L θ)
    _ ≤ bound L (θ + δ) + bound L θ := by
          gcongr
          · exact hbound.le_bound L (θ + δ)
          · exact hbound.le_bound L θ

/--
Packaged shift-difference bound from the minimum of the soft small-shift regime and any oscillatory
triangle regime.
-/
theorem finiteGExpIcoShiftDiffBound_of_soft_and_oscillatory
    {bound : ℕ → ℝ → ℝ}
    (hbound : FiniteGExpIcoBound bound) :
    FiniteGExpIcoShiftDiffBound
      (fun L θ δ =>
        if hδ : 2 * |Real.pi| * |δ| ≤ 1 then
          min (finiteGExpIcoSoftShiftBound L δ) (bound L (θ + δ) + bound L θ)
        else
          bound L (θ + δ) + bound L θ) where
  nonneg := by
    intro L θ δ
    by_cases hδ : 2 * |Real.pi| * |δ| ≤ 1
    · have :
          0 ≤
            min (finiteGExpIcoSoftShiftBound L δ) (bound L (θ + δ) + bound L θ) := by
          exact le_min (finiteGExpIcoSoftShiftBound_nonneg L δ)
            (add_nonneg (hbound.nonneg L (θ + δ)) (hbound.nonneg L θ))
      change 0 ≤
          if hδ : 2 * |Real.pi| * |δ| ≤ 1 then
            min (finiteGExpIcoSoftShiftBound L δ) (bound L (θ + δ) + bound L θ)
          else
            bound L (θ + δ) + bound L θ
      simp [hδ, this]
    · have :
          0 ≤ bound L (θ + δ) + bound L θ := by
          exact add_nonneg (hbound.nonneg L (θ + δ)) (hbound.nonneg L θ)
      change 0 ≤
          if hδ : 2 * |Real.pi| * |δ| ≤ 1 then
            min (finiteGExpIcoSoftShiftBound L δ) (bound L (θ + δ) + bound L θ)
          else
            bound L (θ + δ) + bound L θ
      simp [hδ, this]
  le_bound := by
    intro L θ δ
    by_cases hδ : 2 * |Real.pi| * |δ| ≤ 1
    · have :
          ‖finiteGExpIcoShiftDiff L θ δ‖
            ≤
          min (finiteGExpIcoSoftShiftBound L δ) (bound L (θ + δ) + bound L θ) := by
          have hδ' : |2 * Real.pi * δ| ≤ 1 := by
            simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm]
              using hδ
          exact le_min
            (norm_finiteGExpIcoShiftDiff_le_soft L θ δ hδ')
            (norm_finiteGExpIcoShiftDiff_le_oscillatory hbound L θ δ)
      change ‖finiteGExpIcoShiftDiff L θ δ‖ ≤
          if hδ : 2 * |Real.pi| * |δ| ≤ 1 then
            min (finiteGExpIcoSoftShiftBound L δ) (bound L (θ + δ) + bound L θ)
          else
            bound L (θ + δ) + bound L θ
      simp [hδ, this]
    · have :
          ‖finiteGExpIcoShiftDiff L θ δ‖ ≤ bound L (θ + δ) + bound L θ := by
          exact norm_finiteGExpIcoShiftDiff_le_oscillatory hbound L θ δ
      change ‖finiteGExpIcoShiftDiff L θ δ‖ ≤
          if hδ : 2 * |Real.pi| * |δ| ≤ 1 then
            min (finiteGExpIcoSoftShiftBound L δ) (bound L (θ + δ) + bound L θ)
          else
            bound L (θ + δ) + bound L θ
      simp [hδ, this]

/--
Symmetric plus/minus specialization surface for later use in the `q = 1` common-piece proof.
-/
theorem finiteGExpIcoShiftDiff_negBeta
    (L : ℕ) (β δ : ℝ) :
    finiteGExpIcoShiftDiff L (-β) δ
      =
    ∑ n ∈ Finset.Ico 4 ((L - 2) + 1),
      gExp (-β) n * (gExp δ n - 1) := by
  simpa using finiteGExpIcoShiftDiff_eq_sum_base_mul_shift_sub_one L (-β) δ

theorem finiteGExpIcoShiftDiff_posBeta
    (L : ℕ) (β δ : ℝ) :
    finiteGExpIcoShiftDiff L β δ
      =
    ∑ n ∈ Finset.Ico 4 ((L - 2) + 1),
      gExp β n * (gExp δ n - 1) := by
  simpa using finiteGExpIcoShiftDiff_eq_sum_base_mul_shift_sub_one L β δ

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers
