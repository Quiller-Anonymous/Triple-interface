import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
import Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec
import Goldbach.Cert.MajorArcStep24IntegralExtraction
import Goldbach.Cert.MajorArcStep23RamanujanSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Step 5 (ε₂-large, TT*/Toeplitz): explicit α-weight Fourier coefficient formulas.

This file supplies the deterministic “Step 4a” resources for the hybrid Step-5 certificate plan:

* rewrite `majorArcWeightFourier X Δ t` (an interval integral over `[0,1]`) into a finite `(q,a)`
  sum of arc integrals (`SepQ0` disjointness / Step 24 extraction),
* evaluate each *interior* arc integral explicitly (Ramanujan sum × sinc factor) for `q ≥ 2`,
* split the `q ≥ 13` part by Taylor linearization of `sin`,
* bound the resulting remainder uniformly on the TT*/Toeplitz bandwidth.

This is still “structure-preserving”: Ramanujan sums are kept intact in the linearized main term;
absolute values are taken only after isolating a tiny remainder.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit

open scoped BigOperators Interval

open Complex MeasureTheory AddCircle

open Goldbach

open Goldbach.Cert.MajorArcExponential
open Goldbach.Cert.MajorArcStep23RamanujanSum
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarAlgebra
open Goldbach.Cert.MajorArcModules.RamanujanDispersionSpec

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

/-!
## Integer-frequency Ramanujan sums (same reduced residue convention as `Rcop`)
-/

-- Re-export the project-neutral definition from `RamanujanDispersionSpec` so that the “Ramanujan
-- factor” identity is literally definitional in Step 5.
noncomputable abbrev ramanujanSumZ (q : ℕ) (t : ℤ) : ℂ :=
  RamanujanDispersionSpec.ramanujanSumZ q t

lemma ramanujanSumZ_eq_sum (q : ℕ) (t : ℤ) :
    ramanujanSumZ q t = ∑ a ∈ Rcop q, e ((a : ℝ) * (t : ℝ) / (q : ℝ)) := by
  rfl

lemma norm_ramanujanSumZ_le_totient (q : ℕ) (t : ℤ) :
    ‖ramanujanSumZ q t‖ ≤ (Nat.totient q : ℝ) := by
  classical
  -- triangle inequality + `‖e(·)‖=1`
  have hsum := norm_sum_le (s := Rcop q) (f := fun a => e ((a : ℝ) * (t : ℝ) / (q : ℝ)))
  have hterm : ∀ a ∈ Rcop q, ‖e ((a : ℝ) * (t : ℝ) / (q : ℝ))‖ ≤ (1 : ℝ) := by
    intro a ha
    simpa [MajorArcExponential.norm_e] using (le_rfl : (1 : ℝ) ≤ 1)
  have hsum' :
      (∑ a ∈ Rcop q, ‖e ((a : ℝ) * (t : ℝ) / (q : ℝ))‖)
        ≤
      ∑ _a ∈ Rcop q, (1 : ℝ) := by
    exact Finset.sum_le_sum (fun a ha => hterm a ha)
  have hcard : (∑ _a ∈ Rcop q, (1 : ℝ)) = (Rcop q).card := by
    simp
  calc
    ‖ramanujanSumZ q t‖
        = ‖∑ a ∈ Rcop q, e ((a : ℝ) * (t : ℝ) / (q : ℝ))‖ := by
            simpa [ramanujanSumZ_eq_sum]
    _ ≤ ∑ a ∈ Rcop q, ‖e ((a : ℝ) * (t : ℝ) / (q : ℝ))‖ := hsum
    _ ≤ ∑ _a ∈ Rcop q, (1 : ℝ) := hsum'
    _ = (Rcop q).card := by simpa [hcard]
    _ = Nat.totient q := by simpa [card_Rcop_eq_totient (q := q)]

/-!
## Elementary analytic inequalities
-/

lemma abs_sin_sub_le_seven_div_thirtyTwo_mul_abs_pow_three {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - x| ≤ (7 / 32 : ℝ) * |x| ^ 3 := by
  -- From `Real.sin_bound` and the triangle inequality:
  -- `|sin x - x| ≤ |x|^3/6 + |x|^4*(5/96) ≤ |x|^3*(1/6+5/96) = (7/32)|x|^3` for `|x|≤1`.
  have hsin : |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96 : ℝ) :=
    Real.sin_bound hx
  have htri0 :
      |Real.sin x - x|
        ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := by
    have htri1 :
        |Real.sin x - x|
          ≤ |Real.sin x - (x - x ^ 3 / 6)| + |(x - x ^ 3 / 6) - x| :=
      abs_sub_le (Real.sin x) (x - x ^ 3 / 6) x
    have hlast : |(x - x ^ 3 / 6) - x| = |x ^ 3 / 6| := by
      have : (x - x ^ 3 / 6) - x = -(x ^ 3 / 6) := by ring
      simp [this]
    simpa [hlast] using htri1
  have hx3div : |x ^ 3 / 6| = |x| ^ 3 / 6 := by
    simp [abs_div, abs_pow]
  have hx4_le_x3 : |x| ^ 4 ≤ |x| ^ 3 := by
    -- `|x| ≤ 1` implies `|x|^4 ≤ |x|^3`.
    have hx1 : |x| ≤ 1 := hx
    have : |x| ^ 4 = |x| ^ 3 * |x| := by
      simp [pow_succ, mul_assoc]
    calc
      |x| ^ 4 = |x| ^ 3 * |x| := this
      _ ≤ |x| ^ 3 * (1 : ℝ) := mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ |x| ^ 3)
      _ = |x| ^ 3 := by simp
  calc
    |Real.sin x - x|
        ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x| ^ 3 / 6 := by
          simpa [hx3div] using htri0
    _ ≤ |x| ^ 4 * (5 / 96 : ℝ) + |x| ^ 3 / 6 := by
          exact add_le_add_right hsin _
    _ ≤ |x| ^ 3 * (5 / 96 : ℝ) + |x| ^ 3 / 6 := by
          exact add_le_add_right (mul_le_mul_of_nonneg_right hx4_le_x3 (by positivity)) _
    _ = (7 / 32 : ℝ) * |x| ^ 3 := by ring

/-!
## Step 24 extraction specialized to `majorArcWeightFourier`
-/

private lemma intervalIntegrable_fourier_int (t : ℤ) :
    IntervalIntegrable (fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ))
      volume (0 : ℝ) (1 : ℝ) := by
  -- `fourier t` is continuous on `AddCircle 1`, and `α ↦ (α : AddCircle 1)` is continuous.
  exact
    (((map_continuous (fourier (T := (1 : ℝ)) t)).comp (AddCircle.continuous_mk' (1 : ℝ))).intervalIntegrable
      (μ := volume) (0 : ℝ) (1 : ℝ))

private lemma majorArcWeightFourier_eq_indicator (X : ℕ) (Δ : ℝ) (t : ℤ) :
    majorArcWeightFourier X Δ t
      =
    ∫ α in (0 : ℝ)..(1 : ℝ),
      (majorArcSetQ0 X Δ).indicator (fun a : ℝ => (fourier (T := (1 : ℝ)) t (a : UC) : ℂ)) α := by
  classical
  unfold majorArcWeightFourier majorArcWeightC
  refine congrArg (fun f : ℝ → ℂ => ∫ α in (0 : ℝ)..(1 : ℝ), f α) ?_
  funext α
  by_cases hα : α ∈ majorArcSetQ0 X Δ
  · simp [hα]
  · simp [hα]

lemma majorArcWeightFourier_eq_sum_arc_integrals
    (X : ℕ) (Δ : ℝ) (hsep : SepQ0 X Δ) (t : ℤ) :
    majorArcWeightFourier X Δ t
      =
    ∑ q ∈ (Finset.Icc (1 : ℕ) Q0), ∑ a ∈ (Rcop q),
      ∫ α in (0 : ℝ)..(1 : ℝ),
        (arcSetTextbook X q a Δ).indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α := by
  classical
  have hf : IntervalIntegrable (fun a : ℝ => (fourier (T := (1 : ℝ)) t (a : UC) : ℂ))
      volume (0 : ℝ) (1 : ℝ) := intervalIntegrable_fourier_int (t := t)
  -- apply Step 24 extraction to the indicator of `fourier t`
  have :=
    intervalIntegral_majorArcSetQ0_indicator_eq_sum
      (X := X) (Δ := Δ) (hsep := hsep)
      (f := fun a : ℝ => (fourier (T := (1 : ℝ)) t (a : UC) : ℂ)) hf
  -- rewrite the LHS as `majorArcWeightFourier`
  simpa [majorArcWeightFourier_eq_indicator (X := X) (Δ := Δ) (t := t)] using this

/-!
## Evaluating the individual arc integrals (Ramanujan × sinc)

The Step-24 extraction reduces `majorArcWeightFourier` to a finite sum over individual arc
integrals. For `q ≥ 2` these arcs lie strictly inside `(0,1)`, so the indicator integral on
`[0,1]` equals the full symmetric integral over the arc. The case `q = 1` is boundary-truncated and
is handled separately.
-/

private lemma arcSetTextbook_eq_Icc (X q a : ℕ) (Δ : ℝ) :
    arcSetTextbook X q a Δ
      =
    Set.Icc ((a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))
      ((a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))) := by
  ext α
  -- `|α - c| ≤ r` ↔ `c - r ≤ α ∧ α ≤ c + r`
  constructor
  · intro h
    have h' : |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      simpa [MajorArcStep24IntegralExtraction.arcSetTextbook] using h
    have h'' :
        -(Δ / ((q : ℝ) * (X : ℝ))) ≤ α - (a : ℝ) / (q : ℝ) ∧
          α - (a : ℝ) / (q : ℝ) ≤ Δ / ((q : ℝ) * (X : ℝ)) :=
      (abs_le).1 h'
    refine (Set.mem_Icc).2 ?_
    constructor <;> linarith
  · intro hIcc
    rcases (Set.mem_Icc).1 hIcc with ⟨hL, hU⟩
    have h' : |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      refine (abs_le).2 ?_
      constructor <;> linarith
    simpa [MajorArcStep24IntegralExtraction.arcSetTextbook] using h'

private lemma one_le_of_mem_Rcop_of_two_le {q a : ℕ} (hq : 2 ≤ q) (ha : a ∈ Rcop q) : 1 ≤ a := by
  classical
  rcases Finset.mem_filter.mp ha with ⟨haRange, haCoprime⟩
  cases a with
  | zero =>
      have : Nat.Coprime 0 q := by simpa using haCoprime
      have : q = 1 := (Nat.coprime_zero_left q).1 this
      have : (2 : ℕ) ≤ 1 := by simpa [this] using hq
      exact (Nat.not_succ_le_self 1 this).elim
  | succ a =>
      exact Nat.succ_le_succ (Nat.zero_le a)

private lemma lt_one_of_a_over_q_add_delta_div_qX_of_mem_Rcop
    {X q a : ℕ} {Δ : ℝ} (hX : 2 ≤ X) (hq : 2 ≤ q) (ha : a ∈ Rcop q) (hΔ : Δ = (1 : ℝ)) :
    (a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ)) < 1 := by
  -- Use `a < q` and `1/(qX) < 1/q`.
  rcases Finset.mem_filter.mp ha with ⟨haRange, _haCoprime⟩
  have haLt : a < q := Finset.mem_range.mp haRange
  have hq1 : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hXgt1 : (1 : ℝ) < (X : ℝ) := by
    have : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hX
    exact_mod_cast this
  have hq_lt_qX : (q : ℝ) < (q : ℝ) * (X : ℝ) := by nlinarith [hqpos, hXgt1]
  have h1div : (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < (1 : ℝ) / (q : ℝ) := by
    -- `1/(qX) < 1/q`
    simpa [one_div] using (one_div_lt_one_div_of_lt hqpos hq_lt_qX)
  -- bound `a/q ≤ 1 - 1/q`
  have haLe : (a : ℝ) / (q : ℝ) ≤ ((q - 1 : ℕ) : ℝ) / (q : ℝ) := by
    have : (a : ℝ) ≤ (q - 1 : ℕ) := by
      exact_mod_cast (Nat.le_pred_of_lt haLt)
    exact div_le_div_of_nonneg_right this (le_of_lt hqpos)
  have hsum_one :
      ((q - 1 : ℕ) : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ) = 1 := by
    have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hn : ((q - 1 : ℕ) : ℝ) + (1 : ℝ) = (q : ℝ) := by
      have hnNat : (q - 1) + 1 = q := Nat.sub_add_cancel hq1
      exact_mod_cast hnNat
    calc
      ((q - 1 : ℕ) : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ)
          = (((q - 1 : ℕ) : ℝ) + (1 : ℝ)) / (q : ℝ) := by simp [add_div]
      _ = (q : ℝ) / (q : ℝ) := by simp [hn]
      _ = 1 := by simp [hqne]
  have hΔ1 : Δ / ((q : ℝ) * (X : ℝ)) < (1 : ℝ) / (q : ℝ) := by
    simpa [hΔ] using h1div
  -- conclude
  calc
    (a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))
        < (a : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ) := by
            exact add_lt_add_left hΔ1 _
    _ ≤ ((q - 1 : ℕ) : ℝ) / (q : ℝ) + (1 : ℝ) / (q : ℝ) := by
            exact add_le_add_right haLe _
    _ = 1 := hsum_one

private lemma lt_of_delta_div_qX_of_two_le {X q a : ℕ} {Δ : ℝ}
    (hX : 2 ≤ X) (hq : 2 ≤ q) (ha : a ∈ Rcop q) (hΔ : Δ = (1 : ℝ)) :
    (0 : ℝ) < (a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)) := by
  have hq1 : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hXgt1 : (1 : ℝ) < (X : ℝ) := by
    have : (1 : ℕ) < X := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hX
    exact_mod_cast this
  have hq_lt_qX : (q : ℝ) < (q : ℝ) * (X : ℝ) := by nlinarith [hqpos, hXgt1]
  have h1div : (1 : ℝ) / ((q : ℝ) * (X : ℝ)) < (1 : ℝ) / (q : ℝ) := by
    simpa [one_div] using (one_div_lt_one_div_of_lt hqpos hq_lt_qX)
  have ha1 : 1 ≤ a := one_le_of_mem_Rcop_of_two_le (hq := hq) ha
  have ha_over_q : (1 : ℝ) / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha1) (le_of_lt hqpos)
  have hΔ1 : (Δ : ℝ) / ((q : ℝ) * (X : ℝ)) < (1 : ℝ) / (q : ℝ) := by
    simpa [hΔ] using h1div
  have hsmall : (Δ : ℝ) / ((q : ℝ) * (X : ℝ)) < (a : ℝ) / (q : ℝ) :=
    lt_of_lt_of_le hΔ1 ha_over_q
  -- `0 < a/q - Δ/(qX)`
  exact sub_pos.mpr hsmall

private lemma arcSetTextbook_subset_Ioc_0_1
    {X q a : ℕ} {Δ : ℝ} (hX : 2 ≤ X) (hq : 2 ≤ q) (ha : a ∈ Rcop q) (hΔ : Δ = (1 : ℝ)) :
    arcSetTextbook X q a Δ ⊆ Set.Ioc (0 : ℝ) (1 : ℝ) := by
  intro α hα
  -- Use the `Icc` description of the arc and show its endpoints lie in `(0,1)`.
  have hIcc : α ∈ Set.Icc ((a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))
      ((a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))) := by
    simpa [arcSetTextbook_eq_Icc (X := X) (q := q) (a := a) (Δ := Δ)] using hα
  have hl : (0 : ℝ) < (a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)) :=
    lt_of_delta_div_qX_of_two_le (X := X) (q := q) (a := a) (Δ := Δ) hX hq ha hΔ
  have hu : (a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ)) < 1 :=
    lt_one_of_a_over_q_add_delta_div_qX_of_mem_Rcop (X := X) (q := q) (a := a) (Δ := Δ) hX hq ha hΔ
  refine ⟨?_, ?_⟩
  · exact lt_of_lt_of_le hl hIcc.1
  · exact le_of_lt (lt_of_le_of_lt hIcc.2 hu)

private lemma intervalIntegral_arc_indicator_eq
    {X q a : ℕ} {Δ : ℝ} (hX : 2 ≤ X) (hq : 2 ≤ q) (ha : a ∈ Rcop q) (hΔ : Δ = (1 : ℝ))
    (t : ℤ) :
    (∫ α in (0 : ℝ)..(1 : ℝ),
        (arcSetTextbook X q a Δ).indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α)
      =
    ∫ α in ((a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ)))..
        ((a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))),
        (fourier (T := (1 : ℝ)) t (α : UC) : ℂ) := by
  classical
  set s : Set ℝ := arcSetTextbook X q a Δ
  set l : ℝ := (a : ℝ) / (q : ℝ) - Δ / ((q : ℝ) * (X : ℝ))
  set u : ℝ := (a : ℝ) / (q : ℝ) + Δ / ((q : ℝ) * (X : ℝ))
  have hs_meas : MeasurableSet s := by
    simpa [s] using measurableSet_arcSetTextbook (X := X) (q := q) (a := a) (Δ := Δ)
  have hs_sub : s ⊆ Set.Ioc (0 : ℝ) (1 : ℝ) := by
    simpa [s] using
      arcSetTextbook_subset_Ioc_0_1 (X := X) (q := q) (a := a) (Δ := Δ) hX hq ha hΔ
  have hs_eq : s = Set.Icc l u := by
    -- the `Icc` form of the arc, with the above `l,u`
    ext α
    simp [s, l, u, arcSetTextbook_eq_Icc (X := X) (q := q) (a := a) (Δ := Δ)]
  have hlu : l ≤ u := by
    have hq1 : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      have : 0 < X := lt_of_lt_of_le (by decide : 0 < 2) hX
      exact_mod_cast this
    have hden : 0 ≤ (Δ : ℝ) / ((q : ℝ) * (X : ℝ)) := by
      have hΔ0 : (0 : ℝ) ≤ Δ := by simpa [hΔ] using (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
      exact div_nonneg hΔ0 (le_of_lt (mul_pos hqpos hXpos))
    -- `a/q - r ≤ a/q + r` for `r ≥ 0`
    have : -(Δ / ((q : ℝ) * (X : ℝ))) ≤ Δ / ((q : ℝ) * (X : ℝ)) := by linarith
    -- unfold `l,u`
    simp [l, u]
    linarith

  -- Step 1: rewrite the interval integral as a set integral over `Ioc 0 1`.
  rw [intervalIntegral.integral_of_le (μ := volume)
    (f := fun α : ℝ => s.indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α) (a := (0 : ℝ))
    (b := (1 : ℝ)) (by norm_num)]
  -- Now work with the restricted measure on `Ioc 0 1`.
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (1 : ℝ))
  -- turn indicator integral into an integral over `s` w.r.t `μ0`
  have hInd :
      (∫ x, s.indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) x ∂μ0)
        =
      ∫ x in s, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂μ0 := by
    simpa [μ0, s] using
      (MeasureTheory.integral_indicator (μ := μ0)
        (s := s)
        (f := fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) hs_meas)
  -- collapse `μ0.restrict s` to `volume.restrict s` since `s ⊆ Ioc 0 1`
  have hRestr :
      (μ0.restrict s) = volume.restrict s := by
    -- `μ0.restrict s = volume.restrict ((Set.Ioc 0 1) ∩ s) = volume.restrict s`
    ext x hx
    -- unfold restrictions using `restrict_apply`, then use `s ⊆ Ioc 0 1`
    have hs' : MeasurableSet s := hs_meas
    have hsubset : x ∩ s ⊆ Set.Ioc (0 : ℝ) (1 : ℝ) := by
      intro y hy
      exact hs_sub hy.2
    have hxinter : x ∩ (Set.Ioc (0 : ℝ) (1 : ℝ) ∩ s) = x ∩ s := by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1, hy.2.2⟩
      · intro hy
        refine ⟨hy.1, ?_⟩
        exact ⟨hsubset ⟨hy.1, hy.2⟩, hy.2⟩
    -- compute both sides via `restrict_apply`
    simp [μ0, Measure.restrict_apply, hx, hs', hxinter, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
  have hSet :
      (∫ x in s, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂μ0)
        =
      ∫ x in s, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) := by
    -- unfold set integrals as integrals over restricted measures and rewrite using `hRestr`
    change
      (∫ x, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂(μ0.restrict s))
        =
      ∫ x, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂(volume.restrict s)
    simpa [hRestr]

  -- rewrite the set integral over `s` as an interval integral over `l..u`
  have hIcc_restrict :
      volume.restrict (Set.Ioc l u) = volume.restrict (Set.Icc l u) := by
    simpa using (MeasureTheory.restrict_Ioc_eq_restrict_Icc (μ := volume) (a := l) (b := u))
  have hIcc_to_interval :
      (∫ x in s, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ))
        =
      ∫ x in l..u, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) := by
    -- `s = Icc l u`, and interval integrals use `Ioc`; swap `Icc` with `Ioc` by no-atoms.
    rw [hs_eq]
    -- unfold the set integral on the LHS
    change
      (∫ x, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂volume.restrict (Set.Icc l u))
        =
      ∫ x in l..u, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ)
    -- rewrite the interval integral to a set integral on `Ioc l u`
    rw [intervalIntegral.integral_of_le (μ := volume)
      (f := fun x : ℝ => (fourier (T := (1 : ℝ)) t (x : UC) : ℂ)) (a := l) (b := u) hlu]
    -- unfold the set integral on the RHS
    change
      (∫ x, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂volume.restrict (Set.Icc l u))
        =
      ∫ x, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂volume.restrict (Set.Ioc l u)
    -- swap `Ioc` with `Icc` under `volume` (no atoms)
    simpa [hIcc_restrict] using (rfl : (∫ x, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ)
      ∂volume.restrict (Set.Icc l u))
        =
      ∫ x, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂volume.restrict (Set.Icc l u))

  -- assemble
  -- At this point, the goal is an equality in the default measure `volume`.
  -- The only remaining step is to unfold the set integral produced by `intervalIntegral.integral_of_le`.
  have hIoc :
      (∫ x in Set.Ioc (0 : ℝ) (1 : ℝ),
        s.indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) x ∂volume)
        =
      ∫ x, s.indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) x ∂μ0 := by
    rfl
  calc
    (∫ x in Set.Ioc (0 : ℝ) (1 : ℝ),
        s.indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) x ∂volume)
        =
      ∫ x in s, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) ∂μ0 := by
        simpa [hIoc] using hInd
    _ =
      ∫ x in s, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) := hSet
    _ =
      ∫ x in l..u, (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) := hIcc_to_interval

/-- Rewrite `fourier` on `AddCircle 1` in terms of the major-arc additive character `e`. -/
private lemma fourier_T1_coe_eq_e (t : ℤ) (x : ℝ) :
    (fourier (T := (1 : ℝ)) t (x : UC) : ℂ) = e ((t : ℝ) * x) := by
  -- `fourier` is `exp(2π i t x)` and `e` is `exp(2π i ((t:ℝ) * x))`.
  -- Both are the same by commutativity of multiplication in `ℂ`.
  simp [Goldbach.Cert.MajorArcExponential.e, fourier_coe_apply, div_one,
    mul_assoc, mul_left_comm, mul_comm]

private lemma intervalIntegral_fourier_center
    {t : ℤ} (ht : t ≠ 0) (c r : ℝ) :
    (∫ x in (c - r)..(c + r), (fourier (T := (1 : ℝ)) t (x : UC) : ℂ))
      =
    (fourier (T := (1 : ℝ)) t (c : UC) : ℂ)
      * (Real.sin (2 * Real.pi * (t : ℝ) * r) / (Real.pi * (t : ℝ)) : ℂ) := by
  -- Evaluate the integral explicitly and simplify to a center phase times a sinc factor.
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := by simp
  set K : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
  have hK : K ≠ 0 := by
    -- `K = (2 * π * I) * t`
    have h2pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := mul_ne_zero h2 hpi
    have h2piI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero h2pi hI
    simpa [K, mul_assoc] using mul_ne_zero h2piI htC
  have hfourier : (fun x : ℝ => (fourier (T := (1 : ℝ)) t (x : UC) : ℂ)) = fun x : ℝ => Complex.exp (K * x) := by
    funext x
    -- `fourier t (x:UC) = exp(2π i t x / 1) = exp(K*x)`
    simpa [K, div_one, mul_assoc, mul_left_comm, mul_comm] using
      (fourier_coe_apply (T := (1 : ℝ)) (n := t) (x := x))
  -- Evaluate the exponential integral.
  have hInt :
      (∫ x in (c - r)..(c + r), Complex.exp (K * x))
        =
      (Complex.exp (K * (c + r)) - Complex.exp (K * (c - r))) / K := by
    -- `integral_exp_mul_complex` is a general formula for `∫ exp(c*x)`.
    simpa [mul_assoc] using (integral_exp_mul_complex (a := c - r) (b := c + r) (c := K) hK)
  -- Rewrite the LHS integral in terms of `exp (K*x)`.
  have hL :
      (∫ x in (c - r)..(c + r), (fourier (T := (1 : ℝ)) t (x : UC) : ℂ))
        =
      ∫ x in (c - r)..(c + r), Complex.exp (K * x) := by
    -- `simp` does not rewrite under the integral from a function equality; use `congrArg`.
    simpa using congrArg (fun f : ℝ → ℂ => ∫ x in (c - r)..(c + r), f x) hfourier
  -- Factor out the center phase and simplify the sinc ratio.
  have hcenter :
      (fourier (T := (1 : ℝ)) t (c : UC) : ℂ) = Complex.exp (K * c) := by
    simpa [K, div_one, mul_assoc, mul_left_comm, mul_comm] using
      (fourier_coe_apply (T := (1 : ℝ)) (n := t) (x := c))
  have hsinc :
      (Complex.exp (K * r) - Complex.exp (-(K * r))) / K
        =
      (Real.sin (2 * Real.pi * (t : ℝ) * r) / (Real.pi * (t : ℝ)) : ℂ) := by
    -- Let `θ := 2π t r` (real). Then `K*r = (θ:ℂ) * I` and
    -- `(exp(θ I) - exp(-θ I)) / (2π I t) = sin θ / (π t)`.
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have hpiR : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    set θ : ℝ := 2 * Real.pi * (t : ℝ) * r
    have hKr : K * r = ((θ : ℂ) * Complex.I) := by
      -- Move the `I` to the right and collect real factors.
      simp [K, θ, mul_assoc, mul_left_comm, mul_comm]
    have hKneg : -(K * r) = ((-θ : ℂ) * Complex.I) := by
      simp [hKr]
    have hsintheta : Complex.sin (θ : ℂ) = (Real.sin θ : ℂ) := by
      refine Complex.ext ?_ ?_
      · simp [Complex.sin_ofReal_re]
      · simp [Complex.sin_ofReal_im]
    have hnum :
        Complex.exp (K * r) - Complex.exp (-(K * r))
          =
        (2 : ℂ) * (Real.sin θ : ℂ) * Complex.I := by
      -- Expand both exponentials using `exp_mul_I` and cancel the cosine terms.
      have hθ :
          Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((-θ : ℂ) * Complex.I)
            = (2 : ℂ) * Complex.sin (θ : ℂ) * Complex.I := by
        -- Use `exp_mul_I` at `±θ`.
        have hpos :
            Complex.exp ((θ : ℂ) * Complex.I)
              = Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I := by
          simpa using (Complex.exp_mul_I (θ : ℂ))
        have hneg :
            Complex.exp ((-θ : ℂ) * Complex.I)
              = Complex.cos (-θ : ℂ) + Complex.sin (-θ : ℂ) * Complex.I := by
          simpa using (Complex.exp_mul_I (-θ : ℂ))
        -- Now simplify using `cos_neg` and `sin_neg` and collect terms.
        calc
          Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((-θ : ℂ) * Complex.I)
              =
            (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)
              - (Complex.cos (-θ : ℂ) + Complex.sin (-θ : ℂ) * Complex.I) := by
                rw [hpos, hneg]
          _ =
            (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I)
              - (Complex.cos (θ : ℂ) + (-Complex.sin (θ : ℂ)) * Complex.I) := by
                simp [Complex.cos_neg, Complex.sin_neg]
          _ = (2 : ℂ) * Complex.sin (θ : ℂ) * Complex.I := by
                ring
      have :
          Complex.exp (K * r) - Complex.exp (-(K * r))
            =
          (2 : ℂ) * Complex.sin (θ : ℂ) * Complex.I := by
        simpa [hKr, hKneg] using hθ
      -- Avoid heavy simp; just rewrite `sin` and finish.
      have this' := this
      -- `rw` avoids the recursion-depth blowup we hit with `simp`.
      rw [hsintheta] at this'
      exact this'
    -- Now divide by `K = 2π I t` and cancel `2` and `I`.
    -- We normalize the denominator to `(2 * π * t) * I`.
    have hK' : K = (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I := by
      -- `K = 2 * π * I * t`.
      simp [K, mul_assoc, mul_left_comm, mul_comm]
    calc
      (Complex.exp (K * r) - Complex.exp (-(K * r))) / K
          =
        ((2 : ℂ) * (Real.sin θ : ℂ) * Complex.I) / ((2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) * Complex.I) := by
            -- Rewrite numerator via `hnum` and denominator via `hK'` without `simp` unfolding.
            rw [hnum, hK']
      _ = (Real.sin θ : ℂ) / ((Real.pi : ℂ) * (t : ℂ)) := by
            field_simp [h2, hpi, htC, hI]
      _ = (Real.sin θ / (Real.pi * (t : ℝ)) : ℂ) := by
            -- Everything is real; convert back to a real division without triggering `simp` recursion.
            have ht_cast : (t : ℂ) = ((t : ℝ) : ℂ) := by
              norm_cast
            calc
              (Real.sin θ : ℂ) / ((Real.pi : ℂ) * (t : ℂ))
                  =
                (Real.sin θ : ℂ) / ((Real.pi : ℂ) * ((t : ℝ) : ℂ)) := by
                    -- Avoid `simp` recursion; a single rewrite reduces to reflexivity.
                    rw [ht_cast]
              _ =
                (Real.sin θ : ℂ) / ((Real.pi * (t : ℝ)) : ℂ) := by
                    -- regroup the denominator
                    -- `(π : ℂ) * (t : ℂ) = ((π*t) : ℂ)`
                    simpa using congrArg (fun z : ℂ => (Real.sin θ : ℂ) / z)
                      (Complex.ofReal_mul Real.pi (t : ℝ)).symm
              _ = (Real.sin θ / (Real.pi * (t : ℝ)) : ℂ) := by
                    simpa using (Complex.ofReal_div (Real.sin θ) (Real.pi * (t : ℝ))).symm
  -- Combine: integral = `exp(K*c)` times the sinc factor.
  calc
    (∫ x in (c - r)..(c + r), (fourier (T := (1 : ℝ)) t (x : UC) : ℂ))
        =
      (Complex.exp (K * (c + r)) - Complex.exp (K * (c - r))) / K := by
        simpa [hL, hInt]
    _ =
      Complex.exp (K * c) * ((Complex.exp (K * r) - Complex.exp (-(K * r))) / K) := by
        -- factor `exp(K*c)` using `exp_add` and `exp_sub`.
        have h1 : Complex.exp (K * (c + r)) = Complex.exp (K * c) * Complex.exp (K * r) := by
          -- `K*(c+r) = K*c + K*r` then `exp_add`
          have : K * (c + r) = K * c + K * r := by simpa [mul_add]
          -- rewrite and apply `exp_add`
          rw [this]
          simpa [Complex.exp_add, add_comm, add_left_comm, add_assoc, mul_assoc]
        have h2' : Complex.exp (K * (c - r)) = Complex.exp (K * c) * Complex.exp (-(K * r)) := by
          -- `K*(c-r) = K*c - K*r = K*c + (-(K*r))`, then apply `exp_add`.
          have hmulsub : K * (c - r) = K * c - K * r := by
            simpa [mul_sub]
          have hmulsub' : K * (c - r) = K * c + (-(K * r)) := by
            simpa [hmulsub, sub_eq_add_neg]
          rw [hmulsub']
          simpa [Complex.exp_add] using (Complex.exp_add (K * c) (-(K * r)))
        -- Rewrite the difference using `h1`/`h2'`, then factor `exp (K*c)` and move the division.
        rw [h1, h2']
        have hfac :
            Complex.exp (K * c) * Complex.exp (K * r) - Complex.exp (K * c) * Complex.exp (-(K * r))
              =
            Complex.exp (K * c) * (Complex.exp (K * r) - Complex.exp (-(K * r))) := by
          simpa using
            (mul_sub (Complex.exp (K * c)) (Complex.exp (K * r)) (Complex.exp (-(K * r)))).symm
        rw [hfac]
        simpa [mul_div_assoc, mul_assoc]
    _ =
      (fourier (T := (1 : ℝ)) t (c : UC) : ℂ)
        * (Real.sin (2 * Real.pi * (t : ℝ) * r) / (Real.pi * (t : ℝ)) : ℂ) := by
          simp [hcenter, hsinc]

private lemma intervalIntegral_arc_indicator_eq_sinc
    {X q a : ℕ} {Δ : ℝ}
    (hX : 2 ≤ X) (hq : 2 ≤ q) (ha : a ∈ Rcop q) (hΔ : Δ = (1 : ℝ))
    {t : ℤ} (ht : t ≠ 0) :
    (∫ α in (0 : ℝ)..(1 : ℝ),
        (arcSetTextbook X q a Δ).indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α)
      =
    (fourier (T := (1 : ℝ)) t ((a : ℝ) / (q : ℝ) : UC) : ℂ)
      * (Real.sin (2 * Real.pi * (t : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))))
          / (Real.pi * (t : ℝ)) : ℂ) := by
  -- First rewrite the indicator integral as an interval integral over the symmetric arc.
  have h0 :=
    intervalIntegral_arc_indicator_eq (X := X) (q := q) (a := a) (Δ := Δ) hX hq ha hΔ (t := t)
  -- Then evaluate that interval integral as a center phase times a sinc factor.
  -- The arc endpoints are `a/q ± Δ/(qX)`.
  -- (We use the `intervalIntegral_fourier_center` lemma.)
  have :=
    intervalIntegral_fourier_center (t := t) ht ((a : ℝ) / (q : ℝ)) (Δ / ((q : ℝ) * (X : ℝ)))
  -- Combine and simplify.
  simpa [hΔ, mul_assoc, mul_left_comm, mul_comm] using h0.trans this

private lemma norm_intervalIntegral_arc_indicator_q1_le
    {X : ℕ} {Δ : ℝ} (hX : 2 ≤ X) (hΔ : Δ = (1 : ℝ)) (t : ℤ) :
    ‖∫ α in (0 : ℝ)..(1 : ℝ),
        (arcSetTextbook X 1 0 Δ).indicator (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α‖
      ≤
    Δ / (X : ℝ) := by
  -- For `q=1,a=0`, on `[0,1]` the arc condition `|α| ≤ Δ/X` is equivalent (a.e.) to `α ≤ Δ/X`,
  -- so the indicator integral reduces to an integral on `0..(Δ/X)`.
  set r : ℝ := Δ / (X : ℝ)
  have hr0 : 0 ≤ r := by
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      have : (0 : ℕ) < X := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hX
      exact_mod_cast this
    have hΔ0 : 0 ≤ (Δ : ℝ) := by simpa [hΔ] using (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
    exact div_nonneg hΔ0 (le_of_lt hXpos)
  have hr1 : r ≤ 1 := by
    -- `Δ=1` and `X≥2` imply `r=1/X ≤ 1`.
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
      have : (1 : ℕ) ≤ X := le_trans (by decide : (1 : ℕ) ≤ 2) hX
      exact_mod_cast this
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      have : (0 : ℕ) < X := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hX
      exact_mod_cast this
    -- `r = Δ/X = 1/X`.
    have : r = (1 : ℝ) / (X : ℝ) := by simpa [r, hΔ]
    rw [this]
    simpa [one_div] using (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (1 : ℝ)) hX1)
  have hrIcc : r ∈ Set.Icc (0 : ℝ) (1 : ℝ) := ⟨hr0, hr1⟩
  -- Rewrite the indicator to `{x | x ≤ r}` on the integration interval.
  have hEqOn :
      Set.EqOn
        ((arcSetTextbook X 1 0 Δ).indicator
          (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)))
        (({x : ℝ | x ≤ r}).indicator
          (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)))
        (Set.uIcc (0 : ℝ) (1 : ℝ)) := by
    intro x hx
    have hx0 : 0 ≤ x := by simpa using hx.1
    -- On `x ≥ 0`, membership in `arcSetTextbook X 1 0 Δ` is equivalent to `x ≤ r`.
    have hxArc_iff : x ∈ arcSetTextbook X 1 0 Δ ↔ x ≤ r := by
      -- unfold the arc condition and use `abs_of_nonneg`.
      -- `arcSetTextbook X 1 0 Δ` is `|x| ≤ Δ/(1*X) = r`.
      have : x ∈ arcSetTextbook X 1 0 Δ ↔ |x - (0 : ℝ)| ≤ r := by
        simp [MajorArcStep24IntegralExtraction.arcSetTextbook, r, one_mul]
      -- simplify `|x-0| = |x| = x` since `x ≥ 0`
      simpa [abs_of_nonneg hx0] using this
    by_cases hxle : x ≤ r
    · have hxArc : x ∈ arcSetTextbook X 1 0 Δ := (hxArc_iff).2 hxle
      simp [hxArc, hxle]
    · have hxArc : x ∉ arcSetTextbook X 1 0 Δ := by
        intro hxArc
        exact hxle ((hxArc_iff).1 hxArc)
      simp [hxArc, hxle]
  have hRewrite :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          (arcSetTextbook X 1 0 Δ).indicator
            (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α)
        =
      ∫ α in (0 : ℝ)..(1 : ℝ),
        ({x : ℝ | x ≤ r}).indicator
          (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α := by
    -- change-of-integrand on the interval
    simpa using (intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) hEqOn)
  -- Now reduce to the shorter interval `0..r`.
  have hShort :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          ({x : ℝ | x ≤ r}).indicator
            (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α)
        =
      ∫ α in (0 : ℝ)..r, (fourier (T := (1 : ℝ)) t (α : UC) : ℂ) := by
    simpa using
      (intervalIntegral.integral_indicator (μ := volume) (a₁ := (0 : ℝ)) (a₂ := r) (a₃ := (1 : ℝ))
        (f := fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) hrIcc)
  -- Bound the short integral by `r` using `‖fourier‖=1`.
  have hnorm : ‖∫ α in (0 : ℝ)..r, (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)‖ ≤ |r| := by
    -- First bound by `1 * |r - 0|`, then simplify.
    have hnorm0 :
        ‖∫ α in (0 : ℝ)..r, (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)‖ ≤ (1 : ℝ) * |r - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := r) (C := (1 : ℝ))
        (f := fun α : ℝ => (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)) ?_
      intro x hx
      -- `‖fourier‖=1` on `AddCircle 1`.
      have : ‖(fourier (T := (1 : ℝ)) t (x : UC) : ℂ)‖ = (1 : ℝ) := by
        -- via the real additive character `e`
        rw [fourier_T1_coe_eq_e]
        simpa [MajorArcExponential.norm_e]
      exact le_of_eq this
    -- Simplify `1 * |r - 0| = |r|`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_neg] using hnorm0
  -- Put together.
  have hnorm' : ‖∫ α in (0 : ℝ)..r, (fourier (T := (1 : ℝ)) t (α : UC) : ℂ)‖ ≤ r := by
    simpa [abs_of_nonneg hr0] using hnorm
  -- Finally substitute back and transport the bound to the original `q=1` indicator integral.
  have hEqInt :
      (∫ α in (0 : ℝ)..(1 : ℝ),
          (arcSetTextbook X 1 0 Δ).indicator
            (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α)
        =
      ∫ α in (0 : ℝ)..r, (fourier (T := (1 : ℝ)) t (α : UC) : ℂ) := by
    exact hRewrite.trans hShort
  have : ‖∫ α in (0 : ℝ)..(1 : ℝ),
          (arcSetTextbook X 1 0 Δ).indicator
            (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α‖
        ≤ r := by
    -- Avoid `simp` here (it can unfold `fourier` into `cexp`); just rewrite the integral.
    rw [hEqInt]
    exact hnorm'
  simpa [r] using this

/-!
## Hybrid Step-5 split in `q` and Taylor remainder bound (q ≥ 13)

This section provides the deterministic “Step 5.2” resource lemma used by the generator-aligned
certificate plan:

* express `majorArcWeightFourier X 1 t` (for `t ≠ 0`) as:
  - a `q=1` boundary piece,
  - plus a finite sum over `q ≥ 2` of a Ramanujan sum `ramanujanSumZ q t` times a sinc factor;
* split the `q ≥ 13` part by Taylor linearization `sin y = y + (sin y - y)`;
* bound the remainder uniformly on the TT*/Toeplitz bandwidth.

This is intentionally “structure-preserving”: Ramanujan sums are kept intact in the linearized term.
Absolute values are taken only for the tiny remainder.
-/

private abbrev X0 : ℕ := Goldbach.BankParams.X0
private abbrev H : ℕ := Goldbach.BankParams.H

private lemma X0_pos : 0 < X0 := by
  -- `X0 = 10^6`.
  have : 0 < Goldbach.BankParams.X0 := by
    -- `10^6 > 0`
    simpa [Goldbach.BankParams.X0] using (pow_pos (by decide : (0 : ℕ) < 10) 6)
  simpa [X0] using this

private lemma Q0_ge_two : 2 ≤ Q0 := by
  -- `Q0 = 30000`.
  decide

private lemma Q0_ge_one : 1 ≤ Q0 := le_trans (by decide : (1 : ℕ) ≤ 2) Q0_ge_two

private lemma one_mem_Icc_Q0 : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) Q0 := by
  simp [Q0_ge_one]

private lemma two_mem_Icc_Q0 : (2 : ℕ) ∈ Finset.Icc (1 : ℕ) Q0 := by
  have : 2 ≤ Q0 := Q0_ge_two
  simp [this]

private lemma two_le_of_mem_Icc_two {q : ℕ} (hq : q ∈ Finset.Icc (2 : ℕ) Q0) : 2 ≤ q :=
  (Finset.mem_Icc.mp hq).1

private lemma le_Q0_of_mem_Icc_two {q : ℕ} (hq : q ∈ Finset.Icc (2 : ℕ) Q0) : q ≤ Q0 :=
  (Finset.mem_Icc.mp hq).2

private lemma two_le_of_mem_Icc_one {q : ℕ} (hq : q ∈ Finset.Icc (2 : ℕ) Q0) : 1 ≤ q :=
  le_trans (by decide : (1 : ℕ) ≤ 2) (two_le_of_mem_Icc_two hq)

private lemma cast_q_pos {q : ℕ} (hq : 1 ≤ q) : (0 : ℝ) < (q : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)

private lemma cast_X_pos {X : ℕ} (hX : 1 ≤ X) : (0 : ℝ) < (X : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)

/-- The sinc factor for the hard arc around `a/q` with radius `Δ/(qX)`. -/
noncomputable def sincFactor (X q : ℕ) (Δ : ℝ) (t : ℤ) : ℂ :=
  (Real.sin (2 * Real.pi * (t : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))))
      / (Real.pi * (t : ℝ)) : ℂ)

lemma sincFactor_eq (X q : ℕ) (Δ : ℝ) (t : ℤ) :
    sincFactor X q Δ t
      =
    (Real.sin (2 * Real.pi * (t : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))))
        / (Real.pi * (t : ℝ)) : ℂ) := by
  rfl

private noncomputable def arcIntegralFourier (X q a : ℕ) (Δ : ℝ) (t : ℤ) : ℂ :=
  ∫ α in (0 : ℝ)..(1 : ℝ),
    (arcSetTextbook X q a Δ).indicator
      (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α

private lemma arcIntegralFourier_eq (X q a : ℕ) (Δ : ℝ) (t : ℤ) :
    arcIntegralFourier X q a Δ t
      =
    ∫ α in (0 : ℝ)..(1 : ℝ),
      (arcSetTextbook X q a Δ).indicator
        (fun u : ℝ => (fourier (T := (1 : ℝ)) t (u : UC) : ℂ)) α := by
  rfl

noncomputable def q1Part (X : ℕ) (Δ : ℝ) (t : ℤ) : ℂ :=
  ∑ a ∈ Rcop 1, arcIntegralFourier X 1 a Δ t

lemma norm_q1Part_le (X : ℕ) (hX : 2 ≤ X) (Δ : ℝ) (hΔ : Δ = (1 : ℝ)) (t : ℤ) :
    ‖q1Part X Δ t‖ ≤ Δ / (X : ℝ) := by
  classical
  -- For `q=1`, `Rcop 1` is a singleton; still, a triangle inequality bound suffices.
  -- First bound each summand by `Δ/X`, then sum.
  have hterm :
      ∀ a ∈ Rcop 1,
        ‖arcIntegralFourier X 1 a Δ t‖ ≤ Δ / (X : ℝ) := by
    intro a ha
    -- In fact `a=0` on `Rcop 1`, but we only need the uniform bound.
    -- Use the already-proved `q=1` truncation bound (which is for `a=0`).
    -- Since `arcSetTextbook X 1 a Δ` is definitionaly the same set for all `a ∈ Rcop 1`,
    -- we can replace `a` by `0` by rewriting via the `Rcop` membership.
    -- (We keep it coarse and just bound by the `a=0` case.)
    -- NOTE: `arcSetTextbook X 1 a Δ` is `|α - a| ≤ Δ/X` and `a=0` in `Rcop 1`.
    have ha0 : a = 0 := by
      -- `a < 1` from `a ∈ range 1`, hence `a=0`.
      rcases Finset.mem_filter.mp ha with ⟨haRange, _⟩
      have : a < 1 := Finset.mem_range.mp haRange
      exact Nat.lt_one_iff.mp this
    subst ha0
    simpa [arcIntegralFourier_eq] using
      norm_intervalIntegral_arc_indicator_q1_le (X := X) (Δ := Δ) (hX := hX) (hΔ := hΔ) (t := t)
  have hsum := norm_sum_le (s := Rcop 1) (f := fun a => arcIntegralFourier X 1 a Δ t)
  have hsum' :
      (∑ a ∈ Rcop 1, ‖arcIntegralFourier X 1 a Δ t‖) ≤
        ∑ _a ∈ Rcop 1, (Δ / (X : ℝ)) := by
    exact Finset.sum_le_sum (fun a ha => hterm a ha)
  have hcard : (∑ _a ∈ Rcop 1, (Δ / (X : ℝ))) = (Rcop 1).card * (Δ / (X : ℝ)) := by
    simp [mul_comm, mul_left_comm, mul_assoc]
  have htot : (Rcop 1).card = 1 := by
    simpa [card_Rcop_eq_totient (q := (1 : ℕ))] using (show (Rcop (1 : ℕ)).card = Nat.totient 1 from
      card_Rcop_eq_totient (q := (1 : ℕ)))
  calc
    ‖q1Part X Δ t‖
        = ‖∑ a ∈ Rcop 1, arcIntegralFourier X 1 a Δ t‖ := by simp [q1Part]
    _ ≤ ∑ a ∈ Rcop 1, ‖arcIntegralFourier X 1 a Δ t‖ := hsum
    _ ≤ ∑ _a ∈ Rcop 1, (Δ / (X : ℝ)) := hsum'
    _ = (Rcop 1).card * (Δ / (X : ℝ)) := hcard
    _ = Δ / (X : ℝ) := by simp [htot]

private lemma sum_arcIntegralFourier_eq_ramanujan_mul_sinc
    {X q : ℕ} {Δ : ℝ} (hX : 2 ≤ X) (hq : 2 ≤ q) (hΔ : Δ = (1 : ℝ))
    {t : ℤ} (ht : t ≠ 0) :
    (∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t)
      =
    ramanujanSumZ q t * sincFactor X q Δ t := by
  classical
  -- Use the explicit arc integral evaluation for each `a`, then sum and factor.
  have hArc :
      ∀ a ∈ Rcop q,
        arcIntegralFourier X q a Δ t
          =
        (fourier (T := (1 : ℝ)) t ((a : ℝ) / (q : ℝ) : UC) : ℂ)
          * sincFactor X q Δ t := by
    intro a ha
    have h0 :=
      intervalIntegral_arc_indicator_eq_sinc (X := X) (q := q) (a := a) (Δ := Δ)
        (hX := hX) (hq := hq) (ha := ha) (hΔ := hΔ) (t := t) (ht := ht)
    -- unfold `arcIntegralFourier` and rewrite
    simpa [arcIntegralFourier, sincFactor, mul_assoc, mul_left_comm, mul_comm] using h0
  calc
    (∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t)
        = ∑ a ∈ Rcop q,
            (fourier (T := (1 : ℝ)) t ((a : ℝ) / (q : ℝ) : UC) : ℂ)
              * sincFactor X q Δ t := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            exact hArc a ha
    _ = (∑ a ∈ Rcop q, (fourier (T := (1 : ℝ)) t ((a : ℝ) / (q : ℝ) : UC) : ℂ))
            * sincFactor X q Δ t := by
            -- factor out the `a`-independent term
            simpa using
              (Finset.sum_mul (s := Rcop q)
                (f := fun a : ℕ => (fourier (T := (1 : ℝ)) t ((a : ℝ) / (q : ℝ) : UC) : ℂ))
                (a := sincFactor X q Δ t)).symm
    _ = (∑ a ∈ Rcop q, e ((t : ℝ) * ((a : ℝ) / (q : ℝ)))) * sincFactor X q Δ t := by
            have hfour :
                (∑ a ∈ Rcop q, (fourier (T := (1 : ℝ)) t ((a : ℝ) / (q : ℝ) : UC) : ℂ))
                  =
                ∑ a ∈ Rcop q, e ((t : ℝ) * ((a : ℝ) / (q : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro a _ha
              simpa using (fourier_T1_coe_eq_e t ((a : ℝ) / (q : ℝ)))
            -- rewrite the sum inside the product
            rw [hfour]
    _ = ramanujanSumZ q t * sincFactor X q Δ t := by
            -- `ramanujanSumZ` uses `e ((a*t)/q)`; commute multiplication inside the sum.
            have hsum :
                (∑ a ∈ Rcop q, e ((t : ℝ) * ((a : ℝ) / (q : ℝ))))
                  =
                ramanujanSumZ q t := by
              -- First rewrite `t*(a/q)` as `a*t/q`, then use the definition of `ramanujanSumZ`.
              have :
                  (∑ a ∈ Rcop q, e ((t : ℝ) * ((a : ℝ) / (q : ℝ))))
                    =
                  (∑ a ∈ Rcop q, e ((a : ℝ) * (t : ℝ) / (q : ℝ))) := by
                refine Finset.sum_congr rfl ?_
                intro a _ha
                -- commute multiplication inside `e`
                -- (avoid `simp` canceling a common factor and generating a disjunction)
                congr 1
                -- rewrite `/` as `* (·)⁻¹` and use commutativity/associativity in `ℝ`
                simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                  (by ac_rfl :
                    (t : ℝ) * ((a : ℝ) * (q : ℝ)⁻¹) =
                      ((a : ℝ) * (t : ℝ)) * (q : ℝ)⁻¹)
              simpa [ramanujanSumZ] using this
            -- Now rewrite and close by reflexivity.
            rw [hsum]

private lemma majorArcWeightFourier_eq_q1Part_add_sum_ramanujan_sinc
    (X : ℕ) {Δ : ℝ} (hsep : SepQ0 X Δ) (hX : 2 ≤ X) (hΔ : Δ = (1 : ℝ))
    {t : ℤ} (ht : t ≠ 0) :
    majorArcWeightFourier X Δ t
      =
    q1Part X Δ t
      +
    ∑ q ∈ Finset.Icc (2 : ℕ) Q0, ramanujanSumZ q t * sincFactor X q Δ t := by
  classical
  -- Start from Step-24 extraction.
  have hsum :=
    majorArcWeightFourier_eq_sum_arc_integrals (X := X) (Δ := Δ) (hsep := hsep) (t := t)
  -- Split `q=1` vs `q≥2`.
  -- Define the `q=1` fiber explicitly.
  have hq1 :
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t
        =
      (∑ a ∈ Rcop 1, arcIntegralFourier X 1 a Δ t)
        +
      ∑ q ∈ (Finset.Icc (1 : ℕ) Q0).erase 1, ∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t := by
    have hmem : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) Q0 := one_mem_Icc_Q0
    -- `sum_erase_add` gives the desired split (after reordering the summands).
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := Finset.Icc (1 : ℕ) Q0)
        (f := fun q : ℕ => ∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t) hmem).symm
  -- Rewrite the `erase 1` set as `Icc 2 Q0` (since `Q0 ≥ 2`).
  have herase :
      (Finset.Icc (1 : ℕ) Q0).erase 1 = Finset.Icc (2 : ℕ) Q0 := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_erase.mp hq with ⟨hqne, hqIcc⟩
      rcases Finset.mem_Icc.mp hqIcc with ⟨hq1, hqQ⟩
      have hq2 : 2 ≤ q := by
        -- from `1 ≤ q` and `q ≠ 1` in naturals.
        have : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hqne)
        exact Nat.succ_le_iff.mp this
      exact Finset.mem_Icc.mpr ⟨hq2, hqQ⟩
    · intro hq
      rcases Finset.mem_Icc.mp hq with ⟨hq2, hqQ⟩
      have hqne : q ≠ 1 := by
        intro h
        subst h
        exact Nat.not_succ_le_self 1 (show (2 : ℕ) ≤ 1 from hq2)
      exact Finset.mem_erase.mpr ⟨hqne, Finset.mem_Icc.mpr ⟨le_trans (by decide : (1 : ℕ) ≤ 2) hq2, hqQ⟩⟩
  -- Now expand `majorArcWeightFourier` using `hsum` and the split.
  have hMain :
      majorArcWeightFourier X Δ t
        =
      (∑ a ∈ Rcop 1, arcIntegralFourier X 1 a Δ t)
        +
      ∑ q ∈ Finset.Icc (2 : ℕ) Q0, ∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t := by
    -- rewrite `majorArcWeightFourier` as the double sum over arcs, then split q.
    -- Convert the integrand to `arcIntegralFourier`.
    have hsum' :
        majorArcWeightFourier X Δ t
          =
        ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t := by
      simpa [arcIntegralFourier] using hsum
    -- apply the split lemma `hq1` and rewrite `erase` as `Icc 2 Q0`.
    rw [hsum', hq1, herase]
  -- Evaluate each `q ≥ 2` fiber as a Ramanujan sum times the sinc factor.
  have hFiber :
      ∀ q ∈ Finset.Icc (2 : ℕ) Q0,
        (∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t)
          =
        ramanujanSumZ q t * sincFactor X q Δ t := by
    intro q hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    exact sum_arcIntegralFourier_eq_ramanujan_mul_sinc (X := X) (q := q) (Δ := Δ)
      (hX := hX) (hq := hq2) (hΔ := hΔ) (ht := ht)
  -- Put together and rename the `q=1` term.
  calc
    majorArcWeightFourier X Δ t
        =
      (∑ a ∈ Rcop 1, arcIntegralFourier X 1 a Δ t)
        +
      ∑ q ∈ Finset.Icc (2 : ℕ) Q0, ∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t := hMain
    _ =
      q1Part X Δ t
        +
      ∑ q ∈ Finset.Icc (2 : ℕ) Q0, ramanujanSumZ q t * sincFactor X q Δ t := by
      have hFiberSum :
          (∑ q ∈ Finset.Icc (2 : ℕ) Q0, ∑ a ∈ Rcop q, arcIntegralFourier X q a Δ t)
            =
          ∑ q ∈ Finset.Icc (2 : ℕ) Q0, ramanujanSumZ q t * sincFactor X q Δ t := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        exact hFiber q hq
      simpa [q1Part, hFiberSum]

noncomputable def qSmall : ℕ := 12
noncomputable def qLarge : ℕ := 13

lemma qSmall_lt_qLarge : qSmall < qLarge := by
  decide

lemma qLarge_le_Q0 : qLarge ≤ Q0 := by
  -- `13 ≤ 30000`.
  decide

lemma qSmall_le_Q0 : qSmall ≤ Q0 := by
  -- `12 ≤ 30000`.
  decide

noncomputable def AX (X : ℕ) (Δ : ℝ) (t : ℤ) : ℂ :=
  q1Part X Δ t
    +
  ∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q Δ t

noncomputable def LX (X : ℕ) (t : ℤ) : ℂ :=
  ((2 : ℝ) / (X : ℝ) : ℂ) *
    ∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ)

noncomputable def yqt (X q : ℕ) (Δ : ℝ) (t : ℤ) : ℝ :=
  2 * Real.pi * (t : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))

noncomputable def RX (X : ℕ) (Δ : ℝ) (t : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc qLarge Q0,
    ramanujanSumZ q t *
      ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)

lemma majorArcWeightFourier_eq_AX_add_LX_add_RX
    {X : ℕ} {Δ : ℝ} (hsep : SepQ0 X Δ) (hX : 2 ≤ X) (hΔ : Δ = (1 : ℝ))
    {t : ℤ} (ht : t ≠ 0) :
    majorArcWeightFourier X Δ t = AX X Δ t + LX X t + RX X Δ t := by
  classical
  -- Start from the `q=1` + `q≥2` sinc formula.
  have h0 :=
    majorArcWeightFourier_eq_q1Part_add_sum_ramanujan_sinc (X := X) (Δ := Δ)
      (hsep := hsep) (hX := hX) (hΔ := hΔ) (t := t) ht
  -- Split the `q≥2` sum into `q≤12` + `q≥13`.
  have hsplit :
      (∑ q ∈ Finset.Icc (2 : ℕ) Q0, ramanujanSumZ q t * sincFactor X q Δ t)
        =
      (∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q Δ t)
        +
      (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * sincFactor X q Δ t) := by
    -- Disjoint union decomposition:
    -- `Icc 2 Q0 = Icc 2 qSmall ∪ Icc qLarge Q0` with `qSmall = 12`, `qLarge = 13`.
    have hunion :
        Finset.Icc (2 : ℕ) Q0 =
          (Finset.Icc (2 : ℕ) qSmall) ∪ (Finset.Icc qLarge Q0) := by
      ext q
      constructor
      · intro hq
        rcases Finset.mem_Icc.mp hq with ⟨hq2, hqQ⟩
        by_cases hqS : q ≤ qSmall
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hq2, hqS⟩))
        · have hqSlt : qSmall < q := Nat.lt_of_not_ge hqS
          have hqL : qLarge ≤ q := by
            have : qSmall.succ ≤ q := Nat.succ_le_of_lt hqSlt
            simpa [qSmall, qLarge] using this
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_Icc.mpr ⟨hqL, hqQ⟩))
      · intro hq
        rcases Finset.mem_union.mp hq with hq | hq
        · rcases Finset.mem_Icc.mp hq with ⟨hq2, hqS⟩
          exact Finset.mem_Icc.mpr ⟨hq2, le_trans hqS qSmall_le_Q0⟩
        · rcases Finset.mem_Icc.mp hq with ⟨hqL, hqQ⟩
          exact Finset.mem_Icc.mpr ⟨le_trans (by decide : (2 : ℕ) ≤ qLarge) hqL, hqQ⟩
    have hdisj : Disjoint (Finset.Icc (2 : ℕ) qSmall) (Finset.Icc qLarge Q0) := by
      refine Finset.disjoint_left.2 ?_
      intro q hq1 hq2
      have hq_le : q ≤ qSmall := (Finset.mem_Icc.mp hq1).2
      have hq_ge : qLarge ≤ q := (Finset.mem_Icc.mp hq2).1
      exact (not_le_of_lt qSmall_lt_qLarge) (le_trans hq_ge hq_le)
    -- Rewrite using the disjoint union.
    -- Prefer explicit `Finset.sum` to avoid binder parsing issues in this toolchain snapshot.
    have :
        (∑ q ∈ Finset.Icc (2 : ℕ) Q0, ramanujanSumZ q t * sincFactor X q Δ t)
          =
        (∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q Δ t)
          +
        (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * sincFactor X q Δ t) := by
      -- `sum_union` after rewriting `Icc 2 Q0` as a disjoint union.
      -- Rewrite the LHS index set using `hunion`, then apply `Finset.sum_union`.
      rw [hunion]
      simpa using
        (Finset.sum_union (s₁ := Finset.Icc (2 : ℕ) qSmall) (s₂ := Finset.Icc qLarge Q0)
          (f := fun q => ramanujanSumZ q t * sincFactor X q Δ t) hdisj)
    simpa using this
  -- For the `q≥13` part, split `sin` into `y + (sin y - y)`.
  have hlin :
      (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * sincFactor X q Δ t)
        =
      LX X t + RX X Δ t := by
    -- Expand `sincFactor = sin(y)/(π t)` and use `sin(y) = y + (sin y - y)`.
    have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hden : (Real.pi * (t : ℝ)) ≠ 0 := mul_ne_zero hpi htR
    have hy :
        ∀ q ∈ Finset.Icc qLarge Q0,
          (Real.sin (yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ)
            =
          ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ)
            +
          ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ) := by
      intro q hq
      -- `yqt = 2π t * Δ/(qX)` so `yqt/(π t) = 2Δ/(qX) = 2/(qX)` since `Δ=1`.
      have hyqt_div :
          (yqt X q Δ t) / (Real.pi * (t : ℝ)) = (2 : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))) := by
        have ht0 : (t : ℝ) ≠ 0 := htR
        have hden0 : (Real.pi * (t : ℝ)) ≠ 0 := mul_ne_zero Real.pi_ne_zero ht0
        have hyqt' :
            yqt X q Δ t = (Real.pi * (t : ℝ)) * ((2 : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))) := by
          unfold yqt
          ring
        calc
          (yqt X q Δ t) / (Real.pi * (t : ℝ))
              =
            ((Real.pi * (t : ℝ)) * ((2 : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))))) / (Real.pi * (t : ℝ)) := by
              simp [hyqt']
          _ = (2 : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))) := by
              simpa using
                (mul_div_cancel_left₀ (b := (2 : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))) hden0)
      have hΔ1 : Δ = (1 : ℝ) := hΔ
      have hy' :
          ((yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ) = ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ) := by
        have hqpos : (q : ℝ) ≠ 0 := by
          have : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) (Finset.mem_Icc.mp hq).1
          exact_mod_cast (ne_of_gt (cast_q_pos this))
        have hXpos : (X : ℝ) ≠ 0 := by
          have : 1 ≤ X := le_trans (by decide : (1 : ℕ) ≤ 2) hX
          exact_mod_cast (ne_of_gt (cast_X_pos this))
        have hyqt_div_qX : (yqt X q Δ t) / (Real.pi * (t : ℝ)) = (2 : ℝ) / ((q : ℝ) * (X : ℝ)) := by
          simpa [hΔ1, div_eq_mul_inv, mul_assoc] using hyqt_div
        have hswap : (2 : ℝ) / ((q : ℝ) * (X : ℝ)) = (2 : ℝ) / (X : ℝ) / (q : ℝ) := by
          field_simp [hqpos, hXpos]
        have hyqt_div' : (yqt X q Δ t) / (Real.pi * (t : ℝ)) = (2 : ℝ) / (X : ℝ) / (q : ℝ) :=
          hyqt_div_qX.trans hswap
        exact_mod_cast hyqt_div'
      have hsplitR :
          Real.sin (yqt X q Δ t) / (Real.pi * (t : ℝ))
            =
          (yqt X q Δ t) / (Real.pi * (t : ℝ))
            + (Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) := by
        have hnumer :
            Real.sin (yqt X q Δ t) =
              (yqt X q Δ t) + (Real.sin (yqt X q Δ t) - (yqt X q Δ t)) := by
          ring
        calc
          Real.sin (yqt X q Δ t) / (Real.pi * (t : ℝ))
              = ((yqt X q Δ t) + (Real.sin (yqt X q Δ t) - (yqt X q Δ t))) / (Real.pi * (t : ℝ)) := by
                  simpa using
                    congrArg (fun s : ℝ => s / (Real.pi * (t : ℝ))) hnumer
          _ = (yqt X q Δ t) / (Real.pi * (t : ℝ))
                + (Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) := by
                  field_simp [hden]
      have hsplitC :
          (Real.sin (yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ)
            =
          ((yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ)
            + ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ) := by
        -- cast the real identity and distribute the cast across addition
        simpa using (congrArg (fun r : ℝ => (r : ℂ)) hsplitR)
      calc
        (Real.sin (yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ)
            = ((yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ)
                + ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ) := hsplitC
        _ = ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ)
                + ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ) := by
                  simpa [hy']
    -- Now sum.
    -- Rewrite `sincFactor` and use `hy` to split each summand.
    unfold LX RX
    -- We use commutativity of `ℂ` to rearrange factors.
    have :
        (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * sincFactor X q Δ t)
          =
        (∑ q ∈ Finset.Icc qLarge Q0,
            ramanujanSumZ q t * ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ))
          +
        (∑ q ∈ Finset.Icc qLarge Q0,
            ramanujanSumZ q t * ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)) := by
      -- Expand `sincFactor` and split termwise.
      have hterm :
          ∀ q ∈ Finset.Icc qLarge Q0,
            ramanujanSumZ q t * sincFactor X q Δ t
              =
            ramanujanSumZ q t * ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ)
              +
            ramanujanSumZ q t * ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ) := by
        intro q hq
        have : sincFactor X q Δ t =
            (Real.sin (yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ) := by
          simp [sincFactor, yqt]
        rw [this]
        -- apply `hy`
        have hyq := hy q hq
        -- multiply out (avoid `simp` commuting factors, which can trigger `mul_eq_mul_right_iff`)
        have hmul :
            ramanujanSumZ q t * (Real.sin (yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ)
              =
            ramanujanSumZ q t * ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ)
              +
            ramanujanSumZ q t * ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ) := by
          simpa [mul_add, mul_assoc] using
            (congrArg (fun z : ℂ => ramanujanSumZ q t * z) hyq)
        simpa [mul_assoc] using hmul
      -- Sum the termwise equalities.
      have hsum :
          (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * sincFactor X q Δ t)
            =
          ∑ q ∈ Finset.Icc qLarge Q0,
            (ramanujanSumZ q t * ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ)
              +
            ramanujanSumZ q t * ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)) := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        exact hterm q hq
      calc
        (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * sincFactor X q Δ t)
            =
          ∑ q ∈ Finset.Icc qLarge Q0,
            (ramanujanSumZ q t * ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ)
              +
            ramanujanSumZ q t * ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)) := hsum
        _ =
          (∑ q ∈ Finset.Icc qLarge Q0,
              ramanujanSumZ q t * ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ))
            +
          (∑ q ∈ Finset.Icc qLarge Q0,
              ramanujanSumZ q t * ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)) := by
          simp [Finset.sum_add_distrib]
    -- Pull out the global factor `2/X` in the first sum.
    -- `∑ ramanujan/q` is exactly the inner sum in `LX`.
    have hfirst :
        (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * ((2 : ℝ) / (X : ℝ) / (q : ℝ) : ℂ))
          =
        ((2 : ℝ) / (X : ℝ) : ℂ) * ∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t / (q : ℝ) := by
      -- factor `(2/X)` out of the sum
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Finset.mul_sum]
    -- finish
    rw [this, hfirst]
  -- Assemble the final identity.
  -- Start with `h0`, rewrite the `q≥2` sum using `hsplit`, then rewrite the `q≥13` part by `hlin`.
  calc
    majorArcWeightFourier X Δ t
        = q1Part X Δ t + (∑ q ∈ Finset.Icc (2 : ℕ) Q0, ramanujanSumZ q t * sincFactor X q Δ t) := h0
    _ = q1Part X Δ t
          + ((∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q Δ t)
              +
            (∑ q ∈ Finset.Icc qLarge Q0, ramanujanSumZ q t * sincFactor X q Δ t)) := by
          simpa [hsplit, add_assoc, add_left_comm, add_comm]
    _ = (q1Part X Δ t + ∑ q ∈ Finset.Icc (2 : ℕ) qSmall, ramanujanSumZ q t * sincFactor X q Δ t)
          + (LX X t + RX X Δ t) := by
          -- rewrite the `q≥13` sum using `hlin`
          rw [hlin]
          ac_rfl
    _ = AX X Δ t + LX X t + RX X Δ t := by
          simp [AX, add_assoc, add_left_comm, add_comm]

private lemma abs_yqt_le_one_of_band
    {X q : ℕ} {Δ : ℝ} (hX : X0 ≤ X) (hq : qLarge ≤ q) (t : ℤ) (ht : t.natAbs ≤ X + H)
    (hΔ : Δ = (1 : ℝ)) :
    |yqt X q Δ t| ≤ 1 := by
  -- Coarse bound:
  -- `|yqt| = 2π * |t| * (Δ/(qX)) ≤ 2π * (X+H) / (qX)`,
  -- then use `2π < 8`, `(X+H)/X ≤ 101/100` (since `X ≥ X0 = 10^6`), and `q ≥ 13`.
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have : 0 < X := lt_of_lt_of_le X0_pos hX
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) hq
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
  have ht_real : |(t : ℝ)| ≤ (X + H : ℝ) := by
    have ht_nat : (t.natAbs : ℝ) ≤ (X + H : ℝ) := by exact_mod_cast ht
    have habs_eq : (t.natAbs : ℝ) = |(t : ℝ)| := by
      calc
        (t.natAbs : ℝ) = (|t| : ℝ) := by simpa using (Nat.cast_natAbs (α := ℝ) t)
        _ = |(t : ℝ)| := by simpa using (Int.cast_abs (R := ℝ) (a := t))
    simpa [habs_eq] using ht_nat
  have hHX : (H : ℝ) ≤ (X : ℝ) / 100 := by
    have hX0leX : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have : (X0 : ℝ) / 100 ≤ (X : ℝ) / 100 :=
      div_le_div_of_nonneg_right hX0leX (by norm_num : (0 : ℝ) ≤ (100 : ℝ))
    have hHX0 : (H : ℝ) = (X0 : ℝ) / 100 := by
      -- `H = 10^4` and `X0 = 10^6`.
      have : (Goldbach.BankParams.H : ℝ) = (Goldbach.BankParams.X0 : ℝ) / 100 := by
        norm_num [Goldbach.BankParams.H, Goldbach.BankParams.X0]
      simpa [H, X0] using this
    exact le_trans (le_of_eq hHX0) this
  have hratio : ((X + H : ℕ) : ℝ) / (X : ℝ) ≤ (101 : ℝ) / 100 := by
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    have hHX' : (H : ℝ) / (X : ℝ) ≤ (1 : ℝ) / 100 := by
      have h1 : (H : ℝ) / (X : ℝ) ≤ ((X : ℝ) / 100) / (X : ℝ) := by
        exact div_le_div_of_nonneg_right hHX (le_of_lt hXpos)
      have hx : ((X : ℝ) / 100) / (X : ℝ) = (1 : ℝ) / 100 := by
        field_simp [hXne]
      simpa [hx] using h1
    calc
      ((X + H : ℕ) : ℝ) / (X : ℝ)
          = 1 + (H : ℝ) / (X : ℝ) := by
              calc
                ((X + H : ℕ) : ℝ) / (X : ℝ) = ((X : ℝ) + (H : ℝ)) / (X : ℝ) := by
                  simp [Nat.cast_add]
                _ = (X : ℝ) / (X : ℝ) + (H : ℝ) / (X : ℝ) := by simp [add_div]
                _ = 1 + (H : ℝ) / (X : ℝ) := by simp [div_self hXne]
      _ ≤ 1 + (1 : ℝ) / 100 := by nlinarith [hHX']
      _ = (101 : ℝ) / 100 := by norm_num
  have hpi_lt : Real.pi < 3.15 := by simpa using (Real.pi_lt_d2 : (Real.pi : ℝ) < 3.15)
  have h2pi_le : (2 * Real.pi : ℝ) ≤ (63 : ℝ) / 10 := by nlinarith [hpi_lt]
  have hq13 : (13 : ℝ) ≤ (q : ℝ) := by
    have : (13 : ℕ) ≤ q := le_trans (by decide : (13 : ℕ) ≤ qLarge) hq
    exact_mod_cast this
  -- Main estimate.
  have hΔ1 : Δ = (1 : ℝ) := hΔ
  have hqXpos : 0 < (q : ℝ) * (X : ℝ) := mul_pos hqpos hXpos
  have hy :
      |yqt X q Δ t|
        ≤ (2 * Real.pi) * ((X + H : ℕ) : ℝ) / ((q : ℝ) * (X : ℝ)) := by
    -- expand and use `|t| ≤ X+H`, `Δ=1`.
    have hΔdiv : 0 ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
      have : 0 ≤ (Δ : ℝ) := by simpa [hΔ1] using (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
      exact div_nonneg this (le_of_lt hqXpos)
    have h2pi0 : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    have hyqt_abs :
        |yqt X q Δ t| = (2 * Real.pi) * |(t : ℝ)| * (Δ / ((q : ℝ) * (X : ℝ))) := by
      have h2pi_abs : |(2 * Real.pi : ℝ)| = (2 * Real.pi : ℝ) := abs_of_nonneg h2pi0
      have hΔ_abs :
          |Δ / ((q : ℝ) * (X : ℝ))| = Δ / ((q : ℝ) * (X : ℝ)) := abs_of_nonneg hΔdiv
      have hmul_abs :
          |(2 * Real.pi) * (t : ℝ)| = (2 * Real.pi) * |(t : ℝ)| := by
        calc
          |(2 * Real.pi) * (t : ℝ)| = |(2 * Real.pi : ℝ)| * |(t : ℝ)| := by
            simp [abs_mul]
          _ = (2 * Real.pi) * |(t : ℝ)| := by
            simp [h2pi_abs]
      calc
        |yqt X q Δ t|
            = |(2 * Real.pi) * (t : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))| := by
                simp [yqt, mul_assoc]
          _ = |(2 * Real.pi) * (t : ℝ)| * |Δ / ((q : ℝ) * (X : ℝ))| := by
                  simp [abs_mul, mul_assoc]
          _ = ((2 * Real.pi) * |(t : ℝ)|) * (Δ / ((q : ℝ) * (X : ℝ))) := by
                  calc
                    |(2 * Real.pi) * (t : ℝ)| * |Δ / ((q : ℝ) * (X : ℝ))|
                        = ((2 * Real.pi) * |(t : ℝ)|) * |Δ / ((q : ℝ) * (X : ℝ))| := by
                          simpa [hmul_abs]
                    _ = ((2 * Real.pi) * |(t : ℝ)|) * (Δ / ((q : ℝ) * (X : ℝ))) := by
                          simpa [hΔ_abs]
          _ = (2 * Real.pi) * |(t : ℝ)| * (Δ / ((q : ℝ) * (X : ℝ))) := by
                  simp [mul_assoc]
    have ht' : |(t : ℝ)| ≤ ((X + H : ℕ) : ℝ) := by
      -- coerce `X+H` to ℝ and use `ht_real`.
      simpa [Nat.cast_add] using ht_real
    have hmult :
        (2 * Real.pi) * |(t : ℝ)| * (Δ / ((q : ℝ) * (X : ℝ)))
          ≤
        (2 * Real.pi) * ((X + H : ℕ) : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))) := by
      have hnonneg : 0 ≤ (Δ / ((q : ℝ) * (X : ℝ))) := hΔdiv
      have hraw :
          (2 * Real.pi) * (|(t : ℝ)| * (Δ / ((q : ℝ) * (X : ℝ))))
            ≤
          (2 * Real.pi) * (((X + H : ℕ) : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht' hnonneg) h2pi0
      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
    have hΔsimp : Δ / ((q : ℝ) * (X : ℝ)) = 1 / ((q : ℝ) * (X : ℝ)) := by
      simp [hΔ1]
    have hprod_eq_div :
        (2 * Real.pi) * ((X + H : ℕ) : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))
          =
        (2 * Real.pi) * ((X + H : ℕ) : ℝ) / ((q : ℝ) * (X : ℝ)) := by
      -- use `Δ=1` and rewrite `a * (1/(qX))` as `a/(qX)`
      simp [hΔsimp, div_eq_mul_inv, mul_assoc]
    have hy1 :
        |yqt X q Δ t|
          ≤ (2 * Real.pi) * ((X + H : ℕ) : ℝ) * (Δ / ((q : ℝ) * (X : ℝ))) := by
      simpa [hyqt_abs] using hmult
    exact le_trans hy1 (le_of_eq hprod_eq_div)
  -- Convert to a purely numeric bound.
  have hy_bound : |yqt X q Δ t| ≤ ((63 : ℝ) / 10) * ((101 : ℝ) / 100) * (1 / (13 : ℝ)) := by
    -- `|yqt| ≤ 2π * ((X+H)/X) * (1/q)`, then `2π ≤ 8`, `((X+H)/X) ≤ 101/100`, and `1/q ≤ 1/13`.
    have hratio' : ((X + H : ℕ) : ℝ) / (X : ℝ) ≤ (101 : ℝ) / 100 := hratio
    have hqinv : 1 / (q : ℝ) ≤ 1 / (13 : ℝ) := by
      have : (0 : ℝ) < (13 : ℝ) := by norm_num
      simpa using (one_div_le_one_div_of_le this hq13)
    have hx :
        ((X + H : ℕ) : ℝ) / ((q : ℝ) * (X : ℝ))
          ≤ (((101 : ℝ) / 100) * (1 / (13 : ℝ))) := by
      have hXne' : (X : ℝ) ≠ 0 := ne_of_gt hXpos
      have :
          ((X + H : ℕ) : ℝ) / ((q : ℝ) * (X : ℝ))
            = (((X + H : ℕ) : ℝ) / (X : ℝ)) * (1 / (q : ℝ)) := by
        field_simp [hXne', ne_of_gt hqpos]
      rw [this]
      exact mul_le_mul hratio' hqinv (by positivity) (by positivity)
    have hy' :
        |yqt X q Δ t|
          ≤ (2 * Real.pi) * (((101 : ℝ) / 100) * (1 / (13 : ℝ))) := by
      have hy0 : |yqt X q Δ t|
            ≤ (2 * Real.pi) * (((X + H : ℕ) : ℝ) / ((q : ℝ) * (X : ℝ))) := by
        simpa [div_eq_mul_inv, mul_assoc] using hy
      have h2pi0 : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
      have hy1 :
          (2 * Real.pi) * (((X + H : ℕ) : ℝ) / ((q : ℝ) * (X : ℝ)))
            ≤ (2 * Real.pi) * (((101 : ℝ) / 100) * (1 / (13 : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hx h2pi0
      exact le_trans hy0 hy1
    have h2pi0 : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    have : (2 * Real.pi) * (((101 : ℝ) / 100) * (1 / (13 : ℝ)))
          ≤ ((63 : ℝ) / 10) * (((101 : ℝ) / 100) * (1 / (13 : ℝ))) := by
      have hnonneg : 0 ≤ ((101 : ℝ) / 100) * (1 / (13 : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_right h2pi_le hnonneg
    exact le_trans hy' (by simpa [mul_assoc] using this)
  have hconst : ((63 : ℝ) / 10) * ((101 : ℝ) / 100) * (1 / (13 : ℝ)) ≤ 1 := by
    norm_num
  exact le_trans hy_bound hconst

lemma norm_RX_le_const_div_X
    {X : ℕ} {Δ : ℝ} (hX : X0 ≤ X) (hΔ : Δ = (1 : ℝ)) {t : ℤ}
    (ht0 : t ≠ 0) (htBand : t.natAbs ≤ X + H) :
    ‖RX X Δ t‖ ≤ (3 / 2 : ℝ) / (X : ℝ) := by
  classical
  -- Coarse uniform bound with the correct `q^{-2}` decay:
  -- `‖RX‖ ≤ ∑_{q≥13} ‖c_q(t)‖ * |sin y - y|/(π|t|)`,
  -- `‖c_q(t)‖ ≤ φ(q) ≤ q`,
  -- `|sin y - y| ≤ (7/32)|y|^3` for `|y|≤1`,
  -- `|y| = 2π|t|/(qX)` (since `Δ=1`),
  -- so each term is `O(|t|^2/(q^2 X^3))`, and `∑_{q≥13} 1/q^2 ≤ 2/13`.
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have : 0 < X := lt_of_lt_of_le X0_pos hX
    exact_mod_cast this
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht0
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  -- `|t| = natAbs t` in ℝ.
  have ht_abs : |(t : ℝ)| = (t.natAbs : ℝ) := by
    -- `Nat.cast_natAbs` gives `(t.natAbs : ℝ) = (|t| : ℝ)` and `Int.cast_abs` gives `(↑|t| : ℝ) = |(t:ℝ)|`.
    have : (t.natAbs : ℝ) = |(t : ℝ)| := by
      calc
        (t.natAbs : ℝ) = (|t| : ℝ) := by simpa using (Nat.cast_natAbs (α := ℝ) t)
        _ = |(t : ℝ)| := by simpa using (Int.cast_abs (R := ℝ) (a := t))
    exact this.symm
  -- Bound `|t| ≤ (101/100)X` from `t.natAbs ≤ X+H` and `X ≥ X0`.
  have ht_le : |(t : ℝ)| ≤ ((101 : ℝ) / 100) * (X : ℝ) := by
    have ht_nat : (t.natAbs : ℝ) ≤ (X + H : ℝ) := by exact_mod_cast htBand
    have ht1 : |(t : ℝ)| ≤ (X + H : ℝ) := by
      calc
        |(t : ℝ)| = (t.natAbs : ℝ) := ht_abs
        _ ≤ (X + H : ℝ) := ht_nat
    have hHle : (H : ℝ) ≤ (X : ℝ) / 100 := by
      have hX0leX : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have : (X0 : ℝ) / 100 ≤ (X : ℝ) / 100 :=
        div_le_div_of_nonneg_right hX0leX (by norm_num : (0 : ℝ) ≤ (100 : ℝ))
      have hHX0 : (H : ℝ) = (X0 : ℝ) / 100 := by
        have : (Goldbach.BankParams.H : ℝ) = (Goldbach.BankParams.X0 : ℝ) / 100 := by
          norm_num [Goldbach.BankParams.H, Goldbach.BankParams.X0]
        simpa [H, X0] using this
      exact le_trans (le_of_eq hHX0) this
    have hXH : (X + H : ℝ) ≤ (101 : ℝ) / 100 * (X : ℝ) := by
      have : (H : ℝ) ≤ (1 : ℝ) / 100 * (X : ℝ) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hHle
      nlinarith
    exact le_trans ht1 hXH
  -- `∑_{q=13..Q0} 1/q^2 ≤ 1/12`.
  have hsum_q :
      (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2) ≤ (1 : ℝ) / 12 := by
    have hsub : Finset.Icc qLarge Q0 ⊆ Finset.Ioo (12 : ℕ) (Q0 + 1) := by
      intro q hq
      rcases Finset.mem_Icc.mp hq with ⟨hqL, hqU⟩
      have hq12 : 12 < q := lt_of_lt_of_le (by decide : (12 : ℕ) < qLarge) hqL
      have hqU' : q < Q0 + 1 := Nat.lt_succ_of_le hqU
      simpa [Finset.mem_Ioo, hq12, hqU']
    have hnonneg : ∀ q : ℕ, 0 ≤ (1 : ℝ) / (q : ℝ) ^ 2 := by intro q; positivity
    have hle :
        (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2)
          ≤
        ∑ q ∈ Finset.Ioo (12 : ℕ) (Q0 + 1), (1 : ℝ) / (q : ℝ) ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro q _hq _hq'
      exact hnonneg q
    have hIoo :
        (∑ q ∈ Finset.Ioo (12 : ℕ) (Q0 + 1), (1 : ℝ) / (q : ℝ) ^ 2)
          ≤ (1 : ℝ) / 12 := by
      have hIoo_eq : (Finset.Ioo (12 : ℕ) (Q0 + 1)) = Finset.Ioc (12 : ℕ) Q0 := by
        ext q
        simp [Finset.mem_Ioo, Finset.mem_Ioc, Nat.lt_succ_iff]
      -- `sum_Ioc_inv_sq_le_sub` is stated in terms of `(q^2)⁻¹`.
      have hIoc :
          (∑ q ∈ Finset.Ioc (12 : ℕ) Q0, (1 : ℝ) / (q : ℝ) ^ 2)
            ≤ (1 : ℝ) / 12 - (1 : ℝ) / (Q0 : ℝ) := by
        have hraw :
            (∑ q ∈ Finset.Ioc (12 : ℕ) Q0, ((q : ℝ) ^ 2)⁻¹)
              ≤ ((12 : ℝ)⁻¹ - (Q0 : ℝ)⁻¹) := by
          have hk : (12 : ℕ) ≠ 0 := by decide
          have h12Q : (12 : ℕ) ≤ Q0 := by decide
          simpa using (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := (12 : ℕ)) (n := Q0) hk h12Q)
        have hrepl :
            (∑ q ∈ Finset.Ioc (12 : ℕ) Q0, (1 : ℝ) / (q : ℝ) ^ 2)
              =
            (∑ q ∈ Finset.Ioc (12 : ℕ) Q0, ((q : ℝ) ^ 2)⁻¹) := by
          refine Finset.sum_congr rfl ?_
          intro q _hq
          simp [one_div]
        have hrhs :
            ((12 : ℝ)⁻¹ - (Q0 : ℝ)⁻¹) = (1 : ℝ) / 12 - (1 : ℝ) / (Q0 : ℝ) := by
          simp [one_div]
        simpa [hrepl, hrhs] using hraw
      have hIoc_le : (1 : ℝ) / 12 - (1 : ℝ) / (Q0 : ℝ) ≤ (1 : ℝ) / 12 := by
        have : 0 ≤ (1 : ℝ) / (Q0 : ℝ) := by positivity
        linarith
      calc
        (∑ q ∈ Finset.Ioo (12 : ℕ) (Q0 + 1), (1 : ℝ) / (q : ℝ) ^ 2)
            =
          (∑ q ∈ Finset.Ioc (12 : ℕ) Q0, (1 : ℝ) / (q : ℝ) ^ 2) := by
            rw [hIoo_eq]
        _ ≤ (1 : ℝ) / 12 - (1 : ℝ) / (Q0 : ℝ) := hIoc
        _ ≤ (1 : ℝ) / 12 := hIoc_le
    exact le_trans hle hIoo
  -- Now bound `‖RX‖` by summing the pointwise `q^{-2}` estimate.
  have htri : ‖RX X Δ t‖ ≤
      ∑ q ∈ Finset.Icc qLarge Q0,
        ‖ramanujanSumZ q t *
          ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖ := by
    simpa [RX] using (norm_sum_le (s := Finset.Icc qLarge Q0)
      (f := fun q =>
        ramanujanSumZ q t *
          ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)))
  have hterm :
      ∀ q ∈ Finset.Icc qLarge Q0,
        ‖ramanujanSumZ q t *
          ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖
          ≤ (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 2 * (X : ℝ) ^ 3) := by
    intro q hq
    have hq13 : qLarge ≤ q := (Finset.mem_Icc.mp hq).1
    have hy1 : |yqt X q Δ t| ≤ 1 :=
      abs_yqt_le_one_of_band (X := X) (q := q) (Δ := Δ)
        (hX := hX) (hq := hq13) (t := t) (ht := htBand) (hΔ := hΔ)
    have hsin :
        |Real.sin (yqt X q Δ t) - yqt X q Δ t|
          ≤ (7 / 32 : ℝ) * |yqt X q Δ t| ^ 3 :=
      abs_sin_sub_le_seven_div_thirtyTwo_mul_abs_pow_three (x := yqt X q Δ t) hy1
    have hram : ‖ramanujanSumZ q t‖ ≤ (q : ℝ) := by
      have h1 : ‖ramanujanSumZ q t‖ ≤ (Nat.totient q : ℝ) := norm_ramanujanSumZ_le_totient q t
      have h2 : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.totient_le q)
      exact le_trans h1 h2
    have hnorm_re :
        ‖((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖
          =
        |Real.sin (yqt X q Δ t) - yqt X q Δ t| / (Real.pi * |(t : ℝ)|) := by
      -- This is a real scalar coerced to `ℂ`, so we can reduce to a real absolute value.
      -- (`Complex.norm_real` + `Real.norm_eq_abs` + `abs_div/abs_mul`.)
      have :
          ‖((Real.sin (yqt X q Δ t) - yqt X q Δ t) / (Real.pi * (t : ℝ)) : ℂ)‖
            =
          ‖(Real.sin (yqt X q Δ t) - yqt X q Δ t) / (Real.pi * (t : ℝ))‖ := by
        simpa using
          (Complex.norm_real ((Real.sin (yqt X q Δ t) - yqt X q Δ t) / (Real.pi * (t : ℝ))))
      -- Now expand norms/absolute values.
      -- `‖x‖ = |x|` on `ℝ`, and `|a / b| = |a| / |b|`.
      -- Also `|Real.pi| = Real.pi` since `0 < pi`.
      -- This yields the stated formula.
      simpa [this, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos, mul_assoc, mul_left_comm,
        mul_comm]
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have : 1 ≤ q := le_trans (by decide : (1 : ℕ) ≤ qLarge) hq13
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
    have hdenpos : 0 < Real.pi * |(t : ℝ)| := by
      have : 0 < |(t : ℝ)| := abs_pos.mpr htR
      nlinarith [Real.pi_pos, this]
    have h2pi0 : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
    have hyqt_abs :
        |yqt X q Δ t| = (2 * Real.pi) * |(t : ℝ)| / ((q : ℝ) * (X : ℝ)) := by
      have hΔ1 : Δ = (1 : ℝ) := hΔ
      have hqXpos : 0 < (q : ℝ) * (X : ℝ) := mul_pos hqpos hXpos
      have hΔdiv : 0 ≤ Δ / ((q : ℝ) * (X : ℝ)) := by
        have : 0 ≤ (Δ : ℝ) := by simpa [hΔ1] using (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
        exact div_nonneg this (le_of_lt hqXpos)
      -- expand `yqt`, take absolute values termwise, then simplify using `Δ=1` and positivity
      calc
        |yqt X q Δ t|
            = |(2 * Real.pi) * (t : ℝ) * (Δ / ((q : ℝ) * (X : ℝ)))| := by
                simp [yqt, mul_assoc]
        _ = |(2 * Real.pi) * (t : ℝ)| * |Δ / ((q : ℝ) * (X : ℝ))| := by
                simp [abs_mul, mul_assoc]
        _ = (2 * Real.pi) * |(t : ℝ)| * (Δ / ((q : ℝ) * (X : ℝ))) := by
                -- `2π ≥ 0` and `Δ/(qX) ≥ 0`, so their absolute values drop.
                have h2pi_abs : |(2 * Real.pi : ℝ)| = (2 * Real.pi : ℝ) := abs_of_nonneg h2pi0
                have hΔ_abs :
                    |Δ / ((q : ℝ) * (X : ℝ))| = Δ / ((q : ℝ) * (X : ℝ)) := abs_of_nonneg hΔdiv
                calc
                  |(2 * Real.pi) * (t : ℝ)| * |Δ / ((q : ℝ) * (X : ℝ))|
                      = (|(2 * Real.pi : ℝ)| * |(t : ℝ)|) * |Δ / ((q : ℝ) * (X : ℝ))| := by
                          simp [abs_mul, mul_assoc]
                  _ = ((2 * Real.pi) * |(t : ℝ)|) * (Δ / ((q : ℝ) * (X : ℝ))) := by
                          simp [h2pi_abs, hΔ_abs, mul_assoc]
                  _ = (2 * Real.pi) * |(t : ℝ)| * (Δ / ((q : ℝ) * (X : ℝ))) := by
                          simp [mul_assoc]
        _ = (2 * Real.pi) * |(t : ℝ)| / ((q : ℝ) * (X : ℝ)) := by
                -- use `Δ=1` to rewrite the remaining factor
                simp [hΔ1, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hrem :
        ‖((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖
          ≤ (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 3 * (X : ℝ) ^ 3) := by
      -- Apply Taylor remainder then substitute `hyqt_abs`.
      rw [hnorm_re]
      have h0 :
          |Real.sin (yqt X q Δ t) - yqt X q Δ t| / (Real.pi * |(t : ℝ)|)
            ≤ ((7 / 32 : ℝ) * |yqt X q Δ t| ^ 3) / (Real.pi * |(t : ℝ)|) := by
        exact div_le_div_of_nonneg_right hsin (le_of_lt hdenpos)
      have ht_abs_ne : (|(t : ℝ)|) ≠ 0 := abs_ne_zero.mpr htR
      have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
      have hX_ne : (X : ℝ) ≠ 0 := hXne
      have hden_ne : (Real.pi * |(t : ℝ)|) ≠ 0 := mul_ne_zero Real.pi_ne_zero ht_abs_ne
      -- Compute the RHS exactly from `hyqt_abs`.
      have hbound_eq :
          ((7 / 32 : ℝ) * |yqt X q Δ t| ^ 3) / (Real.pi * |(t : ℝ)|)
            =
          (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 3 * (X : ℝ) ^ 3) := by
        -- Expand `|yqt|` and simplify constants:
        -- `(7/32) * (2π)^3 / π = (7/4) * π^2`, and `(qX)^3 = q^3 X^3`.
        -- We keep the proof purely algebraic (`field_simp` + `ring`).
        -- First, rewrite using `hyqt_abs` (only in the goal).
        simp [hyqt_abs, div_eq_mul_inv, one_div]
        -- Now clear denominators and finish by algebra.
        field_simp [hq_ne, hX_ne, hden_ne, Real.pi_ne_zero]
        simp [sq_abs]
        ring
      have h1 :
          ((7 / 32 : ℝ) * |yqt X q Δ t| ^ 3) / (Real.pi * |(t : ℝ)|)
            ≤ (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 3 * (X : ℝ) ^ 3) := by
        exact le_of_eq hbound_eq
      exact le_trans h0 h1
    have hmul :
        ‖ramanujanSumZ q t *
          ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖
          ≤ (q : ℝ) * ((7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 3 * (X : ℝ) ^ 3)) := by
      have h0 :
          ‖ramanujanSumZ q t *
            ((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖
            ≤ ‖ramanujanSumZ q t‖ *
              ‖((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖ := by
        simpa using (norm_mul_le (ramanujanSumZ q t)
          (((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)))
      have h1 :
          ‖ramanujanSumZ q t‖ *
              ‖((Real.sin (yqt X q Δ t) - (yqt X q Δ t)) / (Real.pi * (t : ℝ)) : ℂ)‖
            ≤ (q : ℝ) * ((7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 3 * (X : ℝ) ^ 3)) := by
        exact mul_le_mul hram hrem (by positivity) (by positivity)
      exact le_trans h0 h1
    -- Simplify `q*(…/q^3) = …/q^2`.
    have hqpos' : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hsimp :
        (q : ℝ) * ((7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 3 * (X : ℝ) ^ 3))
          =
        (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 2 * (X : ℝ) ^ 3) := by
      field_simp [hqpos', hXne]
    simpa [hsimp] using le_trans hmul (le_of_eq hsimp)
  have hmain :
      ‖RX X Δ t‖ ≤
        (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((X : ℝ) ^ 3) *
          (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2) := by
    have h0 := le_trans htri (Finset.sum_le_sum (fun q hq => hterm q hq))
    -- Rewrite the sum as a constant times `∑ 1/q^2`.
    have hsum :
        (∑ q ∈ Finset.Icc qLarge Q0,
            (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 2 * (X : ℝ) ^ 3))
          =
        ((7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((X : ℝ) ^ 3)) *
          (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2) := by
      -- Termwise: `a/(q^2*X^3) = (a/X^3) * (1/q^2)`.
      classical
      have hterm' :
          ∀ q ∈ Finset.Icc qLarge Q0,
            (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 2 * (X : ℝ) ^ 3)
              =
            ((7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((X : ℝ) ^ 3)) *
              ((1 : ℝ) / (q : ℝ) ^ 2) := by
        intro q _hq
        -- Use `a/(b*c) = a/b * (1/c)` (no nonzero assumptions needed).
        -- Then commute to put the `q`-dependent factor on the right.
        simp [div_mul_eq_div_mul_one_div, div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm]
      -- Pull out the constant factor.
      calc
        (∑ q ∈ Finset.Icc qLarge Q0,
            (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((q : ℝ) ^ 2 * (X : ℝ) ^ 3))
            =
            ∑ q ∈ Finset.Icc qLarge Q0,
              (((7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((X : ℝ) ^ 3)) *
                ((1 : ℝ) / (q : ℝ) ^ 2)) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              simpa using hterm' q hq
        _ = ((7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / ((X : ℝ) ^ 3)) *
              (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2) := by
              simp [Finset.mul_sum]
    -- Conclude using `h0` and the rewritten sum.
    exact le_trans h0 (le_of_eq hsum)
  -- Final numeric bound: replace `|(t:ℝ)|` using `ht_le`, use the sharper `π < 3.15`,
  -- and the sharper `∑_{q=13..Q0} 1/q^2 ≤ 1/12`.
  have hpi2 : (Real.pi ^ 2 : ℝ) ≤ ((63 : ℝ) / 20) ^ 2 := by
    have hpi0 : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    have hpi_le : Real.pi ≤ (63 : ℝ) / 20 := by
      have hlt : Real.pi < (63 : ℝ) / 20 := by
        simpa [show (3.15 : ℝ) = (63 : ℝ) / 20 by norm_num] using (Real.pi_lt_d2 : (Real.pi : ℝ) < 3.15)
      exact le_of_lt hlt
    exact pow_le_pow_left₀ hpi0 hpi_le 2
  have ht2 : (|(t : ℝ)| ^ 2) ≤ (((101 : ℝ) / 100) ^ 2) * ((X : ℝ) ^ 2) := by
    nlinarith [ht_le]
  have : ‖RX X Δ t‖ ≤ (3 / 2 : ℝ) / (X : ℝ) := by
    have hXpos' : 0 < (X : ℝ) := hXpos
    have h0 :
        ‖RX X Δ t‖
          ≤ (4⁻¹ * (7 * (12⁻¹ * ((20⁻¹ * 63) ^ 2 * (100⁻¹ * 101) ^ 2)))) / (X : ℝ) := by
      have hS : (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2) ≤ (1 : ℝ) / 12 := hsum_q
      -- Apply the bounds directly to `hmain`.
      have hpi_part :
          (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / (X : ℝ) ^ 3
            ≤ (7 / 4 : ℝ) * (((63 : ℝ) / 20) ^ 2) * (((101 : ℝ) / 100) ^ 2) * ((X : ℝ) ^ 2) / (X : ℝ) ^ 3 := by
        have hconst_nonneg : 0 ≤ (7 / 4 : ℝ) := by norm_num
        have h1 :
            (7 / 4 : ℝ) * (Real.pi ^ 2) ≤ (7 / 4 : ℝ) * (((63 : ℝ) / 20) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hpi2 hconst_nonneg
        have h2 :
            (|(t : ℝ)| ^ 2) / (X : ℝ) ^ 3
              ≤ (((101 : ℝ) / 100) ^ 2) * ((X : ℝ) ^ 2) / (X : ℝ) ^ 3 := by
          exact div_le_div_of_nonneg_right ht2 (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ 3)
        have h2_nonneg : 0 ≤ (|(t : ℝ)| ^ 2) / (X : ℝ) ^ 3 := by positivity
        have h1'_nonneg : 0 ≤ (7 / 4 : ℝ) * (((63 : ℝ) / 20) ^ 2) := by positivity
        have h12 :
            ((7 / 4 : ℝ) * (Real.pi ^ 2)) * ((|(t : ℝ)| ^ 2) / (X : ℝ) ^ 3)
              ≤ ((7 / 4 : ℝ) * (((63 : ℝ) / 20) ^ 2)) *
                  ((((101 : ℝ) / 100) ^ 2) * ((X : ℝ) ^ 2) / (X : ℝ) ^ 3) := by
          exact mul_le_mul h1 h2 h2_nonneg h1'_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h12
      have hfinal :
          (7 / 4 : ℝ) * (Real.pi ^ 2) * (|(t : ℝ)| ^ 2) / (X : ℝ) ^ 3 *
              (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2)
            ≤
          (7 / 4 : ℝ) * (((63 : ℝ) / 20) ^ 2) * (((101 : ℝ) / 100) ^ 2) * ((X : ℝ) ^ 2) / (X : ℝ) ^ 3 * ((1 : ℝ) / 12) := by
        have hS_nonneg : 0 ≤ (∑ q ∈ Finset.Icc qLarge Q0, (1 : ℝ) / (q : ℝ) ^ 2) := by positivity
        have hpi_part_nonneg :
            0 ≤ (7 / 4 : ℝ) * (((63 : ℝ) / 20) ^ 2) * (((101 : ℝ) / 100) ^ 2) * ((X : ℝ) ^ 2) / (X : ℝ) ^ 3 := by
          positivity
        exact mul_le_mul hpi_part hS hS_nonneg hpi_part_nonneg
      have h1 := le_trans hmain hfinal
      -- Rearrange to match the claimed shape: the RHS simplifies to `C / X`.
      have hx : ((X : ℝ) ^ 2) * ((X : ℝ) ^ 3)⁻¹ = (X : ℝ)⁻¹ := by
        field_simp [hXne]
      have h1' :
          ‖RX X Δ t‖
            ≤ ((X : ℝ) ^ 2) * ((X : ℝ) ^ 3)⁻¹ *
                (4⁻¹ * (7 * (12⁻¹ * ((20⁻¹ * 63) ^ 2 * (100⁻¹ * 101) ^ 2)))) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h1
      have h1'' :
          ‖RX X Δ t‖
            ≤ (X : ℝ)⁻¹ *
                (4⁻¹ * (7 * (12⁻¹ * ((20⁻¹ * 63) ^ 2 * (100⁻¹ * 101) ^ 2)))) := by
        simpa [mul_assoc, hx] using h1'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h1''
    have hconst :
        (4⁻¹ * (7 * (12⁻¹ * ((20⁻¹ * 63) ^ 2 * (100⁻¹ * 101) ^ 2)))) ≤ (3 / 2 : ℝ) := by
      norm_num
    have h2 :
        (4⁻¹ * (7 * (12⁻¹ * ((20⁻¹ * 63) ^ 2 * (100⁻¹ * 101) ^ 2)))) / (X : ℝ)
          ≤ (3 / 2 : ℝ) / (X : ℝ) := by
      exact div_le_div_of_nonneg_right hconst (le_of_lt hXpos')
    exact le_trans h0 h2
  exact this

end
end Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarStep5WeightSplit
