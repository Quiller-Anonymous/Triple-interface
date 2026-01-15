import Goldbach.Cert.MajorArcModules.IntegralPipeline
import Goldbach.Cert.MajorArcModules.CoprimePreservingApprox
import Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0
import Goldbach.Cert.MajorArcStep8FejerKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
`MajorArcModules/BetaLocalization` provides small, reusable lemmas for handling the outer `β`
variable in the shifted-frequency major-arc integral.

The key technical issue is that the exponential-sum bounds (Steps 2–5/20–21) assume a *small*
real offset `β` (e.g. `|2πβ| ≤ 1`), while in the correlation integral the variable `β` is
integrated over `[0,1]` and represents a point on `AddCircle 1`.

The helper `betaRep` picks the standard representative in `[-1/2, 1/2]`.  This lets later steps
replace occurrences of `(β : UC)` by `(betaRep β : UC)` while keeping the `AddCircle` value
unchanged, and then reason about the size of the real number `betaRep β`.

This file intentionally does **not** provide any analytic decay/localization bounds yet; it only
sets up the stable bookkeeping layer needed to state them cleanly.
-/

namespace Goldbach.Cert.MajorArcModules.BetaLocalization

open scoped Interval

open Complex MeasureTheory AddCircle

open Goldbach
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.CoprimePreservingApprox
open Goldbach.Cert.MajorArcStep10RLSmoothIntegral

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

/-!
## A canonical real representative for `β : AddCircle 1`
-/

/--
Representative of a real `β` modulo `1`, chosen in `[-1/2, 1/2]`.

On the interval `β ∈ [0,1]`, this is `β` for `β ≤ 1/2` and `β-1` for `β > 1/2`.
-/
noncomputable def betaRep (β : ℝ) : ℝ :=
  if β ≤ ((2 : ℝ)⁻¹) then β else β - 1

lemma betaRep_eq_self_of_le {β : ℝ} (hβ : β ≤ ((2 : ℝ)⁻¹)) : betaRep β = β := by
  simp [betaRep, hβ]

lemma betaRep_eq_sub_one_of_gt {β : ℝ} (hβ : ((2 : ℝ)⁻¹) < β) : betaRep β = β - 1 := by
  have : ¬ β ≤ ((2 : ℝ)⁻¹) := not_le_of_gt hβ
  simp [betaRep, this]

lemma betaRep_coe_eq (β : ℝ) : ((betaRep β : ℝ) : UC) = (β : UC) := by
  by_cases hβ : β ≤ ((2 : ℝ)⁻¹)
  · simp [betaRep, hβ]
  · -- use periodicity: `(β - 1 : UC) = (β : UC)`
    have hper :
        (((β - 1 : ℝ) + (1 : ℝ) : ℝ) : AddCircle (1 : ℝ)) = ((β - 1 : ℝ) : AddCircle (1 : ℝ)) :=
      AddCircle.coe_add_period (p := (1 : ℝ)) (x := (β - 1 : ℝ))
    -- simplify `(β - 1) + 1 = β` and rewrite
    have hper' : ((β : ℝ) : UC) = ((β - 1 : ℝ) : UC) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper
    have : betaRep β = β - 1 := by simp [betaRep, hβ]
    -- goal is `(betaRep β : UC) = (β : UC)`
    simpa [this] using hper'.symm

lemma abs_betaRep_le_half {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    |betaRep β| ≤ ((2 : ℝ)⁻¹) := by
  by_cases hβ : β ≤ ((2 : ℝ)⁻¹)
  · -- `betaRep β = β ∈ [0,1/2]`
    have : betaRep β = β := by simp [betaRep, hβ]
    rw [this]
    have : |β| = β := abs_of_nonneg hβ0
    rw [this]
    exact hβ
  · -- `betaRep β = β-1 ∈ [-1/2,0]`
    have hβgt : ((2 : ℝ)⁻¹) < β := lt_of_not_ge hβ
    have hrep : betaRep β = β - 1 := by simp [betaRep, hβ]
    rw [hrep]
    have hle0 : β - 1 ≤ 0 := by linarith
    have habs : |β - 1| = -(β - 1) := abs_of_nonpos hle0
    rw [habs]
    have : -(β - 1) = 1 - β := by ring
    rw [this]
    have h1mβ_nonneg : 0 ≤ 1 - β := by linarith
    have h1mβ_le_half : 1 - β ≤ ((2 : ℝ)⁻¹) := by linarith
    -- `|β-1| = 1-β ≤ 1/2`
    exact h1mβ_le_half

/-!
## Rewriting shifted arguments using `betaRep`
-/

lemma coe_sub_betaRep (α β : ℝ) : ((α : UC) - (β : UC)) = ((α - betaRep β : ℝ) : UC) := by
  -- replace `(β : UC)` by `(betaRep β : UC)` and use `AddCircle.coe_sub`.
  have hβ : (β : UC) = ((betaRep β : ℝ) : UC) := by
    simpa using (betaRep_coe_eq β).symm
  calc
    (α : UC) - (β : UC) = (α : UC) - ((betaRep β : ℝ) : UC) := by simpa [hβ]
    _ = ((α - betaRep β : ℝ) : UC) := by
          simpa using (AddCircle.coe_sub (p := (1 : ℝ)) α (betaRep β)).symm

lemma coe_add_betaRep (α β : ℝ) : ((α : UC) + (β : UC)) = ((α + betaRep β : ℝ) : UC) := by
  have hβ : (β : UC) = ((betaRep β : ℝ) : UC) := by
    simpa using (betaRep_coe_eq β).symm
  calc
    (α : UC) + (β : UC) = (α : UC) + ((betaRep β : ℝ) : UC) := by simpa [hβ]
    _ = ((α + betaRep β : ℝ) : UC) := by
          simpa using (AddCircle.coe_add (p := (1 : ℝ)) α (betaRep β)).symm

/-!
### A convenient identity for the “minus” shifted argument

In the shifted-frequency integrand we see both `(α : UC) + (β : UC)` and `(α : UC) - (β : UC)`.
For certificate bookkeeping it is often convenient to treat the “minus” term as an “add” term by
passing to `1 - β`, using the fact that `AddCircle 1` quotients by integer shifts.
-/

lemma coe_sub_eq_add_one_sub (α β : ℝ) :
    ((α : UC) - (β : UC)) = (α : UC) + ((1 - β : ℝ) : UC) := by
  have hsub : ((α : UC) - (β : UC)) = ((α - β : ℝ) : UC) := by
    simpa using (AddCircle.coe_sub (p := (1 : ℝ)) α β).symm
  have hper :
      ((α - β : ℝ) : UC) = ((α + (1 - β) : ℝ) : UC) := by
    -- `(α - β) + 1 = α + (1 - β)` and adding `1` is a period in `AddCircle 1`.
    have h :
        (((α - β : ℝ) + (1 : ℝ) : ℝ) : UC) = ((α - β : ℝ) : UC) :=
      AddCircle.coe_add_period (p := (1 : ℝ)) (x := (α - β : ℝ))
    have hre : (α - β : ℝ) + (1 : ℝ) = α + (1 - β) := by ring
    have h' : ((α + (1 - β) : ℝ) : UC) = ((α - β : ℝ) : UC) := by
      simpa [hre] using h
    exact h'.symm
  calc
    ((α : UC) - (β : UC)) = ((α - β : ℝ) : UC) := hsub
    _ = ((α + (1 - β) : ℝ) : UC) := hper
    _ = (α : UC) + ((1 - β : ℝ) : UC) := by
          simpa using (AddCircle.coe_add (p := (1 : ℝ)) α (1 - β))

/-!
## A smallness wrapper for later major-arc steps
-/

lemma abs_two_pi_mul_betaRep_le_one_of_abs_le
    {β : ℝ} (hβ : |betaRep β| ≤ (1 / (2 * Real.pi) : ℝ)) :
    |2 * Real.pi * betaRep β| ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have htwoPi : 0 < (2 * Real.pi : ℝ) := by nlinarith
  -- `|2π * r| = (2π) * |r|` (avoid `simp`'s attempts to split `2π` further).
  have habs : |2 * Real.pi * betaRep β| = (2 * Real.pi) * |betaRep β| := by
    have hnonneg : 0 ≤ (2 * Real.pi : ℝ) := le_of_lt htwoPi
    calc
      |2 * Real.pi * betaRep β|
          = |(2 * Real.pi : ℝ) * betaRep β| := by ring
      _ = |(2 * Real.pi : ℝ)| * |betaRep β| := by simp [abs_mul]
      _ = (2 * Real.pi) * |betaRep β| := by simp [abs_of_nonneg hnonneg]
  rw [habs]
  -- multiply the hypothesis by the positive constant `2π`
  have := mul_le_mul_of_nonneg_left hβ (le_of_lt htwoPi)
  -- simplify `(2π) * (1/(2π)) = 1`
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this

/-!
## Smallness lemmas for shifted offsets

Steps 2–5/20–21 assume a “small arc” hypothesis of the form `|2πβ| ≤ 1`. When applying those
results to shifted arguments `(α ± β) - a/q`, it is convenient to use a symmetric “half-budget”
`|2π·| ≤ 1/2` for each summand and then combine them by the triangle inequality.
-/

noncomputable def betaSmallRadius : ℝ := (1 : ℝ) / (4 * Real.pi)

lemma betaSmallRadius_pos : 0 < betaSmallRadius := by
  have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
  have hden : 0 < (4 * Real.pi : ℝ) := by nlinarith
  simpa [betaSmallRadius] using (one_div_pos.2 hden)

lemma abs_two_pi_mul_le_half_of_abs_le {β : ℝ} (hβ : |β| ≤ betaSmallRadius) :
    |2 * Real.pi * β| ≤ ((2 : ℝ)⁻¹) := by
  have htwoPi : 0 < (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
  have habs : |2 * Real.pi * β| = (2 * Real.pi) * |β| := by
    have hnonneg : 0 ≤ (2 * Real.pi : ℝ) := le_of_lt htwoPi
    calc
      |2 * Real.pi * β| = |(2 * Real.pi : ℝ) * β| := by ring
      _ = |(2 * Real.pi : ℝ)| * |β| := by simp [abs_mul]
      _ = (2 * Real.pi) * |β| := by simp [abs_of_nonneg hnonneg]
  rw [habs]
  have hmul := mul_le_mul_of_nonneg_left hβ (le_of_lt htwoPi)
  -- `(2π) * (1/(4π)) = 1/2`
  have hconst : (2 * Real.pi : ℝ) * betaSmallRadius = ((2 : ℝ)⁻¹) := by
    have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    -- keep `simp` localized; avoid global `field_simp` rewriting too much.
    unfold betaSmallRadius
    field_simp [hpi0]
    ring
  exact le_trans hmul (le_of_eq hconst)

lemma abs_two_pi_mul_betaRep_le_half_of_abs_le
    {β : ℝ} (hβ : |betaRep β| ≤ betaSmallRadius) :
    |2 * Real.pi * betaRep β| ≤ ((2 : ℝ)⁻¹) :=
  abs_two_pi_mul_le_half_of_abs_le (β := betaRep β) hβ

lemma abs_two_pi_mul_add_le_one_of_le_half
    {x y : ℝ} (hx : |2 * Real.pi * x| ≤ ((2 : ℝ)⁻¹)) (hy : |2 * Real.pi * y| ≤ ((2 : ℝ)⁻¹)) :
    |2 * Real.pi * (x + y)| ≤ 1 := by
  -- `2π(x+y) = (2πx) + (2πy)` and `|a+b| ≤ |a|+|b|`.
  have hrewrite : 2 * Real.pi * (x + y) = (2 * Real.pi * x) + (2 * Real.pi * y) := by ring
  have htri :
      |(2 * Real.pi * x) + (2 * Real.pi * y)|
        ≤ |2 * Real.pi * x| + |2 * Real.pi * y| := by
      simpa using (abs_add_le (2 * Real.pi * x) (2 * Real.pi * y))
  calc
    |2 * Real.pi * (x + y)|
        = |(2 * Real.pi * x) + (2 * Real.pi * y)| := by simpa [hrewrite]
    _ ≤ |2 * Real.pi * x| + |2 * Real.pi * y| := htri
    _ ≤ ((2 : ℝ)⁻¹) + ((2 : ℝ)⁻¹) := add_le_add hx hy
    _ = 1 := by norm_num

lemma abs_two_pi_mul_sub_le_one_of_le_half
    {x y : ℝ} (hx : |2 * Real.pi * x| ≤ ((2 : ℝ)⁻¹)) (hy : |2 * Real.pi * y| ≤ ((2 : ℝ)⁻¹)) :
    |2 * Real.pi * (x - y)| ≤ 1 := by
  -- `x - y = x + (-y)` and `|2π(-y)| = |2πy|`.
  have hy' : |2 * Real.pi * (-y)| ≤ ((2 : ℝ)⁻¹) := by simpa [mul_assoc] using hy
  simpa [sub_eq_add_neg] using (abs_two_pi_mul_add_le_one_of_le_half (x := x) (y := -y) hx hy')

lemma abs_two_pi_mul_sub_rat_le_half_of_arcSetTextbook
    {X q a : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α : ℝ} (hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ) :
    |2 * Real.pi * (α - (a : ℝ) / (q : ℝ))| ≤ ((2 : ℝ)⁻¹) := by
  -- Start from the defining distance bound on the arc.
  have hdist :
      |α - (a : ℝ) / (q : ℝ)| ≤ Δ / ((q : ℝ) * (X : ℝ)) := hα
  have hXposR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have htwoPi_nonneg : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]

  -- Multiply the distance bound by `2π`.
  have hmul1 :
      |2 * Real.pi * (α - (a : ℝ) / (q : ℝ))|
        ≤ (2 * Real.pi) * (Δ / ((q : ℝ) * (X : ℝ))) := by
    have habs :
        |2 * Real.pi * (α - (a : ℝ) / (q : ℝ))|
          = (2 * Real.pi) * |α - (a : ℝ) / (q : ℝ)| := by
      simpa [abs_of_nonneg htwoPi_nonneg, mul_assoc] using
        (abs_mul (2 * Real.pi : ℝ) (α - (a : ℝ) / (q : ℝ)))
    have := mul_le_mul_of_nonneg_left hdist htwoPi_nonneg
    simpa [habs] using this

  -- Use `q ≥ 1` to drop the `q` from the denominator.
  have hqX_ge : (X : ℝ) ≤ (q : ℝ) * (X : ℝ) := by
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := le_of_lt hXposR
    nlinarith [hqge1, hX0]
  have hdiv_le : Δ / ((q : ℝ) * (X : ℝ)) ≤ Δ / (X : ℝ) := by
    -- larger denominator -> smaller quotient
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (div_le_div_of_nonneg_left hΔ hXposR hqX_ge)
  have hmul2 :
      (2 * Real.pi) * (Δ / ((q : ℝ) * (X : ℝ))) ≤ (2 * Real.pi) * (Δ / (X : ℝ)) :=
    mul_le_mul_of_nonneg_left hdiv_le htwoPi_nonneg

  -- From `4πΔ ≤ X` derive `(2π) * (Δ / X) ≤ 1/2`.
  have hmain :
      (2 * Real.pi) * (Δ / (X : ℝ)) ≤ ((2 : ℝ)⁻¹) := by
    have hmul :=
        mul_le_mul_of_nonneg_right hXΔ (le_of_lt (inv_pos.2 hXposR))
    have hright : (X : ℝ) * (X : ℝ)⁻¹ = (1 : ℝ) := by simp [hXposR.ne']
    have hleft :
        (4 * Real.pi * Δ) * (X : ℝ)⁻¹ = (4 * Real.pi) * (Δ / (X : ℝ)) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have h4 :
        (4 * Real.pi) * (Δ / (X : ℝ)) ≤ (1 : ℝ) := by
      simpa [hleft, hright, div_eq_mul_inv] using hmul
    have hhalf : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) := by norm_num
    have h4' := mul_le_mul_of_nonneg_left h4 hhalf
    -- Simplify the left factor: `(1/2) * (4 * t) = 2 * t`.
    have h4'' : Real.pi * (Δ / (X : ℝ) * ((2 : ℝ)⁻¹ * 4)) ≤ ((2 : ℝ)⁻¹) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h4'
    have hconst : ((2 : ℝ)⁻¹) * (4 : ℝ) = (2 : ℝ) := by norm_num
    have h4''' : Real.pi * (Δ / (X : ℝ) * (2 : ℝ)) ≤ ((2 : ℝ)⁻¹) := by
      simpa [hconst] using h4''
    -- Now reassociate to `2π * (Δ/X)`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using h4'''

  exact le_trans hmul1 (le_trans hmul2 hmain)

/-!
## Splitting the β-integral by an explicit “small β” set
-/

noncomputable def betaSmallSet : Set ℝ :=
  Set.Icc (-betaSmallRadius) betaSmallRadius

lemma measurableSet_betaSmallSet : MeasurableSet betaSmallSet :=
  measurableSet_Icc

lemma abs_two_pi_mul_sub_rat_add_beta_le_one_of_arcSetTextbook_of_mem_betaSmallSet
    {X q a : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ)
    (hβ : β ∈ betaSmallSet) :
    |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + β)| ≤ 1 := by
  have hx :
      |2 * Real.pi * (α - (a : ℝ) / (q : ℝ))| ≤ ((2 : ℝ)⁻¹) :=
    abs_two_pi_mul_sub_rat_le_half_of_arcSetTextbook
      (X := X) (q := q) (a := a) (Δ := Δ) hΔ hXpos hq hXΔ hα
  have hβ' : -betaSmallRadius ≤ β ∧ β ≤ betaSmallRadius := by
    simpa [betaSmallSet] using hβ
  have habsβ : |β| ≤ betaSmallRadius := (abs_le).2 hβ'
  have hy : |2 * Real.pi * β| ≤ ((2 : ℝ)⁻¹) := abs_two_pi_mul_le_half_of_abs_le (β := β) habsβ
  simpa using
    (abs_two_pi_mul_add_le_one_of_le_half (x := (α - (a : ℝ) / (q : ℝ))) (y := β) hx hy)

lemma abs_two_pi_mul_sub_rat_sub_beta_le_one_of_arcSetTextbook_of_mem_betaSmallSet
    {X q a : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ)
    (hβ : β ∈ betaSmallSet) :
    |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) - β)| ≤ 1 := by
  have hx :
      |2 * Real.pi * (α - (a : ℝ) / (q : ℝ))| ≤ ((2 : ℝ)⁻¹) :=
    abs_two_pi_mul_sub_rat_le_half_of_arcSetTextbook
      (X := X) (q := q) (a := a) (Δ := Δ) hΔ hXpos hq hXΔ hα
  have hβ' : -betaSmallRadius ≤ β ∧ β ≤ betaSmallRadius := by
    simpa [betaSmallSet] using hβ
  have habsβ : |β| ≤ betaSmallRadius := (abs_le).2 hβ'
  have hy : |2 * Real.pi * β| ≤ ((2 : ℝ)⁻¹) := abs_two_pi_mul_le_half_of_abs_le (β := β) habsβ
  simpa using
    (abs_two_pi_mul_sub_le_one_of_le_half (x := (α - (a : ℝ) / (q : ℝ))) (y := β) hx hy)

/-!
## Coprime-preserving rational shifts for arbitrary `β ∈ [0,1]`

For bounding shifted exponential sums at phases `(α : UC) ± (β : UC)`, one sometimes wants to
rewrite `β` as `β' + z/q` so that:
- the residual `β' = β - z/q` satisfies a smallness hypothesis, and
- the shifted numerator `a+z` stays coprime to `q` (so we can reuse “reduced residue” machinery).

The actual existence of such a `z` is delegated to the bounded-shift oracle
`CoprimeShiftBound q K` (from `MajorArcModules/CoprimePreservingApprox`).

Important sign note:
to control both `(α : UC) + (β : UC)` and `(α : UC) - (β : UC)` while **preserving coprimality**
with the *same* modulus `q`, it is often cleaner to handle the “minus” term via
`coe_sub_eq_add_one_sub` and approximate `1-β` separately.
-/

theorem exists_coprime_shift_small_offsets_of_arcSetTextbook_plus_minus
    {X q a K : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hqK : 8 * (2 * K + 1) ≤ q)
    (hShift : Goldbach.Cert.MajorArcModules.CoprimePreservingApprox.CoprimeShiftBound q K) :
    ∃ zPlus zMinus : ℕ,
      Nat.Coprime (a + zPlus) q ∧
      Nat.Coprime (a + zMinus) q ∧
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + (β - (zPlus : ℝ) / (q : ℝ)))| ≤ 1 ∧
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + ((1 - β) - (zMinus : ℝ) / (q : ℝ)))| ≤ 1 := by
  have hx :
      |2 * Real.pi * (α - (a : ℝ) / (q : ℝ))| ≤ ((2 : ℝ)⁻¹) :=
    abs_two_pi_mul_sub_rat_le_half_of_arcSetTextbook
      (X := X) (q := q) (a := a) (Δ := Δ) hΔ hXpos hq hXΔ hα
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq

  -- Approximate `β` by `zPlus/q` while preserving coprimality of `a+zPlus`.
  rcases
    Goldbach.Cert.MajorArcModules.CoprimePreservingApprox.CoprimeShiftBound.exists_coprime_shift_abs_two_pi_mul_le_half
      (q := q) (K := K) hqpos hqK hShift (a := a) ha (β := β) hβ0 hβ1
      with ⟨zPlus, hzPlusC, hyPlus⟩

  -- Approximate `1-β` by `zMinus/q` while preserving coprimality of `a+zMinus`.
  have h1mβ0 : 0 ≤ (1 - β) := by linarith
  have h1mβ1 : (1 - β) ≤ 1 := by linarith
  rcases
    Goldbach.Cert.MajorArcModules.CoprimePreservingApprox.CoprimeShiftBound.exists_coprime_shift_abs_two_pi_mul_le_half
      (q := q) (K := K) hqpos hqK hShift (a := a) ha (β := (1 - β)) h1mβ0 h1mβ1
      with ⟨zMinus, hzMinusC, hyMinus⟩

  refine ⟨zPlus, zMinus, hzPlusC, hzMinusC, ?_, ?_⟩
  · -- plus phase: `(α - a/q) + (β - zPlus/q)` has `|2π⋅| ≤ 1` by the half-budget split
    simpa [add_assoc, add_comm, add_left_comm] using
      (abs_two_pi_mul_add_le_one_of_le_half
        (x := (α - (a : ℝ) / (q : ℝ))) (y := (β - (zPlus : ℝ) / (q : ℝ))) hx hyPlus)
  · -- minus phase handled as `α + (1-β)` (same half-budget split)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (abs_two_pi_mul_add_le_one_of_le_half
        (x := (α - (a : ℝ) / (q : ℝ))) (y := ((1 - β) - (zMinus : ℝ) / (q : ℝ))) hx hyMinus)

/--
`Q0`-specialized wrapper for `exists_coprime_shift_small_offsets_of_arcSetTextbook_plus_minus`:
discharges the bounded-shift oracle using `CoprimeShiftBoundQ0`.
-/
theorem exists_coprime_shift_small_offsets_of_arcSetTextbook_plus_minus_of_le_Q0
    {X q a : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hqQ0 : q ≤ Goldbach.AO_OffDiag.TailBlock.Q0)
    (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hqK :
      8 * (2 * Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.K_coprimeShift + 1) ≤ q) :
    ∃ zPlus zMinus : ℕ,
      Nat.Coprime (a + zPlus) q ∧
      Nat.Coprime (a + zMinus) q ∧
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + (β - (zPlus : ℝ) / (q : ℝ)))| ≤ 1 ∧
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + ((1 - β) - (zMinus : ℝ) / (q : ℝ)))| ≤ 1 := by
  have hShift :
      Goldbach.Cert.MajorArcModules.CoprimePreservingApprox.CoprimeShiftBound q
        Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.K_coprimeShift :=
    Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.coprimeShiftBound_of_le_Q0
      (q := q) hq hqQ0
  simpa using
    (exists_coprime_shift_small_offsets_of_arcSetTextbook_plus_minus
      (X := X) (q := q) (a := a) (K := Goldbach.Cert.MajorArcModules.CoprimeShiftBoundQ0.K_coprimeShift)
      (Δ := Δ) hΔ hXpos hq hXΔ hα ha hβ0 hβ1 hqK hShift)

/--
Corollary of `exists_coprime_shift_small_offsets_of_arcSetTextbook_plus_minus` that explicitly
packages the two “small offsets” in the exact `β + a/q` form used by Step 20/21 style bounds.

The second identity targets the representative `α + (1-β)` (which equals `α-β` in `AddCircle 1`).
-/
theorem exists_coprime_phase_decomp_of_arcSetTextbook_plus_minus
    {X q a K : ℕ} {Δ : ℝ}
    (hΔ : 0 ≤ Δ) (hXpos : 0 < X) (hq : 1 ≤ q) (hXΔ : (4 * Real.pi * Δ) ≤ (X : ℝ))
    {α β : ℝ}
    (hα : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a Δ)
    (ha : a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hqK : 8 * (2 * K + 1) ≤ q)
    (hShift : Goldbach.Cert.MajorArcModules.CoprimePreservingApprox.CoprimeShiftBound q K) :
    ∃ zPlus zMinus : ℕ,
      Nat.Coprime (a + zPlus) q ∧
      Nat.Coprime (a + zMinus) q ∧
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + (β - (zPlus : ℝ) / (q : ℝ)))| ≤ 1 ∧
      |2 * Real.pi * ((α - (a : ℝ) / (q : ℝ)) + ((1 - β) - (zMinus : ℝ) / (q : ℝ)))| ≤ 1 ∧
      ((α - (a : ℝ) / (q : ℝ)) + (β - (zPlus : ℝ) / (q : ℝ)))
          + ((a + zPlus : ℕ) : ℝ) / (q : ℝ) = α + β ∧
      ((α - (a : ℝ) / (q : ℝ)) + ((1 - β) - (zMinus : ℝ) / (q : ℝ)))
          + ((a + zMinus : ℕ) : ℝ) / (q : ℝ) = α + (1 - β) := by
  rcases
    exists_coprime_shift_small_offsets_of_arcSetTextbook_plus_minus
      (X := X) (q := q) (a := a) (K := K) (Δ := Δ)
      hΔ hXpos hq hXΔ hα ha hβ0 hβ1 hqK hShift
      with ⟨zPlus, zMinus, hzPlusC, hzMinusC, hβPlus, hβMinus⟩
  refine ⟨zPlus, zMinus, hzPlusC, hzMinusC, hβPlus, hβMinus, ?_, ?_⟩
  · have hq0 : (q : ℝ) ≠ 0 := by
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
      exact_mod_cast (Nat.ne_of_gt hqpos)
    field_simp [hq0]
    -- after clearing denominators, this is just a cancellation of the `a+zPlus` terms
    simp [Nat.cast_add]
    ring_nf
  · have hq0 : (q : ℝ) ≠ 0 := by
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
      exact_mod_cast (Nat.ne_of_gt hqpos)
    field_simp [hq0]
    simp [Nat.cast_add]
    ring_nf

lemma intervalIntegrable_indicator_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (s.indicator f) volume a b := by
  refine ⟨?_, ?_⟩
  · exact (hf.1.indicator hs)
  · exact (hf.2.indicator hs)

lemma intervalIntegrable_indicator_compl_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (sᶜ.indicator f) volume a b :=
  intervalIntegrable_indicator_of_intervalIntegrable (a := a) (b := b) (s := sᶜ) hs.compl hf

theorem intervalIntegral_eq_indicator_add_indicator_compl
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {s : Set ℝ} (hs : MeasurableSet s) {f : ℝ → E}
    (hf : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x)
      =
    (∫ x in a..b, s.indicator f x)
      +
    (∫ x in a..b, sᶜ.indicator f x) := by
  have hMaj : IntervalIntegrable (s.indicator f) volume a b :=
    intervalIntegrable_indicator_of_intervalIntegrable (a := a) (b := b) (s := s) hs hf
  have hMin : IntervalIntegrable (sᶜ.indicator f) volume a b :=
    intervalIntegrable_indicator_compl_of_intervalIntegrable (a := a) (b := b) (s := s) hs hf
  have hsum : s.indicator f + sᶜ.indicator f = f :=
    Set.indicator_self_add_compl s f
  calc
    (∫ x in a..b, f x)
        =
      ∫ x in a..b, (s.indicator f + sᶜ.indicator f) x := by
        simpa [hsum] using congrArg (fun g : ℝ → E => ∫ x in a..b, g x) hsum.symm
    _ =
      (∫ x in a..b, s.indicator f x) + (∫ x in a..b, sᶜ.indicator f x) := by
        simpa [Pi.add_apply] using
          (intervalIntegral.integral_add (a := a) (b := b) (μ := volume)
            (f := fun x => s.indicator f x) (g := fun x => sᶜ.indicator f x) hMaj hMin)

theorem intervalIntegral_negHalf_half_eq_small_add_large
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) :
    (∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ), f β)
      =
    (∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ), betaSmallSet.indicator f β)
      +
    (∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ), betaSmallSetᶜ.indicator f β) := by
  simpa [betaSmallSet] using
    (intervalIntegral_eq_indicator_add_indicator_compl
      (a := (-( (2 : ℝ)⁻¹) : ℝ)) (b := ((2 : ℝ)⁻¹ : ℝ))
      (s := betaSmallSet) measurableSet_betaSmallSet (f := f) hf)

/-!
## Shifting the β-interval using periodicity

The map `β ↦ (β : AddCircle 1)` is 1-periodic, so any expression depending only on `(β : UC)` is
1-periodic as a function of the real variable `β`.  This lets us rewrite the β-integral from
`[0,1]` to the symmetric interval `[-1/2, 1/2]`, which is the natural domain for bounding the real
representative `betaRep β`.
-/

lemma intervalIntegral_zero_one_eq_intervalIntegral_negHalf_half
    (f : ℝ → ℂ) (hf : Function.Periodic f (1 : ℝ)) :
    (∫ β in (0 : ℝ)..(1 : ℝ), f β) = ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ), f β := by
  -- Use `Periodic.intervalIntegral_add_eq` with `T = 1`, `t = 0`, `s = -1/2`.
  have h :=
    (hf.intervalIntegral_add_eq (T := (1 : ℝ)) (t := (0 : ℝ)) (s := (-( (2 : ℝ)⁻¹) : ℝ)))
  have h0 : (0 : ℝ) + 1 = (1 : ℝ) := by ring
  have h1 : (-( (2 : ℝ)⁻¹) : ℝ) + 1 = ((2 : ℝ)⁻¹ : ℝ) := by nlinarith
  -- simplify interval endpoints
  simpa [h0, h1, add_assoc] using h

private lemma innerIntegrand_congr_of_coe_eq
    (X N : ℕ) {β₁ β₂ α : ℝ} (hβ : (β₁ : UC) = (β₂ : UC)) :
    innerIntegrand X N β₁ α = innerIntegrand X N β₂ α := by
  have hsub : ((α : UC) - (β₁ : UC)) = ((α : UC) - (β₂ : UC)) := by
    simpa [hβ] using congrArg (fun t : UC => (α : UC) - t) hβ
  have hadd : ((α : UC) + (β₁ : UC)) = ((α : UC) + (β₂ : UC)) := by
    simpa [hβ] using congrArg (fun t : UC => (α : UC) + t) hβ
  simp [Goldbach.Cert.MajorArcStep17MajorMinorSplit.innerIntegrand, hsub, hadd]

lemma innerMajorQ0_periodic (X N : ℕ) (Δ : ℝ) :
    Function.Periodic (fun β : ℝ => innerMajorQ0 X N Δ β) (1 : ℝ) := by
  intro β
  -- show `innerIntegrand` is unchanged when shifting `β` by 1 (since `(β+1 : UC) = (β : UC)`).
  have hβ : ((β + 1 : ℝ) : UC) = (β : UC) := by
    -- `AddCircle.coe_add_period` gives `((β+1):AddCircle 1)=β`.
    simpa using (AddCircle.coe_add_period (p := (1 : ℝ)) (x := β))
  -- apply congruence under the interval integral defining `innerMajorQ0`
  unfold Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.innerMajorQ0
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro α _hα
  have hpoint :
      innerIntegrand X N (β + 1) α = innerIntegrand X N β α :=
    innerIntegrand_congr_of_coe_eq (X := X) (N := N) (α := α) hβ
  by_cases hmem : α ∈ Goldbach.Cert.MajorArcStep24IntegralExtraction.majorArcSetQ0 X Δ
  · simp [hmem, hpoint]
  · simp [hmem, hpoint]

lemma corr_integral_major_Q0_eq_intervalIntegral_negHalf_half
    (X N : ℕ) (Δ : ℝ) :
    corr_integral_major_Q0 X N Δ
      =
    ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ),
      kernelPolyC (β : UC) * innerMajorQ0 X N Δ β := by
  -- The integrand depends only on `(β : UC)`, hence it is 1-periodic.
  have hper :
      Function.Periodic
        (fun β : ℝ => kernelPolyC (β : UC) * innerMajorQ0 X N Δ β)
        (1 : ℝ) := by
    intro β
    have hβ : ((β + 1 : ℝ) : UC) = (β : UC) := by
      simpa using (AddCircle.coe_add_period (p := (1 : ℝ)) (x := β))
    have hk : kernelPolyC ((β + 1 : ℝ) : UC) = kernelPolyC (β : UC) := by
      simpa [hβ]
    have hinner : innerMajorQ0 X N Δ (β + 1) = innerMajorQ0 X N Δ β := by
      simpa using (innerMajorQ0_periodic (X := X) (N := N) (Δ := Δ) β)
    simp [hk, hinner]
  -- Now shift the interval integral.
  unfold Goldbach.Cert.MajorArcStep26Q0MajorArcIntegral.corr_integral_major_Q0
  simpa using
    (intervalIntegral_zero_one_eq_intervalIntegral_negHalf_half
      (f := fun β : ℝ => kernelPolyC (β : UC) * innerMajorQ0 X N Δ β) hper)

end

end Goldbach.Cert.MajorArcModules.BetaLocalization
