import Twin.ChecklistAxioms
import Twin.ChecklistIntegrability
import Twin.MajorArc.MajMass
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Minor-arc dispersion/energy hypothesis (Core 1 replacement)
==========================================================

The checklist route ultimately needs the square-sum budget

* `Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme)`

on the *minor-arc correlation integrals* `minorMassAt (sme := sme) Y`.

Earlier attempts tried to derive this from pointwise or fourth-moment control on the raw
exponential sum `S_Y(α)`.  A mathematician correctly noted that those scales are not realistic:
`S_Y(α)` has natural size `≈ H` and its fourth moment typically scales like `H^3` (up to logs).

The right “conventional” analytic input is instead a **dispersion/energy estimate**
tailored to the *shifted correlation functional itself*:

  `M_Y := ∫_{α ∈ minor(Y)} S_Y(α) * conj(S_Y(α)) * e(-2α) dα`.

This is exactly the kind of quantity one attacks via Vaughan/Heath–Brown identities,
Type-II bilinear forms, and large-sieve/dispersion technology.

This file introduces a conventional-looking hypothesis `MinorArcDispersionEnergyBound`
about the *second moment* of the complex-valued minor masses `M_Y` over
`Y ∈ bigIcc(X) = [X-H, X+H]`.  From that hypothesis, the existing checklist class
`MinorMassAtSqSumBudget` follows by the elementary inequality `|Re z| ≤ ‖z‖`.
-/

namespace Twin.ChecklistAxioms

noncomputable section

open Twin
open scoped BigOperators
open scoped ComplexConjugate
open MeasureTheory

variable (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)

/-!
## Complex minor mass on a window center

This is the same object as `minorMassAt` but kept in complex form (no `re` taken).
It is the natural target for dispersion estimates.
-/

noncomputable def minorMassAtC (Y : ℕ) : ℂ :=
  Twin.MajorArc.minorMassC_nat (sme := sme) (Λ := Lambda) (W := Wwin) Y P.H

/-!
## Normalization suggested by analytic feedback

Analytic feedback indicates that a plausible “theorem-shaped” minor-arc dispersion bound may only
hold after normalizing the correlation integral by a factor of the form `H · log X`.

We record that normalization here as a conventional interface *separate from* the unnormalized
budget currently consumed by the checklist gate.
-/

noncomputable def energyNorm (X : ℕ) : ℝ :=
  (P.H : ℝ) * Real.log (max (X : ℝ) 3)

private lemma minorMassAt_eq_re_minorMassAtC (Y : ℕ) :
    minorMassAt (sme := sme) Y = (minorMassAtC (sme := sme) Y).re := by
  -- Unfold both sides to integrals on `[0,1]` and commute `re` with the integral.
  classical
  -- notation for the restricted measure on `[0,1]`
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)
  -- the complex minor-arc integrand
  let fC : ℝ → ℂ :=
    fun α =>
      Twin.MajorArc.minorArcTwinIntegrandC (sme := sme) (Λ := Lambda) (W := Wwin) (Y : ℝ) (P.H : ℝ) α
  -- the real minor-arc integrand
  let fR : ℝ → ℝ :=
    fun α =>
      Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin) (Y : ℝ) (P.H : ℝ) α

  have hre : (fun α => (fC α).re) = fR := by
    funext α
    by_cases hMaj : Twin.MajorArc.IsMajorArc (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α
    · -- both are zero on major arcs
      simp [fC, fR, Twin.MajorArc.minorArcTwinIntegrandC, Twin.MajorArc.minorArcTwinIntegrand,
        Twin.MajorArc.minorArcInd, hMaj]
    ·
      -- on minor arcs, `minorArcInd = 1` and `twinCorrIntegrand = re(twinCorrIntegrandC)`
      simp [fC, fR, Twin.MajorArc.minorArcTwinIntegrandC, Twin.MajorArc.minorArcTwinIntegrand,
        Twin.MajorArc.minorArcInd, hMaj, Twin.MajorArc.twinCorrIntegrand, Twin.MajorArc.twinCorrIntegrandC]

  -- Integrability: continuity on `[0,1]` (proved in `Twin.ChecklistIntegrability`) plus
  -- indicator-measurability gives integrability of the minor-arc complex integrand.
  have hFull : IntegrableOn
      (fun α => Twin.MajorArc.fullTwinIntegrandC (Λ := Lambda) (W := Wwin)
        (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
      (Set.Icc (0 : ℝ) 1) := by
    -- `Twin.ChecklistIntegrability.fullIntegrableC` is stated with its own `P/Lambda/Wwin`;
    -- we `simpa` to match the checklist abbreviations.
    simpa [Twin.ChecklistIntegrability.P, Twin.ChecklistIntegrability.Lambda,
      Twin.ChecklistIntegrability.Wwin, P, Lambda, Wwin] using
      (Twin.ChecklistIntegrability.fullIntegrableC (X := Y))

  have hMinorC : IntegrableOn
      (fun α => Twin.MajorArc.minorArcTwinIntegrandC (sme := sme) (Λ := Lambda) (W := Wwin)
        (Y : ℝ) (P.H : ℝ) α)
      (Set.Icc (0 : ℝ) 1) :=
    Twin.MajorArc.integrableOn_minorArcTwinIntegrandC_of_full (sme := sme) (Λ := Lambda) (W := Wwin)
      (X := (Y : ℝ)) (H := (P.H : ℝ)) hFull

  -- Now compute:
  -- `minorMassAt = ∫ fR` and `minorMassAtC = ∫ fC`, and `∫ re(fC) = re(∫ fC)`.
  have hIntegralRe :
      (∫ α in Set.Icc (0 : ℝ) 1, (fC α).re) = (∫ α in Set.Icc (0 : ℝ) 1, fC α).re := by
    -- `MeasureTheory.integral_re` needs `Integrable` on the restricted measure.
    have hInt : Integrable fC μ := by
      simpa [MeasureTheory.IntegrableOn, μ, fC] using hMinorC
    -- unfold `setIntegral` as integral over restricted measure
    simpa [μ] using (integral_re (μ := μ) (f := fC) hInt)

  have hEqIntegral :
      (∫ α in Set.Icc (0 : ℝ) 1,
          Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
            (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
        =
      (∫ α in Set.Icc (0 : ℝ) 1,
          Twin.MajorArc.minorArcTwinIntegrandC (sme := sme) (Λ := Lambda) (W := Wwin)
            (X := (Y : ℝ)) (H := (P.H : ℝ)) α).re := by
    -- Rewrite the real integrand as the real-part of the complex integrand, then commute `re` with `∫`.
    calc
      (∫ α in Set.Icc (0 : ℝ) 1,
          Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
            (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
          = ∫ α in Set.Icc (0 : ℝ) 1, (fC α).re := by
              simpa [fR, hre]
      _ = (∫ α in Set.Icc (0 : ℝ) 1, fC α).re := hIntegralRe
      _ = (∫ α in Set.Icc (0 : ℝ) 1,
          Twin.MajorArc.minorArcTwinIntegrandC (sme := sme) (Λ := Lambda) (W := Wwin)
            (X := (Y : ℝ)) (H := (P.H : ℝ)) α).re := by
              simp [fC]

  -- Expand definitions of the masses.
  -- `minorMassAt` is defined as `Twin.MajorArc.minorMass (sme := sme) Y P.H`.
  -- `minorMassAtC` is defined as `Twin.MajorArc.minorMassC_nat ...`.
  simpa [minorMassAt, minorMassAtC, Twin.MajorArc.minorMass, Twin.MajorArc.minorMassReal,
    Twin.MajorArc.minorMassC_nat, Twin.MajorArc.minorMassC] using hEqIntegral

private lemma abs_minorMassAt_le_norm_minorMassAtC (Y : ℕ) :
    |minorMassAt (sme := sme) Y| ≤ ‖minorMassAtC (sme := sme) Y‖ := by
  have hEq : minorMassAt (sme := sme) Y = (minorMassAtC (sme := sme) Y).re :=
    minorMassAt_eq_re_minorMassAtC (sme := sme) Y
  -- `|re z| ≤ ‖z‖`
  simpa [hEq] using Complex.abs_re_le_norm (minorMassAtC (sme := sme) Y)

/-!
## Conventional hypothesis: dispersion/energy bound for the minor masses
-/

class MinorArcDispersionEnergyBound
    (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : Prop where
  /-- Second-moment bound for the complex-valued minor masses `minorMassAtC`. -/
  budget :
    ∀ X, P.X0 ≤ X →
      (bigIcc (X := X)).sum (fun Y => ‖minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ))
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

/-!
### Normalized dispersion/energy hypothesis (mathematician-facing)

This is the “plausible” conventional hypothesis suggested by feedback:
we bound the second moment of the *normalized* minor masses `minorMassAtC / (H log X)` on `bigIcc(X)`.

Note: this does **not** by itself imply the unnormalized checklist Core 1 budget above; further
analytic input would be needed to remove the normalization factor.
-/

class MinorArcDispersionEnergyBoundNorm
    (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : Prop where
  /-- Second-moment bound for the normalized minor masses `minorMassAtC / energyNorm(X)`. -/
  budget_norm :
    ∀ X, P.X0 ≤ X →
      (bigIcc (X := X)).sum (fun Y => (‖minorMassAtC (sme := sme) Y‖ / energyNorm X) ^ (2 : ℕ))
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

theorem unnormalized_budget_of_normalized
    [MinorArcDispersionEnergyBoundNorm (sme := sme)] :
    ∀ X, P.X0 ≤ X →
      (bigIcc (X := X)).sum (fun Y => ‖minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ))
        ≤ ((P.eps^2 * SS^2) * (P.H + 1) / 9) * (energyNorm X) ^ (2 : ℕ) := by
  classical
  intro X hX
  have hnorm := (MinorArcDispersionEnergyBoundNorm.budget_norm (sme := sme) X hX)
  -- Multiply the normalized inequality by `energyNorm(X)^2`.
  have hEpos : 0 < energyNorm (X := X) := by
    -- For the repo-default parameters, `P.X0 = 10000` and `P.H = 10000`, so `energyNorm > 0`.
    have hHpos : 0 < (P.H : ℝ) := by
      -- unfold `P` to the concrete parameters
      norm_num [Twin.ChecklistAxioms.P, Twin.Main.P, Twin.PaperParams.P, Twin.PaperParams.H]
    have hmax : (1 : ℝ) < max (X : ℝ) 3 := by
      have h3 : (1 : ℝ) < (3 : ℝ) := by norm_num
      have hle : (3 : ℝ) ≤ max (X : ℝ) 3 := le_max_right _ _
      exact lt_of_lt_of_le h3 hle
    have hlog : 0 < Real.log (max (X : ℝ) 3) := Real.log_pos hmax
    simpa [energyNorm, mul_pos_iff] using mul_pos hHpos hlog
  have hE0' : energyNorm (X := X) ≠ 0 := ne_of_gt hEpos

  have hE :
      (energyNorm X) ^ (2 : ℕ)
        * (bigIcc (X := X)).sum (fun Y => (‖minorMassAtC (sme := sme) Y‖ / energyNorm X) ^ (2 : ℕ))
        =
      (bigIcc (X := X)).sum (fun Y => ‖minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ)) := by
    -- Distribute `energyNorm(X)^2` into each summand and cancel the division.
    have hterm :
        ∀ Y : ℕ,
          (energyNorm X) ^ (2 : ℕ) * (‖minorMassAtC (sme := sme) Y‖ / energyNorm X) ^ (2 : ℕ)
            = ‖minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ) := by
      intro Y
      field_simp [hE0', pow_two]
    calc
      (energyNorm X) ^ (2 : ℕ)
          * (bigIcc (X := X)).sum (fun Y => (‖minorMassAtC (sme := sme) Y‖ / energyNorm X) ^ (2 : ℕ))
          =
        (bigIcc (X := X)).sum (fun Y =>
          (energyNorm X) ^ (2 : ℕ) * (‖minorMassAtC (sme := sme) Y‖ / energyNorm X) ^ (2 : ℕ)) := by
            simp [Finset.mul_sum]
      _ =
        (bigIcc (X := X)).sum (fun Y => ‖minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro Y _hY
            simp [hterm Y]
  -- Combine.
  have := mul_le_mul_of_nonneg_left hnorm (pow_two_nonneg (energyNorm X))
  -- rewrite using `hE`
  simpa [hE, mul_assoc, mul_comm, mul_left_comm] using this

/-!
## Dispersion energy ⇒ the checklist Core 1 budget
-/

theorem minorMassAtSqSumBudget_of_dispersionEnergy
    [MinorArcDispersionEnergyBound (sme := sme)] :
    MinorMassAtSqSumBudget (sme := sme) := by
  classical
  refine ⟨?_⟩
  intro X hX
  have hle : ∀ Y : ℕ, |minorMassAt (sme := sme) Y| ^ 2 ≤ ‖minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ) := by
    intro Y
    have h0 := abs_minorMassAt_le_norm_minorMassAtC (sme := sme) Y
    -- square both sides (both nonnegative)
    have hL : 0 ≤ |minorMassAt (sme := sme) Y| := abs_nonneg _
    have hR : 0 ≤ ‖minorMassAtC (sme := sme) Y‖ := by exact norm_nonneg _
    -- `x ≤ y` ⇒ `x^2 ≤ y^2`
    have := mul_self_le_mul_self hL h0
    simpa [pow_two] using this
  have hsum :
      (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2)
        ≤ (bigIcc (X := X)).sum (fun Y => ‖minorMassAtC (sme := sme) Y‖ ^ (2 : ℕ)) :=
    Finset.sum_le_sum (fun Y _ => hle Y)
  exact le_trans hsum ((MinorArcDispersionEnergyBound.budget (sme := sme)) X hX)

end

end Twin.ChecklistAxioms
