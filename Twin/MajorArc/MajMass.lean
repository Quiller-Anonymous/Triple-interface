import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Twin.MajorArc.SWUniform
import Twin.SW.Defs

/-!
`majMass`: a concrete *analytic* major-arc mass (definition only)
===============================================================

This file defines a canonical “major-arc contribution” functional in the spirit of the paper:

* use the major-arc boxes determined by a `SmoothMajorArcEstimate` (polylog moduli + width `δ/(H+1)`),
* integrate the standard twin-correlation Fourier integrand `|S_X(α)|^2 e(-2α)` over those major arcs.

This is intentionally just a **definition** layer: the hard theorems (`routing_onWindow`,
`pinnedMajors_lower`, etc.) are proved/axiomatized elsewhere.

Import note: this file avoids the heavy SW derivation layer (and does not import
`Twin.SW.PartialSummation`).
-/

namespace Twin.MajorArc

noncomputable section

open scoped BigOperators
open scoped ComplexConjugate
open MeasureTheory

open Twin

variable {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}

/-- The (naïve) major-arc predicate used by the SW interface: there exist coprime `a/q`
with `q ≤ (log X)^B` and `|α - a/q| ≤ δ/(H+1)`.

Note: this is *not* reduced modulo `1`; we integrate on `[0,1]` anyway. -/
def IsMajorArc (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : Prop :=
  ∃ (q a : ℕ),
    1 ≤ q ∧
    (q : ℝ) ≤ Real.rpow (Real.log X) B ∧
    Nat.Coprime a q ∧
    |α - (a : ℝ) / q| ≤ sme.δ / (H + 1)

/-- Indicator of the major-arc set as a real-valued function. -/
def majorArcInd (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : ℝ :=
  by
    classical
    exact if IsMajorArc (sme := sme) X H α then 1 else 0

/-- Indicator of the minor-arc set (complementary to `majorArcInd`). -/
def minorArcInd (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : ℝ :=
  by
    classical
    exact if IsMajorArc (sme := sme) X H α then 0 else 1

/-- Twin-correlation Fourier integrand: `|S_X(α)|^2 e(-2α)` (real part).

Here `S_X(α)` is the smoothed prime exponential sum `Twin.SW.sumValue`.
This matches the standard identity that, upon integrating over `α ∈ [0,1]`,
recovers a smoothed version of `∑ Λ(n)Λ(n+2)` (the “twin payload”). -/
def twinCorrIntegrand (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H α : ℝ) : ℝ :=
  let S : ℂ := Twin.SW.sumValue Λ W X H α
  ((S * conj S) * Twin.SW.χ_add (-2 * α)).re

/-- Complex-valued twin-correlation integrand `|S_X(α)|^2 e(-2α)` (no real-part taken). -/
def twinCorrIntegrandC (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H α : ℝ) : ℂ :=
  let S : ℂ := Twin.SW.sumValue Λ W X H α
  (S * conj S) * Twin.SW.χ_add (-2 * α)

/-- The major-arc integrand: multiply the correlation integrand by the major-arc indicator. -/
def majorArcTwinIntegrand (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : ℝ :=
  majorArcInd (sme := sme) X H α * twinCorrIntegrand Λ W X H α

/-- Complex-valued major-arc integrand. -/
def majorArcTwinIntegrandC (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : ℂ :=
  (majorArcInd (sme := sme) X H α : ℂ) * twinCorrIntegrandC Λ W X H α

/-- The minor-arc integrand: multiply the correlation integrand by the minor-arc indicator. -/
def minorArcTwinIntegrand (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : ℝ :=
  minorArcInd (sme := sme) X H α * twinCorrIntegrand Λ W X H α

/-- Complex-valued minor-arc integrand. -/
def minorArcTwinIntegrandC (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : ℂ :=
  (minorArcInd (sme := sme) X H α : ℂ) * twinCorrIntegrandC Λ W X H α

/-- The full (all-α) integrand on `[0,1]`: just the twin-correlation integrand. -/
def fullTwinIntegrand (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H α : ℝ) : ℝ :=
  twinCorrIntegrand Λ W X H α

/-- Complex-valued full integrand. -/
def fullTwinIntegrandC (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H α : ℝ) : ℂ :=
  twinCorrIntegrandC Λ W X H α

lemma major_minor_integrand
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) :
    majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α
      + minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α
      = fullTwinIntegrand (Λ := Λ) (W := W) X H α := by
  classical
  by_cases h : IsMajorArc (sme := sme) X H α
  · simp [majorArcTwinIntegrand, minorArcTwinIntegrand, majorArcInd, minorArcInd, fullTwinIntegrand, h]
  · simp [majorArcTwinIntegrand, minorArcTwinIntegrand, majorArcInd, minorArcInd, fullTwinIntegrand, h]

lemma major_minor_integrandC
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) :
    majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α
      + minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α
      = fullTwinIntegrandC (Λ := Λ) (W := W) X H α := by
  classical
  by_cases h : IsMajorArc (sme := sme) X H α
  · simp [majorArcTwinIntegrandC, minorArcTwinIntegrandC, majorArcInd, minorArcInd, fullTwinIntegrandC, h]
  · simp [majorArcTwinIntegrandC, minorArcTwinIntegrandC, majorArcInd, minorArcInd, fullTwinIntegrandC, h]

/-- The major-arc mass on the window centered at `X` with scale `H`, integrated over `α ∈ [0,1]`. -/
noncomputable def majMassReal (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1, majorArcTwinIntegrand (sme := sme) (X := X) (H := H) α

/-- Complex-valued major-arc mass over `α ∈ [0,1]`. -/
noncomputable def majMassC (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) : ℂ :=
  ∫ α in Set.Icc (0 : ℝ) 1, majorArcTwinIntegrandC (sme := sme) (X := X) (H := H) α

/-- The minor-arc mass (complementary contribution) over `α ∈ [0,1]`. -/
noncomputable def minorMassReal (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1, minorArcTwinIntegrand (sme := sme) (X := X) (H := H) α

/-- Complex-valued minor-arc mass over `α ∈ [0,1]`. -/
noncomputable def minorMassC (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) : ℂ :=
  ∫ α in Set.Icc (0 : ℝ) 1, minorArcTwinIntegrandC (sme := sme) (X := X) (H := H) α

/-- The full mass over `α ∈ [0,1]` (no major/minor restriction). -/
noncomputable def fullMassReal (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H : ℝ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1, fullTwinIntegrand (Λ := Λ) (W := W) (X := X) (H := H) α

/-- Complex-valued full mass over `α ∈ [0,1]`. -/
noncomputable def fullMassC (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H : ℝ) : ℂ :=
  ∫ α in Set.Icc (0 : ℝ) 1, fullTwinIntegrandC (Λ := Λ) (W := W) (X := X) (H := H) α

/-- Under integrability, the full mass splits as major + minor. -/
theorem majMassReal_add_minorMassReal_eq_fullMassReal
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hMajor : IntegrableOn (fun α => majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
    (Set.Icc (0 : ℝ) 1))
  (hMinor : IntegrableOn (fun α => minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
    (Set.Icc (0 : ℝ) 1)) :
  majMassReal (sme := sme) (X := X) (H := H)
    + minorMassReal (sme := sme) (X := X) (H := H)
    = fullMassReal (Λ := Λ) (W := W) (X := X) (H := H) := by
  -- use `∫ (f+g) = ∫ f + ∫ g` (restricted to `[0,1]`) and the pointwise integrand decomposition
  have hAdd :
      (∫ α in Set.Icc (0 : ℝ) 1,
          (majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α
            + minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α))
        =
        (∫ α in Set.Icc (0 : ℝ) 1,
            majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
          +
          (∫ α in Set.Icc (0 : ℝ) 1,
            minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α) := by
    -- `integral_add` over the restricted measure
    simpa [Measure.restrict_restrict, add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.integral_add
        (μ := (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (f := fun α => majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
        (g := fun α => minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
        hMajor hMinor)
  -- flip sides and rewrite integrand sum
  have hAdd' := congrArg (fun t => t) hAdd
  -- `maj + min = ∫ (maj+min)` and then rewrite by `major_minor_integrand`
  have hSum :
      (∫ α in Set.Icc (0 : ℝ) 1,
          majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
        +
      (∫ α in Set.Icc (0 : ℝ) 1,
          minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
      =
      (∫ α in Set.Icc (0 : ℝ) 1,
          fullTwinIntegrand (Λ := Λ) (W := W) X H α) := by
    -- use `hAdd` and simplify the integrand with the pointwise identity
    have := hAdd.symm
    -- rewrite the integrand sum pointwise
    simpa [major_minor_integrand, fullTwinIntegrand, add_comm, add_left_comm, add_assoc] using this
  simpa [majMassReal, minorMassReal, fullMassReal] using hSum

/-- Under integrability, the full complex mass splits as major + minor. -/
theorem majMassC_add_minorMassC_eq_fullMassC
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hMajor : IntegrableOn (fun α => majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
    (Set.Icc (0 : ℝ) 1))
  (hMinor : IntegrableOn (fun α => minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
    (Set.Icc (0 : ℝ) 1)) :
  majMassC (sme := sme) (X := X) (H := H)
    + minorMassC (sme := sme) (X := X) (H := H)
    = fullMassC (Λ := Λ) (W := W) (X := X) (H := H) := by
  have hAdd :
      (∫ α in Set.Icc (0 : ℝ) 1,
          (majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α
            + minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α))
        =
        (∫ α in Set.Icc (0 : ℝ) 1,
            majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
          +
          (∫ α in Set.Icc (0 : ℝ) 1,
            minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α) := by
    simpa [Measure.restrict_restrict, add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.integral_add
        (μ := (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (f := fun α => majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
        (g := fun α => minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
        hMajor hMinor)
  have hSum :
      (∫ α in Set.Icc (0 : ℝ) 1,
          majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
        +
      (∫ α in Set.Icc (0 : ℝ) 1,
          minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
      =
      (∫ α in Set.Icc (0 : ℝ) 1,
          fullTwinIntegrandC (Λ := Λ) (W := W) X H α) := by
    have := hAdd.symm
    simpa [major_minor_integrandC, fullTwinIntegrandC, add_comm, add_left_comm, add_assoc] using this
  simpa [majMassC, minorMassC, fullMassC] using hSum

/-- Convenience wrapper: take `X : ℕ` and `H : ℕ` (used by the checklist route). -/
noncomputable def majMass (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℕ) : ℝ :=
  majMassReal (sme := sme) (X := (X : ℝ)) (H := (H : ℝ))

/-- Convenience wrapper for the complex-valued major-arc mass. -/
noncomputable def majMassC_nat (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℕ) : ℂ :=
  majMassC (sme := sme) (X := (X : ℝ)) (H := (H : ℝ))

/-- Convenience wrapper for the minor-arc mass. -/
noncomputable def minorMass (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℕ) : ℝ :=
  minorMassReal (sme := sme) (X := (X : ℝ)) (H := (H : ℝ))

/-- Convenience wrapper for the complex-valued minor-arc mass. -/
noncomputable def minorMassC_nat (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℕ) : ℂ :=
  minorMassC (sme := sme) (X := (X : ℝ)) (H := (H : ℝ))

/-- Convenience wrapper for the full mass. -/
noncomputable def fullMass (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H : ℕ) : ℝ :=
  fullMassReal (Λ := Λ) (W := W) (X := (X : ℝ)) (H := (H : ℝ))

/-- Convenience wrapper for the complex-valued full mass. -/
noncomputable def fullMassC_nat (Λ : ℕ → ℝ) (W : ℝ → ℝ) (X H : ℕ) : ℂ :=
  fullMassC (Λ := Λ) (W := W) (X := (X : ℝ)) (H := (H : ℝ))

end

end Twin.MajorArc
