import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
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
with `q ≤ (log H)^B` and `|α - a/q| ≤ δ/(H+1)`.

Note: this is *not* reduced modulo `1`; we integrate on `[0,1]` anyway. -/
def IsMajorArc (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H α : ℝ) : Prop :=
  ∃ (q a : ℕ),
    1 ≤ q ∧
    (q : ℝ) ≤ Real.rpow (Real.log H) B ∧
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

/-!
Measurability + integrability plumbing for the major/minor decomposition
-----------------------------------------------------------------------

The basic “major + minor = full” integral identity is proved below under explicit
`IntegrableOn` hypotheses. For later use, it is convenient to:

* package the major-arc set as an explicit measurable set on `[0,1]`,
* reduce integrability of the major/minor integrands to integrability of the full integrand,
  via `IntegrableOn.indicator`.

This keeps the measure-theory bookkeeping separate from the analytic content (which is
responsible for proving that the full integrand is indeed integrable for the chosen model).
-/

def majorArcSet (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) : Set ℝ :=
  {α | IsMajorArc (sme := sme) X H α}

lemma measurableSet_majorArcSet (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) :
    MeasurableSet (majorArcSet (sme := sme) X H) := by
  classical
  -- Expand the existential definition into a countable union of measurable sets.
  let cond : ℕ → ℕ → Prop :=
    fun q a =>
      1 ≤ q ∧ (q : ℝ) ≤ Real.rpow (Real.log H) B ∧ Nat.Coprime a q
  let arc : ℕ → ℕ → Set ℝ :=
    fun q a => {α : ℝ | |α - (a : ℝ) / q| ≤ sme.δ / (H + 1)}
  have hEq :
      majorArcSet (sme := sme) X H
        = ⋃ q : ℕ, ⋃ a : ℕ, (if cond q a then arc q a else (∅ : Set ℝ)) := by
    ext α
    constructor
    · intro h
      rcases h with ⟨q, a, hq1, hqB, hcop, hα⟩
      refine Set.mem_iUnion.2 ⟨q, ?_⟩
      refine Set.mem_iUnion.2 ⟨a, ?_⟩
      have hc : cond q a := ⟨hq1, hqB, hcop⟩
      simp [hc, arc, hα]
    · intro h
      rcases Set.mem_iUnion.1 h with ⟨q, hq⟩
      rcases Set.mem_iUnion.1 hq with ⟨a, ha⟩
      by_cases hc : cond q a
      · have hα : |α - (a : ℝ) / q| ≤ sme.δ / (H + 1) := by
          simpa [hc, arc] using ha
        rcases hc with ⟨hq1, hqB, hcop⟩
        exact ⟨q, a, hq1, hqB, hcop, hα⟩
      · -- membership in the `if`-branch forces a contradiction
        simpa [hc] using ha
  -- Prove measurability of the RHS union.
  have hMeas :
      MeasurableSet (⋃ q : ℕ, ⋃ a : ℕ, (if cond q a then arc q a else (∅ : Set ℝ))) := by
    refine MeasurableSet.iUnion ?_
    intro q
    refine MeasurableSet.iUnion ?_
    intro a
    by_cases hc : cond q a
    · have hArc : MeasurableSet (arc q a) := by
        -- `{α | |α - c| ≤ r}` is measurable since `α ↦ |α - c|` is measurable.
        have h1 : Measurable (fun α : ℝ => |α - (a : ℝ) / q|) := by fun_prop
        have h2 : Measurable (fun _ : ℝ => sme.δ / (H + 1)) := measurable_const
        simpa [arc] using (measurableSet_le h1 h2)
      simpa [hc] using hArc
    · simpa [hc] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))
  simpa [hEq] using hMeas

lemma measurableSet_minorArcSet (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) :
    MeasurableSet {α | ¬ IsMajorArc (sme := sme) X H α} := by
  -- this is just the complement of `majorArcSet`
  change MeasurableSet ((majorArcSet (sme := sme) X H)ᶜ)
  exact (measurableSet_majorArcSet (sme := sme) X H).compl

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

/-!
Integrability reduction lemmas
-----------------------------

Once you know the *full* integrand is integrable on `[0,1]`, measurability of the
major-arc set implies that the major/minor integrands are also integrable (as indicators),
and then the “full = major + minor” identity follows from `integral_add`.
-/

lemma majorArcTwinIntegrand_eq_indicator
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) :
    (fun α => majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
      =
    (majorArcSet (sme := sme) X H).indicator (fun α => fullTwinIntegrand (Λ := Λ) (W := W) X H α) := by
  classical
  funext α
  by_cases h : IsMajorArc (sme := sme) X H α
  · have : α ∈ majorArcSet (sme := sme) X H := by simpa [majorArcSet] using h
    simp [majorArcTwinIntegrand, majorArcInd, fullTwinIntegrand, majorArcSet, h, this]
  · have : α ∉ majorArcSet (sme := sme) X H := by simpa [majorArcSet] using h
    simp [majorArcTwinIntegrand, majorArcInd, fullTwinIntegrand, majorArcSet, h, this]

lemma minorArcTwinIntegrand_eq_indicator
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) :
    (fun α => minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α)
      =
    {α | ¬ IsMajorArc (sme := sme) X H α}.indicator (fun α => fullTwinIntegrand (Λ := Λ) (W := W) X H α) := by
  classical
  funext α
  by_cases h : IsMajorArc (sme := sme) X H α
  · have : α ∉ {α | ¬ IsMajorArc (sme := sme) X H α} := by simp [h]
    simp [minorArcTwinIntegrand, minorArcInd, fullTwinIntegrand, h, this]
  · have : α ∈ {α | ¬ IsMajorArc (sme := sme) X H α} := by simp [h]
    simp [minorArcTwinIntegrand, minorArcInd, fullTwinIntegrand, h, this]

lemma majorArcTwinIntegrandC_eq_indicator
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) :
    (fun α => majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
      =
    (majorArcSet (sme := sme) X H).indicator (fun α => fullTwinIntegrandC (Λ := Λ) (W := W) X H α) := by
  classical
  funext α
  by_cases h : IsMajorArc (sme := sme) X H α
  · have : α ∈ majorArcSet (sme := sme) X H := by simpa [majorArcSet] using h
    simp [majorArcTwinIntegrandC, majorArcInd, fullTwinIntegrandC, majorArcSet, h, this]
  · have : α ∉ majorArcSet (sme := sme) X H := by simpa [majorArcSet] using h
    simp [majorArcTwinIntegrandC, majorArcInd, fullTwinIntegrandC, majorArcSet, h, this]

lemma minorArcTwinIntegrandC_eq_indicator
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ) :
    (fun α => minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α)
      =
    {α | ¬ IsMajorArc (sme := sme) X H α}.indicator (fun α => fullTwinIntegrandC (Λ := Λ) (W := W) X H α) := by
  classical
  funext α
  by_cases h : IsMajorArc (sme := sme) X H α
  · have : α ∉ {α | ¬ IsMajorArc (sme := sme) X H α} := by simp [h]
    simp [minorArcTwinIntegrandC, minorArcInd, fullTwinIntegrandC, h, this]
  · have : α ∈ {α | ¬ IsMajorArc (sme := sme) X H α} := by simp [h]
    simp [minorArcTwinIntegrandC, minorArcInd, fullTwinIntegrandC, h, this]

theorem integrableOn_majorArcTwinIntegrand_of_full
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hFull : IntegrableOn (fun α => fullTwinIntegrand (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1)) :
  IntegrableOn (fun α => majorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1) := by
  have hMA : MeasurableSet (majorArcSet (sme := sme) X H) :=
    measurableSet_majorArcSet (sme := sme) X H
  simpa [majorArcTwinIntegrand_eq_indicator (sme := sme) (Λ := Λ) (W := W) X H] using
    (IntegrableOn.indicator (h := hFull) (ht := hMA))

theorem integrableOn_minorArcTwinIntegrand_of_full
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hFull : IntegrableOn (fun α => fullTwinIntegrand (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1)) :
  IntegrableOn (fun α => minorArcTwinIntegrand (sme := sme) (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1) := by
  have hMi : MeasurableSet {α | ¬ IsMajorArc (sme := sme) X H α} :=
    measurableSet_minorArcSet (sme := sme) X H
  simpa [minorArcTwinIntegrand_eq_indicator (sme := sme) (Λ := Λ) (W := W) X H] using
    (IntegrableOn.indicator (h := hFull) (ht := hMi))

theorem integrableOn_majorArcTwinIntegrandC_of_full
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hFull : IntegrableOn (fun α => fullTwinIntegrandC (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1)) :
  IntegrableOn (fun α => majorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1) := by
  have hMA : MeasurableSet (majorArcSet (sme := sme) X H) :=
    measurableSet_majorArcSet (sme := sme) X H
  simpa [majorArcTwinIntegrandC_eq_indicator (sme := sme) (Λ := Λ) (W := W) X H] using
    (IntegrableOn.indicator (h := hFull) (ht := hMA))

theorem integrableOn_minorArcTwinIntegrandC_of_full
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hFull : IntegrableOn (fun α => fullTwinIntegrandC (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1)) :
  IntegrableOn (fun α => minorArcTwinIntegrandC (sme := sme) (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1) := by
  have hMi : MeasurableSet {α | ¬ IsMajorArc (sme := sme) X H α} :=
    measurableSet_minorArcSet (sme := sme) X H
  simpa [minorArcTwinIntegrandC_eq_indicator (sme := sme) (Λ := Λ) (W := W) X H] using
    (IntegrableOn.indicator (h := hFull) (ht := hMi))

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

/-- If the full integrand is integrable on `[0,1]`, then the full mass splits as major + minor. -/
theorem majMassReal_add_minorMassReal_eq_fullMassReal_of_full
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hFull : IntegrableOn (fun α => fullTwinIntegrand (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1)) :
  majMassReal (sme := sme) (X := X) (H := H)
    + minorMassReal (sme := sme) (X := X) (H := H)
    = fullMassReal (Λ := Λ) (W := W) (X := X) (H := H) := by
  refine majMassReal_add_minorMassReal_eq_fullMassReal (sme := sme) (Λ := Λ) (W := W) (X := X) (H := H) ?_ ?_
  · exact integrableOn_majorArcTwinIntegrand_of_full (sme := sme) (Λ := Λ) (W := W) (X := X) (H := H) hFull
  · exact integrableOn_minorArcTwinIntegrand_of_full (sme := sme) (Λ := Λ) (W := W) (X := X) (H := H) hFull

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

/-- Complex-valued version: if the full integrand is integrable on `[0,1]`, then full = major + minor. -/
theorem majMassC_add_minorMassC_eq_fullMassC_of_full
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℝ)
  (hFull : IntegrableOn (fun α => fullTwinIntegrandC (Λ := Λ) (W := W) X H α) (Set.Icc (0 : ℝ) 1)) :
  majMassC (sme := sme) (X := X) (H := H)
    + minorMassC (sme := sme) (X := X) (H := H)
    = fullMassC (Λ := Λ) (W := W) (X := X) (H := H) := by
  refine majMassC_add_minorMassC_eq_fullMassC (sme := sme) (Λ := Λ) (W := W) (X := X) (H := H) ?_ ?_
  · exact integrableOn_majorArcTwinIntegrandC_of_full (sme := sme) (Λ := Λ) (W := W) (X := X) (H := H) hFull
  · exact integrableOn_minorArcTwinIntegrandC_of_full (sme := sme) (Λ := Λ) (W := W) (X := X) (H := H) hFull

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

/-! Convenience nat-level split lemmas. -/

theorem majMass_add_minorMass_eq_fullMass_of_full
  (sme : SmoothMajorArcEstimate A B Λ W W_hat) (X H : ℕ)
  (hFull : IntegrableOn (fun α => fullTwinIntegrand (Λ := Λ) (W := W) (X : ℝ) (H : ℝ) α) (Set.Icc (0 : ℝ) 1)) :
  majMass (sme := sme) (X := X) (H := H)
    + minorMass (sme := sme) (X := X) (H := H)
    = fullMass (Λ := Λ) (W := W) (X := X) (H := H) := by
  simpa [majMass, minorMass, fullMass] using
    (majMassReal_add_minorMassReal_eq_fullMassReal_of_full (sme := sme) (Λ := Λ) (W := W)
      (X := (X : ℝ)) (H := (H : ℝ)) hFull)

end

end Twin.MajorArc
