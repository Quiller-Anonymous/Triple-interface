import Twin.ChecklistAxioms
import Twin.MajorArc.MajMass

/-!
Minor-arc fourth-moment hypothesis (Core 1 replacement candidate)
===============================================================

This file introduces a more “theorem-shaped” conventional analytic input that implies the
existing square-sum Core 1 budget:

* `Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme)`

Idea: if we can bound the minor-arc fourth moment of the smoothed prime exponential sum on the
family of windows `Y ∈ bigIcc(X)`, then the square-mass of the minor-arc correlation integrals
follows from:

1. Cauchy–Schwarz on `[0,1]` (already in `Twin.ChecklistAxioms`): `|minorMassAt Y|^2 ≤ L2At(Y)`.
2. Pointwise domination: on minor arcs, `|twinCorrIntegrand| ≤ ‖sumValue‖^2`, hence
   `|minorArcTwinIntegrand|^2 ≤ ‖sumValue‖^4`.

This still represents serious analytic number theory, but it is a more reusable interface than the
project-specific squared-sum statement.
-/

namespace Twin.ChecklistAxioms

noncomputable section

open Twin
open MeasureTheory
open scoped BigOperators
open scoped ComplexConjugate

variable (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What)

/-!
## Fourth-moment functional
-/

noncomputable def minorArcFourthMomentAt (Y : ℕ) : ℝ :=
  ∫ α in Set.Icc (0 : ℝ) 1,
    (Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
      * (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ))

/-!
## Conventional hypothesis: summed fourth-moment budget on `bigIcc(X)`
-/

class MinorArcFourthMomentBound
    (sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What) : Prop where
  /-- Integrability of the fourth-moment integrand on `[0,1]` (used only for monotonicity). -/
  integrable :
    ∀ Y : ℕ,
      IntegrableOn
        (fun α : ℝ =>
          (Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
            * (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ)))
        (Set.Icc (0 : ℝ) 1)
  /-- The fourth-moment budget at the canonical `/9` scale. -/
  budget :
    ∀ X : ℕ, P.X0 ≤ X →
      (bigIcc (X := X)).sum (fun Y => minorArcFourthMomentAt (sme := sme) Y)
        ≤ (P.eps^2 * SS^2) * (P.H + 1) / 9

/-!
## Fourth moment ⇒ square-sum budget (Core 1)
-/

private lemma norm_chi_add (t : ℝ) : ‖Twin.SW.χ_add t‖ = 1 := by
  simp [Twin.SW.χ_add, Complex.norm_exp]

private lemma abs_twinCorrIntegrand_le_norm_sumValue_sq (Y : ℕ) (α : ℝ) :
    |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α|
      ≤ ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ) := by
  set S : ℂ := Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α
  set t : ℝ := (-2 : ℝ) * α
  have hre :
      |((S * conj S) * Twin.SW.χ_add t).re|
        ≤ ‖(S * conj S) * Twin.SW.χ_add t‖ := by
    simpa using Complex.abs_re_le_norm ((S * conj S) * Twin.SW.χ_add t)
  have hχ : ‖Twin.SW.χ_add t‖ = 1 := by
    simpa using norm_chi_add t
  have hnorm : ‖(S * conj S) * Twin.SW.χ_add t‖ = ‖S‖ ^ (2 : ℕ) := by
    have hconj : ‖conj S‖ = ‖S‖ := by
      simpa using (Complex.norm_conj S)
    calc
      ‖(S * conj S) * Twin.SW.χ_add t‖
          = ‖S * conj S‖ * ‖Twin.SW.χ_add t‖ := by
              simpa [mul_assoc] using (norm_mul (S * conj S) (Twin.SW.χ_add t))
      _ = ‖S * conj S‖ := by
            rw [hχ, mul_one]
      _ = ‖S‖ * ‖conj S‖ := by
            simpa using (norm_mul S (conj S))
      _ = ‖S‖ ^ (2 : ℕ) := by
            simp [hconj, pow_two]
  have h' :
      |((S * conj S) * Twin.SW.χ_add t).re| ≤ ‖S‖ ^ (2 : ℕ) := by
    calc
      |((S * conj S) * Twin.SW.χ_add t).re| ≤ ‖(S * conj S) * Twin.SW.χ_add t‖ := hre
      _ = ‖S‖ ^ (2 : ℕ) := hnorm
  simpa [Twin.MajorArc.twinCorrIntegrand, S, t] using h'

private lemma minorMassAt_L2At_le_fourthMomentAt (Y : ℕ)
    [MinorArcFourthMomentBound (sme := sme)] :
    minorMassAt_L2At (sme := sme) Y ≤ minorArcFourthMomentAt (sme := sme) Y := by
  classical
  let f : ℝ → ℝ :=
    fun α =>
      |Twin.MajorArc.minorArcTwinIntegrand (sme := sme) (Λ := Lambda) (W := Wwin)
          (X := (Y : ℝ)) (H := (P.H : ℝ)) α| ^ (2 : ℕ)
  let g : ℝ → ℝ :=
    fun α =>
      (Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α)
        * (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ))
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    refine Filter.Eventually.of_forall ?_
    intro α
    exact pow_nonneg (abs_nonneg _) _

  have hg_int : Integrable g μ := by
    simpa [MeasureTheory.IntegrableOn, μ, g] using
      (MinorArcFourthMomentBound.integrable (sme := sme) Y)

  have hfg : f ≤ᵐ[μ] g := by
    refine Filter.Eventually.of_forall ?_
    intro α
    by_cases hMaj :
        Twin.MajorArc.IsMajorArc (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α
    · simp [f, g, Twin.MajorArc.minorArcInd, Twin.MajorArc.minorArcTwinIntegrand, hMaj]
    ·
      have hCorr :
          |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ^ (2 : ℕ)
            ≤ ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ) := by
        have hle := abs_twinCorrIntegrand_le_norm_sumValue_sq (Y := Y) α
        have h0 : 0 ≤ |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| :=
          abs_nonneg _
        have hsq :
            |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ^ (2 : ℕ)
              ≤ (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
          -- square both sides via `mul_self_le_mul_self`
          have hmul :
              |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α|
                  * |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α|
                ≤ (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ))
                    * (‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (2 : ℕ)) :=
            mul_self_le_mul_self h0 hle
          simpa [pow_two] using hmul
        -- rewrite `(‖S‖^2)^2 = ‖S‖^4`
        set R : ℝ := ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖
        have hpow : (R ^ (2 : ℕ)) ^ (2 : ℕ) = R ^ (4 : ℕ) := by
          simpa [R] using (pow_mul R 2 2).symm
        -- apply the rewrite
        simpa [R, hpow] using (le_trans hsq (le_of_eq hpow))
      have hInd :
          Twin.MajorArc.minorArcInd (sme := sme) (X := (Y : ℝ)) (H := (P.H : ℝ)) α = 1 := by
        simp [Twin.MajorArc.minorArcInd, hMaj]
      have hf : f α = |Twin.MajorArc.twinCorrIntegrand Lambda Wwin (Y : ℝ) (P.H : ℝ) α| ^ (2 : ℕ) := by
        simp [f, Twin.MajorArc.minorArcTwinIntegrand, Twin.MajorArc.minorArcInd, hMaj, hInd]
      have hg : g α = ‖Twin.SW.sumValue Lambda Wwin (Y : ℝ) (P.H : ℝ) α‖ ^ (4 : ℕ) := by
        simp [g, Twin.MajorArc.minorArcInd, hMaj, hInd]
      simpa [hf, hg] using hCorr

  have hmono : (∫ α, f α ∂μ) ≤ ∫ α, g α ∂μ :=
    MeasureTheory.integral_mono_of_nonneg (μ := μ) hf_nonneg hg_int hfg

  simpa [minorMassAt_L2At, minorArcFourthMomentAt, f, g, μ] using hmono

theorem minorMassAtSqSumBudget_of_fourthMoment
    [MinorArcFourthMomentBound (sme := sme)] :
    MinorMassAtSqSumBudget (sme := sme) := by
  classical
  refine ⟨?_⟩
  intro X hX
  have hle : ∀ Y : ℕ, |minorMassAt (sme := sme) Y| ^ 2 ≤ minorArcFourthMomentAt (sme := sme) Y := by
    intro Y
    have h1 := minorMassAt_sq_le_L2At_raw (sme := sme) Y
    have h2 := minorMassAt_L2At_le_fourthMomentAt (sme := sme) (Y := Y)
    exact le_trans h1 h2
  have hsum :
      (bigIcc (X := X)).sum (fun Y => |minorMassAt (sme := sme) Y| ^ 2)
        ≤ (bigIcc (X := X)).sum (fun Y => minorArcFourthMomentAt (sme := sme) Y) :=
    Finset.sum_le_sum (fun Y _ => hle Y)
  exact le_trans hsum ((MinorArcFourthMomentBound.budget (sme := sme)) X hX)

end

end Twin.ChecklistAxioms
