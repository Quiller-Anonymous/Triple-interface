import Goldbach.Cert.MajorArcModules.Q0MajorRoute

/-!
`MajorArcModules/Q0MajorTailSpec` isolates the *remaining* analytic input for the large-β tail
bound in the turnkey `Q0` major-arc route.

The file `MajorArcModules/Q0MajorBoundSplit` already provides deterministic control of the kernel
polynomial `kernelPolyC` on `betaSmallSetᶜ` (via a second-difference identity).  What is still
missing, in order to turn that into an explicit bound on

`‖corr_integral_major_Q0_large X N Δ‖`,

is a usable analytic “engine” input for the already-extracted inner `α`-integral
`innerMajorQ0 X N Δ β` on the large-β region.  The original (option-2) plan asked for a uniform
`L∞` bound in `β`, which is fragile because of β-resonance.  The option-3 plan replaces this by an
`L²` (energy) bound in `β` on `betaSmallSetᶜ`, which is much more stable and matches the
TT*/large-sieve technology used elsewhere in the project.

This module records that missing ingredient as a Lean-facing interface, and packages the
resulting one-line reduction to the `Q0MajorRoute.Q0MajorLargeBound` interface.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorTailSpec

open scoped Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
open Goldbach.Cert.MajorArcModules.Q0MajorRoute

noncomputable section

set_option maxRecDepth 2048

-- Match the ambient circle type used throughout the major-arc pipeline.
abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private abbrev aβ : ℝ := (-( (2 : ℝ)⁻¹) : ℝ)
private abbrev bβ : ℝ := ((2 : ℝ)⁻¹ : ℝ)
private abbrev Iβ : Set ℝ := Set.Ioc aβ bβ

private lemma measurableSet_Iβ : MeasurableSet Iβ := by
  simp [Iβ]

/-!
## Option 3 interface: `L²` (energy) control in β

This is the major-arc-side analogue of the ε₁ energy interfaces: it asks for a uniform bound on
the `L²` mass of `β ↦ innerMajorQ0 X N Δ β` on the tail region `betaSmallSetᶜ` inside
`[-1/2,1/2]`.
-/

/-- An `L²` bound on `innerMajorQ0` on the large-β region `betaSmallSetᶜ`. -/
structure Q0InnerMajorLargeBetaEnergyBound (Δ M2 : ℝ) : Prop where
  nonneg : 0 ≤ M2
  memLp :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        MemLp (betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖))
          (ENNReal.ofReal (2 : ℝ)) (volume.restrict Iβ)
  bound :
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        -- `M2` bounds the `L²` norm of `β ↦ innerMajorQ0 ...` on the tail.
        (∫ β in Iβ,
            (betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖) β) ^ 2)
          ≤ M2 ^ 2

/--
`L²` bound on `innerMajorQ0` ⇒ large-β tail bound.

This is the simplest (and most robust) way to discharge the large-β piece once an analytic engine
is available.
-/
theorem largeBound_of_innerMajorQ0_energy
    {Δ M2 : ℝ} (h : Q0InnerMajorLargeBetaEnergyBound Δ M2) :
    Q0MajorLargeBound Δ (kernelTailCap * M2) := by
  refine ⟨?_⟩
  intro X N hX hN
  classical
  -- Notation: work on `Iβ = Ι (-1/2) (1/2)` with the restricted measure.
  let μβ : Measure ℝ := volume.restrict Iβ
  have hμ : IsFiniteMeasure μβ := by
    -- `Ι aβ bβ` is a bounded interval, hence finite measure.
    simpa [μβ] using (by infer_instance : IsFiniteMeasure (volume.restrict Iβ))

  -- Tail `L²` control hypothesis.
  let fIn : ℝ → ℝ := betaSmallSetᶜ.indicator (fun β : ℝ => ‖innerMajorQ0 X N Δ β‖)
  have hfInLp : MemLp fIn (ENNReal.ofReal (2 : ℝ)) μβ := by
    simpa [fIn, μβ] using h.memLp (X := X) (N := N) hX hN

  have h0In : 0 ≤ᵐ[μβ] fIn := by
    refine Filter.Eventually.of_forall ?_
    intro β
    by_cases hβ : β ∈ betaSmallSetᶜ <;>
      simp [fIn, Set.indicator_of_mem, Set.indicator_of_notMem, hβ, norm_nonneg]

  have hIn_sq :
      (∫ β, (fIn β) ^ 2 ∂μβ) ≤ M2 ^ 2 := by
    simpa [fIn, μβ] using h.bound (X := X) (N := N) hX hN

  have hM2 : 0 ≤ M2 := h.nonneg
  have hker0 : 0 ≤ kernelTailCap := kernelTailCap_nonneg

  -- Pointwise bound on the large-β integrand: `‖kernelPolyC‖ ≤ kernelTailCap` on the tail.
  have hpoint :
      ∀ᵐ β ∂μβ,
        ‖betaSmallSetᶜ.indicator (betaIntegrand X N Δ) β‖ ≤ kernelTailCap * fIn β := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Iβ).2 ?_
    refine Filter.Eventually.of_forall ?_
    intro β hβI
    by_cases hβ : β ∈ betaSmallSetᶜ
    · have hle : |β| ≤ ((2 : ℝ)⁻¹) := by
        -- `β ∈ Ι (-1/2) (1/2)` ⇒ `|β| ≤ 1/2`.
        have hab : aβ ≤ bβ := by
          -- `-1/2 ≤ 1/2`
          simp [aβ, bβ]
        have hmem : β ∈ Set.Ioc aβ bβ := by
          -- `Ι a b = Ioc a b` since `a ≤ b` here.
          simpa [Iβ, Set.uIoc_of_le hab] using hβI
        refine (abs_le).2 ?_
        exact ⟨le_of_lt hmem.1, hmem.2⟩
      have hK :
          ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelTailCap :=
        norm_kernelPolyC_le_kernelTailCap_of_mem_betaSmallSet_compl (β := β) hle hβ
      have :
          ‖betaSmallSetᶜ.indicator (betaIntegrand X N Δ) β‖
            =
          ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
              * ‖innerMajorQ0 X N Δ β‖ := by
        simp [betaIntegrand, fIn, Set.indicator_of_mem hβ, norm_mul, mul_assoc]
      -- Rewrite RHS as `kernelTailCap * fIn β`.
      -- `fIn β = ‖innerMajorQ0 ...‖` on the tail.
      have hfIn : fIn β = ‖innerMajorQ0 X N Δ β‖ := by
        simp [fIn, Set.indicator_of_mem hβ]
      -- combine
      simpa [this, hfIn, mul_assoc] using (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
    · -- off the tail, the indicator is zero
      simp [fIn, Set.indicator_of_notMem hβ, Set.indicator_of_notMem hβ, hker0]

  -- Turn the pointwise bound into an integral bound (need integrability for `integral_mono_ae`).
  have hIn_int : Integrable fIn μβ :=
    (MeasureTheory.MemLp.integrable (μ := μβ) (q := ENNReal.ofReal (2 : ℝ)) (hq1 := by
        -- `1 ≤ 2`
        simpa using (show (1 : ℝ) ≤ (2 : ℝ) from by norm_num))
      (by
        -- `MemLp fIn 2`
        simpa using hfInLp))
  have hRHS_int : Integrable (fun β : ℝ => kernelTailCap * fIn β) μβ :=
    hIn_int.const_mul kernelTailCap

  -- Use the interval-integral dominated estimate directly: it avoids measurability issues for the
  -- complex-valued integrand and only requires `IntervalIntegrable` of the (real) majorant.
  have hab : aβ ≤ bβ := by simp [aβ, bβ]
  have hIβ : Iβ = Set.Ioc aβ bβ := by simp [Iβ, Set.uIoc_of_le hab]
  have hIntMajorant : IntervalIntegrable (fun β : ℝ => kernelTailCap * fIn β) volume aβ bβ := by
    refine ⟨?_, ?_⟩
    · -- integrable on `Ioc aβ bβ` (this is exactly `μβ`)
      simpa [MeasureTheory.IntegrableOn, μβ, hIβ] using hRHS_int
    · -- the reverse interval is empty
      have : Set.Ioc bβ aβ = (∅ : Set ℝ) := by
        ext x
        simp [aβ, bβ]
      simpa [MeasureTheory.integrableOn_empty, this]

  have houter :
      ∀ᵐ β ∂volume, β ∈ Set.Ioc aβ bβ →
        ‖betaSmallSetᶜ.indicator (betaIntegrand X N Δ) β‖ ≤ kernelTailCap * fIn β := by
    refine Filter.Eventually.of_forall ?_
    intro β hβI
    -- we can reuse `hpoint` since it already proves the inequality for every `β ∈ Iβ`.
    have : β ∈ Iβ := by simpa [hIβ] using hβI
    have h' :
        ‖betaSmallSetᶜ.indicator (betaIntegrand X N Δ) β‖ ≤ kernelTailCap * fIn β := by
      -- `hpoint` is an `ae` statement on the restricted measure; extract the pointwise content.
      -- Since `hpoint` was proved from a pointwise-for-all lemma, we can just redo the case split.
      by_cases hβ : β ∈ betaSmallSetᶜ
      · have hle : |β| ≤ ((2 : ℝ)⁻¹) := by
          refine (abs_le).2 ?_
          exact ⟨le_of_lt hβI.1, hβI.2⟩
        have hK :
            ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelTailCap :=
          norm_kernelPolyC_le_kernelTailCap_of_mem_betaSmallSet_compl (β := β) hle hβ
        have hfIn : fIn β = ‖innerMajorQ0 X N Δ β‖ := by
          simp [fIn, Set.indicator_of_mem hβ]
        have hmul :
            ‖betaSmallSetᶜ.indicator (betaIntegrand X N Δ) β‖ ≤ kernelTailCap * fIn β := by
          -- On the tail, `indicator` keeps the integrand, so we reduce to a product inequality.
          have hmul' :
              ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
                  * ‖innerMajorQ0 X N Δ β‖
                ≤
              kernelTailCap * ‖innerMajorQ0 X N Δ β‖ :=
            mul_le_mul_of_nonneg_right hK (norm_nonneg _)
          simpa [betaIntegrand, fIn, Set.indicator_of_mem hβ, hfIn, norm_mul, mul_assoc] using hmul'
        exact hmul
      · simp [fIn, Set.indicator_of_notMem hβ, Set.indicator_of_notMem hβ, hker0]
    exact h'

  have hnorm_le :
      ‖corr_integral_major_Q0_large X N Δ‖ ≤ ∫ β in aβ..bβ, kernelTailCap * fIn β := by
    -- `corr_integral_major_Q0_large` is an interval integral over `aβ..bβ`.
    have := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := aβ) (b := bβ)
      (f := fun β : ℝ => betaSmallSetᶜ.indicator (betaIntegrand X N Δ) β)
      (g := fun β : ℝ => kernelTailCap * fIn β) hab houter hIntMajorant
    simpa [corr_integral_major_Q0_large] using this

  -- Cauchy–Schwarz on `∫ fIn`: `∫ fIn ≤ (∫ fIn^2)^(1/2)` since `μβ(univ)=1`.
  have hμIβ : μβ.real Set.univ = 1 := by
    have hab : aβ ≤ bβ := by simp [aβ, bβ]
    have hIβ : Iβ = Set.Ioc aβ bβ := by simp [Iβ, Set.uIoc_of_le hab]
    -- `μ.restrict s` gives mass `volume s`, and `volume (Ioc a b) = ofReal (b-a)`.
    have h' : μβ.real Set.univ = (bβ - aβ) := by
      -- `μβ univ = volume (Ioc aβ bβ)` and `volume (Ioc a b) = ofReal (b-a)`.
      simp [Measure.real, μβ, hIβ, Real.volume_Ioc, hab]
    have hab' : bβ - aβ = 1 := by
      norm_num [aβ, bβ]
    exact h'.trans hab'

  have hIn_le :
      (∫ β, fIn β ∂μβ) ≤ M2 := by
    -- Hölder with `f≡1` and `g=fIn`, `p=q=2`.
    have hconstLp : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μβ := by
      classical
      simpa using (MeasureTheory.memLp_const (p := ENNReal.ofReal (2 : ℝ)) (μ := μβ) (c := (1 : ℝ)))
    have hconst0 : 0 ≤ᵐ[μβ] (fun _ : ℝ => (1 : ℝ)) := by
      refine Filter.Eventually.of_forall ?_
      intro _; norm_num
    have hpq : (2 : ℝ).HolderConjugate 2 := by
      simpa using (Real.HolderConjugate.two_two : (2 : ℝ).HolderConjugate 2)
    have hCS :=
      MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μβ) (p := (2 : ℝ)) (q := (2 : ℝ))
        hpq hconst0 h0In hconstLp hfInLp
    -- Simplify the `f≡1` pieces and use the `L²` bound.
    have hInSq_rpow :
        (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) ^ (1 / (2 : ℝ)) ≤ M2 := by
      -- Use `hIn_sq` and monotonicity of `sqrt`.
      -- rewrite `∫ fIn^(2:ℝ)` as `∫ (fIn^2)` (nat square) so we can use `hIn_sq`.
      have hInSq_eq : (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) = ∫ β, (fIn β) ^ 2 ∂μβ := by
        refine MeasureTheory.integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro β
        simp [pow_two]
      have hInSq_le : (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) ≤ M2 ^ 2 := by
        simpa [hInSq_eq] using hIn_sq
      -- Convert to `sqrt` via `Real.sqrt_eq_rpow`.
      have hsqrt : Real.sqrt (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) ≤ Real.sqrt (M2 ^ 2) :=
        Real.sqrt_le_sqrt hInSq_le
      have hsqrt' :
          (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) ^ (1 / (2 : ℝ)) ≤ M2 := by
        -- `x^(1/2) = sqrt x`, `sqrt(M2^2)=M2`.
        have hM2sqrt : Real.sqrt (M2 ^ 2) = M2 := by
          simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hM2] using (Real.sqrt_sq_eq_abs M2).symm
        have hsqrt2 : Real.sqrt (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) ≤ M2 := by
          simpa [hM2sqrt] using hsqrt
        -- rewrite the LHS `sqrt` as `rpow (1/2)`
        simpa [Real.sqrt_eq_rpow] using hsqrt2
      exact hsqrt'
    -- Finish: `∫ fIn = ∫ (1*fIn) ≤ ...`
    have hmul1 : (∫ β, (fun _ : ℝ => (1 : ℝ)) β * fIn β ∂μβ) = ∫ β, fIn β ∂μβ := by
      simp
    -- In `hCS`, simplify `f≡1` and the `μβ.real univ` factor (`=1`).
    have hCS' :
        ∫ β, fIn β ∂μβ
          ≤ (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) ^ (1 / (2 : ℝ)) := by
      -- `hCS` gives `∫ 1*fIn ≤ (∫ 1^2)^(1/2) * (∫ fIn^2)^(1/2)`.
      -- Here `∫ 1^2 = μβ.real univ = 1`, so the first factor disappears.
      have hCS0 := hCS
      -- rewrite LHS and the constant factor
      have hCS1 :
          ∫ β, fIn β ∂μβ
            ≤ (μβ.real Set.univ) ^ (1 / (2 : ℝ))
                * (∫ β, (fIn β) ^ (2 : ℝ) ∂μβ) ^ (1 / (2 : ℝ)) := by
        simpa [hmul1] using hCS0
      -- `μβ.real univ = 1`
      simpa [hμIβ] using hCS1
    exact le_trans hCS' hInSq_rpow

  -- Put everything together.
  calc
    ‖corr_integral_major_Q0_large X N Δ‖
        ≤ ∫ β, kernelTailCap * fIn β ∂μβ := by
            -- convert the interval integral bound to a restricted-measure integral on `Iβ`
            have hab : aβ ≤ bβ := by simp [aβ, bβ]
            have hIβ : Iβ = Set.Ioc aβ bβ := by simp [Iβ, Set.uIoc_of_le hab]
            have hRHS :
                (∫ β in aβ..bβ, kernelTailCap * fIn β) = ∫ β, kernelTailCap * fIn β ∂μβ := by
              -- `intervalIntegral` over `[aβ,bβ]` is the set integral over `Ioc aβ bβ`,
              -- and `μβ = volume.restrict Iβ`.
              simpa [intervalIntegral.integral_of_le hab, μβ, hIβ]
            exact (le_trans hnorm_le (by simpa [hRHS]))
    _ = kernelTailCap * (∫ β, fIn β ∂μβ) := by
          simp [MeasureTheory.integral_const_mul]
    _ ≤ kernelTailCap * M2 := by
          exact mul_le_mul_of_nonneg_left hIn_le hker0

end

end Goldbach.Cert.MajorArcModules.Q0MajorTailSpec
