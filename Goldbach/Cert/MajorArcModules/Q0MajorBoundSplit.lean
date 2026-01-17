import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcModules.InnerMajorQ0Bound
import Goldbach.Cert.MajorArcModules.KernelPolyDecay
import Goldbach.Cert.MajorArcStep25MinorArcBound

/-!
`MajorArcModules/Q0MajorBoundSplit` is a bookkeeping reduction for the remaining analytic task
`‖corr_integral_major_Q0 - corrModel‖ ≤ ε₂`.

It rewrites the outer `β` integral to `[-1/2, 1/2]` and splits it into a “small β” region
`|β| ≤ 1/(4π)` and its complement. This is the clean point to insert:

- a major-arc approximation argument on the small-β region (Steps 2–5/20–21), and
- a separate tail bound on the large-β region.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit

open scoped BigOperators Interval

open Complex MeasureTheory

open Goldbach
open Goldbach.Cert.MajorArcModules.IntegralPipeline
open Goldbach.Cert.MajorArcModules.BetaLocalization
open Goldbach.Cert.MajorArcModules.CorrModel
open Goldbach.Cert.MajorArcModules.InnerMajorQ0Bound
open Goldbach.Cert.MajorArcModules.KernelPolyDecay
open Goldbach.Cert.MajorArcStep24IntegralExtraction
open Goldbach.Cert.MajorArcExponential

noncomputable section

abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0

-- Reuse the Step-25 kernel cap (purely project-defined, not analytic).
noncomputable abbrev kernelCap : ℝ := Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap

lemma kernelCap_nonneg : 0 ≤ kernelCap :=
  Goldbach.Cert.MajorArcStep25MinorArcBound.kernelCap_nonneg

lemma norm_kernelPolyC_le_kernelCap (x : UC) :
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC x‖ ≤ kernelCap := by
  simpa [kernelCap] using
    (Goldbach.Cert.MajorArcStep25MinorArcBound.norm_kernelPolyC_le_kernelCap (x := x))

/-!
### Optional: improved large-β kernel cap via second-difference decay

This is a purely deterministic bound on `kernelPolyC` restricted to `betaSmallSetᶜ` inside
`[-1/2, 1/2]`.  It is intended for the large-β tail bound in the `Q0` route.
-/

noncomputable def kernelTailCap : ℝ :=
  Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass / (16 * betaSmallRadius ^ 2)

lemma kernelTailCap_eq_pi_sq_div_255025 :
    kernelTailCap = (Real.pi ^ 2) / 255025 := by
  have hpi : (Real.pi : ℝ) ≠ 0 := by exact ne_of_gt Real.pi_pos
  unfold kernelTailCap
  rw [Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass_eq_one_div_255025]
  -- `betaSmallRadius = 1 / (4π)`, so `16 * betaSmallRadius^2 = 1 / π^2`
  simp [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, pow_two]
  field_simp [hpi]
  ring

lemma kernelTailCap_nonneg : 0 ≤ kernelTailCap := by
  have hmass : 0 ≤ Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass := by
    classical
    unfold Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass
    refine Finset.sum_nonneg ?_
    intro k hk
    exact norm_nonneg _
  have hr : 0 < betaSmallRadius := betaSmallRadius_pos
  have hden : 0 < (16 * betaSmallRadius ^ 2 : ℝ) := by
    have : 0 < betaSmallRadius ^ 2 := sq_pos_of_pos hr
    nlinarith
  exact div_nonneg hmass (le_of_lt hden)

lemma norm_kernelPolyC_le_kernelTailCap_of_mem_betaSmallSet_compl
    {β : ℝ} (hβI : |β| ≤ ((2 : ℝ)⁻¹)) (hβlarge : β ∈ betaSmallSetᶜ) :
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelTailCap := by
  classical
  have hβabs : betaSmallRadius < |β| := by
    have hnot : ¬ |β| ≤ betaSmallRadius := by
      intro hle
      have : β ∈ betaSmallSet := by
        have : -betaSmallRadius ≤ β ∧ β ≤ betaSmallRadius := (abs_le.1 hle)
        simpa [betaSmallSet, Set.mem_Icc] using this
      exact hβlarge (by simpa using this)
    exact lt_of_not_ge hnot
  have hne : ‖e β - 1‖ ≠ 0 := by
    have hlow : (4 : ℝ) * |β| ≤ ‖e β - 1‖ :=
      Goldbach.Cert.MajorArcModules.KernelPolyDecay.norm_e_sub_one_ge_four_abs (β := β) hβI
    have hpos : 0 < (4 : ℝ) * |β| := by
      have : 0 < |β| := lt_of_lt_of_le betaSmallRadius_pos (le_of_lt hβabs)
      nlinarith
    exact ne_of_gt (lt_of_lt_of_le hpos hlow)
  have hmain :
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        ≤
      Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass / ‖e β - 1‖ ^ 2 := by
    simpa [Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass] using
      (Goldbach.Cert.MajorArcModules.KernelPolyDecay.norm_kernelPolyC_le_secondDiff (β := β) hne)
  have hden_le :
      (16 : ℝ) * betaSmallRadius ^ 2 ≤ ‖e β - 1‖ ^ 2 := by
    have hlow : (4 : ℝ) * |β| ≤ ‖e β - 1‖ :=
      Goldbach.Cert.MajorArcModules.KernelPolyDecay.norm_e_sub_one_ge_four_abs (β := β) hβI
    have hsq :
        (16 : ℝ) * |β| ^ 2 ≤ ‖e β - 1‖ ^ 2 := by
      have h0 : 0 ≤ (4 : ℝ) * |β| := by nlinarith [abs_nonneg β]
      have h1 : 0 ≤ ‖e β - 1‖ := norm_nonneg _
      have hmul : ((4 : ℝ) * |β|) * ((4 : ℝ) * |β|) ≤ ‖e β - 1‖ * ‖e β - 1‖ :=
        mul_le_mul hlow hlow h0 h1
      -- normalize `(4|β|)*(4|β|)` to `16*|β|^2`
      have : (16 : ℝ) * |β| ^ 2 ≤ ‖e β - 1‖ ^ 2 := by
        have hleft : ((4 : ℝ) * |β|) * ((4 : ℝ) * |β|) = (16 : ℝ) * |β| ^ 2 := by
          ring_nf
        calc
          (16 : ℝ) * |β| ^ 2 = ((4 : ℝ) * |β|) * ((4 : ℝ) * |β|) := by simpa [hleft]
          _ ≤ ‖e β - 1‖ * ‖e β - 1‖ := hmul
          _ = ‖e β - 1‖ ^ 2 := by simp [pow_two]
      exact this
    have hr : 0 < betaSmallRadius := betaSmallRadius_pos
    have hrad : betaSmallRadius ≤ |β| := le_of_lt hβabs
    have hradSq : betaSmallRadius ^ 2 ≤ |β| ^ 2 := by
      have hr0 : 0 ≤ betaSmallRadius := le_of_lt hr
      have hβ0 : 0 ≤ |β| := abs_nonneg β
      simpa [pow_two] using (mul_le_mul hrad hrad hr0 hβ0)
    have : (16 : ℝ) * betaSmallRadius ^ 2 ≤ (16 : ℝ) * |β| ^ 2 :=
      mul_le_mul_of_nonneg_left hradSq (by norm_num)
    exact le_trans this hsq
  have hmass : 0 ≤ Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass := by
    classical
    unfold Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass
    refine Finset.sum_nonneg ?_
    intro k hk
    exact norm_nonneg _
  have hdenpos : 0 < ‖e β - 1‖ ^ 2 := by
    have : 0 < ‖e β - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    exact pow_pos this 2
  have hdiv :
      Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass / ‖e β - 1‖ ^ 2
        ≤
      Goldbach.Cert.MajorArcModules.KernelPolyDecay.secondDiffMass / (16 * betaSmallRadius ^ 2) :=
    by
      have hr : 0 < betaSmallRadius := betaSmallRadius_pos
      have hCdenpos : 0 < (16 * betaSmallRadius ^ 2 : ℝ) := by
        have : 0 < betaSmallRadius ^ 2 := sq_pos_of_pos hr
        nlinarith
      exact div_le_div_of_nonneg_left hmass hCdenpos hden_le
  exact le_trans hmain (by simpa [kernelTailCap] using hdiv)

noncomputable def betaIntegrand (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β

-- Backwards-compatible alias (older files/lemmas use the Greek-letter name).
noncomputable abbrev βIntegrand (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  betaIntegrand X N Δ β

noncomputable def corr_integral_major_Q0_small (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ),
    betaSmallSet.indicator (betaIntegrand X N Δ) β

noncomputable def corr_integral_major_Q0_large (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ),
    betaSmallSetᶜ.indicator (betaIntegrand X N Δ) β

theorem corr_integral_major_Q0_eq_small_add_large
    (X N : ℕ) (Δ : ℝ)
    (hInt : IntervalIntegrable (βIntegrand X N Δ) volume (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) :
    corr_integral_major_Q0 X N Δ
      =
    corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ := by
  -- Shift `[0,1]` to `[-1/2,1/2]`, then split by `betaSmallSet`.
  have hShift :
      corr_integral_major_Q0 X N Δ
        =
      ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ), betaIntegrand X N Δ β := by
    simpa [betaIntegrand] using
      (Goldbach.Cert.MajorArcModules.BetaLocalization.corr_integral_major_Q0_eq_intervalIntegral_negHalf_half
        (X := X) (N := N) (Δ := Δ))
  rw [hShift]
  have hSplit :=
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegral_negHalf_half_eq_small_add_large
      (f := βIntegrand X N Δ) hInt
  simpa [corr_integral_major_Q0_small, corr_integral_major_Q0_large, betaIntegrand] using hSplit

theorem norm_corr_integral_major_Q0_sub_corrModel_le_of_small_large
    {X N : ℕ} {Δ εs εl : ℝ}
    (hdecomp :
      corr_integral_major_Q0 X N Δ
        =
      corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ)
    (hs :
      ‖corr_integral_major_Q0_small X N Δ - corrModel N‖ ≤ εs)
    (hl :
      ‖corr_integral_major_Q0_large X N Δ‖ ≤ εl) :
    ‖corr_integral_major_Q0 X N Δ - corrModel N‖ ≤ εs + εl := by
  have hrewrite :
      corr_integral_major_Q0 X N Δ - corrModel N
        =
      (corr_integral_major_Q0_small X N Δ - corrModel N) + corr_integral_major_Q0_large X N Δ := by
    -- Substitute `corr = small + large`, then reassociate by ring arithmetic.
    calc
      corr_integral_major_Q0 X N Δ - corrModel N
          =
        (corr_integral_major_Q0_small X N Δ + corr_integral_major_Q0_large X N Δ) - corrModel N := by
            simpa [hdecomp]
      _ =
        (corr_integral_major_Q0_small X N Δ - corrModel N) + corr_integral_major_Q0_large X N Δ := by
            ring
  have htri :
      ‖(corr_integral_major_Q0_small X N Δ - corrModel N) + corr_integral_major_Q0_large X N Δ‖
        ≤ ‖corr_integral_major_Q0_small X N Δ - corrModel N‖ + ‖corr_integral_major_Q0_large X N Δ‖ := by
    simpa using
      (norm_add_le (corr_integral_major_Q0_small X N Δ - corrModel N)
        (corr_integral_major_Q0_large X N Δ))
  calc
    ‖corr_integral_major_Q0 X N Δ - corrModel N‖
        = ‖(corr_integral_major_Q0_small X N Δ - corrModel N) + corr_integral_major_Q0_large X N Δ‖ := by
            simpa [hrewrite]
    _ ≤ ‖corr_integral_major_Q0_small X N Δ - corrModel N‖ + ‖corr_integral_major_Q0_large X N Δ‖ := htri
    _ ≤ εs + εl := add_le_add hs hl

/-!
### Large-β tail reduction (via a direct bound on `innerMajorQ0`)

In some routes it is easier to bound the already-extracted `Q0` major-arc inner integral
`innerMajorQ0 X N Δ β` uniformly on the large-β region, without first producing per-arc bounds on
`innerIntegrand`. The following lemma packages that reduction.
-/

/--
If `innerMajorQ0 X N Δ β` is uniformly bounded by `M` on `[-1/2,1/2]`, then the large-β tail
`corr_integral_major_Q0_large` is bounded by `kernelTailCap * M`.

This uses only the deterministic kernel decay bound on `betaSmallSetᶜ` and does not require any
major-arc (α-side) estimates.
-/
theorem norm_corr_integral_major_Q0_large_le_kernelTailCap_mul_of_innerMajorQ0_le
    {X N : ℕ} {Δ M : ℝ}
    (hM0 : 0 ≤ M)
    (hM :
      ∀ β : ℝ, β ∈ (Ι (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)) →
        β ∈ betaSmallSetᶜ → ‖innerMajorQ0 X N Δ β‖ ≤ M) :
    ‖corr_integral_major_Q0_large X N Δ‖ ≤ kernelTailCap * M := by
  classical
  have houter :
      ∀ β ∈ (Ι (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)),
        ‖betaSmallSetᶜ.indicator (βIntegrand X N Δ) β‖ ≤ kernelTailCap * M := by
    intro β hβI
    by_cases hβ : β ∈ betaSmallSetᶜ
    · have hab : (-( (2 : ℝ)⁻¹) : ℝ) ≤ ((2 : ℝ)⁻¹ : ℝ) := by nlinarith
      have hβabs : |β| ≤ ((2 : ℝ)⁻¹) := by
        have hmem : β ∈ Set.Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ) := by
          simpa [Set.uIoc_of_le hab] using hβI
        refine (abs_le).2 ?_
        exact ⟨le_of_lt hmem.1, hmem.2⟩
      have hK :
          ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelTailCap :=
        norm_kernelPolyC_le_kernelTailCap_of_mem_betaSmallSet_compl (β := β) hβabs hβ
      have hI : ‖innerMajorQ0 X N Δ β‖ ≤ M := hM β hβI hβ
      have hmul :
          ‖βIntegrand X N Δ β‖ ≤ kernelTailCap * M := by
        calc
          ‖βIntegrand X N Δ β‖
              = ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
                  * ‖innerMajorQ0 X N Δ β‖ := by
                    simp [βIntegrand, betaIntegrand, norm_mul]
          _ ≤ kernelTailCap * M := by
                    exact mul_le_mul hK hI (norm_nonneg _) kernelTailCap_nonneg
      simpa [βIntegrand, Set.indicator_of_mem hβ] using hmul
    · have h0 : ‖(0 : ℂ)‖ ≤ kernelTailCap * M := by
        have : 0 ≤ kernelTailCap * M := mul_nonneg kernelTailCap_nonneg hM0
        simpa using this
      simpa [Set.indicator_of_notMem hβ] using h0

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-( (2 : ℝ)⁻¹) : ℝ)) (b := ((2 : ℝ)⁻¹ : ℝ)) (C := kernelTailCap * M)
      (f := fun β : ℝ => betaSmallSetᶜ.indicator (βIntegrand X N Δ) β)
      houter

  have habs : |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| = (1 : ℝ) := by
    norm_num

  have h' :
      ‖corr_integral_major_Q0_large X N Δ‖
        ≤ (kernelTailCap * M) * |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| := by
    simpa [corr_integral_major_Q0_large] using h
  calc
    ‖corr_integral_major_Q0_large X N Δ‖
        ≤ (kernelTailCap * M) * |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| := h'
    _ = kernelTailCap * M := by
        rw [habs]
        simp [mul_assoc]

/--
Large-β tail reduction: if `innerIntegrand` is uniformly bounded on each textbook arc by a
nonnegative constant `C q a` (independent of `β`), then `corr_integral_major_Q0_large` is bounded
by `kernelCap` times the explicit `(q,a)` arc-length sum.
-/
theorem norm_corr_integral_major_Q0_large_le_of_arc_bounds
    {X N : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hXpos : 0 < X)
    (hsep : SepQ0 X Δ)
    (hInt : ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (C : ℕ → ℕ → ℝ)
    (hC0 :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, 0 ≤ C q a)
    (hC :
      ∀ (β : ℝ),
        ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            ∀ α : ℝ, α ∈ arcSetTextbook X q a Δ → ‖innerIntegrand X N β α‖ ≤ C q a) :
    ‖corr_integral_major_Q0_large X N Δ‖
      ≤
    kernelCap *
      (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ))))) := by
  classical
  -- Define the uniform bound `M` coming from arc lengths.
  set M : ℝ :=
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ))))

  have hM0 : 0 ≤ M := by
    have hXposR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
    refine Finset.sum_nonneg ?_
    intro q hqIcc
    have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hqIcc).1
    have hqposR : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
    have hlen0 : 0 ≤ (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
      have hdenpos : 0 < (q : ℝ) * (X : ℝ) := mul_pos hqposR hXposR
      have : 0 ≤ Δ / ((q : ℝ) * (X : ℝ)) := div_nonneg hΔ (le_of_lt hdenpos)
      nlinarith
    have hinner :
        0 ≤
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
      refine Finset.sum_nonneg ?_
      intro a ha
      exact mul_nonneg (hC0 q hqIcc a ha) hlen0
    exact hinner

  have hInnerMajor : ∀ β : ℝ, ‖innerMajorQ0 X N Δ β‖ ≤ M := by
    intro β
    have h :=
      Goldbach.Cert.MajorArcModules.InnerMajorQ0Bound.norm_innerMajorQ0_le_sum_arc_bounds
        (X := X) (N := N) (Δ := Δ) (β := β)
        hΔ hXpos hsep (hInt β) C hC0 (hC β)
    simpa [M] using h

  -- Pointwise bound for the β-integrand on `[-1/2, 1/2]`.
  have houter :
      ∀ β ∈ (Ι (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)),
        ‖betaSmallSetᶜ.indicator (βIntegrand X N Δ) β‖ ≤ kernelCap * M := by
    intro β _hβI
    by_cases hβ : β ∈ betaSmallSetᶜ
    · have hK : ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelCap :=
        norm_kernelPolyC_le_kernelCap (x := (β : UC))
      have hI : ‖innerMajorQ0 X N Δ β‖ ≤ M := hInnerMajor β
      have hmul :
          ‖βIntegrand X N Δ β‖ ≤ kernelCap * M := by
        calc
          ‖βIntegrand X N Δ β‖
              = ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
                  * ‖innerMajorQ0 X N Δ β‖ := by
                    simp [βIntegrand, betaIntegrand, norm_mul]
          _ ≤ kernelCap * M := by
                    exact mul_le_mul hK hI (norm_nonneg _) kernelCap_nonneg
      simpa [βIntegrand, Set.indicator_of_mem hβ] using hmul
    · have h0 : ‖(0 : ℂ)‖ ≤ kernelCap * M := by
        have : 0 ≤ kernelCap * M := mul_nonneg kernelCap_nonneg hM0
        simpa using this
      simpa [Set.indicator_of_notMem hβ] using h0

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-( (2 : ℝ)⁻¹) : ℝ)) (b := ((2 : ℝ)⁻¹ : ℝ)) (C := kernelCap * M)
      (f := fun β : ℝ => betaSmallSetᶜ.indicator (βIntegrand X N Δ) β)
      houter

  have habs : |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| = (1 : ℝ) := by
    norm_num

  -- The interval length is `1`, so the extra factor from the generic norm bound disappears.
  have h' :
      ‖corr_integral_major_Q0_large X N Δ‖
        ≤ (kernelCap * M) * |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| := by
    simpa [corr_integral_major_Q0_large] using h
  calc
    ‖corr_integral_major_Q0_large X N Δ‖
        ≤ (kernelCap * M) * |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| := h'
    _ = kernelCap * M := by
        rw [habs]
        simp [mul_assoc]
    _ = kernelCap *
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ))))) := by
        simp [M]

end

/--
Variant of `norm_corr_integral_major_Q0_large_le_of_arc_bounds` using the improved tail cap
`kernelTailCap`, which is valid on `betaSmallSetᶜ ⊆ [-1/2,1/2]`.

This is intended for the turnkey `Q0` route, where the large-β term is exactly the integral
of `betaSmallSetᶜ.indicator` over `[-1/2,1/2]`.
-/
theorem norm_corr_integral_major_Q0_large_le_of_arc_bounds_tailCap
    {X N : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hXpos : 0 < X)
    (hsep : SepQ0 X Δ)
    (hInt : ∀ β : ℝ, IntervalIntegrable (fun α : ℝ => innerIntegrand X N β α) volume (0 : ℝ) (1 : ℝ))
    (C : ℕ → ℕ → ℝ)
    (hC0 :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q, 0 ≤ C q a)
    (hC :
      ∀ (β : ℝ),
        ∀ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            ∀ α : ℝ, α ∈ arcSetTextbook X q a Δ → ‖innerIntegrand X N β α‖ ≤ C q a) :
    ‖corr_integral_major_Q0_large X N Δ‖
      ≤
    kernelTailCap *
      (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
        ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
          (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ))))) := by
  classical
  -- Define the uniform bound `M` coming from arc lengths.
  set M : ℝ :=
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ))))

  have hM0 : 0 ≤ M := by
    have hXposR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hXpos
    refine Finset.sum_nonneg ?_
    intro q hqIcc
    have hq1 : 1 ≤ q := (Finset.mem_Icc.1 hqIcc).1
    have hqposR : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
    have hlen0 : 0 ≤ (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
      have hdenpos : 0 < (q : ℝ) * (X : ℝ) := mul_pos hqposR hXposR
      have : 0 ≤ Δ / ((q : ℝ) * (X : ℝ)) := div_nonneg hΔ (le_of_lt hdenpos)
      nlinarith
    have hinner :
        0 ≤
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ)))) := by
      refine Finset.sum_nonneg ?_
      intro a ha
      exact mul_nonneg (hC0 q hqIcc a ha) hlen0
    exact hinner

  have hInnerMajor : ∀ β : ℝ, ‖innerMajorQ0 X N Δ β‖ ≤ M := by
    intro β
    have h :=
      Goldbach.Cert.MajorArcModules.InnerMajorQ0Bound.norm_innerMajorQ0_le_sum_arc_bounds
        (X := X) (N := N) (Δ := Δ) (β := β)
        hΔ hXpos hsep (hInt β) C hC0 (hC β)
    simpa [M] using h

  -- Pointwise bound for the β-integrand on `[-1/2, 1/2]`.
  have houter :
      ∀ β ∈ (Ι (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ)),
        ‖betaSmallSetᶜ.indicator (βIntegrand X N Δ) β‖ ≤ kernelTailCap * M := by
    intro β hβI
    by_cases hβ : β ∈ betaSmallSetᶜ
    · have hβabs : |β| ≤ ((2 : ℝ)⁻¹) := by
        have hab : (-( (2 : ℝ)⁻¹) : ℝ) ≤ ((2 : ℝ)⁻¹ : ℝ) := by nlinarith
        have hmem : β ∈ Set.Ioc (-( (2 : ℝ)⁻¹) : ℝ) ((2 : ℝ)⁻¹ : ℝ) := by
          simpa [Set.uIoc_of_le hab] using hβI
        refine (abs_le).2 ?_
        exact ⟨le_of_lt hmem.1, hmem.2⟩
      have hK :
          ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ ≤ kernelTailCap :=
        norm_kernelPolyC_le_kernelTailCap_of_mem_betaSmallSet_compl (β := β) hβabs hβ
      have hI : ‖innerMajorQ0 X N Δ β‖ ≤ M := hInnerMajor β
      have hmul :
          ‖βIntegrand X N Δ β‖ ≤ kernelTailCap * M := by
        calc
          ‖βIntegrand X N Δ β‖
              = ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
                  * ‖innerMajorQ0 X N Δ β‖ := by
                    simp [βIntegrand, betaIntegrand, norm_mul]
          _ ≤ kernelTailCap * M := by
                    exact mul_le_mul hK hI (norm_nonneg _) kernelTailCap_nonneg
      simpa [βIntegrand, Set.indicator_of_mem hβ] using hmul
    · have h0 : ‖(0 : ℂ)‖ ≤ kernelTailCap * M := by
        have : 0 ≤ kernelTailCap * M := mul_nonneg kernelTailCap_nonneg hM0
        simpa using this
      simpa [Set.indicator_of_notMem hβ] using h0

  have h :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-( (2 : ℝ)⁻¹) : ℝ)) (b := ((2 : ℝ)⁻¹ : ℝ)) (C := kernelTailCap * M)
      (f := fun β : ℝ => betaSmallSetᶜ.indicator (βIntegrand X N Δ) β)
      houter

  have habs : |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| = (1 : ℝ) := by
    norm_num

  -- The interval length is `1`, so the extra factor from the generic norm bound disappears.
  have h' :
      ‖corr_integral_major_Q0_large X N Δ‖
        ≤ (kernelTailCap * M) * |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| := by
    simpa [corr_integral_major_Q0_large] using h
  calc
    ‖corr_integral_major_Q0_large X N Δ‖
        ≤ (kernelTailCap * M) * |((2 : ℝ)⁻¹ - (-( (2 : ℝ)⁻¹)))| := h'
    _ = kernelTailCap * M := by
        rw [habs]
        simp [mul_assoc]
    _ = kernelTailCap *
        (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
          ∑ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            (C q a) * (2 * (Δ / ((q : ℝ) * (X : ℝ))))) := by
        simp [M]

end Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
