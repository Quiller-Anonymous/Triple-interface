import Goldbach.Cert.MajorArcModules.BetaLocalization
import Goldbach.Cert.MajorArcModules.CorrModel
import Goldbach.Cert.MajorArcModules.InnerMajorQ0Bound
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
open Goldbach.Cert.MajorArcStep24IntegralExtraction

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

private noncomputable def βIntegrand (X N : ℕ) (Δ : ℝ) (β : ℝ) : ℂ :=
  Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) * innerMajorQ0 X N Δ β

noncomputable def corr_integral_major_Q0_small (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ),
    betaSmallSet.indicator (βIntegrand X N Δ) β

noncomputable def corr_integral_major_Q0_large (X N : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ),
    betaSmallSetᶜ.indicator (βIntegrand X N Δ) β

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
      ∫ β in (-( (2 : ℝ)⁻¹) : ℝ)..((2 : ℝ)⁻¹ : ℝ), βIntegrand X N Δ β := by
    simpa [βIntegrand] using
      (Goldbach.Cert.MajorArcModules.BetaLocalization.corr_integral_major_Q0_eq_intervalIntegral_negHalf_half
        (X := X) (N := N) (Δ := Δ))
  rw [hShift]
  have hSplit :=
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegral_negHalf_half_eq_small_add_large
      (f := βIntegrand X N Δ) hInt
  simpa [corr_integral_major_Q0_small, corr_integral_major_Q0_large, βIntegrand] using hSplit

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
                    simp [βIntegrand]
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

end Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
