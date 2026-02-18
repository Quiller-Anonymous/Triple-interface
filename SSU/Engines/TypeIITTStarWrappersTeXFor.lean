import SSU.Engines.TypeII
import SSU.Engines.TypeIILargeSieveTeXFor
import SSU.Engines.TypeIIBalancedXiTeX
import SSU.Engines.TypeIITTStarWrappersTeX

/-!
Per-signal (“use-site”) TeX TT* wrapper.

`SSU/Engines/TypeIITTStarWrappersTeX.lean` produces a *global* `SingleTubeSSUStatement` from
global Step 3–5 and balanced-ξ hypotheses (i.e. bounds that quantify over **all** `F`).

In practice, many intermediate reductions only need the TeX TT* conclusion for one extracted
coefficient array `F`. This file provides that deterministic wrapper.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

open MeasureTheory

private theorem tubeEnergy_nonneg (T : Finset TubePoint) (F : TubePoint → ℂ) :
    0 ≤ _root_.SSU.tubeEnergy T F := by
  classical
  unfold _root_.SSU.tubeEnergy
  refine Finset.sum_nonneg ?_
  intro p hp
  positivity

/-- TeX TT* wrapper specialized to a single coefficient array `F`. -/
theorem norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor
    (td : TubeData) (K : ℤ → ℝ) (F : TubePoint → ℂ)
    (h2 : Step2ToTubeForm td K)
    (h34 : Step34LargeSieveTeXFor td F)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D) :
    ‖tubeForm K td.T F‖ ≤
      (h34.C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
        tubeEnergy td.T F := by
  classical
  let s : Set ℝ := Set.Icc (-(1 / td.H)) (1 / td.H)
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability

  -- Reduce to a real ξ-integral.
  let r : ℝ :=
    ∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)
  have htube : tubeForm K td.T F = (r : ℂ) := by
    -- Start from the complex-valued integral form, then convert it into the cast of the real integral.
    have htex :
        tubeForm K td.T F =
          ∫ ξ in s,
            ((h2.Khat ξ : ℝ) : ℂ) *
              (↑‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) := by
      -- `h2.tubeForm_eq` is stated as a cast of a real integral; `simp` rewrites it into this form.
      simpa [s] using (h2.tubeForm_eq (td := td) (K := K) F)
    have hrew0 :
        (∫ ξ in s,
            ((h2.Khat ξ : ℝ) : ℂ) *
              (↑‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2))
          =
        ∫ ξ in s,
          (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ) := by
      refine integral_congr_ae ?_
      refine ae_of_all _ (fun ξ => ?_)
      simp [mul_assoc]
    have hrew1 :
        (∫ ξ in s,
            (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ))
          =
        (r : ℂ) := by
      -- `integral_ofReal` on the restricted measure.
      have hbase :
          (∫ ξ in s,
              (((h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2) : ℝ) : ℂ))
            =
          (↑(∫ ξ in s, (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ) := by
        exact
          (integral_ofReal
            (𝕜 := ℂ)
            (μ := (volume : Measure ℝ).restrict s)
            (f := fun ξ : ℝ =>
              (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)))
      simpa [r] using hbase
    exact htex.trans (hrew0.trans hrew1)
  have hnorm : ‖tubeForm K td.T F‖ = |r| := by
    simpa [htube, RCLike.norm_ofReal] using congrArg (fun z : ℂ => ‖z‖) htube

  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    refine integral_nonneg_of_ae ?_
    refine ae_of_all _ (fun ξ => ?_)
    have hK0 : 0 ≤ h2.Khat ξ := hbal.Khat_nonneg ξ
    have hS0 : 0 ≤ (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2 : ℝ) := by positivity
    exact mul_nonneg hK0 hS0
  have habs_r : |r| = r := abs_of_nonneg hr_nonneg

  -- Pointwise (a.e.) Step 5 bound on `‖S(ξ)‖²`, multiplied by `Khat(ξ)`.
  have hbound_ae :
      (fun ξ : ℝ =>
          (h2.Khat ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2))
        ≤ᵐ[(volume : Measure ℝ).restrict s]
      fun ξ : ℝ =>
        (h2.Khat ξ) *
          (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X * invAbs ξ) *
                Real.sqrt (td.D + td.X * invAbs ξ) *
                  tubeEnergy td.T F) := by
    -- Work a.e. on `s` and away from `0`.
    have hne0 : ∀ᵐ ξ ∂(volume : Measure ℝ).restrict s, ξ ≠ 0 := by
      refine (ae_iff.2 ?_)
      have hnull : ((volume : Measure ℝ).restrict s) ({0} : Set ℝ) = 0 := by
        simp [Measure.restrict_apply, hs]
      have hset : {ξ : ℝ | ¬ ξ ≠ 0} = ({0} : Set ℝ) := by
        ext ξ
        by_cases hξ : ξ = 0 <;> simp [hξ]
      simpa [hset] using hnull
    filter_upwards [ae_restrict_mem hs, hne0] with ξ hξs hξ0
    have hinv : invAbs ξ = 1 / |ξ| := invAbs_eq_one_div_abs (ξ := ξ) hξ0
    have hS :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        h34.C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            Real.sqrt (td.U + td.X / |ξ|) *
              Real.sqrt (td.D + td.X / |ξ|) *
                tubeEnergy td.T F :=
      h34.bound_outerGeom ξ hξ0 (by simpa [s] using hξs)
    have hS' :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        h34.C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            Real.sqrt (td.U + td.X * invAbs ξ) *
              Real.sqrt (td.D + td.X * invAbs ξ) *
                tubeEnergy td.T F := by
      simpa [hinv, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hS
    have hK0 : 0 ≤ h2.Khat ξ := hbal.Khat_nonneg ξ
    exact mul_le_mul_of_nonneg_left hS' hK0

  have hint :
      r
        ≤
      ∫ ξ in s,
        (h2.Khat ξ) *
          (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              Real.sqrt (td.U + td.X * invAbs ξ) *
                Real.sqrt (td.D + td.X * invAbs ξ) *
                  tubeEnergy td.T F) := by
    dsimp [r]
    refine
      MeasureTheory.integral_mono_of_nonneg
        (μ := (volume : Measure ℝ).restrict s)
        (by
          refine ae_of_all _ (fun ξ => ?_)
          have hK0 : 0 ≤ h2.Khat ξ := hbal.Khat_nonneg ξ
          have hS0 : 0 ≤ (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2 : ℝ) := by positivity
          exact mul_nonneg hK0 hS0)
        (by
          have hintBase :
              IntegrableOn
                (fun ξ : ℝ =>
                  (h2.Khat ξ) *
                    Real.sqrt (td.U + td.X * invAbs ξ) *
                      Real.sqrt (td.D + td.X * invAbs ξ))
                s := by
            simpa [band, s] using (hbal.integrable (U := td.U) (D := td.D) hU hD)
          have hintBase' :
              Integrable
                (fun ξ : ℝ =>
                  (h2.Khat ξ) *
                    Real.sqrt (td.U + td.X * invAbs ξ) *
                      Real.sqrt (td.D + td.X * invAbs ξ))
                ((volume : Measure ℝ).restrict s) := by
            simpa [Measure.restrict_restrict, hs] using hintBase
          have :
              (fun ξ : ℝ =>
                  (h2.Khat ξ) *
                    (h34.C *
                      Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                        Real.sqrt (td.U + td.X * invAbs ξ) *
                          Real.sqrt (td.D + td.X * invAbs ξ) *
                            tubeEnergy td.T F))
                =
              fun ξ : ℝ =>
                (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
                  ((h2.Khat ξ) *
                    Real.sqrt (td.U + td.X * invAbs ξ) *
                      Real.sqrt (td.D + td.X * invAbs ξ)) := by
            funext ξ; ring
          simpa [this] using
            (hintBase'.const_mul
              (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F)))
        hbound_ae

  -- Pull constants out and apply the balanced-ξ bound.
  have hpull :
      (∫ ξ in s,
          (h2.Khat ξ) *
            (h34.C *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + td.X * invAbs ξ) *
                  Real.sqrt (td.D + td.X * invAbs ξ) *
                    tubeEnergy td.T F))
        =
      (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
        (∫ ξ in s,
          (h2.Khat ξ) *
            Real.sqrt (td.U + td.X * invAbs ξ) *
              Real.sqrt (td.D + td.X * invAbs ξ)) := by
    set c : ℝ := h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F
    have hcongr :
        (fun ξ : ℝ =>
            (h2.Khat ξ) *
              (h34.C *
                Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                  Real.sqrt (td.U + td.X * invAbs ξ) *
                    Real.sqrt (td.D + td.X * invAbs ξ) *
                      tubeEnergy td.T F))
          =
        fun ξ : ℝ =>
          c *
            ((h2.Khat ξ) *
              Real.sqrt (td.U + td.X * invAbs ξ) *
                Real.sqrt (td.D + td.X * invAbs ξ)) := by
      funext ξ
      simp [c]
      ring
    simp [hcongr, c, MeasureTheory.integral_const_mul]

  have hbalInt :
      (∫ ξ in s,
          (h2.Khat ξ) *
            Real.sqrt (td.U + td.X * invAbs ξ) *
              Real.sqrt (td.D + td.X * invAbs ξ))
        ≤
      hbal.C *
        ((td.U * td.D) / td.H
          + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
              Real.sqrt (td.H * Real.log td.H)
          + td.X) := by
    simpa [band, s] using (hbal.bound (U := td.U) (D := td.D) hU hD)

  have hr_le :
      r ≤
        (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
          (hbal.C *
            ((td.U * td.D) / td.H
              + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                  Real.sqrt (td.H * Real.log td.H)
              + td.X)) := by
    calc
      r
          ≤
        ∫ ξ in s,
          (h2.Khat ξ) *
            (h34.C *
              Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
                Real.sqrt (td.U + td.X * invAbs ξ) *
                  Real.sqrt (td.D + td.X * invAbs ξ) *
                    tubeEnergy td.T F) := hint
      _ =
        (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
          (∫ ξ in s,
            (h2.Khat ξ) *
              Real.sqrt (td.U + td.X * invAbs ξ) *
                Real.sqrt (td.D + td.X * invAbs ξ)) := hpull
      _ ≤
        (h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F) *
          (hbal.C *
            ((td.U * td.D) / td.H
              + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                  Real.sqrt (td.H * Real.log td.H)
              + td.X)) := by
        have hconst0 :
            0 ≤ h34.C * Real.sqrt ((td.D * td.U) / (td.q : ℝ)) * tubeEnergy td.T F := by
          refine
            mul_nonneg
              (mul_nonneg h34.C_nonneg (Real.sqrt_nonneg _))
              (by simpa [tubeEnergy] using (tubeEnergy_nonneg (T := td.T) (F := F)))
        exact mul_le_mul_of_nonneg_left hbalInt hconst0

  have hEq : ‖tubeForm K td.T F‖ = r := by
    simpa [hnorm, habs_r]
  have hE :
      r ≤
        (h34.C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
          tubeEnergy td.T F := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hr_le
  exact (hEq ▸ hE)

/-!
## Convenience: Step 3 + Step 4 (use-site) ⇒ Step 5 ⇒ TT*

TeX derives Step 5 by combining the Step 3 and Step 4 large-sieve bounds via the geometric mean.
This wrapper constructs the Step 5 bound deterministically and then applies the TT* conclusion.
-/

theorem norm_tubeForm_le_of_step2ToTubeForm_step3_step4TeXFor
    (td : TubeData) (K : ℤ → ℝ) (F : TubePoint → ℂ)
    (h2 : Step2ToTubeForm td K)
    (h3 : Step3LargeSieveOuterUFor td F) (h4 : Step4LargeSieveOuterVFor td F)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hU1 : 1 ≤ td.U) (hD1 : 1 ≤ td.D) (hX : 0 ≤ td.X) :
    ‖tubeForm K td.T F‖ ≤
      ((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
            (td := td) (F := F) h3 h4
            (hD := lt_of_lt_of_le (by linarith) hD1)
            (hU := lt_of_lt_of_le (by linarith) hU1)
            hX).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
        tubeEnergy td.T F := by
  classical
  let h34 : Step34LargeSieveTeXFor td F :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      (td := td) (F := F) h3 h4
      (hD := lt_of_lt_of_le (by linarith) hD1)
      (hU := lt_of_lt_of_le (by linarith) hU1)
      hX
  simpa [h34] using
    (norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor
      (td := td) (K := K) (F := F) (h2 := h2) (h34 := h34) (hbal := hbal)
      (hU := hU1) (hD := hD1))

/-- Convenience specialization: route Step 3/4 Montgomery–Vaughan hypotheses through the
use-site TeX Step 5 combiner and then apply TT*. -/
theorem norm_tubeForm_le_of_step2ToTubeForm_step3MV_step4MV
    (td : TubeData) (K : ℤ → ℝ) (F : TubePoint → ℂ)
    (h2 : Step2ToTubeForm td K)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hU1 : 1 ≤ td.U) (hD1 : 1 ≤ td.D) :
    ‖tubeForm K td.T F‖ ≤
      ((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MV_step4MV
            (td := td) (F := F) (h3MV := h3MV) (h4MV := h4MV)
            (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
            (hD := lt_of_lt_of_le (by linarith) hD1)
            (hU := lt_of_lt_of_le (by linarith) hU1)).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
        tubeEnergy td.T F := by
  classical
  let h34 : Step34LargeSieveTeXFor td F :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MV_step4MV
      (td := td) (F := F) (h3MV := h3MV) (h4MV := h4MV)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hD := lt_of_lt_of_le (by linarith) hD1)
      (hU := lt_of_lt_of_le (by linarith) hU1)
  simpa [h34] using
    (norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor
      (td := td) (K := K) (F := F) (h2 := h2) (h34 := h34) (hbal := hbal)
      (hU := hU1) (hD := hD1))

/-- Convenience specialization: route per-residue Step 3/4 Montgomery–Vaughan hypotheses through
residue summation, the use-site TeX Step 5 combiner, and then apply TT*. -/
theorem norm_tubeForm_le_of_step2ToTubeForm_step3MVByResidue_step4MVByResidue
    (td : TubeData) (K : ℤ → ℝ) (F : TubePoint → ℂ)
    (h2 : Step2ToTubeForm td K)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hU1 : 1 ≤ td.U) (hD1 : 1 ≤ td.D) :
    ‖tubeForm K td.T F‖ ≤
      ((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
            (td := td) (F := F) (h3MV := h3MV) (h4MV := h4MV)
            (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
            (hD := lt_of_lt_of_le (by linarith) hD1)
            (hU := lt_of_lt_of_le (by linarith) hU1)).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
        tubeEnergy td.T F := by
  classical
  let h34 : Step34LargeSieveTeXFor td F :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
      (td := td) (F := F) (h3MV := h3MV) (h4MV := h4MV)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hD := lt_of_lt_of_le (by linarith) hD1)
      (hU := lt_of_lt_of_le (by linarith) hU1)
  simpa [h34] using
    (norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor
      (td := td) (K := K) (F := F) (h2 := h2) (h34 := h34) (hbal := hbal)
      (hU := hU1) (hD := hD1))

/-- Convenience specialization: route fixed-`F` residue-class Step 3/4 fiber hypotheses through
the use-site TeX Step 5 combiner and then apply TT*. -/
theorem norm_tubeForm_le_of_step2ToTubeForm_step3FiberByResidueFor_step4FiberByResidueFor
    (td : TubeData) (K : ℤ → ℝ) (F : TubePoint → ℂ)
    (h2 : Step2ToTubeForm td K)
    (h3R : Step3FiberLargeSieveByResidueFor td F)
    (h4R : Step4FiberLargeSieveByResidueFor td F)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX0 : 0 ≤ td.X)
    (hU1 : 1 ≤ td.U) (hD1 : 1 ≤ td.D) :
    ‖tubeForm K td.T F‖ ≤
      ((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3FiberByResidueFor_step4FiberByResidueFor
            (td := td) (F := F) h3R h4R
            (hD := lt_of_lt_of_le (by linarith) hD1)
            (hU := lt_of_lt_of_le (by linarith) hU1)
            (hX := hX0)).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
        tubeEnergy td.T F := by
  classical
  let h34 : Step34LargeSieveTeXFor td F :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3FiberByResidueFor_step4FiberByResidueFor
      (td := td) (F := F) h3R h4R
      (hD := lt_of_lt_of_le (by linarith) hD1)
      (hU := lt_of_lt_of_le (by linarith) hU1)
      (hX := hX0)
  simpa [h34] using
    (norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor
      (td := td) (K := K) (F := F) (h2 := h2) (h34 := h34) (hbal := hbal)
      (hU := hU1) (hD := hD1))

/-- Convenience specialization: build the use-site Step 3/4 bounds from const-coefficient hypotheses
and then apply the Step 3+4 ⇒ Step 5 ⇒ TT* wrapper. -/
theorem norm_tubeForm_le_of_step2ToTubeForm_constCoeffUZFin_constCoeffVZFin
    (td : TubeData) (K : ℤ → ℝ) (F : TubePoint → ℂ)
    (h2 : Step2ToTubeForm td K)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U) (hU0 : 0 ≤ td.U)
    (hXH1 : 1 ≤ td.X * td.H)
    (hD0 : 0 ≤ td.D)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH_u : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (hXH_v : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (aU : Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td) → ℂ)
    (aV : Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td) → ℂ)
    (hCoeffU :
      ∀ u : ℤ, u ∈ SSU.Engines.TypeII.LargeSieve.uSet td →
        SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F u = aU)
    (hCoeffV :
      ∀ v : ℤ, v ∈ SSU.Engines.TypeII.LargeSieve.vSet td →
        SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F v = aV) :
    ‖tubeForm K td.T F‖ ≤
      ((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
            (td := td) (F := F)
            (SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_constCoeffUZFin
              (td := td) (hDq := hDq) (hU1 := hU1) (hU0 := hU0) (hX := hX) (hH := hH)
              (hXH_u := hXH_u) (F := F) (aU := aU) (hCoeffU := hCoeffU))
            (SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_constCoeffVZFin
              (td := td) (hXH1 := hXH1) (hD1 := hD1) (hU0 := hU0) (hD0 := hD0)
              (hX := hX) (hH := hH) (hXH_v := hXH_v) (F := F) (aV := aV) (hCoeffV := hCoeffV))
            (hD := lt_of_lt_of_le (by linarith) hD1)
            (hU := lt_of_lt_of_le (by linarith) hU1)
            (hX := le_of_lt hX)).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
        tubeEnergy td.T F := by
  classical
  let h3 : Step3LargeSieveOuterUFor td F :=
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_constCoeffUZFin
      (td := td) (hDq := hDq) (hU1 := hU1) (hU0 := hU0) (hX := hX) (hH := hH)
      (hXH_u := hXH_u) (F := F) (aU := aU) (hCoeffU := hCoeffU)
  let h4 : Step4LargeSieveOuterVFor td F :=
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_constCoeffVZFin
      (td := td) (hXH1 := hXH1) (hD1 := hD1) (hU0 := hU0) (hD0 := hD0)
      (hX := hX) (hH := hH) (hXH_v := hXH_v) (F := F) (aV := aV) (hCoeffV := hCoeffV)
  simpa [h3, h4] using
    (norm_tubeForm_le_of_step2ToTubeForm_step3_step4TeXFor
      (td := td) (K := K) (F := F) (h2 := h2) (h3 := h3) (h4 := h4) (hbal := hbal)
      (hU1 := hU1) (hD1 := hD1) (hX := le_of_lt hX))

/-!
### One-shot Gram bound (use-site)

This is the “plug into the reduction” wrapper: if you can provide a use-site TeX Step 5 bound for
the extracted coefficient array `R.F f i j`, then you immediately get a Gram bound for that pair.
-/

theorem norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX0 : 0 ≤ td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (f : H) (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J)
    (h34 : Step34LargeSieveTeXFor td (R.F f i j)) :
    ‖inner ℂ (T i f) (T j f)‖ ≤
      ((h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) *
          R.Cenergy) *
        ‖T i f‖ * ‖T j f‖ := by
  have hId : inner ℂ (T i f) (T j f) = tubeForm K td.T (R.F f i j) :=
    R.inner_eq (f := f) (i := i) hi (j := j) hj
  have hTube :
      ‖tubeForm K td.T (R.F f i j)‖ ≤
        (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) *
          tubeEnergy td.T (R.F f i j) :=
    (norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor
      (td := td) (K := K) (F := R.F f i j) (h2 := h2) (h34 := h34) (hbal := hbal) hU hD)
  have hEnergy :
      tubeEnergy td.T (R.F f i j) ≤ R.Cenergy * ‖T i f‖ * ‖T j f‖ :=
    R.energy_le (f := f) (i := i) hi (j := j) hj
  have hA0 :
      0 ≤
        (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) := by
    have hU0 : 0 ≤ td.U := le_trans (show (0 : ℝ) ≤ 1 by linarith) hU
    have hD0 : 0 ≤ td.D := le_trans (show (0 : ℝ) ≤ 1 by linarith) hD
    have hterm1 : 0 ≤ (td.U * td.D) / td.H :=
      div_nonneg (mul_nonneg hU0 hD0) (le_of_lt hH0)
    have hterm2 :
        0 ≤ Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
            Real.sqrt (td.H * Real.log td.H) := by
      positivity
    have hbig :
        0 ≤
          (td.U * td.D) / td.H
            + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                Real.sqrt (td.H * Real.log td.H)
            + td.X := by
      nlinarith [hterm1, hterm2, hX0]
    have hsqrt : 0 ≤ Real.sqrt ((td.D * td.U) / (td.q : ℝ)) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h34.C_nonneg hsqrt) hbal.C_nonneg) hbig
  have hmul :
      (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) *
          tubeEnergy td.T (R.F f i j)
        ≤
      (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) *
          (R.Cenergy * ‖T i f‖ * ‖T j f‖) :=
    mul_le_mul_of_nonneg_left hEnergy hA0
  have hcomb :
      ‖inner ℂ (T i f) (T j f)‖ ≤
        (h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) *
          (R.Cenergy * ‖T i f‖ * ‖T j f‖) := by
    have : ‖inner ℂ (T i f) (T j f)‖ = ‖tubeForm K td.T (R.F f i j)‖ := by
      simpa [hId]
    exact le_trans (by simpa [this] using hTube) hmul
  -- Rearrange into the advertised `(*) * ‖Ti f‖ * ‖Tj f‖` form.
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcomb

/-- One-shot Gram bound from use-site Step 3/4 hypotheses:
`Step 3 + Step 4 ⇒ Step 5 (use-site) ⇒ TT*`. -/
theorem norm_inner_le_of_reduction_step2ToTubeForm_step3_step4TeXFor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX0 : 0 ≤ td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (f : H) (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J)
    (h3 : Step3LargeSieveOuterUFor td (R.F f i j))
    (h4 : Step4LargeSieveOuterVFor td (R.F f i j)) :
    ‖inner ℂ (T i f) (T j f)‖ ≤
      (((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
            (td := td) (F := R.F f i j) h3 h4
            (hD := lt_of_lt_of_le (by linarith) hD)
            (hU := lt_of_lt_of_le (by linarith) hU)
            hX0).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
          R.Cenergy) *
        ‖T i f‖ * ‖T j f‖ := by
  classical
  let h34 : Step34LargeSieveTeXFor td (R.F f i j) :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      (td := td) (F := R.F f i j) h3 h4
      (hD := lt_of_lt_of_le (by linarith) hD)
      (hU := lt_of_lt_of_le (by linarith) hU)
      hX0
  simpa [h34] using
    (norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
      (R := R) (h2 := h2) (hbal := hbal)
      (hX0 := hX0) (hH0 := hH0) (hU := hU) (hD := hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj)
      (h34 := h34))

/-- One-shot Gram bound from Montgomery–Vaughan Step 3/4 hypotheses:
`Step 3 (MV) + Step 4 (MV) ⇒ Step 5 (use-site) ⇒ TT*`. -/
theorem norm_inner_le_of_reduction_step2ToTubeForm_step3MV_step4MV
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (f : H) (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J) :
    ‖inner ℂ (T i f) (T j f)‖ ≤
      (((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MV_step4MV
            (td := td) (F := R.F f i j) (h3MV := h3MV) (h4MV := h4MV)
            (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
            (hD := lt_of_lt_of_le (by linarith) hD)
            (hU := lt_of_lt_of_le (by linarith) hU)).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
          R.Cenergy) *
        ‖T i f‖ * ‖T j f‖ := by
  classical
  let h34 : Step34LargeSieveTeXFor td (R.F f i j) :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MV_step4MV
      (td := td) (F := R.F f i j) (h3MV := h3MV) (h4MV := h4MV)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hD := lt_of_lt_of_le (by linarith) hD)
      (hU := lt_of_lt_of_le (by linarith) hU)
  simpa [h34] using
    (norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
      (R := R) (h2 := h2) (hbal := hbal)
      (hX0 := hX0) (hH0 := hH0) (hU := hU) (hD := hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj)
      (h34 := h34))

/-- One-shot Gram bound from per-residue Montgomery–Vaughan Step 3/4 hypotheses:
`Step 3 (MV by residue) + Step 4 (MV by residue) ⇒ Step 5 (use-site) ⇒ TT*`. -/
theorem norm_inner_le_of_reduction_step2ToTubeForm_step3MVByResidue_step4MVByResidue
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (f : H) (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J) :
    ‖inner ℂ (T i f) (T j f)‖ ≤
      (((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
            (td := td) (F := R.F f i j) (h3MV := h3MV) (h4MV := h4MV)
            (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
            (hD := lt_of_lt_of_le (by linarith) hD)
            (hU := lt_of_lt_of_le (by linarith) hU)).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
          R.Cenergy) *
        ‖T i f‖ * ‖T j f‖ := by
  classical
  let h34 : Step34LargeSieveTeXFor td (R.F f i j) :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
      (td := td) (F := R.F f i j) (h3MV := h3MV) (h4MV := h4MV)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hD := lt_of_lt_of_le (by linarith) hD)
      (hU := lt_of_lt_of_le (by linarith) hU)
  simpa [h34] using
    (norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
      (R := R) (h2 := h2) (hbal := hbal)
      (hX0 := hX0) (hH0 := hH0) (hU := hU) (hD := hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj)
      (h34 := h34))

/-- One-shot Gram bound from fixed-`F` residue-class Step 3/4 fiber hypotheses:
`Step3/4 (fiber-by-residue, fixed F) ⇒ Step 5 (use-site) ⇒ TT*`. -/
theorem norm_inner_le_of_reduction_step2ToTubeForm_step3FiberByResidueFor_step4FiberByResidueFor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX0 : 0 ≤ td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (f : H) (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J)
    (h3R : Step3FiberLargeSieveByResidueFor td (R.F f i j))
    (h4R : Step4FiberLargeSieveByResidueFor td (R.F f i j)) :
    ‖inner ℂ (T i f) (T j f)‖ ≤
      (((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3FiberByResidueFor_step4FiberByResidueFor
            (td := td) (F := R.F f i j) h3R h4R
            (hD := lt_of_lt_of_le (by linarith) hD)
            (hU := lt_of_lt_of_le (by linarith) hU)
            (hX := hX0)).C *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            hbal.C *
              ((td.U * td.D) / td.H
                + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                    Real.sqrt (td.H * Real.log td.H)
                + td.X)) *
          R.Cenergy) *
        ‖T i f‖ * ‖T j f‖ := by
  classical
  let h34 : Step34LargeSieveTeXFor td (R.F f i j) :=
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3FiberByResidueFor_step4FiberByResidueFor
      (td := td) (F := R.F f i j) h3R h4R
      (hD := lt_of_lt_of_le (by linarith) hD)
      (hU := lt_of_lt_of_le (by linarith) hU)
      (hX := hX0)
  simpa [h34] using
    (norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
      (R := R) (h2 := h2) (hbal := hbal)
      (hX0 := hX0) (hH0 := hH0) (hU := hU) (hD := hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj)
      (h34 := h34))

/-- One-shot Gram bound specialized to BG rank-one coefficients via the proved one-add-log Step 3/4
residue-class bounds:
`BG one-add-log Step 3/4 (fixed F) ⇒ Step 5 (use-site) ⇒ TT*`.

This is a direct reduction-level bridge from the BG geometry/modEq hypotheses to a packet Gram
entry, assuming the extracted coefficient array matches the BG rank-one array. -/
theorem norm_inner_le_of_reduction_step2ToTubeForm_bgTubeRankOne_modEq_oneAddLog
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {K : ℤ → ℝ}
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (R : ReductionToTubeForm
      (J := J) (T := T)
      (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) K)
    (h2 : Step2ToTubeForm
      (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) K)
    (hbal : BalancedXiClaimInv
      (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X
      (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H
      h2.Khat)
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (f : H) (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          β u₁ = β u₂)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          α v₁ = α v₂)
    (hF :
      R.F f i j =
        SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff
          (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) α β) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    let h34 : Step34LargeSieveTeXFor td (R.F f i j) := by
      simpa [hF, td] using
        (SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_bgTubeRankOne_modEq_oneAddLog
          (P := P) (a := a) (q := q) hq hcop
          (ha0 := ha0) (hlower := hlower) (hupper := hupper)
          (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
          (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
          (α := α) (β := β) (hβmod := hβmod) (hαmod := hαmod))
    ‖inner ℂ (T i f) (T j f)‖ ≤
      ((h34.C *
            Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
              hbal.C *
                ((td.U * td.D) / td.H
                  + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                      Real.sqrt (td.H * Real.log td.H)
                  + td.X)) *
          R.Cenergy) *
        ‖T i f‖ * ‖T j f‖ := by
  intro td h34
  simpa [h34] using
    (norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
      (R := R) (h2 := h2) (hbal := hbal)
      (hX0 := le_of_lt hX) (hH0 := hH) (hU := hU1) (hD := hD1)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj)
      (h34 := h34))

noncomputable def gramHypothesis_of_reduction_step2ToTubeForm_step3MV_step4MV
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hX : 0 < td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  have hDpos : 0 < td.D := lt_of_lt_of_le (by linarith) hD
  have hUpos : 0 < td.U := lt_of_lt_of_le (by linarith) hU
  let h3fiber :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := td) h3MV hD0 hU0 hX0
  let h4fiber :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := td) h4MV hD0 hU0 hX0
  let h3outer :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := td) h3fiber
  let h4outer :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := td) h4fiber
  exact
    gramHypothesis_of_step2ToTubeForm_step3_step4_teX
      (h2 := h2) (h3 := h3outer) (h4 := h4outer)
      (hbal := hbal) (hX := hX) (hH := hH0) (hU := hU) (hD := hD) R

noncomputable def gramHypothesis_of_reduction_step2ToTubeForm_box_geometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hX : 0 < td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (hXH1 : 1 ≤ td.X * td.H) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  exact
    gramHypothesis_of_reduction_step2ToTubeForm_step3MV_step4MV
      (R := R) (h2 := h2)
      (h3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_box_geometry
        (td := td) (hDq := hDq) (hD := hD0) (hU := hU) (hX := hX0))
      (h4MV := SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_box_geometry
        (td := td) (hU := hU0) (hX := hX0) (hD1 := hD) (hXH1 := hXH1))
      (hbal := hbal)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hX := hX) (hH0 := hH0) (hU := hU) (hD := hD)

noncomputable def gramHypothesis_of_reduction_step2ToTubeForm_step34TeXFor_uniform
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hX0 : 0 ≤ td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D)
    (C34 : ℝ) (hC34_nonneg : 0 ≤ C34)
    (h34For : ∀ f : H, ∀ i j : ℤ, Step34LargeSieveTeXFor td (R.F f i j))
    (hC34 : ∀ f : H, ∀ i j : ℤ, (h34For f i j).C ≤ C34) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  let B : ℝ :=
      Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
        hbal.C *
          ((td.U * td.D) / td.H
            + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
                Real.sqrt (td.H * Real.log td.H)
            + td.X)
  let cTot : ℝ := (C34 * B) * R.Cenergy
  have hU0 : 0 ≤ td.U := le_trans (show (0 : ℝ) ≤ 1 by linarith) hU
  have hD0 : 0 ≤ td.D := le_trans (show (0 : ℝ) ≤ 1 by linarith) hD
  have hterm1 : 0 ≤ (td.U * td.D) / td.H :=
    div_nonneg (mul_nonneg hU0 hD0) (le_of_lt hH0)
  have hterm2 :
      0 ≤ Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
          Real.sqrt (td.H * Real.log td.H) := by
    positivity
  have hbig :
      0 ≤
        (td.U * td.D) / td.H
          + Real.sqrt td.X * (Real.sqrt td.U + Real.sqrt td.D) *
              Real.sqrt (td.H * Real.log td.H)
          + td.X := by
    nlinarith [hterm1, hterm2, hX0]
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hbal.C_nonneg) hbig
  have hcTot : 0 ≤ cTot := by
    dsimp [cTot]
    exact mul_nonneg (mul_nonneg hC34_nonneg hB_nonneg) R.Cenergy_nonneg
  refine
    { a := fun _ => Real.toNNReal cTot
      gram := ?_ }
  intro f i hi j hj
  have hpair :
      ‖inner ℂ (T i f) (T j f)‖ ≤
        (((h34For f i j).C * B) * R.Cenergy) * ‖T i f‖ * ‖T j f‖ := by
    have hpair0 :=
      norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
        (R := R) (h2 := h2) (hbal := hbal)
        (hX0 := hX0) (hH0 := hH0) (hU := hU) (hD := hD)
        (f := f) (i := i) (hi := hi) (j := j) (hj := hj)
        (h34 := h34For f i j)
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using hpair0
  have hCfac :
      (((h34For f i j).C * B) * R.Cenergy) * ‖T i f‖ * ‖T j f‖
        ≤ ((C34 * B) * R.Cenergy) * ‖T i f‖ * ‖T j f‖ := by
    have hCB : (h34For f i j).C * B ≤ C34 * B :=
      mul_le_mul_of_nonneg_right (hC34 f i j) hB_nonneg
    have hCB' : ((h34For f i j).C * B) * R.Cenergy ≤ (C34 * B) * R.Cenergy :=
      mul_le_mul_of_nonneg_right hCB R.Cenergy_nonneg
    have hnorm : 0 ≤ ‖T i f‖ * ‖T j f‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hCB' hnorm
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hfinal :
      ‖inner ℂ (T i f) (T j f)‖ ≤ cTot * ‖T i f‖ * ‖T j f‖ := by
    have : ‖inner ℂ (T i f) (T j f)‖
        ≤ ((C34 * B) * R.Cenergy) * ‖T i f‖ * ‖T j f‖ :=
      le_trans hpair hCfac
    simpa [cTot] using this
  have ha : ((Real.toNNReal cTot : NNReal) : ℝ) = cTot := by
    simpa using (Real.coe_toNNReal cTot hcTot)
  change ‖inner ℂ (T i f) (T j f)‖ ≤
      ((Real.toNNReal cTot : NNReal) : ℝ) * ‖T i f‖ * ‖T j f‖
  rw [ha]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hfinal

noncomputable def gramHypothesis_of_reduction_step2ToTubeForm_step3MVByResidue_step4MVByResidue
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Finset ℤ} {T : ℤ → (H →L[ℂ] H)} {td : TubeData} {K : ℤ → ℝ}
    (R : ReductionToTubeForm (J := J) (T := T) td K)
    (h2 : Step2ToTubeForm td K)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td)
    (hbal : BalancedXiClaimInv td.X td.H h2.Khat)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hX : 0 < td.X) (hH0 : 0 < td.H)
    (hU : 1 ≤ td.U) (hD : 1 ≤ td.D) :
    SSU.Interzone.GramHypothesis (H := H) J T := by
  exact
    gramHypothesis_of_reduction_step2ToTubeForm_step3MV_step4MV
      (R := R) (h2 := h2)
      (h3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue td h3MV)
      (h4MV := SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue td h4MV)
      (hbal := hbal)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hX := hX) (hH0 := hH0) (hU := hU) (hD := hD)

end

end TypeII
end Engines
end SSU
