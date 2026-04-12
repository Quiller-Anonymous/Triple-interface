import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers
import Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks
import Goldbach.ProofTools
import Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
import Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1CommonWindowTargets

open scoped BigOperators

open Complex
open MeasureTheory
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.ProofTools.Windows

open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassQ1OscillationHelpers
open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.Cert.MajorArcModules.Q0MajorTailTTStarBlocks

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma card_evenIn_le_H_add_one (X : ℕ) :
    (EvenIn X H).card ≤ H + 1 := by
  classical
  unfold EvenIn IccShift
  have hsub :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)
        ⊆
      (Finset.range (H + 1)).image (fun k : ℕ => X + k) := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcard_le :
      (((Finset.range (H + 1)).image (fun k : ℕ => X + k)).filter
          (fun n : ℕ => Goldbach.Windows.IsEven n)).card
        ≤
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card :=
    Finset.card_le_card hsub
  have hcard_eq :
      ((Finset.range (H + 1)).image (fun k : ℕ => X + k)).card = H + 1 := by
    rw [Finset.card_image_of_injective, Finset.card_range]
    intro a b hab
    exact Nat.add_left_cancel hab
  exact le_trans hcard_le (le_of_eq hcard_eq)

private theorem norm_intervalIntegral_zero_one_le
    {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ u, 0 ≤ u → u ≤ 1 → ‖f u‖ ≤ C) :
    ‖∫ u in (0 : ℝ)..(1 : ℝ), f u‖ ≤ C := by
  let s : Set ℝ := Set.Icc (0 : ℝ) (1 : ℝ)
  have hs : MeasurableSet s := measurableSet_Icc
  haveI : IsFiniteMeasure (volume.restrict s) := by
    refine ⟨?_⟩
    have hfin : volume s < ⊤ := by
      simp [s]
    simpa [s] using hfin
  have hAeImp : ∀ᵐ u ∂volume, u ∈ s → ‖f u‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro u hu
    exact hf u hu.1 hu.2
  have hAe : ∀ᵐ u ∂volume.restrict s, ‖f u‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := volume) (s := s) hs).2 hAeImp
  have hbound :
      ‖∫ u, f u ∂(volume.restrict s)‖ ≤ C * (volume.restrict s).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := volume.restrict s) (f := f) (C := C) hAe
  have hind :
      (∫ u in (0 : ℝ)..(1 : ℝ), f u) = ∫ u, f u ∂(volume.restrict s) := by
    calc
      (∫ u in (0 : ℝ)..(1 : ℝ), f u)
          = ∫ u in Set.Ioc (0 : ℝ) (1 : ℝ), f u := by
              simpa using
                (intervalIntegral.integral_of_le (μ := volume)
                  (f := f) (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1))
      _ = ∫ u in Set.Icc (0 : ℝ) (1 : ℝ), f u := by
            simpa using
              (MeasureTheory.integral_Icc_eq_integral_Ioc
                (μ := volume) (f := f) (x := (0 : ℝ)) (y := (1 : ℝ))).symm
      _ = ∫ u, f u ∂(volume.restrict s) := by
            simpa [s] using
              (MeasureTheory.integral_indicator (μ := volume) (s := s) (f := f) hs).symm
  have hreal :
      (volume.restrict s).real Set.univ = (volume s).toReal := by
    simp [Measure.real, s, hs, Measure.restrict_apply]
  calc
    ‖∫ u in (0 : ℝ)..(1 : ℝ), f u‖ = ‖∫ u, f u ∂(volume.restrict s)‖ := by rw [hind]
    _ ≤ C * (volume.restrict s).real Set.univ := hbound
    _ = C * (volume s).toReal := by rw [hreal]
    _ = C := by simp [s, Real.volume_Icc]

private lemma volume_betaSmallSet_toReal_le_one_div_six :
    (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal ≤ (1 : ℝ) / 6 := by
  have hvol :
      volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
        = ENNReal.ofReal
            (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius) := by
    simp [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet, Real.volume_Icc,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, sub_eq_add_neg, two_mul,
      add_assoc, add_left_comm, add_comm, mul_assoc]
  have htoReal :
      (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal
        = (1 : ℝ) / (2 * Real.pi) := by
    have hnonneg :
        0 ≤ (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius : ℝ) := by
      nlinarith [le_of_lt Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius_pos]
    calc
      (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal
          = (ENNReal.ofReal
              (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius)).toReal := by
                simpa [hvol]
      _ = 2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius := by
            simpa using ENNReal.toReal_ofReal hnonneg
      _ = (1 : ℝ) / (2 * Real.pi) := by
            have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
            unfold Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius
            field_simp [hpi0]
            ring
  have h2pi : (6 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hden_le :
      (1 : ℝ) / (2 * Real.pi) ≤ (1 : ℝ) / 6 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) h2pi
  simpa [htoReal] using hden_le

private theorem norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six
    {g : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hg : ∀ β, β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet → ‖g β‖ ≤ C) :
    ‖∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator g β‖
      ≤ C / 6 := by
  let s : Set ℝ := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
  let a : ℝ := Goldbach.Cert.MajorArcModules.BetaInterval.aβ
  let b : ℝ := Goldbach.Cert.MajorArcModules.BetaInterval.bβ
  have hab : a ≤ b := Goldbach.Cert.MajorArcModules.BetaInterval.hle
  have hs : MeasurableSet s := Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
  have hI :
      (∫ β in a..b, s.indicator g β ∂volume) =
      ∫ β in Set.Ioc a b, s.indicator g β ∂volume := by
    simpa [a, b] using
      (intervalIntegral.integral_of_le (μ := volume) (f := fun β => s.indicator g β)
        (a := a) (b := b) hab)
  let μ0 : Measure ℝ := volume.restrict (Set.Ioc a b)
  haveI : IsFiniteMeasure μ0 := by
    refine ⟨?_⟩
    simpa [μ0] using (measure_Ioc_lt_top (μ := volume) (a := a) (b := b))
  have hAeImp : ∀ᵐ β ∂μ0, β ∈ s → ‖g β‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro β hβ
    exact hg β hβ
  have hAe :
      ∀ᵐ β ∂(μ0.restrict s), ‖g β‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := μ0) (s := s) hs).2 hAeImp
  have hbound :
      ‖∫ β, g β ∂(μ0.restrict s)‖ ≤ C * (μ0.restrict s).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := μ0.restrict s) (f := g) (C := C) hAe
  have hind :
      (∫ β in Set.Ioc a b, s.indicator g β ∂volume) = ∫ β, g β ∂(μ0.restrict s) := by
    simpa [μ0, s] using (MeasureTheory.integral_indicator (μ := μ0) (f := g) hs)
  have hμ :
      ((μ0.restrict s).real Set.univ) ≤ (volume s).toReal := by
    have h1 : (μ0.restrict s).real Set.univ = μ0.real s := by
      simpa using (measureReal_restrict_apply_univ (μ := μ0) (s := s))
    have h2 : μ0.real s = volume.real (s ∩ Set.Ioc a b) := by
      simp [μ0, measureReal_restrict_apply hs, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
    have h3 : volume.real (s ∩ Set.Ioc a b) ≤ volume.real s := by
      refine measureReal_mono (Set.inter_subset_left) ?_
      have hfinite : volume s < ⊤ := by
        have hvol : volume s = ENNReal.ofReal
            (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius) := by
          simp [s, Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet, Real.volume_Icc,
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, sub_eq_add_neg, two_mul,
            add_assoc, add_left_comm, add_comm, mul_assoc]
        rw [hvol]
        exact ENNReal.ofReal_lt_top
      exact hfinite.ne
    simpa [h1, h2] using h3
  calc
    ‖∫ β in a..b, s.indicator g β ∂volume‖ = ‖∫ β in Set.Ioc a b, s.indicator g β ∂volume‖ := by
      rw [hI]
    _ = ‖∫ β, g β ∂(μ0.restrict s)‖ := by rw [hind]
    _ ≤ C * (μ0.restrict s).real Set.univ := hbound
    _ ≤ C * (volume s).toReal := by
          gcongr
    _ ≤ C * ((1 : ℝ) / 6) := by
          gcongr
          exact volume_betaSmallSet_toReal_le_one_div_six
    _ = C / 6 := by ring

/--
The exact `β`-integrated common-square contribution in the ordered-pair `q = 1` shell difference.

This is the surviving interior term in the exact decomposition of the paired two-sided-shift
difference. The live `q = 1` bottleneck is to prove that this common contribution cancels or
telescopes on the canonical even window.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonIntegral
    (X N M : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
          X N M β) β

/--
Positive-frequency overlap component of the common-square term.

The first index is the overlap width; the second is the centered-shift parameter carried by the
phase defect. This is the natural exact object for a gap/difference-energy proof.
-/
noncomputable def canonicalQ1TwoSidedShiftCommonPositiveOverlap
    (X overlap K : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (overlap - 5),
    ∑ k ∈ Finset.range (overlap - 5),
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * Goldbach.Cert.MajorArcExponential.e
            (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        * Goldbach.Cert.MajorArcExponential.e
            ((u / (X : ℝ))
              * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))

/-- Product form of the fixed-overlap positive q=1 common piece. -/
noncomputable def canonicalQ1TwoSidedShiftCommonPositiveProduct
    (X overlap : ℕ) (u β : ℝ) : ℂ :=
  (∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n)
    *
  (∑ m ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m)

/-- The positive-shift one-variable exponential sum in the fixed-overlap common branch. -/
noncomputable def canonicalQ1TwoSidedShiftCommonPositivePlusSum
    (X overlap : ℕ) (u β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n

/-- The negative-shift one-variable exponential sum in the fixed-overlap common branch. -/
noncomputable def canonicalQ1TwoSidedShiftCommonPositiveMinusSum
    (X overlap : ℕ) (u β : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ico 4 ((overlap - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m

theorem canonicalQ1TwoSidedShiftCommonPositiveProduct_eq_plus_mul_minus
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β
      =
    canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β
      * canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveProduct
    canonicalQ1TwoSidedShiftCommonPositivePlusSum
    canonicalQ1TwoSidedShiftCommonPositiveMinusSum
  rfl

theorem canonicalQ1TwoSidedShiftCommonPositivePlusSum_eq_sum_base_mul_shift
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β
      =
    ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (u / (X : ℝ)) n := by
  unfold canonicalQ1TwoSidedShiftCommonPositivePlusSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  simpa [mul_comm] using
    (Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add (u / (X : ℝ)) β n)

theorem canonicalQ1TwoSidedShiftCommonPositivePlusSum_eq_finiteGExpIco
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β
      =
    finiteGExpIco overlap ((u / (X : ℝ)) + β) := by
  unfold canonicalQ1TwoSidedShiftCommonPositivePlusSum
  rfl

theorem canonicalQ1TwoSidedShiftCommonPositiveMinusSum_eq_sum_base_mul_shift
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β
      =
    ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n
        * Goldbach.Cert.MajorArcStep2ExpSums.gExp (u / (X : ℝ)) n := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveMinusSum
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hrew :
      (u / (X : ℝ)) - β = (-β) + (u / (X : ℝ)) := by ring
  simpa [hrew, mul_comm] using
    (Goldbach.Cert.MajorArcStep5ExpSumApprox.gExp_add (-β) (u / (X : ℝ)) n)

theorem canonicalQ1TwoSidedShiftCommonPositiveMinusSum_eq_finiteGExpIco
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β
      =
    finiteGExpIco overlap ((u / (X : ℝ)) - β) := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveMinusSum
  rfl

theorem canonicalQ1TwoSidedShiftCommonPositivePlusSum_sub_zero_eq_sum_base_mul_shift_sub_one
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β
      - canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap 0 β
      =
    ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
        * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (u / (X : ℝ)) n - 1) := by
  rw [canonicalQ1TwoSidedShiftCommonPositivePlusSum_eq_sum_base_mul_shift,
    canonicalQ1TwoSidedShiftCommonPositivePlusSum_eq_sum_base_mul_shift]
  have hzero :
      ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 / (X : ℝ)) n
        =
      ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp β n := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [Goldbach.Cert.MajorArcStep2ExpSums.gExp, Goldbach.Cert.MajorArcExponential.e]
  rw [hzero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  ring

theorem canonicalQ1TwoSidedShiftCommonPositivePlusSum_sub_zero_eq_finiteGExpIcoShiftDiff
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β
      - canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap 0 β
      =
    finiteGExpIcoShiftDiff overlap β (u / (X : ℝ)) := by
  rw [canonicalQ1TwoSidedShiftCommonPositivePlusSum_eq_finiteGExpIco,
    canonicalQ1TwoSidedShiftCommonPositivePlusSum_eq_finiteGExpIco]
  unfold finiteGExpIcoShiftDiff
  congr 1
  simp

theorem canonicalQ1TwoSidedShiftCommonPositiveMinusSum_sub_zero_eq_sum_base_mul_shift_sub_one
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β
      - canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap 0 β
      =
    ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
      Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n
        * (Goldbach.Cert.MajorArcStep2ExpSums.gExp (u / (X : ℝ)) n - 1) := by
  rw [canonicalQ1TwoSidedShiftCommonPositiveMinusSum_eq_sum_base_mul_shift,
    canonicalQ1TwoSidedShiftCommonPositiveMinusSum_eq_sum_base_mul_shift]
  have hzero :
      ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n
            * Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 / (X : ℝ)) n
        =
      ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [Goldbach.Cert.MajorArcStep2ExpSums.gExp, Goldbach.Cert.MajorArcExponential.e]
  rw [hzero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  ring

theorem canonicalQ1TwoSidedShiftCommonPositiveMinusSum_sub_zero_eq_finiteGExpIcoShiftDiff
    (X overlap : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β
      - canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap 0 β
      =
    finiteGExpIcoShiftDiff overlap (-β) (u / (X : ℝ)) := by
  rw [canonicalQ1TwoSidedShiftCommonPositiveMinusSum_eq_finiteGExpIco,
    canonicalQ1TwoSidedShiftCommonPositiveMinusSum_eq_finiteGExpIco]
  unfold finiteGExpIcoShiftDiff
  congr 1
  simp

private lemma norm_canonicalQ1TwoSidedShiftCommonPositivePlusSum_le_geomBound
    (X overlap : ℕ) (u β : ℝ) :
    ‖canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β‖
      ≤ finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) + β) := by
  rw [canonicalQ1TwoSidedShiftCommonPositivePlusSum_eq_finiteGExpIco]
  exact finiteGExpIcoBound_of_geom.le_bound overlap ((u / (X : ℝ)) + β)

private lemma norm_canonicalQ1TwoSidedShiftCommonPositiveMinusSum_le_geomBound
    (X overlap : ℕ) (u β : ℝ) :
    ‖canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β‖
      ≤ finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) - β) := by
  rw [canonicalQ1TwoSidedShiftCommonPositiveMinusSum_eq_finiteGExpIco]
  exact finiteGExpIcoBound_of_geom.le_bound overlap ((u / (X : ℝ)) - β)

private lemma
    norm_canonicalQ1TwoSidedShiftCommonPositivePlusSum_sub_zero_le_helper
    {X : ℕ} (overlap : ℕ) (u β : ℝ)
    (hu : |2 * Real.pi * (u / (X : ℝ))| ≤ 1) :
    ‖canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β
        - canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap 0 β‖
      ≤ finiteGExpIcoSoftShiftBound overlap (u / (X : ℝ)) := by
  rw [canonicalQ1TwoSidedShiftCommonPositivePlusSum_sub_zero_eq_finiteGExpIcoShiftDiff]
  exact norm_finiteGExpIcoShiftDiff_le_soft overlap β (u / (X : ℝ)) hu

private lemma
    norm_canonicalQ1TwoSidedShiftCommonPositiveMinusSum_sub_zero_le_helper
    {X : ℕ} (overlap : ℕ) (u β : ℝ)
    (hu : |2 * Real.pi * (u / (X : ℝ))| ≤ 1) :
    ‖canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β
        - canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap 0 β‖
      ≤ finiteGExpIcoSoftShiftBound overlap (u / (X : ℝ)) := by
  rw [canonicalQ1TwoSidedShiftCommonPositiveMinusSum_sub_zero_eq_finiteGExpIcoShiftDiff]
  exact norm_finiteGExpIcoShiftDiff_le_soft overlap (-β) (u / (X : ℝ)) hu

/--
Generalized centered shell with overlap length and Fourier center decoupled.

This is the exact 1D oscillatory object behind the positive adjacent-step product branch.
-/
noncomputable def canonicalQ1TwoSidedShiftCommonPositiveMixedShell
    (overlap K : ℕ) (θ β : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
    * (fourier (T := (1 : ℝ)) (-(K : ℤ)) (θ : UC) : ℂ)
    * ((∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)
        *
        (∑ m ∈ Finset.Ico 4 ((overlap - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m))

theorem canonicalQ1TwoSidedShiftCommonPositiveMixedShell_eq_kernel_mul_fourier_mul_sums
    (overlap K : ℕ) (θ β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K θ β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (fourier (T := (1 : ℝ)) (-(K : ℤ)) (θ : UC) : ℂ)
      * ((∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)
          *
          (∑ m ∈ Finset.Ico 4 ((overlap - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) m)) := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveMixedShell
  rfl

theorem canonicalQ1TwoSidedShiftCommonPositiveMixedShell_eq_kernel_mul_fourier_mul_plus_minus
    (X overlap K : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K (u / (X : ℝ)) β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (fourier (T := (1 : ℝ)) (-(K : ℤ)) ((u / (X : ℝ)) : UC) : ℂ)
      * (canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β
          * canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β) := by
  rw [canonicalQ1TwoSidedShiftCommonPositiveMixedShell_eq_kernel_mul_fourier_mul_sums]
  rw [canonicalQ1TwoSidedShiftCommonPositiveProduct_eq_plus_mul_minus]

/--
Negative-frequency overlap component of the common-square term.
-/
noncomputable def canonicalQ1TwoSidedShiftCommonNegativeOverlap
    (X overlap K : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (overlap - 5),
    ∑ k ∈ Finset.range (overlap - 5),
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * Goldbach.Cert.MajorArcExponential.e
            (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        * Goldbach.Cert.MajorArcExponential.e
            (-((u / (X : ℝ))
              * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))))

/-- The kernel-weighted `u`-integral of the positive overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
    (X overlap K : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
      (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC))
      * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β

/-- The kernel-weighted `u`-integral of the negative overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
    (X overlap K : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
      (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC))
      * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β

/-- The `β`-integrated positive overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral
    (X overlap K : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β) β

/-- The `β`-integrated negative overlap component. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral
    (X overlap K : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β) β

/-- Positive one-variable profile difference for the common-square term. -/
noncomputable def canonicalQ1TwoSidedShiftCommonPositiveProfileDiff
    (X overlap N M : ℕ) (u β : ℝ) : ℂ :=
  canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap N u β
    - canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap M u β

/-- Negative one-variable profile difference for the common-square term. -/
noncomputable def canonicalQ1TwoSidedShiftCommonNegativeProfileDiff
    (X overlap N M : ℕ) (u β : ℝ) : ℂ :=
  canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap N u β
    - canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap M u β

/--
Raw positive-frequency termwise difference for the common-square contribution.

This keeps the one-variable `N` versus `M` phase difference visible without forcing the final sum
rearrangement into packaged overlap-profile objects yet.
-/
noncomputable def canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff
    (X overlap N M : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (overlap - 5),
    ∑ k ∈ Finset.range (overlap - 5),
      let phase :=
        Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
          * Goldbach.Cert.MajorArcExponential.e
              (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
      let zN : ℝ :=
        (u / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))
      let zM : ℝ :=
        (u / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ)))
      phase * Goldbach.Cert.MajorArcExponential.e zN
        - phase * Goldbach.Cert.MajorArcExponential.e zM

/-- Raw negative-frequency termwise difference for the common-square contribution. -/
noncomputable def canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff
    (X overlap N M : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (overlap - 5),
    ∑ k ∈ Finset.range (overlap - 5),
      let phase :=
        Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
          * Goldbach.Cert.MajorArcExponential.e
              (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
      let zN : ℝ :=
        (u / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))
      let zM : ℝ :=
        (u / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ)))
      phase * Goldbach.Cert.MajorArcExponential.e (-zN)
        - phase * Goldbach.Cert.MajorArcExponential.e (-zM)

/-- Kernel-weighted `u`-integral of the positive overlap-difference common piece. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral
    (X overlap N M : ℕ) (β : ℝ) : ℂ :=
  canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap N β
    - canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap M β

/-- Kernel-weighted `u`-integral of the negative overlap-difference common piece. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral
    (X overlap N M : ℕ) (β : ℝ) : ℂ :=
  canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap N β
    - canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap M β

/-- The `β`-integrated positive overlap-difference common piece. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral
    (X overlap N M : ℕ) : ℂ :=
  canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X overlap N
    - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X overlap M

/--
Exact fixed-overlap adjacent-step `u`-integrand for the positive common branch.

This is the sharp replacement for the crude overlap-cardinality route: the `K ↦ K + 2` step is a
scalar phase increment times the product of the two one-dimensional `gExp` sums.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral
    (X overlap K : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * ((Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1)
          * (((fourier (T := (1 : ℝ)) (-(K : ℤ)) ((u / (X : ℝ)) : UC) : ℂ))
              * canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β))

/--
Exact fixed-overlap adjacent-step `β`-integral for the positive common branch.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral
    (X overlap K : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ =>
        canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral X overlap K β) β

/-- The `β`-integrated negative overlap-difference common piece. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral
    (X overlap N M : ℕ) : ℂ :=
  canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X overlap N
    - canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X overlap M

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_kernelPoly_real : Continuous fun β : ℝ =>
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
  dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
    Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
  refine continuous_finset_sum _ ?_
  intro k hk
  exact continuous_const.mul
    (((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC)

private lemma continuous_canonicalQ1TwoSidedShiftCommonPositiveOverlap_uncurry
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K p.2 p.1 := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveOverlap
  refine continuous_finset_sum _ ?_
  intro j hj
  refine continuous_finset_sum _ ?_
  intro k hk
  have h1 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e (2 * p.2 / (X : ℝ)) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ => 2 * Real.pi * (2 * p.2 / (X : ℝ)) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi * (2 * p.2 / (X : ℝ)) : ℝ) : ℂ) := by
      exact continuous_const.mul (continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h2 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        (p.1 * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) : ℝ) : ℂ) := by
      exact continuous_const.mul (continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h3 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        ((p.2 / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi
          * ((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * ((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))) : ℝ) : ℂ) := by
      exact continuous_const.mul (continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  simpa [mul_assoc] using h1.mul (h2.mul h3)

private lemma continuous_canonicalQ1TwoSidedShiftCommonNegativeOverlap_uncurry
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K p.2 p.1 := by
  unfold canonicalQ1TwoSidedShiftCommonNegativeOverlap
  refine continuous_finset_sum _ ?_
  intro j hj
  refine continuous_finset_sum _ ?_
  intro k hk
  have h1 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e (2 * p.2 / (X : ℝ)) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ => 2 * Real.pi * (2 * p.2 / (X : ℝ)) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi * (2 * p.2 / (X : ℝ)) : ℝ) : ℂ) := by
      exact continuous_const.mul (continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h2 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        (p.1 * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * (p.1 * ((((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))) : ℝ) : ℂ) := by
      exact continuous_const.mul (continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  have h3 : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e
        (-((p.2 / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi
          * (-((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi
          * (-((p.2 / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))) : ℝ) : ℂ) := by
      exact continuous_const.mul (continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  simpa [mul_assoc] using h1.mul (h2.mul h3)

private lemma continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand_uncurry
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC))
        * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K p.2 p.1 := by
  have hK : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC) := by
    dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
      Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
    refine continuous_finset_sum _ ?_
    intro k hk
    exact continuous_const.mul
      (((fourier (T := (1 : ℝ)) k).continuous).comp (continuous_coe_UC.comp continuous_fst))
  exact hK.mul (continuous_canonicalQ1TwoSidedShiftCommonPositiveOverlap_uncurry X overlap K)

private lemma continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand_uncurry
    (X overlap K : ℕ) :
    Continuous fun p : ℝ × ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC))
        * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K p.2 p.1 := by
  have hK : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.1 : UC) := by
    dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
      Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
    refine continuous_finset_sum _ ?_
    intro k hk
    exact continuous_const.mul
      (((fourier (T := (1 : ℝ)) k).continuous).comp (continuous_coe_UC.comp continuous_fst))
  exact hK.mul (continuous_canonicalQ1TwoSidedShiftCommonNegativeOverlap_uncurry X overlap K)

private lemma intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand
    (X overlap K : ℕ) (β : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β)
      MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
  let psi : ℝ → ℝ × ℝ := fun u => (β, u)
  have hpsi : Continuous psi := continuous_const.prodMk continuous_id
  have hcont : Continuous fun u : ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β := by
    simpa [psi] using
      (continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand_uncurry X overlap K).comp
        hpsi
  exact hcont.intervalIntegrable (μ := MeasureTheory.volume) _ _

private lemma intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand
    (X overlap K : ℕ) (β : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β)
      MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
  let psi : ℝ → ℝ × ℝ := fun u => (β, u)
  have hpsi : Continuous psi := continuous_const.prodMk continuous_id
  have hcont : Continuous fun u : ℝ =>
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β := by
    simpa [psi] using
      (continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand_uncurry X overlap K).comp
        hpsi
  exact hcont.intervalIntegrable (μ := MeasureTheory.volume) _ _

private lemma continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
    (X overlap K : ℕ) :
    Continuous fun β : ℝ =>
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β)
      (hf := by
        simpa [Function.uncurry] using
          continuous_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand_uncurry X overlap K)
      (0 : ℝ) (1 : ℝ))

private lemma continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
    (X overlap K : ℕ) :
    Continuous fun β : ℝ =>
      canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeOverlap X overlap K u β)
      (hf := by
        simpa [Function.uncurry] using
          continuous_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand_uncurry X overlap K)
      (0 : ℝ) (1 : ℝ))

private lemma intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
    (X overlap K : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β) β)
      MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β)
        MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
      X overlap K).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      (f := fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

private lemma intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
    (X overlap K : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β) β)
      MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β)
        MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
      X overlap K).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      (f := fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

theorem intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
    (X overlap K : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X overlap K β) β)
      MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
  intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
    X overlap K

theorem intervalIntegrable_betaSmall_indicator_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
    (X overlap K : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X overlap K β) β)
      MeasureTheory.volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
  intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
    X overlap K

/--
Ordered-pair window energy of the common-square contribution.

The `if N ≤ M` gate matches the exact common/strip decomposition theorem, which is currently only
proved for ordered pairs.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2 else 0

/--
The forward even-window fiber based at the ordered-pair left endpoint `N`.

This is the natural support on which the positive common-piece profile should be treated as a
one-variable function in the second coordinate.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow
    (X N : ℕ) : Finset ℕ :=
  (EvenIn X H).filter (fun M => N ≤ M)

/-- Ordered-pair window energy of the positive raw termwise-difference common piece. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N N M‖ ^ 2 else 0

/--
Fiberwise pairwise energy for the positive common-piece profile.

For each left endpoint `N`, this is the full pairwise `‖·‖²` energy of the one-variable profile
`K ↦ canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N K` on the forward fiber
`{M ∈ EvenIn X H | N ≤ M}`.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ A ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
      ∑ B ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
        ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
          - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2

/--
The basic fixed-incidence summand for the positive common-piece fiber energy.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairTerm
    (X N A B : ℕ) : ℝ :=
  ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
    - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2

/--
Incidence set of left endpoints whose forward fiber contains both `A` and `B`.

This is the exact multiplicity carrier for the positive common-piece fiber energy after swapping
the order of summation.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberIncidence
    (X A B : ℕ) : Finset ℕ :=
  (EvenIn X H).filter (fun N => N ≤ A ∧ N ≤ B)

/-- Ordered-pair window energy of the negative raw termwise-difference common piece. -/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H,
      if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral X N N M‖ ^ 2 else 0

/--
Abstract cancellation surface for the common-square contribution.

Experiments now show that literal pointwise cancellation is too strong to be the live theorem,
but this exact surface is still useful as a special case: any later symmetry/telescoping theorem
can still feed through it automatically.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonCancellation : Prop where
  vanish :
    ∀ {X N M : ℕ}, N ≤ M →
      canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M = 0

/--
Route-sized target for the ordered-pair common-square contribution.

This is now the live theorem-facing surface for the common piece. The earlier cancellation target
is retained only as a special case feeding into this bound with constant `0`.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/-- Route-sized target for the positive raw termwise-difference ordered-pair energy. -/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Route-sized target for the positive fiberwise pairwise energy.

This is the theorem-facing surface for the next counting/Fubini step: once the full pairwise
energy of each fixed-overlap positive fiber is controlled, the original positive ordered-pair
target follows formally.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Length of the forward even fiber based at `N`, measured in adjacent `+2` steps.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount
    (X N : ℕ) : ℕ :=
  (X + H - N) / 2

/--
Adjacent-step window energy for the positive common-piece fiber profile.

This is the one-dimensional target obtained after reducing the full pairwise energy of each fiber
to adjacent `K ↦ K + 2` differences.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ t ∈ Finset.range (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N),
      ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * (t + 1))
        - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * t)‖ ^ 2

/--
Product-form adjacent-step window energy for the positive common branch.

This is equal to the preceding energy, but its summand is the exact one-dimensional `gExp`-product
object that remains after the fixed-overlap phase extraction.
-/
noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ t ∈ Finset.range (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N),
      ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral
          X N (N + 2 * t)‖ ^ 2

/--
Route-sized target for the adjacent-step energy of the positive common-piece fibers.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Route-sized target for the product-form adjacent-step energy of the positive common-piece fibers.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/--
Generic pairwise-to-adjacent transport on a finite chain.

This is the purely combinatorial core of the positive fiber argument: full pairwise energy on
`0,1,...,m` is controlled by adjacent-step energy with a coarse cubic cardinality factor.
-/
private theorem pairwise_range_norm_sq_le_cube_mul_adjacent
    (m : ℕ) (f : ℕ → ℂ) :
    (∑ A ∈ Finset.range (m + 1),
      ∑ B ∈ Finset.range (m + 1), ‖f A - f B‖ ^ 2)
      ≤
    (((m + 1 : ℕ) : ℝ) ^ 3)
      * ∑ K ∈ Finset.range m, ‖f (K + 1) - f K‖ ^ 2 := by
  let S : ℝ := ∑ K ∈ Finset.range m, ‖f (K + 1) - f K‖ ^ 2
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpair_of_le :
      ∀ A ∈ Finset.range (m + 1), ∀ B ∈ Finset.range (m + 1), A ≤ B →
        ‖f A - f B‖ ^ 2 ≤ (m : ℝ) * S := by
    intro A hA B hB hAB
    have htel :
          (∑ k ∈ Finset.range (B - A), (f (A + k) - f (A + (k + 1))))
            = f A - f B := by
      calc
        (∑ k ∈ Finset.range (B - A), (f (A + k) - f (A + (k + 1))))
            =
          f (A + 0) - f (A + (B - A)) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Finset.sum_range_sub' (f := fun k : ℕ => f (A + k)) (n := B - A))
        _ = f A - f B := by
            rw [Nat.add_zero, Nat.add_sub_of_le hAB]
    have hsq :
          ‖f A - f B‖ ^ 2
            ≤
          ((Finset.range (B - A)).card : ℝ)
            * ∑ k ∈ Finset.range (B - A), ‖f (A + k) - f (A + (k + 1))‖ ^ 2 := by
      rw [← htel]
      simpa using
        (norm_sum_sq_le_card_mul_sum_norm_sq
          (s := Finset.range (B - A))
          (z := fun k => f (A + k) - f (A + (k + 1))))
    have hlocal :
          ∑ k ∈ Finset.range (B - A), ‖f (A + k) - f (A + (k + 1))‖ ^ 2 ≤ S := by
      let T : Finset ℕ := (Finset.range (B - A)).image (fun k : ℕ => A + k)
      have hTsub : T ⊆ Finset.range m := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        have hklt : k < B - A := Finset.mem_range.mp hk
        have hBle : B ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hB)
        have hxlt : A + k < m := by omega
        exact Finset.mem_range.mpr hxlt
      have hinj : Set.InjOn (fun k : ℕ => A + k) ((Finset.range (B - A) : Finset ℕ) : Set ℕ) := by
        intro x hx y hy hxy
        exact Nat.add_left_cancel hxy
      calc
        ∑ k ∈ Finset.range (B - A), ‖f (A + k) - f (A + (k + 1))‖ ^ 2
            =
          ∑ x ∈ T, ‖f x - f (x + 1)‖ ^ 2 := by
            dsimp [T]
            rw [Finset.sum_image hinj]
            refine Finset.sum_congr rfl ?_
            intro k hk
            rfl
        _ ≤ ∑ x ∈ Finset.range m, ‖f x - f (x + 1)‖ ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (by
              intro x hx hxT
              exact sq_nonneg _)
        _ = ∑ K ∈ Finset.range m, ‖f (K + 1) - f K‖ ^ 2 := by
            simp_rw [norm_sub_rev]
        _ = S := by dsimp [S]
    have hcard : ((Finset.range (B - A)).card : ℝ) ≤ (m : ℝ) := by
      have hBAle : B - A ≤ m := by
        have hBle : B ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hB)
        omega
      rw [Finset.card_range]
      exact Nat.cast_le.mpr hBAle
    calc
      ‖f A - f B‖ ^ 2
          ≤ ((Finset.range (B - A)).card : ℝ)
              * ∑ k ∈ Finset.range (B - A), ‖f (A + k) - f (A + (k + 1))‖ ^ 2 := hsq
      _ ≤ ((Finset.range (B - A)).card : ℝ) * S := by
            exact mul_le_mul_of_nonneg_left hlocal (by positivity)
      _ ≤ (m : ℝ) * S := by
            exact mul_le_mul_of_nonneg_right hcard hSnonneg
  have hpair :
      ∀ A ∈ Finset.range (m + 1), ∀ B ∈ Finset.range (m + 1),
        ‖f A - f B‖ ^ 2 ≤ (m : ℝ) * S := by
    intro A hA B hB
    by_cases hAB : A ≤ B
    · exact hpair_of_le A hA B hB hAB
    · have hBA : B ≤ A := le_of_lt (lt_of_not_ge hAB)
      simpa [norm_sub_rev] using hpair_of_le B hB A hA hBA
  calc
    (∑ A ∈ Finset.range (m + 1),
        ∑ B ∈ Finset.range (m + 1), ‖f A - f B‖ ^ 2)
      ≤
    ∑ A ∈ Finset.range (m + 1),
      ∑ B ∈ Finset.range (m + 1), (m : ℝ) * S := by
        refine Finset.sum_le_sum ?_
        intro A hA
        refine Finset.sum_le_sum ?_
        intro B hB
        exact hpair A hA B hB
  _ = (((m + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ)) * S := by
        simp [pow_two, S, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  _ ≤ (((m + 1 : ℕ) : ℝ) ^ 3) * S := by
        have hm : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ m)
        have hsqnonneg : 0 ≤ (((m + 1 : ℕ) : ℝ) ^ 2) := by positivity
        have hmul :
            (((m + 1 : ℕ) : ℝ) ^ 2 * (m : ℝ))
              ≤
            (((m + 1 : ℕ) : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hm hsqnonneg
        exact mul_le_mul_of_nonneg_right (by simpa [pow_succ, pow_two, mul_assoc] using hmul) hSnonneg

/-- Route-sized target for the negative raw termwise-difference ordered-pair energy. -/
structure CanonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy_le_fiberPairwise
    (X : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy X
      ≤
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowEnergy X := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowEnergy
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow
  refine Finset.sum_le_sum ?_
  intro N hN
  let future : Finset ℕ := (EvenIn X H).filter (fun M => N ≤ M)
  have hNmem :
      N ∈ future := by
    dsimp [future]
    simp [hN]
  have hnonnegOuter :
      ∀ A ∈ future,
        0 ≤ ∑ B ∈ future,
          ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
            - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2 := by
    intro A hA
    refine Finset.sum_nonneg ?_
    intro B hB
    exact sq_nonneg _
  have hrewrite :
      (∑ M ∈ EvenIn X H,
          if N ≤ M then ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N N M‖ ^ 2 else 0)
        =
      ∑ M ∈ future,
          ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N N
            - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N M‖ ^ 2 := by
    dsimp [future]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro M hM
    by_cases hNM : N ≤ M
    · simp [hNM, canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral]
    · simp [hNM]
  have hsingle :
      (∑ M ∈ future,
          ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N N
            - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N M‖ ^ 2)
        ≤
      ∑ A ∈ future,
        ∑ B ∈ future,
          ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
            - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2 := by
    refine Finset.single_le_sum
      (s := future)
      (a := N)
      (f := fun A =>
        ∑ B ∈ future,
          ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
            - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2)
      ?_ hNmem
    intro A hA
    exact hnonnegOuter A hA
  exact le_trans (le_of_eq hrewrite) hsingle

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowTarget_of_fiberPairwise
    {C3 : ℝ}
    (hfiber : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowTarget C3) :
    CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowTarget C3 where
  C3_nonneg := hfiber.C3_nonneg
  bound := by
    intro X hX
    exact le_trans
      (canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy_le_fiberPairwise X)
      (hfiber.bound hX)

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberIncidence_card_le_H_add_one
    (X A B : ℕ) :
    (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberIncidence X A B).card ≤ H + 1 := by
  classical
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberIncidence
  exact le_trans (Finset.card_filter_le _ _) (card_evenIn_le_H_add_one X)

private lemma canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount_le_H
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N ≤ H := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount
  have hXleN : X ≤ N := le_left_of_mem_EvenIn hN
  have hsub : X + H - N ≤ H := by omega
  exact le_trans (Nat.div_le_self _ _) hsub

private lemma canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiber_mem_iff_exists_step
    {X N K : ℕ} (hN : N ∈ EvenIn X H) :
    K ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N ↔
      ∃ t : ℕ,
        t ≤ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N ∧
        K = N + 2 * t := by
  constructor
  · intro hK
    have hKwin : K ∈ EvenIn X H := (Finset.mem_filter.mp hK).1
    have hNK : N ≤ K := (Finset.mem_filter.mp hK).2
    have hNeven : Even N := Goldbach.Windows.even_of_isEven ((mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN).2
    have hKeven : Even K := Goldbach.Windows.even_of_isEven ((mem_EvenIn_iff (X := X) (H := H) (N := K)).1 hKwin).2
    have hDiffEven : Even (K - N) := by
      exact (Nat.even_sub hNK).2 <| by simpa [hKeven, hNeven]
    rcases hDiffEven with ⟨t, ht⟩
    refine ⟨t, ?_, ?_⟩
    · unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount
      have hKle : K ≤ X + H := le_right_of_mem_EvenIn hKwin
      have hmul' : t + t ≤ X + H - N := by
        omega
      have hmul : t * 2 ≤ X + H - N := by
        have hmul2 : 2 * t ≤ X + H - N := by
          simpa [two_mul] using hmul'
        simpa [Nat.mul_comm] using hmul2
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 hmul
    · have hEq : K = N + (t + t) := by omega
      simpa [two_mul, Nat.mul_comm, add_assoc, add_left_comm, add_comm] using hEq
  · rintro ⟨t, ht, rfl⟩
    unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow
    refine Finset.mem_filter.mpr ⟨?_, by omega⟩
    have hXleN : X ≤ N := le_left_of_mem_EvenIn hN
    have hNX : N - X ≤ H := sub_left_le_of_mem_EvenIn hN
    have hmul : 2 * t ≤ X + H - N := by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 ht
    have hIcc : N + 2 * t ∈ IccShift X H := by
      have hk : N - X + 2 * t ≤ H := by omega
      exact (mem_IccShift_iff (X := X) (H := H) (N := N + 2 * t)).2 ⟨N - X + 2 * t, hk, by omega⟩
    have hNevenI : IsEven N := ((mem_EvenIn_iff (X := X) (H := H) (N := N)).1 hN).2
    have hEven : IsEven (N + 2 * t) := by
      rcases Goldbach.Windows.even_of_isEven hNevenI with ⟨n0, hn0⟩
      refine Goldbach.Windows.isEven_of_even ?_
      refine ⟨n0 + t, ?_⟩
      simp [hn0, two_mul, add_left_comm, add_comm]
    exact mem_EvenIn_of_mem_IccShift_of_even hIcc hEven

private lemma canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiber_embedding_injective
    (N : ℕ) :
    Function.Injective (fun t : ℕ => N + 2 * t) := by
  intro a b hab
  have hab' : 2 * a = 2 * b := Nat.add_left_cancel hab
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hab'

private lemma canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow_eq_image_range
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N
      =
    (Finset.range (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N + 1)).image
      (fun t : ℕ => N + 2 * t) := by
  classical
  ext K
  constructor
  · intro hK
    rcases (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiber_mem_iff_exists_step (hN := hN)).1 hK with
      ⟨t, ht, rfl⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_succ_of_le ht), rfl⟩
  · intro hK
    rcases Finset.mem_image.mp hK with ⟨t, ht, rfl⟩
    exact (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiber_mem_iff_exists_step (hN := hN)).2
      ⟨t, Nat.le_of_lt_succ (Finset.mem_range.mp ht), rfl⟩

/--
Abstract transport layer from the positive fiberwise pairwise energy to the adjacent-step energy.

The live proof plan now works fiber-by-fiber on the one-variable profile
`K ↦ canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N K`, so this is the exact
reduction surface needed before proving any counting or strip lemmas.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseAdjacentTransport :
    Prop where
  bound :
    ∀ X : ℕ,
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowEnergy X
        ≤
      (((H + 1 : ℕ) : ℝ) ^ 3)
        * canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy X

/--
Per-fiber specialization surface for the abstract chain transport.

This isolates the only genuinely arithmetic step left in the positive branch: reindex each fiber by
adjacent even steps and compare its pairwise energy to the corresponding adjacent-step energy.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPerFiberAdjacentTransport :
    Prop where
  bound :
    ∀ {X N : ℕ}, N ∈ EvenIn X H →
      (∑ A ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
          ∑ B ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
            ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
              - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2)
        ≤
      (((H + 1 : ℕ) : ℝ) ^ 3)
        * ∑ t ∈ Finset.range (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N),
            ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * (t + 1))
              - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * t)‖ ^ 2

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseAdjacentTransport_of_perFiber
    (hper :
      CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPerFiberAdjacentTransport) :
    CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseAdjacentTransport where
  bound := by
    intro X
    have hsum :
        ∑ N ∈ EvenIn X H,
          (∑ A ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
              ∑ B ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
                ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
                  - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2)
          ≤
        ∑ N ∈ EvenIn X H,
          ((((H + 1 : ℕ) : ℝ) ^ 3)
            * ∑ t ∈ Finset.range (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N),
                ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * (t + 1))
                  - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * t)‖ ^ 2) := by
      exact Finset.sum_le_sum (fun N hN => hper.bound hN)
    simpa [canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowEnergy,
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy,
      Finset.mul_sum] using hsum

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPerFiberAdjacentTransport_concrete :
    CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPerFiberAdjacentTransport where
  bound := by
    intro X N hN
    let m := canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N
    have hwindow :
        canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N
          =
        (Finset.range (m + 1)).image (fun t : ℕ => N + 2 * t) := by
      simpa [m] using canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow_eq_image_range (hN := hN)
    have hinj : Set.InjOn (fun t : ℕ => N + 2 * t) ((Finset.range (m + 1) : Finset ℕ) : Set ℕ) := by
      intro a ha b hb hab
      exact canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiber_embedding_injective N hab
    have hpairRange :
        (∑ A ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
            ∑ B ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
              ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
                - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2)
          =
        ∑ a ∈ Finset.range (m + 1),
          ∑ b ∈ Finset.range (m + 1),
            ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * a)
              - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * b)‖ ^ 2 := by
      rw [hwindow, Finset.sum_image hinj]
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa using (Finset.sum_image hinj (f := fun b : ℕ =>
        ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * a)
          - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * b)‖ ^ 2))
    have hcore :=
      pairwise_range_norm_sq_le_cube_mul_adjacent
        m
        (fun t => canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * t))
    have hmle : m ≤ H := by
      simpa [m] using canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount_le_H hN
    have hcoeff :
        (((m + 1 : ℕ) : ℝ) ^ 3) ≤ (((H + 1 : ℕ) : ℝ) ^ 3) := by
      have hm1 : (((m + 1 : ℕ) : ℝ)) ≤ (((H + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (Nat.succ_le_succ hmle)
      exact pow_le_pow_left₀ (by positivity) hm1 3
    calc
      (∑ A ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
          ∑ B ∈ canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberWindow X N,
            ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N A
              - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N B‖ ^ 2)
        =
      ∑ a ∈ Finset.range (m + 1),
        ∑ b ∈ Finset.range (m + 1),
          ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * a)
            - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * b)‖ ^ 2 := hpairRange
      _ ≤
        (((m + 1 : ℕ) : ℝ) ^ 3)
          * ∑ K ∈ Finset.range m,
              ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * (K + 1))
                - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * K)‖ ^ 2 := hcore
      _ ≤
        (((H + 1 : ℕ) : ℝ) ^ 3)
          * ∑ K ∈ Finset.range m,
              ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * (K + 1))
                - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N (N + 2 * K)‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hcoeff (by
              exact Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseAdjacentTransport_concrete :
    CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseAdjacentTransport :=
  canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseAdjacentTransport_of_perFiber
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPerFiberAdjacentTransport_concrete

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy_eq_termwise
    (X : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy X
      =
    ∑ N ∈ EvenIn X H,
      ∑ t ∈ Finset.range (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N),
        ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral
            X N (N + 2 * (t + 1)) (N + 2 * t)‖ ^ 2 := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral
  simp [sub_eq_add_neg]

private lemma majorArcExponential_e_add (x y : ℝ) :
    Goldbach.Cert.MajorArcExponential.e (x + y)
      =
    Goldbach.Cert.MajorArcExponential.e x * Goldbach.Cert.MajorArcExponential.e y := by
  have hmul :
      Complex.exp (Complex.I * (2 * Real.pi * x))
          * Complex.exp (Complex.I * (2 * Real.pi * y))
        =
      Complex.exp
        ((Complex.I * (2 * Real.pi * x)) + (Complex.I * (2 * Real.pi * y))) := by
    exact (Complex.exp_add (Complex.I * (2 * Real.pi * x)) (Complex.I * (2 * Real.pi * y))).symm
  have hadd :
      (Complex.I * (2 * Real.pi * x) : ℂ) + Complex.I * (2 * Real.pi * y)
        =
      Complex.I * (2 * Real.pi * (x + y)) := by
    ring
  calc
    Goldbach.Cert.MajorArcExponential.e (x + y)
      = Complex.exp (Complex.I * (2 * Real.pi * (x + y))) := by
          simp [Goldbach.Cert.MajorArcExponential.e]
    _ = Complex.exp ((Complex.I * (2 * Real.pi * x) : ℂ) + Complex.I * (2 * Real.pi * y)) := by
          simp [hadd]
    _ = Goldbach.Cert.MajorArcExponential.e x * Goldbach.Cert.MajorArcExponential.e y := by
          simpa [Goldbach.Cert.MajorArcExponential.e, mul_assoc] using hmul.symm

/--
Fixed-overlap adjacent-step phase increment for the positive common branch.

Along a fiber, the overlap square is unchanged, so increasing `K` by `2` only inserts the scalar
phase increment `e (-(2u/X))`.
-/
theorem canonicalQ1TwoSidedShiftCommonPositiveOverlap_adjacent_eq_phaseIncrement_mul
    (X overlap K : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap (K + 2) u β
      =
    Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ)))
      * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveOverlap
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  let phase : ℂ :=
    Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
      * Goldbach.Cert.MajorArcExponential.e
          (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
  let z : ℝ :=
    (u / (X : ℝ))
      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ)))
  have hz :
      (u / (X : ℝ))
        * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 + 2 : ℕ) : ℝ)))
        =
      (-(2 * u / (X : ℝ))) + z := by
    dsimp [z]
    have hcast : (((K + 2 + 2 : ℕ) : ℝ)) = (((K + 2 : ℕ) : ℝ)) + 2 := by
      norm_num [Nat.cast_add]
    rw [hcast]
    ring
  calc
    phase
        * Goldbach.Cert.MajorArcExponential.e
            ((u / (X : ℝ))
              * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 + 2 : ℕ) : ℝ))))
      =
    phase * Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ)) + z) := by
        rw [hz]
    _ =
    phase
      * (Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ)))
          * Goldbach.Cert.MajorArcExponential.e z) := by
        rw [majorArcExponential_e_add]
    _ =
    Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ)))
      * (phase * Goldbach.Cert.MajorArcExponential.e z) := by
        ring

/--
Raw adjacent-step factorization for the positive termwise-difference common piece.

This is the exact local proof object for the next adjacent-step window target.
-/
theorem canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_adjacent_eq_phaseIncrement_mul_base
    (X overlap K : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X overlap (K + 2) K u β
      =
      (Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1)
        * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β := by
  have hraw :
      canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X overlap (K + 2) K u β
        =
      canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap (K + 2) u β
        - canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β := by
    unfold canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff
      canonicalQ1TwoSidedShiftCommonPositiveOverlap
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← Finset.sum_sub_distrib]
  have hsub :
      canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap (K + 2) u β
        - canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β
        =
      (Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1)
        * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β := by
    rw [canonicalQ1TwoSidedShiftCommonPositiveOverlap_adjacent_eq_phaseIncrement_mul]
    ring
  exact hraw.trans hsub

private lemma sum_Ico_mul_sum_Ico_eq_double
    (a b : ℕ) (f g : ℕ → ℂ) :
    (∑ n ∈ Finset.Ico a b, f n) * (∑ m ∈ Finset.Ico a b, g m)
      =
    ∑ n ∈ Finset.Ico a b, ∑ m ∈ Finset.Ico a b, f n * g m := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [Finset.mul_sum]

private lemma scalar_mul_sum_Ico_mul_sum_Ico_eq_double
    (a : ℂ) (L U : ℕ) (f g : ℕ → ℂ) :
    a * ((∑ n ∈ Finset.Ico L U, f n) * (∑ m ∈ Finset.Ico L U, g m))
      =
    ∑ n ∈ Finset.Ico L U, ∑ m ∈ Finset.Ico L U, a * (f n * g m) := by
  rw [sum_Ico_mul_sum_Ico_eq_double]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [Finset.mul_sum]

/--
Exact product decomposition of the fixed-overlap positive common piece.

This rewrites the double sum as a Fourier phase times a product of two one-dimensional `gExp`
sums on the Step-21 interval `Ico 4 ((overlap - 2) + 1)`.
-/
theorem canonicalQ1TwoSidedShiftCommonPositiveOverlap_eq_fourier_mul_product
    (X overlap K : ℕ) (u β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β
      =
    ((fourier (T := (1 : ℝ)) (-(K : ℤ))
        ((u / (X : ℝ)) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ))
      * canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β := by
  let s : Finset ℕ := Finset.Ico 4 ((overlap - 2) + 1)
  let φ : ℂ :=
    (fourier (T := (1 : ℝ)) (-(K : ℤ))
      ((u / (X : ℝ)) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
  have hrange :
      canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β
        =
      ∑ n ∈ s,
        ∑ m ∈ s,
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * ((n : ℝ) - (m : ℝ))
                  + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((K + 2 : ℕ) : ℝ)))) := by
    symm
    unfold s
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [majorArcExponential_e_add]
    simp [canonicalQ1TwoSidedShiftCommonPositiveOverlap, s, mul_assoc]
  calc
    canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β
        =
      ∑ n ∈ s,
        ∑ m ∈ s,
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * ((n : ℝ) - (m : ℝ))
                  + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((K + 2 : ℕ) : ℝ)))) := hrange
    _ =
      ∑ n ∈ s,
        ∑ m ∈ s,
          (φ
            * (Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n
                * Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hφ :
              φ = Goldbach.Cert.MajorArcExponential.e (-(K : ℝ) * (u / (X : ℝ))) := by
            unfold φ
            simpa using
              (Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e
                (k := (-(K : ℤ))) (x := (u / (X : ℝ))))
          simpa [φ, hφ, one_mul] using
            (Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation.rescaled_shell_summand_q1_eq_phase_corrected_centered
              (X := X) (N := K) (n := n) (m := m) (u := u) (β := β)).symm
    _ =
      φ * canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β := by
          unfold canonicalQ1TwoSidedShiftCommonPositiveProduct
          simpa [s, mul_assoc, mul_left_comm, mul_comm] using
            (scalar_mul_sum_Ico_mul_sum_Ico_eq_double φ 4 ((overlap - 2) + 1)
              (fun n => Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n)
              (fun m => Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m)).symm
    _ =
      ((fourier (T := (1 : ℝ)) (-(K : ℤ))
          ((u / (X : ℝ)) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ))
        * canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β := by
          rfl

theorem norm_canonicalQ1TwoSidedShiftCommonPositiveOverlap_eq_norm_product
    (X overlap K : ℕ) (u β : ℝ) :
    ‖canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β‖
      =
    ‖canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β‖ := by
  rw [canonicalQ1TwoSidedShiftCommonPositiveOverlap_eq_fourier_mul_product, norm_mul]
  have hF :
      ‖(fourier (T := (1 : ℝ)) (-(K : ℤ))
          (((u / (X : ℝ)) : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)‖ = 1 := by
    simpa [fourier_apply] using
      (norm_fourier
        (T := (1 : ℝ)) (n := (-(K : ℤ)))
        (x := (((u / (X : ℝ)) : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC)))
  simpa [hF]

private lemma norm_majorArcExponential_e_neg_two_u_div_X_sub_one_le
    {X : ℕ} (hX : X0 ≤ X) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1‖
      ≤ (8 * Real.pi) / (X : ℝ) := by
  have hXnat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXnat
  have huabs : |u| ≤ 1 := by
    rw [abs_of_nonneg hu0]
    linarith
  have hsmallX : (4 * Real.pi) / (X : ℝ) ≤ 1 := by
    have hX0real : ((X0 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hXlarge : (4 * Real.pi : ℝ) ≤ (X : ℝ) := by
      have h16 : (16 : ℝ) ≤ (X : ℝ) := by
        norm_num [Goldbach.BankParams.X0] at hX0real ⊢
        linarith
      have hlt : 4 * Real.pi < (16 : ℝ) := by
        nlinarith [Real.pi_lt_four]
      exact le_trans (le_of_lt hlt) h16
    exact (div_le_iff₀ hXpos).2 (by simpa using hXlarge)
  have hsmall :
      |2 * Real.pi * ((-(2 * u / (X : ℝ))) - 0)| ≤ 1 := by
    calc
      |2 * Real.pi * ((-(2 * u / (X : ℝ))) - 0)|
          = |((4 * Real.pi) / (X : ℝ)) * u| := by
              have hcalc :
                  2 * Real.pi * ((-(2 * u / (X : ℝ))) - 0)
                    = -(((4 * Real.pi) / (X : ℝ)) * u) := by
                field_simp [ne_of_gt hXpos]
                ring
              rw [hcalc, abs_neg]
      _ = ((4 * Real.pi) / (X : ℝ)) * |u| := by
            rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ ((4 * Real.pi) / (X : ℝ)) * 1 := by
            gcongr
      _ ≤ 1 := by simpa using hsmallX
  calc
    ‖Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1‖
        ≤ 4 * Real.pi * |(-(2 * u / (X : ℝ))) - 0| := by
            simpa [Goldbach.Cert.MajorArcExponential.e] using
              (Goldbach.Cert.MajorArcExponential.norm_e_sub_e_le_of_abs_two_pi_mul_sub_le_one
                (x := -(2 * u / (X : ℝ))) (y := 0) hsmall)
    _ = 4 * Real.pi * ((2 * |u|) / (X : ℝ)) := by
          rw [sub_zero, abs_neg]
          have habs :
              |2 * u / (X : ℝ)| = (2 * |u|) / (X : ℝ) := by
            rw [div_eq_mul_inv, abs_mul, abs_mul, abs_of_nonneg (by positivity),
              abs_of_nonneg (inv_nonneg.mpr (le_of_lt hXpos))]
            ring
          rw [habs]
    _ = ((8 * Real.pi) / (X : ℝ)) * |u| := by
          field_simp [ne_of_gt hXpos]
          ring
    _ ≤ ((8 * Real.pi) / (X : ℝ)) * 1 := by
          gcongr
    _ = (8 * Real.pi) / (X : ℝ) := by ring

private lemma norm_canonicalQ1TwoSidedShiftCommonPositiveOverlap_le_card_sq
    (X overlap K : ℕ) (u β : ℝ) :
    ‖canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β‖
      ≤ (((overlap - 5 : ℕ) : ℝ) ^ 2) := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveOverlap
  calc
    ‖∑ j ∈ Finset.range (overlap - 5),
        ∑ k ∈ Finset.range (overlap - 5),
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
            * Goldbach.Cert.MajorArcExponential.e
                ((u / (X : ℝ))
                  * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))‖
        ≤
      ∑ j ∈ Finset.range (overlap - 5),
        ‖∑ k ∈ Finset.range (overlap - 5),
            Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
              * Goldbach.Cert.MajorArcExponential.e
                  (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
              * Goldbach.Cert.MajorArcExponential.e
                  ((u / (X : ℝ))
                    * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))‖ := by
            simpa using
              (norm_sum_le
                (s := Finset.range (overlap - 5))
                (f := fun j : ℕ =>
                  ∑ k ∈ Finset.range (overlap - 5),
                    Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
                      * Goldbach.Cert.MajorArcExponential.e
                          (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
                      * Goldbach.Cert.MajorArcExponential.e
                          ((u / (X : ℝ))
                            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))))
    _ ≤
      ∑ j ∈ Finset.range (overlap - 5),
        ∑ k ∈ Finset.range (overlap - 5),
          ‖Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
            * Goldbach.Cert.MajorArcExponential.e
                ((u / (X : ℝ))
                  * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))‖ := by
            refine Finset.sum_le_sum ?_
            intro j hj
            simpa using
              (norm_sum_le
                (s := Finset.range (overlap - 5))
                (f := fun k : ℕ =>
                  Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
                    * Goldbach.Cert.MajorArcExponential.e
                        (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
                    * Goldbach.Cert.MajorArcExponential.e
                        ((u / (X : ℝ))
                          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((K + 2 : ℕ) : ℝ))))))
    _ =
      ∑ _j ∈ Finset.range (overlap - 5),
        ∑ _k ∈ Finset.range (overlap - 5), (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [norm_mul, Goldbach.Cert.MajorArcExponential.norm_e]
    _ = (((overlap - 5 : ℕ) : ℝ) ^ 2) := by
          simp [pow_two, mul_comm, mul_left_comm, mul_assoc]

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowTarget_of_adjacentStep
    {C3 : ℝ}
    (htransport :
      CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseAdjacentTransport)
    (hstep : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowTarget C3) :
  CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowTarget
      ((((H + 1 : ℕ) : ℝ) ^ 3) * C3) where
  C3_nonneg := by
    exact mul_nonneg (by positivity) hstep.C3_nonneg
  bound := by
    intro X hX
    calc
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowEnergy X
          ≤
        (((H + 1 : ℕ) : ℝ) ^ 3)
          * canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy X :=
            htransport.bound X
      _ ≤
        (((H + 1 : ℕ) : ℝ) ^ 3)
          * (2 * (((EvenIn X H).card : ℝ)
              * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
            exact mul_le_mul_of_nonneg_left (hstep.bound hX) (by positivity)
      _ =
        2 * (((EvenIn X H).card : ℝ)
          * ((((H + 1 : ℕ) : ℝ) ^ 3 * C3)
              / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
            ring

/--
Exact phase/cos-defect rewrite of the common-square contribution.

This makes the current obstruction explicit: on the shared overlap square, the geometric support is
the same, but the centered shift still depends on `N + 2` versus `M + 2`, so the common term is
not termwise zero without an additional cancellation theorem.
-/
theorem canonicalQ1TwoSidedShiftCommonSquareDiff_eq_phase_mul_real_cos_defect_sub
    (X N M : ℕ) (u β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N M u β
      =
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        let phase :=
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        let defectN : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((N + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        let defectM : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((M + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        phase * (defectN - defectM) := by
  unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [q1TwoSidedShiftRangeTerm_eq_phase_mul_real_cos_defect]
  rw [q1TwoSidedShiftRangeTerm_eq_phase_mul_real_cos_defect]
  ring

/--
Exact positive/negative profile decomposition of the common-square term.

This is the honest first step toward the common-piece energy theorem. The overlap width still
depends on the left endpoint `N`, so this is not yet a pure gap-only factorization; but it already
separates the geometry from the one-variable phase defects.
-/
theorem canonicalQ1TwoSidedShiftCommonSquareDiff_eq_positive_sub_positive_add_negative_sub_negative
    (X N M : ℕ) (u β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N M u β
      =
    canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β
      + canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β := by
  calc
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N M u β
      =
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        let phase :=
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        let zN : ℝ :=
          (u / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))
        let zM : ℝ :=
          (u / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ)))
        phase
          * ((((2 * (Real.cos (2 * Real.pi * zN) - 1) : ℝ) : ℂ))
              - (((2 * (Real.cos (2 * Real.pi * zM) - 1) : ℝ) : ℂ))) := by
          unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [q1TwoSidedShiftRangeTerm_eq_phase_mul_real_cos_defect]
          rw [q1TwoSidedShiftRangeTerm_eq_phase_mul_real_cos_defect]
          ring
    _ =
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        let phase :=
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        let zN : ℝ :=
          (u / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))
        let zM : ℝ :=
          (u / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ)))
        phase * Goldbach.Cert.MajorArcExponential.e zN
          - phase * Goldbach.Cert.MajorArcExponential.e zM
          + phase * Goldbach.Cert.MajorArcExponential.e (-zN)
          - phase * Goldbach.Cert.MajorArcExponential.e (-zM) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          dsimp
          rw [← Goldbach.Cert.MajorArcExponential.e_add_e_neg_sub_two_eq_real
              ((u / (X : ℝ))
                * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))))]
          rw [← Goldbach.Cert.MajorArcExponential.e_add_e_neg_sub_two_eq_real
              ((u / (X : ℝ))
                * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ))))]
          ring
    _ =
      (∑ j ∈ Finset.range (N - 5),
        ∑ k ∈ Finset.range (N - 5),
          let phase :=
            Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
              * Goldbach.Cert.MajorArcExponential.e
                  (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
          let zN : ℝ :=
            (u / (X : ℝ))
              * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))
          let zM : ℝ :=
            (u / (X : ℝ))
              * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ)))
          (phase * Goldbach.Cert.MajorArcExponential.e zN
            - phase * Goldbach.Cert.MajorArcExponential.e zM)
          +
          (phase * Goldbach.Cert.MajorArcExponential.e (-zN)
            - phase * Goldbach.Cert.MajorArcExponential.e (-zM))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine Finset.sum_congr rfl ?_
          intro k hk
          dsimp
          ring
    _ =
      ∑ j ∈ Finset.range (N - 5),
        ((∑ k ∈ Finset.range (N - 5),
            let phase :=
              Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
                * Goldbach.Cert.MajorArcExponential.e
                    (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
            let zN : ℝ :=
              (u / (X : ℝ))
                * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))
            let zM : ℝ :=
              (u / (X : ℝ))
                * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ)))
            phase * Goldbach.Cert.MajorArcExponential.e zN
              - phase * Goldbach.Cert.MajorArcExponential.e zM)
          +
          (∑ k ∈ Finset.range (N - 5),
            let phase :=
              Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
                * Goldbach.Cert.MajorArcExponential.e
                    (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
            let zN : ℝ :=
              (u / (X : ℝ))
                * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))
            let zM : ℝ :=
              (u / (X : ℝ))
                * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((M + 2 : ℕ) : ℝ)))
            phase * Goldbach.Cert.MajorArcExponential.e (-zN)
              - phase * Goldbach.Cert.MajorArcExponential.e (-zM))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← Finset.sum_add_distrib]
    _ =
      canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β
        + canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β := by
          unfold canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff
            canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff
          rw [Finset.sum_add_distrib]

/--
Pointwise two-term square upper for the common-square contribution.

This is the first theorem-strength upper bound separating the common piece into positive and
negative one-variable profile differences. The overlap width is still carried by `N`; later gap
arguments can be layered on top of this bound.
-/
theorem sq_norm_canonicalQ1TwoSidedShiftCommonSquareDiff_le_two_mul_profile_diffs
    (X N M : ℕ) (u β : ℝ) :
    ‖Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N M u β‖ ^ 2
      ≤
    2 * ‖canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β‖ ^ 2
      +
    2 * ‖canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β‖ ^ 2 := by
  rw [canonicalQ1TwoSidedShiftCommonSquareDiff_eq_positive_sub_positive_add_negative_sub_negative]
  set A : ℂ :=
    canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β
  set B : ℂ :=
    canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β
  have hnorm :=
    norm_add_le A B
  have hsq1 :
      ‖A + B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by
    have habs :
        |‖A + B‖| ≤ |‖A‖ + ‖B‖| := by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
      simpa using hnorm
    exact sq_le_sq.mpr habs
  have hsq2 : (‖A‖ + ‖B‖) ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    have hnonneg :
        0 ≤ (‖A‖ - ‖B‖) ^ 2 := by
      exact sq_nonneg _
    nlinarith
  simpa [A, B, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using le_trans hsq1 hsq2

private theorem kernel_mul_canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_eq_sub
    (X N M : ℕ) (u β : ℝ) :
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β
      =
    ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonPositiveOverlap X N N u β)
      -
    ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonPositiveOverlap X N M u β) := by
  have hraw :
      canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β
        =
      canonicalQ1TwoSidedShiftCommonPositiveOverlap X N N u β
        - canonicalQ1TwoSidedShiftCommonPositiveOverlap X N M u β := by
    unfold canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff
      canonicalQ1TwoSidedShiftCommonPositiveOverlap
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← Finset.sum_sub_distrib]
  rw [hraw, mul_sub]

private theorem kernel_mul_canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_eq_sub_general
    (X overlap N M : ℕ) (u β : ℝ) :
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X overlap N M u β
      =
    ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap N u β)
      -
    ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap M u β) := by
  have hraw :
      canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X overlap N M u β
        =
      canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap N u β
        - canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap M u β := by
    unfold canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff
      canonicalQ1TwoSidedShiftCommonPositiveOverlap
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← Finset.sum_sub_distrib]
  rw [hraw, mul_sub]

private theorem kernel_mul_canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff_eq_sub
    (X N M : ℕ) (u β : ℝ) :
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β
      =
    ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonNegativeOverlap X N N u β)
      -
    ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonNegativeOverlap X N M u β) := by
  have hraw :
      canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β
        =
      canonicalQ1TwoSidedShiftCommonNegativeOverlap X N N u β
        - canonicalQ1TwoSidedShiftCommonNegativeOverlap X N M u β := by
    unfold canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff
      canonicalQ1TwoSidedShiftCommonNegativeOverlap
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← Finset.sum_sub_distrib]
  rw [hraw, mul_sub]

private theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_eq_integral_termwiseDiff
    (X overlap N M : ℕ) (β : ℝ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X overlap N M β
      =
    ∫ u in (0 : ℝ)..(1 : ℝ),
      (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X overlap N M u β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand X overlap N β)
    (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand X overlap M β)]
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun u _ => by
    exact (kernel_mul_canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_eq_sub_general
      X overlap N M u β).symm

private theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral_eq_integral_termwiseUIntegral
    (X overlap N M : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X overlap N M
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X overlap N M β) β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
      X overlap N)
    (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
      X overlap M)]
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun β _ => by
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [hβ, canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral]
    · simp [hβ]

private theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_adjacent_eq_product
    (X overlap K : ℕ) (β : ℝ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X overlap (K + 2) K β
      =
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral X overlap K β := by
  rw [canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_eq_integral_termwiseDiff]
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun u _ => by
    rw [canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_adjacent_eq_phaseIncrement_mul_base,
      canonicalQ1TwoSidedShiftCommonPositiveOverlap_eq_fourier_mul_product]

private theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral_adjacent_eq_product
    (X overlap K : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X overlap (K + 2) K
      =
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral X overlap K := by
  rw [canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral_eq_integral_termwiseUIntegral]
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun β _ => by
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [hβ, canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_adjacent_eq_product]
    · simp [hβ]

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy_eq_product
    (X : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy X
      =
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowEnergy X := by
  rw [canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy_eq_termwise]
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowEnergy
  refine Finset.sum_congr rfl ?_
  intro N hN
  refine Finset.sum_congr rfl ?_
  intro t ht
  have hstep : N + 2 * (t + 1) = (N + 2 * t) + 2 := by omega
  have hEq :
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N (N + 2 * (t + 1))
        (N + 2 * t)
        =
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral X N (N + 2 * t) := by
    simpa [hstep] using
      (canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral_adjacent_eq_product
        X N (N + 2 * t))
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hEq

theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowTarget_of_product
    {C3 : ℝ}
    (hprod : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowTarget C3) :
    CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowTarget C3 where
  C3_nonneg := hprod.C3_nonneg
  bound := by
    intro X hX
    rw [canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentStepWindowEnergy_eq_product]
    exact hprod.bound hX

private theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral_eq_integral_mixedShell_sub
    (X overlap K : ℕ) (β : ℝ) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral X overlap K β
      =
    ∫ u in (0 : ℝ)..(1 : ℝ),
      canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) (u / (X : ℝ)) β
        - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K (u / (X : ℝ)) β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun u _ => by
    have hfour :
        ((fourier (T := (1 : ℝ)) (-(K + 2 : ℤ)) ((u / (X : ℝ)) : UC) : ℂ))
          =
        (Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))))
          * (fourier (T := (1 : ℝ)) (-(K : ℤ)) ((u / (X : ℝ)) : UC) : ℂ) := by
      rw [Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e,
        Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e]
      have hphase :
          (((-(K + 2 : ℤ)) : ℝ) * (u / (X : ℝ)))
            = (-(2 * u / (X : ℝ))) + (((-(K : ℤ)) : ℝ) * (u / (X : ℝ))) := by
        ring
      calc
        Goldbach.Cert.MajorArcExponential.e (((( -(K + 2 : ℤ)) : ℝ) * (u / (X : ℝ))))
            = Goldbach.Cert.MajorArcExponential.e
                (-(2 * u / (X : ℝ)) + (((-(K : ℤ)) : ℝ) * (u / (X : ℝ)))) := by
                  rw [hphase]
        _ = Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ)))
              * Goldbach.Cert.MajorArcExponential.e (((( -(K : ℤ)) : ℝ) * (u / (X : ℝ)))) := by
                rw [majorArcExponential_e_add]
        _ = (Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))))
              * (fourier (T := (1 : ℝ)) (-(K : ℤ)) ((u / (X : ℝ)) : UC) : ℂ) := by
                rw [Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e]
    rw [canonicalQ1TwoSidedShiftCommonPositiveMixedShell_eq_kernel_mul_fourier_mul_plus_minus,
      canonicalQ1TwoSidedShiftCommonPositiveMixedShell_eq_kernel_mul_fourier_mul_plus_minus, hfour]
    ring

private theorem canonicalQ1TwoSidedShiftCommonPositiveMixedShell_zero_indep
    (overlap K L : ℕ) (β : ℝ) :
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K 0 β
      =
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap L 0 β := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveMixedShell
  simp [Goldbach.Cert.MajorArcStep13RealToCircle.fourier_coe_eq_e]

private lemma norm_gExp_sum_Ico_le_card_local (x : ℝ) (overlap : ℕ) :
    ‖∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖
      ≤ (Finset.Ico 4 ((overlap - 2) + 1)).card := by
  calc
    ‖∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖
      ≤ ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
          ‖Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖ := by
            exact norm_sum_le _ _
    _ = (Finset.Ico 4 ((overlap - 2) + 1)).card := by
          simp [Goldbach.Cert.MajorArcStep2ExpSums.norm_gExp]

private lemma norm_canonicalQ1TwoSidedShiftCommonPositiveMixedShell_shift_sub_zero_le
    (overlap K : ℕ) (θ β : ℝ)
    (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K θ β
        - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K 0 β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((overlap - 2) + 1)).card : ℝ) ^ 2
              * (((K : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ)) * (4 * Real.pi * |θ|))) := by
  let Kβ : ℂ := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
  let φθ : ℂ := (fourier (T := (1 : ℝ)) (-(K : ℤ)) (θ : UC) : ℂ)
  let Vpθ : ℂ := ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
  let Vmθ : ℂ := ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n
  let Vp0 : ℂ := ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
  let Vm0 : ℂ := ∑ n ∈ Finset.Ico 4 ((overlap - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n
  let cardN : ℝ := (Finset.Ico 4 ((overlap - 2) + 1)).card
  let L : ℝ := 4 * Real.pi * |θ|
  have hKβ :
      ‖Kβ‖ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap := by
    dsimp [Kβ]
    exact Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap
      (x := (β : UC))
  have hVpθ : ‖Vpθ‖ ≤ cardN := by
    dsimp [Vpθ, cardN]
    exact norm_gExp_sum_Ico_le_card_local (x := θ + β) overlap
  have hVmθ : ‖Vmθ‖ ≤ cardN := by
    dsimp [Vmθ, cardN]
    exact norm_gExp_sum_Ico_le_card_local (x := θ - β) overlap
  have hVp0 : ‖Vp0‖ ≤ cardN := by
    dsimp [Vp0, cardN]
    exact norm_gExp_sum_Ico_le_card_local (x := β) overlap
  have hφsub : ‖φθ - 1‖ ≤ (K : ℝ) * L := by
    dsimp [φθ, L]
    simpa using
      Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation.norm_fourier_neg_nat_sub_one_le K θ hθ
  have hVpDiff : ‖Vpθ - Vp0‖ ≤ cardN * ((overlap - 2 : ℕ) : ℝ) * L := by
    dsimp [Vpθ, Vp0, cardN, L]
    simpa [add_comm, add_left_comm, add_assoc] using
      Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation.norm_gExp_sum_Ico_add_shift_sub_le
        β θ overlap hθ
  have hVmDiff : ‖Vmθ - Vm0‖ ≤ cardN * ((overlap - 2 : ℕ) : ℝ) * L := by
    dsimp [Vmθ, Vm0, cardN, L]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation.norm_gExp_sum_Ico_add_shift_sub_le
        (-β) θ overlap hθ
  have hsplit :
      φθ * Vpθ * Vmθ - Vp0 * Vm0
        = (((φθ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ + Vp0 * (Vmθ - Vm0) := by
    ring
  have hmid :
      ‖φθ * Vpθ * Vmθ - Vp0 * Vm0‖
        ≤ ((((K : ℝ) * L) * cardN) + cardN * ((overlap - 2 : ℕ) : ℝ) * L) * cardN
            + cardN * (cardN * ((overlap - 2 : ℕ) : ℝ) * L) := by
    rw [hsplit]
    calc
      ‖((((φθ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ) + Vp0 * (Vmθ - Vm0)‖
        ≤ ‖(((φθ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ‖ + ‖Vp0 * (Vmθ - Vm0)‖ := by
            simpa using
              norm_add_le ((((φθ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ) (Vp0 * (Vmθ - Vm0))
      _ ≤ (‖((φθ - 1) * Vpθ) + (Vpθ - Vp0)‖ * ‖Vmθ‖) + (‖Vp0‖ * ‖Vmθ - Vm0‖) := by
            gcongr <;> simp [norm_mul]
      _ ≤ ((‖(φθ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖) * ‖Vmθ‖) + (‖Vp0‖ * ‖Vmθ - Vm0‖) := by
            gcongr
            simpa using norm_add_le ((φθ - 1) * Vpθ) (Vpθ - Vp0)
      _ ≤ ((((K : ℝ) * L) * cardN) + cardN * ((overlap - 2 : ℕ) : ℝ) * L) * cardN
            + cardN * (cardN * ((overlap - 2 : ℕ) : ℝ) * L) := by
            have hA :
                ‖(φθ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖
                  ≤ (((K : ℝ) * L) * cardN) + cardN * ((overlap - 2 : ℕ) : ℝ) * L := by
              have hmul :
                  ‖(φθ - 1) * Vpθ‖ ≤ ((K : ℝ) * L) * cardN := by
                calc
                  ‖(φθ - 1) * Vpθ‖ = ‖φθ - 1‖ * ‖Vpθ‖ := by simp [norm_mul]
                  _ ≤ ((K : ℝ) * L) * cardN := by gcongr
              linarith
            have hB :
                (‖(φθ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖) * ‖Vmθ‖
                  ≤ ((((K : ℝ) * L) * cardN) + cardN * ((overlap - 2 : ℕ) : ℝ) * L) * cardN := by
              exact mul_le_mul hA hVmθ (norm_nonneg _) (by positivity)
            have hC :
                ‖Vp0‖ * ‖Vmθ - Vm0‖ ≤ cardN * (cardN * ((overlap - 2 : ℕ) : ℝ) * L) := by
              exact mul_le_mul hVp0 hVmDiff (norm_nonneg _) (by positivity)
            linarith
  have hrew :
      canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K θ β
        - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K 0 β
        = Kβ * (φθ * Vpθ * Vmθ - Vp0 * Vm0) := by
    unfold canonicalQ1TwoSidedShiftCommonPositiveMixedShell
    dsimp [Kβ, φθ, Vpθ, Vmθ, Vp0, Vm0]
    simp
    ring
  calc
    ‖canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K θ β
        - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K 0 β‖
      = ‖Kβ * (φθ * Vpθ * Vmθ - Vp0 * Vm0)‖ := by rw [hrew]
    _ = ‖Kβ‖ * ‖φθ * Vpθ * Vmθ - Vp0 * Vm0‖ := by simp [norm_mul]
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((((K : ℝ) * L) * cardN) + cardN * ((overlap - 2 : ℕ) : ℝ) * L) * cardN
              + cardN * (cardN * ((overlap - 2 : ℕ) : ℝ) * L)) := by
            exact mul_le_mul hKβ hmid (norm_nonneg _) Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (cardN ^ 2 * (((K : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ)) * L)) := by
            ring
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((overlap - 2) + 1)).card : ℝ) ^ 2
              * (((K : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ)) * (4 * Real.pi * |θ|))) := by
            rfl

private lemma abs_u_div_X_le_inv_of_unitInterval
    {X : ℕ} (hX : 1 ≤ X) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |u / (X : ℝ)| ≤ 1 / (X : ℝ) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    |u / (X : ℝ)| = |u| / (X : ℝ) := by
      rw [abs_div, abs_of_nonneg (le_of_lt hXpos)]
    _ ≤ 1 / (X : ℝ) := by
      gcongr
      have huabs : |u| ≤ 1 := by
        rw [abs_of_nonneg hu0]
        exact hu1
      simpa using huabs

private lemma abs_two_pi_mul_u_div_X_le_one_of_unitInterval
    {X : ℕ} (hX : X0 ≤ X) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |2 * Real.pi * (u / (X : ℝ))| ≤ 1 := by
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ X0) hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hsmallX : ((2 * Real.pi) / (X : ℝ)) ≤ 1 := by
    have hXlarge : (8 : ℝ) ≤ X := by
      exact_mod_cast (le_trans (by decide : 8 ≤ X0) hX)
    have htwo_pi_le_eight : (2 * Real.pi : ℝ) ≤ 8 := by
      nlinarith [le_of_lt Real.pi_lt_four]
    have hmain : (2 * Real.pi : ℝ) ≤ (X : ℝ) := le_trans htwo_pi_le_eight hXlarge
    exact (div_le_iff₀ hXpos).2 (by simpa using hmain)
  calc
    |2 * Real.pi * (u / (X : ℝ))|
      = |((2 * Real.pi) / (X : ℝ)) * u| := by
          field_simp [ne_of_gt hXpos]
          ring
    _ = ((2 * Real.pi) / (X : ℝ)) * |u| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ ((2 * Real.pi) / (X : ℝ)) * 1 := by
          gcongr
          have huabs : |u| ≤ 1 := by
            rw [abs_of_nonneg hu0]
            exact hu1
          simpa using huabs
    _ ≤ 1 := by
          simpa using hsmallX

private noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductGeomBound
    (X overlap : ℕ) (u β : ℝ) : ℝ :=
  Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
    * (((8 * Real.pi) / (X : ℝ))
        * (finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) + β)
            * finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) - β)))

private lemma canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductGeomBound_nonneg
    (X overlap : ℕ) (u β : ℝ) :
    0 ≤ canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductGeomBound X overlap u β := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductGeomBound
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast Nat.succ_pos X
  positivity

private lemma norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductRawIntegrand_le_geom
    {X overlap K : ℕ} (hX : X0 ≤ X) {u β : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * ((Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1)
            * (((fourier (T := (1 : ℝ)) (-(K : ℤ)) ((u / (X : ℝ)) : UC) : ℂ))
                * canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β))‖
      ≤ canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductGeomBound X overlap u β := by
  have hK :
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap := by
    exact Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap
      (x := (β : UC))
  have hphase :
      ‖Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1‖
        ≤ (8 * Real.pi) / (X : ℝ) := by
    exact norm_majorArcExponential_e_neg_two_u_div_X_sub_one_le hX hu0 hu1
  have hfour :
      ‖(fourier (T := (1 : ℝ)) (-(K : ℤ))
          ((u / (X : ℝ)) : UC) : ℂ)‖ = 1 := by
    simpa [fourier_apply] using
      (norm_fourier
        (T := (1 : ℝ)) (n := (-(K : ℤ)))
        (x := (((u / (X : ℝ)) : ℝ) : UC)))
  have hplus :
      ‖canonicalQ1TwoSidedShiftCommonPositivePlusSum X overlap u β‖
        ≤ finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) + β) :=
    norm_canonicalQ1TwoSidedShiftCommonPositivePlusSum_le_geomBound X overlap u β
  have hminus :
      ‖canonicalQ1TwoSidedShiftCommonPositiveMinusSum X overlap u β‖
        ≤ finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) - β) :=
    norm_canonicalQ1TwoSidedShiftCommonPositiveMinusSum_le_geomBound X overlap u β
  calc
    ‖(Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * ((Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1)
            * (((fourier (T := (1 : ℝ)) (-(K : ℤ)) ((u / (X : ℝ)) : UC) : ℂ))
                * canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β))‖
      = ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
          * ‖Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1‖
          * ‖(fourier (T := (1 : ℝ)) (-(K : ℤ)) ((u / (X : ℝ)) : UC) : ℂ)‖
          * ‖canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β‖ := by
            rw [canonicalQ1TwoSidedShiftCommonPositiveProduct_eq_plus_mul_minus]
            simp [norm_mul, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((8 * Real.pi) / (X : ℝ))
          * 1
          * (finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) + β)
              * finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) - β)) := by
            have hprod :
                ‖canonicalQ1TwoSidedShiftCommonPositiveProduct X overlap u β‖
                  ≤ finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) + β)
                      * finiteGExpIcoGeomBound overlap ((u / (X : ℝ)) - β) := by
              rw [canonicalQ1TwoSidedShiftCommonPositiveProduct_eq_plus_mul_minus, norm_mul]
              exact mul_le_mul hplus hminus (by positivity) (by positivity)
            gcongr
            · exact hK
            · exact hphase
            · rw [hfour]
            · exact hprod
    _ = canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductGeomBound X overlap u β := by
          unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductGeomBound
          ring

/--
Pointwise oscillation-driven upper bound for the fixed-overlap adjacent product `u`-integrand.

This is the first genuinely theorem-facing bound on the positive adjacent-step branch. It uses the
exact mixed-shell reduction and the one-dimensional oscillation lemmas, not the crude overlap-card
route.
-/
private noncomputable def canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound
    (X overlap K : ℕ) : ℝ :=
  Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
    * (((Finset.Ico 4 ((overlap - 2) + 1)).card : ℝ) ^ 2
        * (((K : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ)) * ((4 * Real.pi) / (X : ℝ))))

private lemma canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound_nonneg
    (X overlap K : ℕ) :
    0 ≤ canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K := by
  unfold canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast Nat.succ_pos X
  have hXnn : 0 ≤ (X : ℝ) := le_of_lt hXpos
  have hdivnn : 0 ≤ (4 * Real.pi) / (X : ℝ) := by
    exact div_nonneg (by positivity) hXnn
  positivity

private lemma norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegrand_le
    {X overlap K : ℕ} (hX : X0 ≤ X) {u β : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) (u / (X : ℝ)) β
        - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K (u / (X : ℝ)) β‖
      ≤
    canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2)
      + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K := by
  have hθ : |2 * Real.pi * (u / (X : ℝ))| ≤ 1 :=
    abs_two_pi_mul_u_div_X_le_one_of_unitInterval hX hu0 hu1
  have hθ' : |u / (X : ℝ)| ≤ 1 / (X : ℝ) :=
    abs_u_div_X_le_inv_of_unitInterval (hX := le_trans (by decide : 1 ≤ X0) hX) hu0 hu1
  let S2 :=
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) (u / (X : ℝ)) β
  let S0 :=
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) 0 β
  let T :=
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K (u / (X : ℝ)) β
  have hzero :
      canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) 0 β
        =
      canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K 0 β :=
    canonicalQ1TwoSidedShiftCommonPositiveMixedShell_zero_indep overlap (K + 2) K β
  have hsplit : S2 - T = (S2 - S0) - (T - S0) := by
    dsimp [S2, S0, T]
    ring
  have hshift2_raw :=
    norm_canonicalQ1TwoSidedShiftCommonPositiveMixedShell_shift_sub_zero_le
      overlap (K + 2) (u / (X : ℝ)) β hθ
  have hshiftK_raw :=
    norm_canonicalQ1TwoSidedShiftCommonPositiveMixedShell_shift_sub_zero_le
      overlap K (u / (X : ℝ)) β hθ
  have hshift2 :
      ‖S2 - S0‖
        ≤ canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2) := by
    dsimp [S2, S0]
    unfold canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound
    calc
      ‖canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) (u / (X : ℝ)) β
          - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) 0 β‖
        ≤
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((Finset.Ico 4 ((overlap - 2) + 1)).card : ℝ) ^ 2
            * ((((K + 2 : ℕ) : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ))
                * (4 * Real.pi * |u / (X : ℝ)|))) := hshift2_raw
      _ ≤
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((Finset.Ico 4 ((overlap - 2) + 1)).card : ℝ) ^ 2
            * ((((K + 2 : ℕ) : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ))
                * ((4 * Real.pi) / (X : ℝ)))) := by
              gcongr
              have hmul :
                  (4 * Real.pi) * |u / (X : ℝ)|
                    ≤ (4 * Real.pi) * (1 / (X : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hθ' (by positivity)
              simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
  have hshiftK :
      ‖T - S0‖
        ≤ canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K := by
    dsimp [T, S0]
    rw [hzero]
    unfold canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound
    calc
      ‖canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K (u / (X : ℝ)) β
          - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K 0 β‖
        ≤
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((Finset.Ico 4 ((overlap - 2) + 1)).card : ℝ) ^ 2
            * (((K : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ))
                * (4 * Real.pi * |u / (X : ℝ)|))) := hshiftK_raw
      _ ≤
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((Finset.Ico 4 ((overlap - 2) + 1)).card : ℝ) ^ 2
            * (((K : ℝ) + 2 * ((overlap - 2 : ℕ) : ℝ))
                * ((4 * Real.pi) / (X : ℝ)))) := by
              gcongr
              have hmul :
                  (4 * Real.pi) * |u / (X : ℝ)|
                    ≤ (4 * Real.pi) * (1 / (X : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hθ' (by positivity)
              simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
  calc
    ‖canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap (K + 2) (u / (X : ℝ)) β
        - canonicalQ1TwoSidedShiftCommonPositiveMixedShell overlap K (u / (X : ℝ)) β‖
      = ‖(S2 - S0) - (T - S0)‖ := by rw [hsplit]
    _ ≤ ‖S2 - S0‖ + ‖T - S0‖ := by simpa using norm_sub_le (S2 - S0) (T - S0)
    _ ≤ canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2)
          + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K := by
          linarith

private lemma norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral_le
    {X overlap K : ℕ} (hX : X0 ≤ X) (β : ℝ) :
    ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral X overlap K β‖
      ≤
    canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2)
      + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K := by
  rw [canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral_eq_integral_mixedShell_sub]
  have hCnonneg :
      0 ≤
        canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2)
          + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K := by
    exact add_nonneg
      (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound_nonneg X overlap (K + 2))
      (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound_nonneg X overlap K)
  refine norm_intervalIntegral_zero_one_le (hC := hCnonneg) ?_
  intro u hu0 hu1
  exact norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegrand_le hX hu0 hu1

private lemma norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral_le
    {X overlap K : ℕ} (hX : X0 ≤ X) :
    ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral X overlap K‖
      ≤
    (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2)
      + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K) / 6 := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral
  have hCnonneg :
      0 ≤ canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2)
          + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K := by
    exact add_nonneg
      (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound_nonneg X overlap (K + 2))
      (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound_nonneg X overlap K)
  refine norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six (hC := hCnonneg) ?_
  intro β hβ
  exact norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductUIntegral_le hX β

private noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegralBound
    (X overlap K : ℕ) : ℝ :=
  (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap (K + 2)
    + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X overlap K) / 6

private lemma canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegralBound_nonneg
    (X overlap K : ℕ) :
    0 ≤ canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegralBound X overlap K := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegralBound
  positivity

private theorem canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowEnergy_le_boundSum
    {X : ℕ} (hX : X0 ≤ X) :
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowEnergy X
      ≤
    ∑ N ∈ EvenIn X H,
      ∑ t ∈ Finset.range (canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberStepCount X N),
        (canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegralBound
          X N (N + 2 * t)) ^ 2 := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberAdjacentProductWindowEnergy
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegralBound
  refine Finset.sum_le_sum ?_
  intro N hN
  refine Finset.sum_le_sum ?_
  intro t ht
  have hnorm :=
    norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral_le
      (hX := hX) (overlap := N) (K := N + 2 * t)
  have hnonneg :
      0 ≤
        (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X N (N + 2 * t + 2)
          + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X N (N + 2 * t)) / 6 := by
    exact div_nonneg
      (add_nonneg
        (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound_nonneg X N (N + 2 * t + 2))
        (canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound_nonneg X N (N + 2 * t)))
      (by positivity)
  have hsquare :
      ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral X N (N + 2 * t)‖ ^ 2
        ≤
      (((canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X N (N + 2 * t + 2)
          + canonicalQ1TwoSidedShiftCommonPositiveMixedShellStepBound X N (N + 2 * t)) / 6) ^ 2) := by
    nlinarith [hnorm, norm_nonneg (canonicalQ1TwoSidedShiftBoundaryCommonPositiveAdjacentProductIntegral X N (N + 2 * t)), hnonneg]
  simpa [pow_two] using hsquare

private lemma norm_kernel_mul_canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_adjacent_le
    {X overlap K : ℕ} (hX : X0 ≤ X) {u β : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X overlap (K + 2) K u β‖
      ≤
    ((8 * Real.pi) / (X : ℝ))
      * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((overlap - 5 : ℕ) : ℝ) ^ 2)) := by
  rw [canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_adjacent_eq_phaseIncrement_mul_base]
  calc
    ‖(Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * ((Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1)
            * canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β)‖
      =
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
      * (‖Goldbach.Cert.MajorArcExponential.e (-(2 * u / (X : ℝ))) - 1‖
          * ‖canonicalQ1TwoSidedShiftCommonPositiveOverlap X overlap K u β‖) := by
        simp [norm_mul, mul_assoc, mul_left_comm, mul_comm]
    _ ≤
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
      * (((8 * Real.pi) / (X : ℝ))
          * (((overlap - 5 : ℕ) : ℝ) ^ 2)) := by
        gcongr
        · exact norm_majorArcExponential_e_neg_two_u_div_X_sub_one_le hX hu0 hu1
        · exact norm_canonicalQ1TwoSidedShiftCommonPositiveOverlap_le_card_sq X overlap K u β
    _ ≤
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
      * (((8 * Real.pi) / (X : ℝ))
          * (((overlap - 5 : ℕ) : ℝ) ^ 2)) := by
        gcongr
        exact Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap
          (x := (β : UC))
    _ = ((8 * Real.pi) / (X : ℝ))
        * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * (((overlap - 5 : ℕ) : ℝ) ^ 2)) := by
        ring

private lemma norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_adjacent_le
    {X overlap K : ℕ} (hX : X0 ≤ X) (β : ℝ) :
    ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X overlap (K + 2) K β‖
      ≤
    ((8 * Real.pi) / (X : ℝ))
      * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((overlap - 5 : ℕ) : ℝ) ^ 2)) := by
  rw [canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_eq_integral_termwiseDiff]
  have hXnat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hCnonneg :
      0 ≤
        ((8 * Real.pi) / (X : ℝ))
          * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * (((overlap - 5 : ℕ) : ℝ) ^ 2)) := by
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXnat
    have hdiv : 0 ≤ (8 * Real.pi) / (X : ℝ) := by positivity
    have hk : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    have hsquare : 0 ≤ (((overlap - 5 : ℕ) : ℝ) ^ 2) := by positivity
    exact mul_nonneg hdiv (mul_nonneg hk hsquare)
  refine norm_intervalIntegral_zero_one_le (hC := hCnonneg) ?_
  intro u hu0 hu1
  exact norm_kernel_mul_canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_adjacent_le
    hX hu0 hu1

private lemma norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral_adjacent_le
    {X overlap K : ℕ} (hX : X0 ≤ X) :
    ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X overlap (K + 2) K‖
      ≤
    (((8 * Real.pi) / (X : ℝ))
      * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((overlap - 5 : ℕ) : ℝ) ^ 2))) / 6 := by
  rw [canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral_eq_integral_termwiseUIntegral]
  have hXnat : 0 < X := lt_of_lt_of_le (by decide : 0 < X0) hX
  have hCnonneg :
      0 ≤
        ((8 * Real.pi) / (X : ℝ))
          * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * (((overlap - 5 : ℕ) : ℝ) ^ 2)) := by
    have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXnat
    have hdiv : 0 ≤ (8 * Real.pi) / (X : ℝ) := by positivity
    have hk : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    have hsquare : 0 ≤ (((overlap - 5 : ℕ) : ℝ) ^ 2) := by positivity
    exact mul_nonneg hdiv (mul_nonneg hk hsquare)
  refine
    norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six
      (hC := hCnonneg) ?_
  intro β hmem
  exact norm_canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral_adjacent_le
    hX β

theorem canonicalQ1TwoSidedShiftBoundaryCommonUIntegral_eq_positive_and_negative
    (X N M : ℕ) (β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
        X N M β
      =
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β
      + canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β := by
  unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
  calc
    ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
              X N M u β
      =
    ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * (canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β
            + canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun u _ => by
            rw [canonicalQ1TwoSidedShiftCommonSquareDiff_eq_positive_sub_positive_add_negative_sub_negative]
    _ =
    ∫ u in (0 : ℝ)..(1 : ℝ),
        ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β)
        +
        ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun u _ => by ring
    _ =
    (∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β)
      +
    ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β := by
          have hposDiff :
              IntervalIntegrable
                (fun u : ℝ =>
                  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β)
                MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
            let hbase :=
              (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand X N N β).sub
                (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand X N M β)
            refine hbase.congr ?_
            intro u hu
            exact (kernel_mul_canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_eq_sub X N M u β).symm
          have hnegDiff :
              IntervalIntegrable
                (fun u : ℝ =>
                  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β)
                MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
            let hbase :=
              (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand X N N β).sub
                (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand X N M β)
            refine hbase.congr ?_
            intro u hu
            exact (kernel_mul_canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff_eq_sub X N M u β).symm
          simpa using intervalIntegral.integral_add hposDiff hnegDiff
    _ =
    ((∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveOverlap X N N u β)
      -
      ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonPositiveOverlap X N M u β)
      +
    ((∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeOverlap X N N u β)
      -
      ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonNegativeOverlap X N M u β) := by
          congr 1
          · have hrewrite :
                (∫ u in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff X N N M u β)
                  =
                ∫ u in (0 : ℝ)..(1 : ℝ),
                  ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonPositiveOverlap X N N u β)
                  -
                  ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonPositiveOverlap X N M u β) := by
              refine intervalIntegral.integral_congr_ae ?_
              exact Filter.Eventually.of_forall <| fun u _ => by
                exact kernel_mul_canonicalQ1TwoSidedShiftCommonPositiveTermwiseDiff_eq_sub X N M u β
            rw [hrewrite, intervalIntegral.integral_sub
              (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand X N N β)
              (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegrand X N M β)]
          · have hrewrite :
                (∫ u in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff X N N M u β)
                  =
                ∫ u in (0 : ℝ)..(1 : ℝ),
                  ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonNegativeOverlap X N N u β)
                  -
                  ((Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                    * canonicalQ1TwoSidedShiftCommonNegativeOverlap X N M u β) := by
              refine intervalIntegral.integral_congr_ae ?_
              exact Filter.Eventually.of_forall <| fun u _ => by
                exact kernel_mul_canonicalQ1TwoSidedShiftCommonNegativeTermwiseDiff_eq_sub X N M u β
            rw [hrewrite, intervalIntegral.integral_sub
              (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand X N N β)
              (intervalIntegrable_canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegrand X N M β)]
    _ = canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β
          + canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β := by
          rfl

theorem canonicalQ1TwoSidedShiftBoundaryCommonIntegral_eq_positive_and_negative
    (X N M : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M
      =
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N N M
      + canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral X N N M := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral
    canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral
  calc
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
            X N M β) β
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral X N N M β
            + canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral X N N M β) β := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun β _ => by
            by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
            · simp [hβ, canonicalQ1TwoSidedShiftBoundaryCommonUIntegral_eq_positive_and_negative]
            · simp [hβ]
    _ =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      ((Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N N β) β)
        -
        (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N M β) β))
      +
      ((Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N N β) β)
        -
        (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N M β) β)) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun β _ => by
            by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
            · simp [hβ, canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseUIntegral,
                canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseUIntegral,
                sub_eq_add_neg, add_assoc]
            · simp [hβ]
    _ =
    ((∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N N β) β)
      -
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral X N M β) β))
      +
    ((∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N N β) β)
      -
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral X N M β) β)) := by
          rw [intervalIntegral.integral_add
            ((intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
              X N N).sub
              (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
                X N M))
            ((intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
              X N N).sub
              (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
                X N M))]
          congr 1
          · rw [intervalIntegral.integral_sub
              (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
                X N N)
              (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonPositiveUIntegral
                X N M)]
          · rw [intervalIntegral.integral_sub
              (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
                X N N)
              (intervalIntegrable_betaSmall_indicator_inner_canonicalQ1TwoSidedShiftBoundaryCommonNegativeUIntegral
                X N M)]
    _ = canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N N M
          + canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral X N N M := by
          rfl

/--
Abstract `β`-transport surface for the common branch.

The square-level decomposition is now proved. The next live proof step is to transport that
decomposition through the `u`- and `β`-integrals to obtain this pointwise common-integral upper.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport : Prop where
  bound :
    ∀ X N M,
      ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2
        ≤
      2 * ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N N M‖ ^ 2
        +
      2 * ‖canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral X N N M‖ ^ 2

structure CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport : Prop where
  bound :
    ∀ X,
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X
        ≤
      2 * canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy X
        +
      2 * canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowEnergy X

private theorem orderedPairGateSum_le
    (s : Finset ℕ) (F G Hf : ℕ → ℕ → ℝ)
    (hbound : ∀ N M, N ≤ M → F N M ≤ 2 * G N M + 2 * Hf N M) :
    (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then F N M else 0)
      ≤
    2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then G N M else 0)
      +
    2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then Hf N M else 0) := by
  have hmain :
      (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then F N M else 0)
        ≤
      ∑ N ∈ s, ∑ M ∈ s, if N ≤ M then (2 * G N M + 2 * Hf N M) else 0 := by
    refine Finset.sum_le_sum ?_
    intro N hN
    refine Finset.sum_le_sum ?_
    intro M hM
    by_cases hNM : N ≤ M
    · simp [hNM]
      exact hbound N M hNM
    · simp [hNM]
  calc
    (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then F N M else 0)
      ≤
    ∑ N ∈ s, ∑ M ∈ s, if N ≤ M then (2 * G N M + 2 * Hf N M) else 0 := hmain
    _ =
    ∑ N ∈ s, ((∑ M ∈ s, if N ≤ M then 2 * G N M else 0)
      + ∑ M ∈ s, if N ≤ M then 2 * Hf N M else 0) := by
        refine Finset.sum_congr rfl ?_
        intro N hN
        calc
          (∑ M ∈ s, if N ≤ M then 2 * G N M + 2 * Hf N M else 0)
            =
          ∑ M ∈ s, ((if N ≤ M then 2 * G N M else 0)
            + (if N ≤ M then 2 * Hf N M else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro M hM
              by_cases hNM : N ≤ M <;> simp [hNM]
          _ =
          (∑ M ∈ s, if N ≤ M then 2 * G N M else 0)
            + ∑ M ∈ s, if N ≤ M then 2 * Hf N M else 0 := by
              rw [Finset.sum_add_distrib]
    _ =
    (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then 2 * G N M else 0)
      + (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then 2 * Hf N M else 0) := by
        rw [Finset.sum_add_distrib]
    _ =
    (∑ N ∈ s, ∑ M ∈ s, 2 * (if N ≤ M then G N M else 0))
      + (∑ N ∈ s, ∑ M ∈ s, 2 * (if N ≤ M then Hf N M else 0)) := by
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro N hN
          refine Finset.sum_congr rfl ?_
          intro M hM
          by_cases hNM : N ≤ M <;> simp [hNM]
        · refine Finset.sum_congr rfl ?_
          intro N hN
          refine Finset.sum_congr rfl ?_
          intro M hM
          by_cases hNM : N ≤ M <;> simp [hNM]
    _ =
    2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then G N M else 0)
      +
    2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then Hf N M else 0) := by
        have hG :
            (∑ N ∈ s, ∑ M ∈ s, 2 * (if N ≤ M then G N M else 0))
              =
            2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then G N M else 0) := by
          calc
            (∑ N ∈ s, ∑ M ∈ s, 2 * (if N ≤ M then G N M else 0))
                =
              ∑ N ∈ s, (2 * (∑ M ∈ s, if N ≤ M then G N M else 0)) := by
                refine Finset.sum_congr rfl ?_
                intro N hN
                rw [Finset.mul_sum]
            _ = 2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then G N M else 0) := by
                rw [← Finset.mul_sum]
        have hH :
            (∑ N ∈ s, ∑ M ∈ s, 2 * (if N ≤ M then Hf N M else 0))
              =
            2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then Hf N M else 0) := by
          calc
            (∑ N ∈ s, ∑ M ∈ s, 2 * (if N ≤ M then Hf N M else 0))
                =
              ∑ N ∈ s, (2 * (∑ M ∈ s, if N ≤ M then Hf N M else 0)) := by
                refine Finset.sum_congr rfl ?_
                intro N hN
                rw [Finset.mul_sum]
            _ = 2 * (∑ N ∈ s, ∑ M ∈ s, if N ≤ M then Hf N M else 0) := by
                rw [← Finset.mul_sum]
        rw [hG, hH]

/--
Finite-sum transport from the pointwise `β`-integrated common bound to the ordered-pair energy
bound.

The common, positive, and negative ordered-pair energies all use the same ordered-pair gate
`N ≤ M`, so the pointwise transport theorem can be summed directly with `Finset.sum_le_sum`.
-/
theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport_of_integral
    (htransport : CanonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport := by
  refine ⟨?_⟩
  intro X
  simpa [canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy,
    canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy,
    canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowEnergy]
    using
      orderedPairGateSum_le (EvenIn X H)
        (fun N M => ‖canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M‖ ^ 2)
        (fun N M => ‖canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N N M‖ ^ 2)
        (fun N M => ‖canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral X N N M‖ ^ 2)
        (fun N M hNM => htransport.bound X N M)

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergyTarget_of_transport
    (htransport : CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport)
    (X : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X
      ≤
    2 * canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy X
      +
    2 * canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowEnergy X :=
  htransport.bound X

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_positive_and_negative
    {C3pos C3neg : ℝ}
    (htransport : CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport)
    (hpos : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowTarget C3pos)
    (hneg : CanonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowTarget C3neg) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget (2 * (C3pos + C3neg)) where
  C3_nonneg := by
    nlinarith [hpos.C3_nonneg, hneg.C3_nonneg]
  bound := by
    intro X hX
    have hmain :=
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergyTarget_of_transport
        htransport X
    have hpos' := hpos.bound hX
    have hneg' := hneg.bound hX
    calc
      canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X
        ≤
      2 * canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowEnergy X
        + 2 * canonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowEnergy X := hmain
      _ ≤
      2 * (2 * (((EvenIn X H).card : ℝ)
        * (C3pos / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))))
        +
      2 * (2 * (((EvenIn X H).card : ℝ)
        * (C3neg / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))) := by
          nlinarith [hpos', hneg']
      _ =
      2 * (((EvenIn X H).card : ℝ)
        * ((2 * (C3pos + C3neg))
            / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
          ring

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_integral_transport_and_positive_and_negative
    {C3pos C3neg : ℝ}
    (htransport : CanonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport)
    (hpos : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowTarget C3pos)
    (hneg : CanonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowTarget C3neg) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget (2 * (C3pos + C3neg)) :=
  canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_positive_and_negative
    (canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport_of_integral htransport)
    hpos hneg

/--
Exact gap/decomposition surface for the common `β`-integrated contribution.

The proven raw square decomposition above shows the right overlap profiles. The next live theorem is
to transport that structure through the `u`- and `β`-integrals without reintroducing cancellation
claims.
-/
structure CanonicalQ1TwoSidedShiftBoundaryCommonIntegralGapDecomposition : Prop where
  eq_add :
    ∀ X N M,
      canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N M
        =
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N N
        - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N M
        + canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X N N
        - canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X N M

theorem canonicalQ1TwoSidedShiftBoundaryCommonIntegralGapDecomposition_explicit :
    CanonicalQ1TwoSidedShiftBoundaryCommonIntegralGapDecomposition := by
  refine ⟨?_⟩
  intro X N M
  rw [canonicalQ1TwoSidedShiftBoundaryCommonIntegral_eq_positive_and_negative]
  simp [canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral,
    canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral,
    sub_eq_add_neg, add_assoc]

theorem canonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport_of_gapDecomposition
    (hdecomp : CanonicalQ1TwoSidedShiftBoundaryCommonIntegralGapDecomposition) :
    CanonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport := by
  refine ⟨?_⟩
  intro X N M
  rw [hdecomp.eq_add X N M]
  set A : ℂ := canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral X N N M
  set B : ℂ := canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral X N N M
  have hrewrite :
      canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N N
        - canonicalQ1TwoSidedShiftBoundaryCommonPositiveIntegral X N M
        + canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X N N
        - canonicalQ1TwoSidedShiftBoundaryCommonNegativeIntegral X N M
        = A + B := by
    simp [A, B, canonicalQ1TwoSidedShiftBoundaryCommonPositiveTermwiseIntegral,
      canonicalQ1TwoSidedShiftBoundaryCommonNegativeTermwiseIntegral, sub_eq_add_neg, add_assoc]
  rw [hrewrite]
  have hnorm := norm_add_le A B
  have hsq1 :
      ‖A + B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 := by
    have habs :
        |‖A + B‖| ≤ |‖A‖ + ‖B‖| := by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
      simpa using hnorm
    exact sq_le_sq.mpr habs
  have hsq2 : (‖A‖ + ‖B‖) ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    have hnonneg : 0 ≤ (‖A‖ - ‖B‖) ^ 2 := sq_nonneg _
    nlinarith
  simpa [A, B] using le_trans hsq1 hsq2

/--
The exact common-branch decomposition proved above already yields the pointwise common-integral
transport inequality.

This is the concrete replacement for the earlier abstract “transport through the integrals” step:
the common branch is now reduced to the positive and negative ordered-pair targets with no further
decomposition work.
-/
theorem canonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport_explicit :
    CanonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport :=
  canonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport_of_gapDecomposition
    canonicalQ1TwoSidedShiftBoundaryCommonIntegralGapDecomposition_explicit

/--
Concrete ordered-pair transport for the common branch.

After this theorem, the live common-piece proof is no longer to control the full common integral
directly, but only the positive and negative ordered-pair energies.
-/
theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport_explicit :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport :=
  canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport_of_integral
    canonicalQ1TwoSidedShiftBoundaryCommonIntegralTransport_explicit

/--
Concrete reduction of the common ordered-pair target to the positive and negative ordered-pair
subtargets.
-/
theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_explicit_positive_and_negative
    {C3pos C3neg : ℝ}
    (hpos : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowTarget C3pos)
    (hneg : CanonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowTarget C3neg) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget (2 * (C3pos + C3neg)) :=
  canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_positive_and_negative
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseTransport_explicit hpos hneg

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_explicit_positiveFiber_and_negative
    {C3pos C3neg : ℝ}
    (hpos : CanonicalQ1TwoSidedShiftBoundaryCommonPositiveFiberPairwiseWindowTarget C3pos)
    (hneg : CanonicalQ1TwoSidedShiftBoundaryCommonNegativeOrderedPairwiseWindowTarget C3neg) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget (2 * (C3pos + C3neg)) :=
  canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_explicit_positive_and_negative
    (canonicalQ1TwoSidedShiftBoundaryCommonPositiveOrderedPairwiseWindowTarget_of_fiberPairwise hpos)
    hneg

/--
The common-square contribution is not termwise zero in general.

The shared overlap square carries the same geometric support, but the centered shift defect still
depends on `N + 2` versus `M + 2`. So the proof route for the common piece must be a direct
ordered-pair energy bound, not a strip-only argument and not naive pointwise cancellation.
-/
theorem canonicalQ1TwoSidedShiftCommonSquareDiff_obstruction_comment
    (X N M : ℕ) (u β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N M u β
      =
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        let phase :=
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
        let defectN : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((N + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        let defectM : ℂ :=
          (((2 * (Real.cos
                (2 * Real.pi
                  * ((u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                          - (((M + 2 : ℕ) : ℝ)))))
              - 1) : ℝ) : ℂ))
        phase * (defectN - defectM) := by
  exact canonicalQ1TwoSidedShiftCommonSquareDiff_eq_phase_mul_real_cos_defect_sub X N M u β

theorem canonicalQ1TwoSidedShiftCommonSquareDiff_self
    (X N : ℕ) (u β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
        X N N u β = 0 := by
  unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff
  simp

theorem canonicalQ1TwoSidedShiftBoundaryCommonUIntegral_self
    (X N : ℕ) (β : ℝ) :
    Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
        X N N β = 0 := by
  unfold Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
  have hfun :
      (fun u : ℝ =>
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC
          (β : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC))
          * Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftCommonSquareDiff X N N u β)
        =
      fun _ : ℝ => (0 : ℂ) := by
        funext u
        rw [canonicalQ1TwoSidedShiftCommonSquareDiff_self]
        simp
  rw [hfun]
  simp

theorem canonicalQ1TwoSidedShiftBoundaryCommonIntegral_self
    (X N : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonIntegral X N N = 0 := by
  have hpoint :
      ∀ β : ℝ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ =>
              (Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
                X N N β : ℂ)) β
          = 0 := by
    intro β
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · rw [Set.indicator_of_mem hβ]
      rw [canonicalQ1TwoSidedShiftBoundaryCommonUIntegral_self]
    · simp [hβ]
  unfold canonicalQ1TwoSidedShiftBoundaryCommonIntegral
  have hfun :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            (Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets.canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
              X N N β : ℂ)) β)
        =
      fun _ : ℝ => (0 : ℂ) := by
        funext β
        exact hpoint β
  rw [hfun]
  simp

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy_eq_zero_of_cancellation
    (hCancel : CanonicalQ1TwoSidedShiftBoundaryCommonCancellation)
    (X : ℕ) :
    canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy X = 0 := by
  unfold canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy
  refine Finset.sum_eq_zero ?_
  intro N hN
  refine Finset.sum_eq_zero ?_
  intro M hM
  by_cases hNM : N ≤ M
  · rw [if_pos hNM, hCancel.vanish hNM]
    simp
  · rw [if_neg hNM]

theorem canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget_of_cancellation
    (hCancel : CanonicalQ1TwoSidedShiftBoundaryCommonCancellation) :
    CanonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowTarget 0 where
  C3_nonneg := by positivity
  bound := by
    intro X hX
    rw [canonicalQ1TwoSidedShiftBoundaryCommonOrderedPairwiseWindowEnergy_eq_zero_of_cancellation
      hCancel X]
    have hright :
        2 * (((EvenIn X H).card : ℝ)
          * (0 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))
          =
        0 := by
      rw [zero_div, mul_zero, mul_zero]
    have hnonneg :
        0 ≤
          2 * (((EvenIn X H).card : ℝ)
            * (0 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))) := by
      rw [hright]
    exact hnonneg

end
