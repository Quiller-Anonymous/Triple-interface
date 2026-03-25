import Goldbach.BankPieces.Cert.RawScaleSmallBetaQCollapse
import Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
import Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted
import Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation
import Goldbach.BankPieces.Cert.ProjectedConstGapBridge
import Goldbach.Cert.MajorArcExponentialPrelude
import Goldbach.Cert.MajorArcModules.ArcSetBounds
import Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze

open scoped BigOperators Interval

open Complex MeasureTheory
open Goldbach
open Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaOscillation
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactor
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQFactorC
open Goldbach.BankPieces.Cert.RawScaleSmallBetaQCollapse

noncomputable section

private abbrev Q0 : ℕ := Goldbach.AO_OffDiag.TailBlock.Q0
private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma weight_mass_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) :
    0 < Goldbach.AO_WeightMass.weight_mass X := by
  have hx : (1 : ℝ) < (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) this
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hx
  have hband : 0 < (2 * (Goldbach.BG_Bank.H : ℝ) + 1) := by positivity
  have hwScale_pos : 0 < Goldbach.BG_Bank.wScale X := by
    unfold Goldbach.BG_Bank.wScale
    exact one_div_pos.mpr (mul_pos hlog hband)
  simpa [Goldbach.AO_WeightMass.weight_mass] using sq_pos_of_pos hwScale_pos

private lemma measurableSet_centeredUnitSet (Δ : ℝ) :
    MeasurableSet (centeredUnitSet Δ) := by
  simpa [centeredUnitSet] using
    (measurableSet_le (Continuous.measurable continuous_abs) measurable_const)

private lemma centeredUnitSet_one_eq_Icc :
    centeredUnitSet (1 : ℝ) = Set.Icc (-1 : ℝ) (1 : ℝ) := by
  ext u
  simp [centeredUnitSet, abs_le]

private lemma volume_centeredUnitSet_one_toReal :
    (volume (centeredUnitSet (1 : ℝ))).toReal = 2 := by
  rw [centeredUnitSet_one_eq_Icc]
  norm_num [Real.volume_Icc]

private lemma betaSmallSet_subset_Ioc :
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
      ⊆ Set.Ioc Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  intro β hβ
  have hβ' : -Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius ≤ β
      ∧ β ≤ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius := by
    simpa [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet, Set.mem_Icc] using hβ
  have hrad_lt_half :
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius < ((2 : ℝ)⁻¹) := by
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have hlt : (2 : ℝ) < (4 * Real.pi : ℝ) := by
      nlinarith [Real.pi_gt_three]
    have :
        (1 : ℝ) / (4 * Real.pi) < (1 : ℝ) / (2 : ℝ) :=
      one_div_lt_one_div_of_lt h2 hlt
    simpa [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, one_div] using this
  have hleft : Goldbach.Cert.MajorArcModules.BetaInterval.aβ < β := by
    have : (-( (2 : ℝ)⁻¹) : ℝ)
        < -Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius := by
      have := neg_lt_neg hrad_lt_half
      simpa [Goldbach.Cert.MajorArcModules.BetaInterval.aβ] using this
    exact lt_of_lt_of_le (lt_of_lt_of_le this hβ'.1) le_rfl
  have hright : β ≤ Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
    have :
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius ≤ ((2 : ℝ)⁻¹) :=
      le_of_lt hrad_lt_half
    exact le_trans hβ'.2 (by simpa [Goldbach.Cert.MajorArcModules.BetaInterval.bβ] using this)
  exact ⟨hleft, hright⟩

private lemma volume_betaSmallSet_toReal_le_one_div_six :
    (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal
      ≤ (1 : ℝ) / 6 := by
  have htoReal :
      (volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet).toReal
        = (1 : ℝ) / (2 * Real.pi) := by
    have hvol :
        volume Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
          =
        ENNReal.ofReal
          (2 * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius) := by
      simp [Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet, Real.volume_Icc,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallRadius, sub_eq_add_neg, two_mul,
        add_assoc, add_left_comm, add_comm, mul_assoc]
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

/--
The rescaled archimedean shell with the surviving `u/(qX)` oscillation frozen away.

This is the natural next comparison target after the exact local factorization: it removes the tiny
oscillatory phase without yet claiming any collapse in `q`.
-/
noncomputable def smallBetaFrozenRescaledArchShell (N : ℕ) (_u β : ℝ) : ℂ :=
  smallBetaCenteredArchShell N 0 β

/-- The rescaled shell-difference integrand after freezing the tiny `u/(qX)` oscillation. -/
noncomputable def smallBetaRescaledShellGap (X N q : ℕ) (u β : ℝ) : ℂ :=
  smallBetaRescaledArchShell X N q u β - smallBetaFrozenRescaledArchShell N u β

/-- The corresponding rescaled extracted archimedean gap integral. -/
noncomputable def smallBetaRescaledGapExtractedArc (X N q : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u : ℝ,
        (centeredUnitSet Δ).indicator
          (fun u => smallBetaRescaledShellGap X N q u β) u) β

private lemma smallBetaRescaledShellGap_eq_sub
    (X N q : ℕ) (u β : ℝ) :
    smallBetaRescaledShellGap X N q u β
      = smallBetaRescaledArchShell X N q u β - smallBetaFrozenRescaledArchShell N u β := by
  rfl

private lemma centeredUnitSet_indicator_smallBetaRescaledShellGap_eq_sub
    (X N q : ℕ) (Δ u β : ℝ) :
    (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledShellGap X N q u β) u
      =
    (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u
      -
    (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u := by
  by_cases hu : u ∈ centeredUnitSet Δ
  · simp [hu, smallBetaRescaledShellGap_eq_sub]
  · simp [hu]

private lemma integral_indicator_centeredUnitSet_smallBetaRescaledShellGap_eq_sub
    {X N q : ℕ} {Δ β : ℝ}
    (hcent :
      Integrable (fun u : ℝ =>
        (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u))
    (hfroz :
      Integrable (fun u : ℝ =>
        (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u)) :
    (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledShellGap X N q u β) u)
      =
    (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u)
      -
    (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u) := by
  rw [show
      (fun u : ℝ => (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledShellGap X N q u β) u)
        =
      (fun u : ℝ =>
        (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u
          -
        (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u) by
      funext u
      exact centeredUnitSet_indicator_smallBetaRescaledShellGap_eq_sub X N q Δ u β]
  simpa using MeasureTheory.integral_sub hcent hfroz

private lemma betaSmall_indicator_innerRescaledGap_eq_sub
    (X N q : ℕ) (Δ β : ℝ)
    (hinner :
      (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledShellGap X N q u β) u)
        =
      (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u)
        -
      (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u)) :
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledShellGap X N q u β) u) β
      =
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) β
      -
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u) β := by
  by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
  · simp [hβ, hinner]
  · simp [hβ]

private theorem norm_integral_indicator_centeredUnitSet_one_le
    {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ u, u ∈ centeredUnitSet (1 : ℝ) → ‖f u‖ ≤ C) :
    ‖∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator f u‖ ≤ 2 * C := by
  let s : Set ℝ := centeredUnitSet (1 : ℝ)
  have hs : MeasurableSet s := measurableSet_centeredUnitSet (1 : ℝ)
  haveI : IsFiniteMeasure (volume.restrict s) := by
    refine ⟨?_⟩
    have hfin : volume s < ⊤ := by
      simp [s, centeredUnitSet_one_eq_Icc]
    simpa [s] using hfin
  have hAeImp : ∀ᵐ u ∂volume, u ∈ s → ‖f u‖ ≤ C := by
    refine Filter.Eventually.of_forall ?_
    intro u hu
    exact hf u hu
  have hAe : ∀ᵐ u ∂volume.restrict s, ‖f u‖ ≤ C :=
    (MeasureTheory.ae_restrict_iff' (μ := volume) (s := s) hs).2 hAeImp
  have hbound :
      ‖∫ u, f u ∂(volume.restrict s)‖ ≤ C * (volume.restrict s).real Set.univ :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := volume.restrict s) (f := f) (C := C) hAe
  have hind :
      (∫ u : ℝ, s.indicator f u) = ∫ u, f u ∂(volume.restrict s) := by
    simpa [s] using (MeasureTheory.integral_indicator (μ := volume) (f := f) hs)
  have hreal :
      (volume.restrict s).real Set.univ = (volume s).toReal := by
    simp [Measure.real, s, hs, Measure.restrict_apply]
  calc
    ‖∫ u : ℝ, s.indicator f u‖ = ‖∫ u, f u ∂(volume.restrict s)‖ := by rw [hind]
    _ ≤ C * (volume.restrict s).real Set.univ := hbound
    _ = C * (volume s).toReal := by rw [hreal]
    _ = C * 2 := by simp [s, volume_centeredUnitSet_one_toReal]
    _ = 2 * C := by ring

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

private lemma norm_gExp_sum_Ico_le_card (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖
      ≤ (Finset.Ico 4 ((N - 2) + 1)).card := by
  calc
    ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1), Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖
      ≤ ∑ n ∈ Finset.Ico 4 ((N - 2) + 1), ‖Goldbach.Cert.MajorArcStep2ExpSums.gExp x n‖ := by
          exact norm_sum_le _ _
    _ = (Finset.Ico 4 ((N - 2) + 1)).card := by
          simp [Goldbach.Cert.MajorArcStep2ExpSums.norm_gExp]

private lemma norm_smallBetaCenteredArchShell_le
    (N : ℕ) (θ β : ℝ) :
    ‖smallBetaCenteredArchShell N θ β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
  have hK :
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap (x := (β : UC))
  have hF :
      ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : UC) : ℂ)‖ = 1 := by
    simpa using
      (Goldbach.Cert.MajorArcExponential.norm_fourier
        (T := (1 : ℝ)) (n := (-(N : ℤ))) (x := (θ : UC)))
  let cardN : ℝ := (Finset.Ico 4 ((N - 2) + 1)).card
  have hVplus :
      ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n‖
        ≤ cardN :=
    norm_gExp_sum_Ico_le_card (x := θ + β) N
  have hVminus :
      ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n‖
        ≤ cardN :=
    norm_gExp_sum_Ico_le_card (x := θ - β) N
  have hcard_nonneg : 0 ≤ cardN := by
    dsimp [cardN]
    positivity
  have hcap_nonneg : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
  calc
    ‖smallBetaCenteredArchShell N θ β‖
      =
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
      * ‖(fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : UC) : ℂ)‖
      * ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n)‖ := by
            unfold smallBetaCenteredArchShell
            rw [norm_mul, norm_mul]
    _ =
    ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
      * ‖(∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n)‖
      * ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n‖ := by
            rw [hF, norm_mul]
            ring
    _ ≤ ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ * (cardN * cardN) := by
            have hVV : ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n‖
                * ‖∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                    Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n‖ ≤ cardN * cardN := by
              exact mul_le_mul hVplus hVminus (norm_nonneg _) hcard_nonneg
            have hkn : 0 ≤ ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖ :=
              norm_nonneg _
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hVV hkn
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap * (cardN * cardN) := by
            gcongr
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap * cardN ^ 2 := by
            ring
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
            rfl

private lemma norm_smallBetaRescaledArchShell_le
    (X N q : ℕ) (u β : ℝ) :
    ‖smallBetaRescaledArchShell X N q u β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
  unfold smallBetaRescaledArchShell
  exact norm_smallBetaCenteredArchShell_le
    N (u / ((q : ℝ) * (X : ℝ))) β

private lemma norm_smallBetaFrozenRescaledArchShell_le
    (N : ℕ) (u β : ℝ) :
    ‖smallBetaFrozenRescaledArchShell N u β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
  unfold smallBetaFrozenRescaledArchShell
  simpa using norm_smallBetaCenteredArchShell_le N 0 β

private lemma norm_smallBetaCenteredArchShell_shift_sub_zero_le
    (N : ℕ) (θ β : ℝ)
    (hθ : |2 * Real.pi * θ| ≤ 1) :
    ‖smallBetaCenteredArchShell N θ β - smallBetaCenteredArchShell N 0 β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
              * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |θ|))) := by
  let K : ℂ := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
  let φ : ℂ := (fourier (T := (1 : ℝ)) (-(N : ℤ)) (θ : UC) : ℂ)
  let Vpθ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ + β) n
  let Vmθ : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp (θ - β) n
  let Vp0 : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp β n
  let Vm0 : ℂ := ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
    Goldbach.Cert.MajorArcStep2ExpSums.gExp (-β) n
  let cardN : ℝ := (Finset.Ico 4 ((N - 2) + 1)).card
  let L : ℝ := 4 * Real.pi * |θ|
  have hK :
      ‖K‖ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap := by
    dsimp [K]
    exact Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap (x := (β : UC))
  have hVpθ : ‖Vpθ‖ ≤ cardN := by
    dsimp [Vpθ, cardN]
    exact norm_gExp_sum_Ico_le_card (x := θ + β) N
  have hVmθ : ‖Vmθ‖ ≤ cardN := by
    dsimp [Vmθ, cardN]
    exact norm_gExp_sum_Ico_le_card (x := θ - β) N
  have hVp0 : ‖Vp0‖ ≤ cardN := by
    dsimp [Vp0, cardN]
    exact norm_gExp_sum_Ico_le_card (x := β) N
  have hφsub : ‖φ - 1‖ ≤ (N : ℝ) * L := by
    dsimp [φ, L]
    simpa using norm_fourier_neg_nat_sub_one_le N θ hθ
  have hVpDiff : ‖Vpθ - Vp0‖ ≤ cardN * ((N - 2 : ℕ) : ℝ) * L := by
    dsimp [Vpθ, Vp0, cardN, L]
    simpa [add_comm, add_left_comm, add_assoc]
      using norm_gExp_sum_Ico_add_shift_sub_le β θ N hθ
  have hVmDiff : ‖Vmθ - Vm0‖ ≤ cardN * ((N - 2 : ℕ) : ℝ) * L := by
    dsimp [Vmθ, Vm0, cardN, L]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using norm_gExp_sum_Ico_add_shift_sub_le (-β) θ N hθ
  have hsplit :
      φ * Vpθ * Vmθ - Vp0 * Vm0
        = (((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ + Vp0 * (Vmθ - Vm0) := by
    ring
  have hmid :
      ‖φ * Vpθ * Vmθ - Vp0 * Vm0‖
        ≤ ((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN
            + cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L) := by
    rw [hsplit]
    calc
      ‖((((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ) + Vp0 * (Vmθ - Vm0)‖
        ≤ ‖(((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ‖ + ‖Vp0 * (Vmθ - Vm0)‖ := by
            simpa using
              norm_add_le ((((φ - 1) * Vpθ) + (Vpθ - Vp0)) * Vmθ) (Vp0 * (Vmθ - Vm0))
      _ ≤ (‖((φ - 1) * Vpθ) + (Vpθ - Vp0)‖ * ‖Vmθ‖) + (‖Vp0‖ * ‖Vmθ - Vm0‖) := by
            gcongr <;> simp [norm_mul]
      _ ≤ ((‖(φ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖) * ‖Vmθ‖) + (‖Vp0‖ * ‖Vmθ - Vm0‖) := by
            gcongr
            simpa using norm_add_le ((φ - 1) * Vpθ) (Vpθ - Vp0)
      _ ≤ (((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN)
            + cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L) := by
            have hA :
                ‖(φ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖
                  ≤ (((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L := by
              have hmul :
                  ‖(φ - 1) * Vpθ‖ ≤ ((N : ℝ) * L) * cardN := by
                calc
                  ‖(φ - 1) * Vpθ‖ = ‖φ - 1‖ * ‖Vpθ‖ := by simp [norm_mul]
                  _ ≤ ((N : ℝ) * L) * cardN := by gcongr
              linarith
            have hB :
                (‖(φ - 1) * Vpθ‖ + ‖Vpθ - Vp0‖) * ‖Vmθ‖
                  ≤ ((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN := by
              exact mul_le_mul hA hVmθ (norm_nonneg _) (by positivity)
            have hC :
                ‖Vp0‖ * ‖Vmθ - Vm0‖ ≤ cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L) := by
              exact mul_le_mul hVp0 hVmDiff (norm_nonneg _) (by positivity)
            linarith
  have hrew :
      smallBetaCenteredArchShell N θ β - smallBetaCenteredArchShell N 0 β
        = K * (φ * Vpθ * Vmθ - Vp0 * Vm0) := by
    unfold smallBetaCenteredArchShell
    dsimp [K, φ, Vpθ, Vmθ, Vp0, Vm0]
    simp
    ring
  calc
    ‖smallBetaCenteredArchShell N θ β - smallBetaCenteredArchShell N 0 β‖
      = ‖K * (φ * Vpθ * Vmθ - Vp0 * Vm0)‖ := by rw [hrew]
    _ = ‖K‖ * ‖φ * Vpθ * Vmθ - Vp0 * Vm0‖ := by simp [norm_mul]
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((((N : ℝ) * L) * cardN) + cardN * ((N - 2 : ℕ) : ℝ) * L) * cardN
              + cardN * (cardN * ((N - 2 : ℕ) : ℝ) * L)) := by
            exact mul_le_mul hK hmid (norm_nonneg _) Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (cardN ^ 2 * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * L)) := by
            ring
    _ = Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
              * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |θ|))) := by
            rfl

private lemma norm_smallBetaRescaledShellGap_le_linear_theta
    (X N q : ℕ) (u β : ℝ)
    (hθ : |2 * Real.pi * (u / ((q : ℝ) * (X : ℝ)))| ≤ 1) :
    ‖smallBetaRescaledShellGap X N q u β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
              * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
                  * (4 * Real.pi * |u / ((q : ℝ) * (X : ℝ))|))) := by
  unfold smallBetaRescaledShellGap smallBetaRescaledArchShell smallBetaFrozenRescaledArchShell
  simpa using norm_smallBetaCenteredArchShell_shift_sub_zero_le
    N (u / ((q : ℝ) * (X : ℝ))) β hθ

private lemma abs_u_div_qX_le_inv_of_mem_centeredUnitSet_one
    {X q : ℕ} {u : ℝ}
    (hX : 1 ≤ X) (hq : 1 ≤ q)
    (hu : u ∈ centeredUnitSet (1 : ℝ)) :
    |u / ((q : ℝ) * (X : ℝ))| ≤ (((q : ℝ) * (X : ℝ))⁻¹) := by
  have hu' : |u| ≤ (1 : ℝ) := by
    simpa [centeredUnitSet] using hu
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hqXpos : (0 : ℝ) < (q : ℝ) * (X : ℝ) := by positivity
  calc
    |u / ((q : ℝ) * (X : ℝ))|
      = |u| / ((q : ℝ) * (X : ℝ)) := by
          rw [abs_div, abs_of_pos hqXpos]
    _ ≤ 1 / ((q : ℝ) * (X : ℝ)) := by
          exact div_le_div_of_nonneg_right hu' (le_of_lt hqXpos)
    _ = (((q : ℝ) * (X : ℝ))⁻¹) := by rw [one_div]

private lemma abs_two_pi_mul_u_div_qX_le_one_of_mem_centeredUnitSet_one
    {X q : ℕ} {u : ℝ}
    (hX : 4 ≤ X) (hq : 2 ≤ q)
    (hu : u ∈ centeredUnitSet (1 : ℝ)) :
    |2 * Real.pi * (u / ((q : ℝ) * (X : ℝ)))| ≤ 1 := by
  have hqX_inv :
      |u / ((q : ℝ) * (X : ℝ))| ≤ (((q : ℝ) * (X : ℝ))⁻¹) :=
    abs_u_div_qX_le_inv_of_mem_centeredUnitSet_one (show 1 ≤ X by omega)
      (show 1 ≤ q by omega) hu
  have htwo_pi_nonneg : 0 ≤ (2 * Real.pi : ℝ) := by positivity
  have hqX_ge_eight : (8 : ℝ) ≤ (q : ℝ) * (X : ℝ) := by
    have hq' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hX' : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    nlinarith
  have htwo_pi_le_qX : (2 * Real.pi : ℝ) ≤ (q : ℝ) * (X : ℝ) := by
    have htwo_pi_le_eight : (2 * Real.pi : ℝ) ≤ 8 := by
      nlinarith [le_of_lt Real.pi_lt_four]
    exact le_trans htwo_pi_le_eight hqX_ge_eight
  have hqXpos : (0 : ℝ) < (q : ℝ) * (X : ℝ) := by
    positivity
  calc
    |2 * Real.pi * (u / ((q : ℝ) * (X : ℝ)))|
      = (2 * Real.pi : ℝ) * |u / ((q : ℝ) * (X : ℝ))| := by
          rw [abs_mul, abs_of_nonneg htwo_pi_nonneg]
    _ ≤ (2 * Real.pi : ℝ) * (((q : ℝ) * (X : ℝ))⁻¹) := by
          exact mul_le_mul_of_nonneg_left hqX_inv htwo_pi_nonneg
    _ ≤ ((q : ℝ) * (X : ℝ)) * (((q : ℝ) * (X : ℝ))⁻¹) := by
          gcongr
    _ = 1 := by
          field_simp [show ((q : ℝ) * (X : ℝ)) ≠ 0 by positivity]

private lemma norm_smallBetaRescaledShellGap_le
    (X N q : ℕ) (u β : ℝ) :
    ‖smallBetaRescaledShellGap X N q u β‖
      ≤ 2 * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) := by
  unfold smallBetaRescaledShellGap
  calc
    ‖smallBetaRescaledArchShell X N q u β - smallBetaFrozenRescaledArchShell N u β‖
      ≤ ‖smallBetaRescaledArchShell X N q u β‖ + ‖smallBetaFrozenRescaledArchShell N u β‖ := by
          simpa using norm_sub_le _ _
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
        + Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
          gcongr
          · exact norm_smallBetaRescaledArchShell_le X N q u β
          · exact norm_smallBetaFrozenRescaledArchShell_le N u β
    _ = 2 * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) := by ring

theorem norm_smallBetaRescaledGapExtractedArc_le_one_third_of_pointwise_bound
    {X N q : ℕ} {Cshell : ℝ}
    (hCshell : 0 ≤ Cshell)
    (hpoint :
      ∀ β, β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet →
        ∀ u, u ∈ centeredUnitSet (1 : ℝ) →
          ‖smallBetaRescaledShellGap X N q u β‖ ≤ Cshell) :
    ‖smallBetaRescaledGapExtractedArc X N q (1 : ℝ)‖ ≤ Cshell / 3 := by
  unfold smallBetaRescaledGapExtractedArc
  refine le_trans
    (norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six
      (C := 2 * Cshell)
      (hC := by positivity)
      (hg := ?_))
    ?_
  · intro β hβ
    exact norm_integral_indicator_centeredUnitSet_one_le
      (C := Cshell) hCshell (hf := fun u hu => hpoint β hβ u hu)
  · ring_nf
    nlinarith

theorem norm_smallBetaRescaledGapExtractedArc_le_linear_q_inv
    {X N q : ℕ}
    (hX : 4 ≤ X) (hq : 2 ≤ q) :
    ‖smallBetaRescaledGapExtractedArc X N q (1 : ℝ)‖
      ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
                * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
                    * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))))) / 3 := by
  refine norm_smallBetaRescaledGapExtractedArc_le_one_third_of_pointwise_bound
    (X := X) (N := N) (q := q)
    (Cshell := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
      * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
          * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
              * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹)))))
    (hCshell := by
      have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
        Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
      positivity) ?_
  intro β hβ u hu
  refine le_trans
    (norm_smallBetaRescaledShellGap_le_linear_theta X N q u β
      (abs_two_pi_mul_u_div_qX_le_one_of_mem_centeredUnitSet_one hX hq hu))
    ?_
  have hqX_inv :
      |u / ((q : ℝ) * (X : ℝ))| ≤ (((q : ℝ) * (X : ℝ))⁻¹) :=
    abs_u_div_qX_le_inv_of_mem_centeredUnitSet_one (show 1 ≤ X by omega)
      (show 1 ≤ q by omega) hu
  have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
  have hcard_nonneg : 0 ≤ (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) := by positivity
  have hA_nonneg : 0 ≤ ((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) := by positivity
  have hfourpi_nonneg : 0 ≤ (4 * Real.pi : ℝ) := by positivity
  have hinner :
      (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |u / ((q : ℝ) * (X : ℝ))|))
        ≤
      (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))) := by
    have hmul :
        (4 * Real.pi * |u / ((q : ℝ) * (X : ℝ))|)
          ≤ (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹)) := by
      exact mul_le_mul_of_nonneg_left hqX_inv hfourpi_nonneg
    exact mul_le_mul_of_nonneg_left hmul hA_nonneg
  have hinner' :
      (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)
        * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * |u / ((q : ℝ) * (X : ℝ))|))
        ≤
      (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)
        * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ)) * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))) := by
    exact mul_le_mul_of_nonneg_left hinner hcard_nonneg
  exact mul_le_mul_of_nonneg_left hinner' hcap0

/--
The rescaled extracted archimedean shell with the local oscillation frozen away.

This is the exact integral-level comparison target for `AqCRescaled`.
-/
noncomputable def smallBetaFrozenArchExtractedArcRescaled (X N q : ℕ) (Δ : ℝ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u : ℝ,
        (centeredUnitSet Δ).indicator
          (fun u => smallBetaFrozenRescaledArchShell N u β) u) β

/--
The `q`-level frozen archimedean scalar family obtained by integrating the frozen rescaled shell.

This keeps the explicit `1 / (qX)` prefactor coming from the unit-arc rescaling, so it is honest
about any residual `q`-dependence after the oscillation has been removed.
-/
noncomputable def AqFrozenC (X N q : ℕ) (Δ : ℝ) : ℂ :=
  ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
    * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
    * smallBetaFrozenArchExtractedArcRescaled X N q Δ

/-- The common frozen archimedean integral before restoring the explicit `1/(qX)` prefactor. -/
noncomputable def frozenRawScalarC (N : ℕ) (Δ : ℝ) : ℂ :=
  smallBetaFrozenArchExtractedArcRescaled 1 N 1 Δ

/--
The one-dimensional `β`-only frozen archimedean scalar.

This is the honest scalar left after the unit-arc `u`-integration is carried out exactly at
`Δ = 1`.
-/
noncomputable def frozenBetaScalarC (N : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
      (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β

/--
The half-interval frozen archimedean integral matching the actual `q = 1` local textbook arc.

Unlike `smallBetaFrozenArchExtractedArcRescaled`, this integrates only over `u ∈ [0,1]`, which
is the correct rescaled surface exposed by the exact `q = 1` local rewrite.
-/
noncomputable def smallBetaFrozenArchExtractedArcRescaledHalfQ1 (N : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β) β

/--
The corrected frozen `q = 1` archimedean scalar family.

This keeps the same explicit `1/X` normalization as `AqLocalC X N 1`, but uses the half-interval
frozen integral that actually matches the principal textbook arc.
-/
noncomputable def AqFrozenHalfQ1C (X N : ℕ) : ℂ :=
  ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
    * ((((X : ℝ) : ℂ))⁻¹)
    * smallBetaFrozenArchExtractedArcRescaledHalfQ1 N

/--
The phase-corrected half-interval frozen shell for the principal arc.

This incorporates the exact deterministic phase `e(2u/X)` suggested by the midpoint correction
`N ↦ N + 2` on the range `n,m ∈ {4,…,N-2}`.
-/
noncomputable def smallBetaPhaseCorrectedFrozenRescaledArchShellQ1
    (X N : ℕ) (u β : ℝ) : ℂ :=
  Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
    * smallBetaFrozenRescaledArchShell N u β

/--
The corresponding phase-corrected half-interval frozen archimedean integral for `q = 1`.
-/
noncomputable def smallBetaPhaseCorrectedFrozenArchExtractedArcRescaledHalfQ1
    (X N : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β) β

/--
The phase-corrected principal-arc frozen scalar family.
-/
noncomputable def AqFrozenHalfQ1CorrectedC (X N : ℕ) : ℂ :=
  ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
    * ((((X : ℝ) : ℂ))⁻¹)
    * smallBetaPhaseCorrectedFrozenArchExtractedArcRescaledHalfQ1 X N

/-- The corresponding half-interval rescaled shell gap for the exceptional arc `q = 1`. -/
noncomputable def smallBetaRescaledGapExtractedArcHalfQ1 (X N : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledShellGap X N 1 u β) β

/--
The corresponding half-interval gap against the phase-corrected frozen principal-arc model.
-/
noncomputable def smallBetaRescaledGapExtractedArcHalfQ1Corrected (X N : ℕ) : ℂ :=
  ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ),
        (smallBetaRescaledArchShell X N 1 u β
          - smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β)) β

/--
The exact midpoint-corrected principal-arc shell defect after factoring out the kernel.

This is the honest `q = 1` cancellation object: the kernel remains outside, and the inner
oscillation is a double sum of exact phase differences.
-/
noncomputable def q1PhaseCorrectedDoubleSumShellDefect (X N : ℕ) (u β : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
    * (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
        ∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * (Goldbach.Cert.MajorArcExponential.e
                (β * ((n : ℝ) - (m : ℝ))
                  + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
              -
              Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))))

/--
The same `q = 1` shell defect rewritten on the shifted box `j,k ∈ range (N-5)` via
`n = 4 + j`, `m = 4 + k`.
-/
noncomputable def q1PhaseCorrectedDoubleSumShellDefectRange (X N : ℕ) (u β : ℝ) : ℂ :=
  (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
    * (∑ j ∈ Finset.range (N - 5),
        ∑ k ∈ Finset.range (N - 5),
          Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
            * (Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ))
                  + (u / (X : ℝ))
                      * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))))
              -
              Goldbach.Cert.MajorArcExponential.e
                (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))))

/--
Exact shell-level rewrite of the corrected principal-arc defect.

This is the first `q = 1` theorem on the honest cancellation surface: the kernel stays outside, and
the inner oscillatory defect is rewritten as a double sum of exact phase differences after the
midpoint correction.
-/
theorem smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_eq_kernel_mul_double_sum
    (X N : ℕ) (u β : ℝ) :
    smallBetaRescaledArchShell X N 1 u β
      - smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β
      = q1PhaseCorrectedDoubleSumShellDefect X N u β := by
  let K : ℂ := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
  have hinner :=
    rescaled_q1_innerFactor_sub_phase_corrected_frozen_eq_double_sum_phase_diff
      (X := X) (N := N) (u := u) (β := β)
  unfold smallBetaRescaledArchShell smallBetaCenteredArchShell
  unfold smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 smallBetaFrozenRescaledArchShell
  calc
    smallBetaCenteredArchShell N (u / (((1 : ℕ) : ℝ) * (X : ℝ))) β
      - Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ)) * smallBetaCenteredArchShell N 0 β
        =
    K
      * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
            (((u / (X : ℝ)) : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
          * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n)
              * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
                  Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m))
        -
        Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
          * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
                ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
              * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                    Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 + β) n)
                      * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
                          Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 - β) m)))) := by
          simp [smallBetaCenteredArchShell, K, one_mul, sub_eq_add_neg]
          ring_nf
    _ =
    K
      * (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          ∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
              * (Goldbach.Cert.MajorArcExponential.e
                  (β * ((n : ℝ) - (m : ℝ))
                    + (u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
                -
                Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ))))) := by
          simpa [K, one_mul] using congrArg (fun z : ℂ => K * z) hinner
    _ = q1PhaseCorrectedDoubleSumShellDefect X N u β := by
          simp [q1PhaseCorrectedDoubleSumShellDefect, K]

/-- Exact box-shift rewrite of the midpoint-corrected `q = 1` shell defect. -/
theorem q1PhaseCorrectedDoubleSumShellDefect_eq_range
    (X N : ℕ) (u β : ℝ) :
    q1PhaseCorrectedDoubleSumShellDefect X N u β
      = q1PhaseCorrectedDoubleSumShellDefectRange X N u β := by
  unfold q1PhaseCorrectedDoubleSumShellDefect q1PhaseCorrectedDoubleSumShellDefectRange
  refine congrArg (fun z : ℂ =>
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)) * z) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp

/--
Exact midpoint-reflection rewrite of the shifted `q = 1` box:
`(j,k) ↦ (N-6-k, N-6-j)`.

This is the finite-sum reindexing needed before forming the paired two-sided-shift expression.
-/
theorem q1PhaseCorrectedDoubleSumShellDefectRange_eq_reflect
    (X N : ℕ) (u β : ℝ) :
    q1PhaseCorrectedDoubleSumShellDefectRange X N u β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5),
            Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
              * (Goldbach.Cert.MajorArcExponential.e
                  (β
                    * ((((N - 5 - 1 - j + 4 : ℕ) : ℝ))
                        - (((N - 5 - 1 - k + 4 : ℕ) : ℝ)))
                    + (u / (X : ℝ))
                        * ((((N - 5 - 1 - j + 4 : ℕ) : ℝ)
                            + ((N - 5 - 1 - k + 4 : ℕ) : ℝ))
                          - (((N + 2 : ℕ) : ℝ))))
                -
                Goldbach.Cert.MajorArcExponential.e
                  (β
                    * ((((N - 5 - 1 - j + 4 : ℕ) : ℝ))
                        - (((N - 5 - 1 - k + 4 : ℕ) : ℝ)))))) := by
  unfold q1PhaseCorrectedDoubleSumShellDefectRange
  refine congrArg (fun z : ℂ =>
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)) * z) ?_
  rw [← Finset.sum_range_reflect
    (fun j =>
      ∑ k ∈ Finset.range (N - 5),
        Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
          * (Goldbach.Cert.MajorArcExponential.e
              (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ))
                + (u / (X : ℝ))
                    * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))))
            -
            Goldbach.Cert.MajorArcExponential.e
              (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))))
    (N - 5)]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [← Finset.sum_range_reflect
    (fun k =>
      Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
        * (Goldbach.Cert.MajorArcExponential.e
            (β * (((4 + (N - 5 - 1 - j) : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ))
              + (u / (X : ℝ))
                  * ((((4 + (N - 5 - 1 - j) : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ))
                    - (((N + 2 : ℕ) : ℝ))))
          -
          Goldbach.Cert.MajorArcExponential.e
            (β * (((4 + (N - 5 - 1 - j) : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))))
    (N - 5)]
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring_nf

/-- The original factorized midpoint-corrected `q = 1` range term. -/
noncomputable def q1FactorizedRangeTerm
    (X N : ℕ) (u β : ℝ) (j k : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
    * Goldbach.Cert.MajorArcExponential.e
        (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
    * (Goldbach.Cert.MajorArcExponential.e
        ((u / (X : ℝ))
          * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))))
      - 1)

/-- The midpoint-reflected factorized `q = 1` range term. -/
noncomputable def q1ReflectedFactorizedRangeTerm
    (X N : ℕ) (u β : ℝ) (j k : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
    * Goldbach.Cert.MajorArcExponential.e
        (β
          * ((((N - 5 - 1 - j + 4 : ℕ) : ℝ))
              - (((N - 5 - 1 - k + 4 : ℕ) : ℝ))))
    * (Goldbach.Cert.MajorArcExponential.e
        ((u / (X : ℝ))
          * ((((N - 5 - 1 - j + 4 : ℕ) : ℝ)
              + ((N - 5 - 1 - k + 4 : ℕ) : ℝ))
            - (((N + 2 : ℕ) : ℝ))))
      - 1)

/--
The midpoint-pair reflected factorized `q = 1` range term, with the reflection
`(n,m) ↦ (N+2-m, N+2-n)`.
-/
noncomputable def q1PairReflectedFactorizedRangeTerm
    (X N : ℕ) (u β : ℝ) (j k : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
    * Goldbach.Cert.MajorArcExponential.e
        (β
          * ((((N - 5 - 1 - k + 4 : ℕ) : ℝ))
              - (((N - 5 - 1 - j + 4 : ℕ) : ℝ))))
    * (Goldbach.Cert.MajorArcExponential.e
        ((u / (X : ℝ))
          * ((((N - 5 - 1 - k + 4 : ℕ) : ℝ)
              + ((N - 5 - 1 - j + 4 : ℕ) : ℝ))
            - (((N + 2 : ℕ) : ℝ))))
      - 1)

/-- The paired two-sided-shift `q = 1` range term after midpoint reflection. -/
noncomputable def q1TwoSidedShiftRangeTerm
    (X N : ℕ) (u β : ℝ) (j k : ℕ) : ℂ :=
  Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
    * Goldbach.Cert.MajorArcExponential.e
        (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
    * ((Goldbach.Cert.MajorArcExponential.e
          ((u / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))))
        +
        Goldbach.Cert.MajorArcExponential.e
          (-((u / (X : ℝ))
            * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))))
      - 2))

theorem norm_q1TwoSidedShiftRangeTerm_le_sq
    (X N : ℕ) (u β : ℝ) (j k : ℕ) :
    ‖q1TwoSidedShiftRangeTerm X N u β j k‖
      ≤
    (((u / (X : ℝ))
        * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))) * (2 * Real.pi)) ^ 2 := by
  unfold q1TwoSidedShiftRangeTerm
  rw [norm_mul, norm_mul]
  rw [Goldbach.Cert.MajorArcExponential.norm_e, Goldbach.Cert.MajorArcExponential.norm_e]
  simp only [one_mul]
  simpa [mul_comm, mul_left_comm, mul_assoc, sq]
    using Goldbach.Cert.MajorArcExponential.norm_e_add_e_neg_sub_two_le_sq
      ((u / (X : ℝ))
        * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))))

theorem q1TwoSidedShiftRangeTerm_eq_phase_mul_real_cos_defect
    (X N : ℕ) (u β : ℝ) (j k : ℕ) :
    q1TwoSidedShiftRangeTerm X N u β j k
      =
    Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
      * Goldbach.Cert.MajorArcExponential.e
          (β * (((4 + j : ℕ) : ℝ) - ((4 + k : ℕ) : ℝ)))
      * (((2 * (Real.cos
            (2 * Real.pi
              * ((u / (X : ℝ))
                  * ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)))))
            - 1) : ℝ) : ℂ)) := by
  unfold q1TwoSidedShiftRangeTerm
  rw [Goldbach.Cert.MajorArcExponential.e_add_e_neg_sub_two_eq_real]

private lemma abs_q1_centered_shift_le_N_of_mem_range
    {N j k : ℕ}
    (hj : j ∈ Finset.range (N - 5)) (hk : k ∈ Finset.range (N - 5)) :
    let t : ℝ := (((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))
    |t| ≤ (N : ℝ) := by
  dsimp
  have hjlt : j < N - 5 := Finset.mem_range.mp hj
  have hklt : k < N - 5 := Finset.mem_range.mp hk
  have hjle : 4 + j ≤ N - 2 := by
    omega
  have hkle : 4 + k ≤ N - 2 := by
    omega
  have hlow : (6 : ℝ) - N ≤ (((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ)) := by
    have h4j : (4 : ℝ) ≤ ((4 + j : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right 4 j)
    have h4k : (4 : ℝ) ≤ ((4 + k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right 4 k)
    have hsum_low : (8 : ℝ) ≤ ((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ) := by
      nlinarith
    have hNcast : (((N + 2 : ℕ) : ℝ)) = (N : ℝ) + 2 := by
      norm_num [Nat.cast_add]
    nlinarith [hsum_low, hNcast]
  have hupp : ((((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))) ≤ (N : ℝ) - 6 := by
    have h4j : ((4 + j : ℕ) : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast hjle
    have h4k : ((4 + k : ℕ) : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := by exact_mod_cast hkle
    have hsum_hi : ((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ) ≤ 2 * ((N - 2 : ℕ) : ℝ) := by
      nlinarith
    have hNge2 : 2 ≤ N := by omega
    have hNm2 : (((N - 2 : ℕ) : ℝ)) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub hNge2]
      norm_num
    have hNcast : (((N + 2 : ℕ) : ℝ)) = (N : ℝ) + 2 := by
      norm_num [Nat.cast_add]
    nlinarith [hsum_hi, hNm2, hNcast]
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  refine abs_le.2 ?_
  constructor
  · nlinarith
  · nlinarith

theorem norm_q1TwoSidedShiftRangeTerm_le_sq_N
    {N : ℕ} (X : ℕ) (u β : ℝ) {j k : ℕ}
    (hj : j ∈ Finset.range (N - 5)) (hk : k ∈ Finset.range (N - 5)) :
    ‖q1TwoSidedShiftRangeTerm X N u β j k‖
      ≤ (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2) := by
  have hmain := norm_q1TwoSidedShiftRangeTerm_le_sq (X := X) (N := N) (u := u) (β := β) (j := j) (k := k)
  have hXnn : 0 ≤ (X : ℝ) := by positivity
  let t : ℝ := (((4 + j : ℕ) : ℝ) + ((4 + k : ℕ) : ℝ)) - (((N + 2 : ℕ) : ℝ))
  have habs_shift :
      |t| ≤ (N : ℝ) := by
    dsimp [t]
    simpa using abs_q1_centered_shift_le_N_of_mem_range hj hk
  have hubound :
      |(u / (X : ℝ)) * t|
        ≤ (|u| * (N : ℝ)) / (X : ℝ) := by
    calc
      |(u / (X : ℝ)) * t| = |u / (X : ℝ)| * |t| := by
            rw [abs_mul]
      _ ≤ |u / (X : ℝ)| * (N : ℝ) := by
          gcongr
      _ = (|u| / (X : ℝ)) * (N : ℝ) := by
          rw [abs_div]
          simp [abs_of_nonneg hXnn]
      _ = (|u| * (N : ℝ)) / (X : ℝ) := by
          ring
  have hsq :
      (((u / (X : ℝ)) * t) * (2 * Real.pi)) ^ 2
        ≤ (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2) := by
    have htwoPi_nonneg : 0 ≤ 2 * Real.pi := by positivity
    let a : ℝ := ((u / (X : ℝ)) * t) * (2 * Real.pi)
    let B : ℝ := ((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ))
    have habs_mul :
        |a| ≤ B := by
      calc
        |a| = |(u / (X : ℝ)) * t| * |2 * Real.pi| := by
          dsimp [a]
          rw [abs_mul]
        _ ≤ ((|u| * (N : ℝ)) / (X : ℝ)) * |2 * Real.pi| := by
          gcongr
        _ = B := by
          dsimp [B]
          rw [abs_of_nonneg htwoPi_nonneg]
          ring_nf
    have hBnonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hsq' : a ^ 2 ≤ B ^ 2 := by
      have hsigned := abs_le.mp habs_mul
      nlinarith
    simpa [a, B] using hsq'
  exact le_trans hmain hsq


/-- The original `q = 1` range defect in factorized form. -/
theorem q1PhaseCorrectedDoubleSumShellDefectRange_eq_factorized
    (X N : ℕ) (u β : ℝ) :
    q1PhaseCorrectedDoubleSumShellDefectRange X N u β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5),
            q1FactorizedRangeTerm X N u β j k) := by
  unfold q1PhaseCorrectedDoubleSumShellDefectRange
  refine congrArg (fun z : ℂ =>
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)) * z) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [q1FactorizedRangeTerm]
  simpa using phase_diff_q1_eq_base_mul_shift_sub_one
    (X := X) (N := N) (n := 4 + j) (m := 4 + k) (u := u) (β := β)

/-- The midpoint-reflected `q = 1` range defect in factorized form. -/
theorem q1PhaseCorrectedDoubleSumShellDefectRange_eq_reflected_factorized
    (X N : ℕ) (u β : ℝ) :
    q1PhaseCorrectedDoubleSumShellDefectRange X N u β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5),
            q1ReflectedFactorizedRangeTerm X N u β j k) := by
  rw [q1PhaseCorrectedDoubleSumShellDefectRange_eq_reflect (X := X) (N := N) (u := u) (β := β)]
  refine congrArg (fun z : ℂ =>
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)) * z) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [q1ReflectedFactorizedRangeTerm]
  simpa using phase_diff_q1_eq_base_mul_shift_sub_one
    (X := X) (N := N)
    (n := N - 5 - 1 - j + 4) (m := N - 5 - 1 - k + 4) (u := u) (β := β)

/--
The summed unswapped reflected box equals the summed midpoint-pair reflected box.
-/
theorem sum_q1ReflectedFactorizedRangeTerm_eq_sum_pairReflected
    (X N : ℕ) (u β : ℝ) :
    (∑ j ∈ Finset.range (N - 5),
        ∑ k ∈ Finset.range (N - 5),
          q1ReflectedFactorizedRangeTerm X N u β j k)
      =
    (∑ j ∈ Finset.range (N - 5),
        ∑ k ∈ Finset.range (N - 5),
          q1PairReflectedFactorizedRangeTerm X N u β j k) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro k hk
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp [q1ReflectedFactorizedRangeTerm, q1PairReflectedFactorizedRangeTerm, add_comm, add_left_comm]

/-- Pointwise midpoint-pair collapse on the shifted `q = 1` box. -/
theorem q1FactorizedRangeTerm_add_pairReflected_eq_two_sided_shift_of_mem_range
    (X N : ℕ) (u β : ℝ) {j k : ℕ}
    (hj : j ∈ Finset.range (N - 5)) (hk : k ∈ Finset.range (N - 5)) :
    q1FactorizedRangeTerm X N u β j k
      + q1PairReflectedFactorizedRangeTerm X N u β j k
      =
    q1TwoSidedShiftRangeTerm X N u β j k := by
  have hjlt : j < N - 5 := Finset.mem_range.mp hj
  have hklt : k < N - 5 := Finset.mem_range.mp hk
  have hn : 4 + j ≤ N + 2 := by
    omega
  have hm : 4 + k ≤ N + 2 := by
    omega
  have hnk : N + 2 - (4 + k) = N - 5 - 1 - k + 4 := by
    omega
  have hnj : N + 2 - (4 + j) = N - 5 - 1 - j + 4 := by
    omega
  simpa [q1FactorizedRangeTerm, q1PairReflectedFactorizedRangeTerm, q1TwoSidedShiftRangeTerm,
    hnk, hnj] using
    factorized_q1_pair_eq_two_sided_shift
      (X := X) (N := N) (n := 4 + j) (m := 4 + k) (u := u) (β := β) hn hm

/-- Summing the original and midpoint-pair reflected range terms gives the two-sided shift sum. -/
theorem sum_q1FactorizedRangeTerm_add_sum_pairReflected_eq_sum_twoSided
    (X N : ℕ) (u β : ℝ) :
    (∑ j ∈ Finset.range (N - 5),
        ∑ k ∈ Finset.range (N - 5),
          q1FactorizedRangeTerm X N u β j k)
      +
    (∑ j ∈ Finset.range (N - 5),
        ∑ k ∈ Finset.range (N - 5),
          q1PairReflectedFactorizedRangeTerm X N u β j k)
      =
    (∑ j ∈ Finset.range (N - 5),
        ∑ k ∈ Finset.range (N - 5),
          q1TwoSidedShiftRangeTerm X N u β j k) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simpa using
    q1FactorizedRangeTerm_add_pairReflected_eq_two_sided_shift_of_mem_range
      (X := X) (N := N) (u := u) (β := β) hj hk

/--
Twice the corrected `q = 1` shifted-box defect collapses to the paired two-sided-shift sum.
-/
theorem two_mul_q1PhaseCorrectedDoubleSumShellDefectRange_eq_kernel_mul_twoSided
    (X N : ℕ) (u β : ℝ) :
    (2 : ℂ) * q1PhaseCorrectedDoubleSumShellDefectRange X N u β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5),
            q1TwoSidedShiftRangeTerm X N u β j k) := by
  let K := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
  let S :=
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        q1FactorizedRangeTerm X N u β j k
  let T :=
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        q1PairReflectedFactorizedRangeTerm X N u β j k
  let U :=
    ∑ j ∈ Finset.range (N - 5),
      ∑ k ∈ Finset.range (N - 5),
        q1TwoSidedShiftRangeTerm X N u β j k
  have hfac : q1PhaseCorrectedDoubleSumShellDefectRange X N u β = K * S := by
    simpa [K, S] using
      q1PhaseCorrectedDoubleSumShellDefectRange_eq_factorized (X := X) (N := N) (u := u) (β := β)
  have hpair : q1PhaseCorrectedDoubleSumShellDefectRange X N u β = K * T := by
    simpa [K, T, sum_q1ReflectedFactorizedRangeTerm_eq_sum_pairReflected (X := X) (N := N) (u := u) (β := β)] using
      q1PhaseCorrectedDoubleSumShellDefectRange_eq_reflected_factorized (X := X) (N := N) (u := u) (β := β)
  have hsum : S + T = U := by
    simpa [S, T, U] using
      sum_q1FactorizedRangeTerm_add_sum_pairReflected_eq_sum_twoSided (X := X) (N := N) (u := u) (β := β)
  calc
    (2 : ℂ) * q1PhaseCorrectedDoubleSumShellDefectRange X N u β
        = q1PhaseCorrectedDoubleSumShellDefectRange X N u β
            + q1PhaseCorrectedDoubleSumShellDefectRange X N u β := by ring
    _ = K * S + q1PhaseCorrectedDoubleSumShellDefectRange X N u β := by rw [hfac]
    _ = K * S + K * T := by rw [hpair]
    _ = K * (S + T) := by ring
    _ = K * U := by rw [hsum]
    _ =
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * (∑ j ∈ Finset.range (N - 5),
              ∑ k ∈ Finset.range (N - 5),
                q1TwoSidedShiftRangeTerm X N u β j k) := by rfl

/--
Twice the corrected `q = 1` shell defect collapses to the paired two-sided-shift sum.
-/
theorem two_mul_q1PhaseCorrectedDoubleSumShellDefect_eq_kernel_mul_twoSided
    (X N : ℕ) (u β : ℝ) :
    (2 : ℂ) * q1PhaseCorrectedDoubleSumShellDefect X N u β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5),
            q1TwoSidedShiftRangeTerm X N u β j k) := by
  rw [q1PhaseCorrectedDoubleSumShellDefect_eq_range (X := X) (N := N) (u := u) (β := β)]
  exact two_mul_q1PhaseCorrectedDoubleSumShellDefectRange_eq_kernel_mul_twoSided
    (X := X) (N := N) (u := u) (β := β)

theorem norm_two_mul_q1PhaseCorrectedDoubleSumShellDefect_le_kernelCap_card_sq_quadratic
    (X N : ℕ) (u β : ℝ) :
    ‖(2 : ℂ) * q1PhaseCorrectedDoubleSumShellDefect X N u β‖
      ≤
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
      * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2)) := by
  rw [two_mul_q1PhaseCorrectedDoubleSumShellDefect_eq_kernel_mul_twoSided]
  have hK :
      ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
        ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.norm_kernelPolyC_le_kernelCap (x := (β : UC))
  have hsum :
      ‖∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5), q1TwoSidedShiftRangeTerm X N u β j k‖
        ≤ (N - 5 : ℝ) ^ 2 * (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2) := by
    calc
      ‖∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5), q1TwoSidedShiftRangeTerm X N u β j k‖
          ≤ ∑ j ∈ Finset.range (N - 5),
              ‖∑ k ∈ Finset.range (N - 5), q1TwoSidedShiftRangeTerm X N u β j k‖ := by
                simpa using
                  (norm_sum_le
                    (s := Finset.range (N - 5))
                    (f := fun j =>
                      ∑ k ∈ Finset.range (N - 5), q1TwoSidedShiftRangeTerm X N u β j k))
      _ ≤ ∑ j ∈ Finset.range (N - 5),
            ∑ k ∈ Finset.range (N - 5), ‖q1TwoSidedShiftRangeTerm X N u β j k‖ := by
              refine Finset.sum_le_sum ?_
              intro j hj
              simpa using
                (norm_sum_le
                  (s := Finset.range (N - 5))
                  (f := fun k => q1TwoSidedShiftRangeTerm X N u β j k))
      _ ≤ ∑ j ∈ Finset.range (N - 5),
            ∑ k ∈ Finset.range (N - 5), (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2) := by
              refine Finset.sum_le_sum ?_
              intro j hj
              refine Finset.sum_le_sum ?_
              intro k hk
              exact norm_q1TwoSidedShiftRangeTerm_le_sq_N (X := X) (u := u) (β := β) hj hk
      _ = (((N - 5 : ℕ) : ℝ))
            * ((((N - 5 : ℕ) : ℝ)) * (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2)) := by
              simp
      _ ≤ (N - 5 : ℝ) ^ 2 * (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2) := by
              by_cases hN : 5 ≤ N
              · have hcast : (((N - 5 : ℕ) : ℝ)) = (N : ℝ) - 5 := by
                  rw [Nat.cast_sub hN]
                  norm_num
                rw [hcast]
                ring_nf
                exact le_rfl
              · have hsmall : N < 5 := by omega
                have hcard0 : (N - 5 : ℕ) = 0 := by omega
                simp [hcard0]
                positivity
  calc
    ‖(Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5), q1TwoSidedShiftRangeTerm X N u β j k)‖
        = ‖Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)‖
            * ‖∑ j ∈ Finset.range (N - 5),
                ∑ k ∈ Finset.range (N - 5), q1TwoSidedShiftRangeTerm X N u β j k‖ := by
            rw [norm_mul]
    _ ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2)) := by
            exact mul_le_mul hK hsum (norm_nonneg _) Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg

theorem norm_smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_le_quadratic
    (X N : ℕ) (u β : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖smallBetaRescaledArchShell X N 1 u β
        - smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β‖
      ≤
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
      * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2)) / 2 := by
  let z : ℂ :=
    smallBetaRescaledArchShell X N 1 u β
      - smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β
  have htwo :=
    norm_two_mul_q1PhaseCorrectedDoubleSumShellDefect_le_kernelCap_card_sq_quadratic
      (X := X) (N := N) (u := u) (β := β)
  have hz :
      q1PhaseCorrectedDoubleSumShellDefect X N u β = z := by
    dsimp [z]
    symm
    exact smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_eq_kernel_mul_double_sum
      (X := X) (N := N) (u := u) (β := β)
  rw [hz] at htwo
  have hnorm2 : ‖(2 : ℂ) * z‖ = 2 * ‖z‖ := by
    rw [norm_mul]
    norm_num
  rw [hnorm2] at htwo
  have huabs : |u| ≤ 1 := by
    rw [abs_of_nonneg hu0]
    exact hu1
  have huquad :
      (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2)
        ≤ (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2) := by
    have huabs_sq : |u| ^ 2 ≤ 1 := by
      have huabs_nonneg : 0 ≤ |u| := abs_nonneg u
      nlinarith
    have hCnonneg : 0 ≤ (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2) := by positivity
    have hrew :
        (((2 * Real.pi * |u| * (N : ℝ)) / (X : ℝ)) ^ 2)
          = (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2) * |u| ^ 2 := by
      ring_nf
    rw [hrew]
    nlinarith
  have hbound :
      2 * ‖z‖
        ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2)) := by
    have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    refine le_trans htwo ?_
    gcongr
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  nlinarith

theorem norm_smallBetaRescaledGapExtractedArcHalfQ1Corrected_le_quadratic
    (X N : ℕ) :
    ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖
      ≤
    Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
      * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2)) / 12 := by
  unfold smallBetaRescaledGapExtractedArcHalfQ1Corrected
  refine le_trans
    (norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six
      (C := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2)) / 2)
      (hC := by
        have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
        positivity)
      (hg := ?_))
    ?_
  · intro β hβ
    exact norm_intervalIntegral_zero_one_le
      (C := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2)) / 2)
      (hC := by
        have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
        positivity)
      (hf := fun u hu0 hu1 =>
        norm_smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_le_quadratic
          (X := X) (N := N) (u := u) (β := β) hu0 hu1)
  · ring_nf
    nlinarith

/--
Twice the corrected `q = 1` shell defect equals the kernel times the paired two-sided-shift sum.
-/
theorem two_mul_smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_eq_kernel_mul_twoSided
    (X N : ℕ) (u β : ℝ) :
    (2 : ℂ)
      * (smallBetaRescaledArchShell X N 1 u β
          - smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β)
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ j ∈ Finset.range (N - 5),
          ∑ k ∈ Finset.range (N - 5),
            q1TwoSidedShiftRangeTerm X N u β j k) := by
  rw [smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_eq_kernel_mul_double_sum
    (X := X) (N := N) (u := u) (β := β)]
  exact two_mul_q1PhaseCorrectedDoubleSumShellDefect_eq_kernel_mul_twoSided
    (X := X) (N := N) (u := u) (β := β)

/--
The same shell-level `q = 1` rewrite with the main base phase factored out and the midpoint
correction isolated in the centered shift defect `e(δ) - 1`.
-/
theorem smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_eq_kernel_mul_base_mul_shift_sub_one
    (X N : ℕ) (u β : ℝ) :
    smallBetaRescaledArchShell X N 1 u β
      - smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β
      =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          ∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
              * Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))
              * (Goldbach.Cert.MajorArcExponential.e
                  ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
                - 1)) := by
  let K : ℂ := Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC)
  have hinner :=
    rescaled_q1_innerFactor_sub_phase_corrected_frozen_eq_double_sum_base_mul_shift_sub_one
      (X := X) (N := N) (u := u) (β := β)
  unfold smallBetaRescaledArchShell smallBetaCenteredArchShell
  unfold smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 smallBetaFrozenRescaledArchShell
  calc
    smallBetaCenteredArchShell N (u / (((1 : ℕ) : ℝ) * (X : ℝ))) β
      - Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ)) * smallBetaCenteredArchShell N 0 β
        =
    K
      * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
            (((u / (X : ℝ)) : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
          * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) + β) n)
              * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
                  Goldbach.Cert.MajorArcStep2ExpSums.gExp ((u / (X : ℝ)) - β) m))
        -
        Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
          * ((fourier (T := (1 : ℝ)) (-(N : ℤ))
                ((0 : ℝ) : Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC) : ℂ)
              * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
                    Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 + β) n)
                  * (∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
                      Goldbach.Cert.MajorArcStep2ExpSums.gExp (0 - β) m)))) := by
          simp [smallBetaCenteredArchShell, K, one_mul, sub_eq_add_neg]
          ring_nf
    _ =
    K
      * (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          ∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
              * Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))
              * (Goldbach.Cert.MajorArcExponential.e
                  ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
                - 1)) := by
          simpa [K, one_mul] using congrArg (fun z : ℂ => K * z) hinner
    _ = (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          ∑ m ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcExponential.e (2 * u / (X : ℝ))
              * Goldbach.Cert.MajorArcExponential.e (β * ((n : ℝ) - (m : ℝ)))
              * (Goldbach.Cert.MajorArcExponential.e
                  ((u / (X : ℝ)) * ((n : ℝ) + (m : ℝ) - (((N + 2 : ℕ) : ℝ))))
                - 1)) := by
          simp [K]

private lemma integral_centeredUnitSet_one_indicator_const (z : ℂ) :
    ∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator (fun _ : ℝ => z) u = (2 : ℂ) * z := by
  have hs : MeasurableSet (centeredUnitSet (1 : ℝ)) := measurableSet_centeredUnitSet (1 : ℝ)
  let s : Set ℝ := centeredUnitSet (1 : ℝ)
  have hvol : (volume.restrict s).real Set.univ = 2 := by
    calc
      (volume.restrict s).real Set.univ = volume.real s := by
        simpa using (measureReal_restrict_apply_univ (μ := volume) (s := s))
      _ = (volume s).toReal := by
        simp [Measure.real]
      _ = 2 := by
        norm_num [s, centeredUnitSet_one_eq_Icc, Real.volume_Icc]
  rw [MeasureTheory.integral_indicator (μ := volume) (s := centeredUnitSet (1 : ℝ))
    (f := fun _ : ℝ => z) hs]
  rw [integral_const]
  simp [hvol, s]

private lemma intervalIntegral_zero_one_const (z : ℂ) :
    ∫ u in (0 : ℝ)..(1 : ℝ), z = z := by
  simpa using (intervalIntegral.integral_const (a := (0 : ℝ)) (b := (1 : ℝ)) (c := z))

theorem smallBetaFrozenArchExtractedArcRescaledHalfQ1_eq_frozenBetaScalarC
    (N : ℕ) :
    smallBetaFrozenArchExtractedArcRescaledHalfQ1 N = frozenBetaScalarC N := by
  unfold smallBetaFrozenArchExtractedArcRescaledHalfQ1 frozenBetaScalarC
  have hrewrite :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β) β)
        =
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β) := by
    funext β
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [hβ, smallBetaFrozenRescaledArchShell, intervalIntegral_zero_one_const]
    · simp [hβ]
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun β _ => by
    have hpt := congrArg (fun f : ℝ → ℂ => f β) hrewrite
    simpa using hpt

theorem AqFrozenHalfQ1C_eq_inv_weight_mass_mul_inv_X_mul_frozenBetaScalarC
    (X N : ℕ) :
    AqFrozenHalfQ1C X N
      =
    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
      * ((((X : ℝ) : ℂ))⁻¹)
      * frozenBetaScalarC N := by
  unfold AqFrozenHalfQ1C
  rw [smallBetaFrozenArchExtractedArcRescaledHalfQ1_eq_frozenBetaScalarC]

theorem smallBetaFrozenArchExtractedArcRescaled_eq_two_mul_frozenBetaScalarC
    (X N q : ℕ) :
    smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ) = (2 : ℂ) * frozenBetaScalarC N := by
  unfold smallBetaFrozenArchExtractedArcRescaled frozenBetaScalarC
  have hrewrite :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u : ℝ,
            (centeredUnitSet (1 : ℝ)).indicator
              (fun u => smallBetaFrozenRescaledArchShell N u β) u) β)
        =
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β) := by
    funext β
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [hβ, smallBetaFrozenRescaledArchShell,
        integral_centeredUnitSet_one_indicator_const, mul_assoc, mul_left_comm, mul_comm]
    · simp [hβ]
  have hfactor :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β)
        =
      (fun β : ℝ =>
        (2 : ℂ)
          * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
              (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β) := by
    funext β
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [hβ, mul_assoc, mul_left_comm, mul_comm]
    · simp [hβ]
  have hEq1 :
      smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)
        =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β := by
    refine intervalIntegral.integral_congr_ae ?_
    exact Filter.Eventually.of_forall <| fun β _ => by
      have hpt := congrArg (fun f : ℝ → ℂ => f β) hrewrite
      simpa [smallBetaFrozenArchExtractedArcRescaled] using hpt
  have hEq2 :
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β)
        =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        (2 : ℂ)
          * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
              (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β := by
    refine intervalIntegral.integral_congr_ae ?_
    exact Filter.Eventually.of_forall <| fun β _ => by
      have hpt := congrArg (fun f : ℝ → ℂ => f β) hfactor
      simpa using hpt
  calc
    smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)
      = ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ => (2 : ℂ) * smallBetaCenteredArchShell N 0 β) β := hEq1
    _ = ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          (2 : ℂ)
            * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
                (fun β : ℝ => smallBetaCenteredArchShell N 0 β) β := hEq2
    _ = (2 : ℂ) * frozenBetaScalarC N := by
          rw [intervalIntegral.integral_const_mul]
          rfl

theorem frozenRawScalarC_eq_two_mul_frozenBetaScalarC (N : ℕ) :
    frozenRawScalarC N (1 : ℝ) = (2 : ℂ) * frozenBetaScalarC N := by
  unfold frozenRawScalarC
  simpa using smallBetaFrozenArchExtractedArcRescaled_eq_two_mul_frozenBetaScalarC 1 N 1

theorem smallBetaFrozenArchExtractedArcRescaled_eq_frozenRawScalarC
    (X N q : ℕ) (Δ : ℝ) :
    smallBetaFrozenArchExtractedArcRescaled X N q Δ = frozenRawScalarC N Δ := by
  unfold frozenRawScalarC smallBetaFrozenArchExtractedArcRescaled
  rfl

private lemma smallBetaRescaledGapExtractedArc_eq_sub_of_intervalIntegrable
    {X N q : ℕ} {Δ : ℝ}
    (hcent :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ =>
              ∫ u : ℝ,
                (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hfroz :
      IntervalIntegrable
        (fun β : ℝ =>
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
            (fun β : ℝ =>
              ∫ u : ℝ,
                (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u) β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hinner :
      ∀ β,
        (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledShellGap X N q u β) u)
          =
        (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u)
          -
        (∫ u : ℝ, (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u)) :
    smallBetaRescaledGapExtractedArc X N q Δ
      =
    smallBetaCenteredArchExtractedArcRescaled X N q Δ
      - smallBetaFrozenArchExtractedArcRescaled X N q Δ := by
  unfold smallBetaRescaledGapExtractedArc
    smallBetaCenteredArchExtractedArcRescaled
    smallBetaFrozenArchExtractedArcRescaled
  calc
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ,
            (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledShellGap X N q u β) u) β
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ,
            (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) β
        -
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ,
            (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u) β) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun β _ =>
            betaSmall_indicator_innerRescaledGap_eq_sub X N q Δ β (hinner β)
    _ =
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ,
            (centeredUnitSet Δ).indicator (fun u => smallBetaRescaledArchShell X N q u β) u) β)
      -
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
        (fun β : ℝ =>
          ∫ u : ℝ,
            (centeredUnitSet Δ).indicator (fun u => smallBetaFrozenRescaledArchShell N u β) u) β) := by
          rw [intervalIntegral.integral_sub hcent hfroz]

private lemma continuous_coe_UC : Continuous fun x : ℝ => (x : UC) := by
  simpa using (AddCircle.continuous_mk' (p := (1 : ℝ)) (𝕜 := ℝ))

private lemma continuous_kernelPoly_real :
    Continuous fun β : ℝ =>
      Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) := by
  dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
    Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
  refine continuous_finset_sum _ ?_
  intro k hk
  exact continuous_const.mul (((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC)

private lemma continuous_gExp_real (n : ℕ) : Continuous fun β : ℝ =>
    Goldbach.Cert.MajorArcStep2ExpSums.gExp β n := by
  unfold Goldbach.Cert.MajorArcStep2ExpSums.gExp Goldbach.Cert.MajorArcExponential.e
  have hmul : Continuous fun β : ℝ => ((β : ℂ) * (n : ℂ)) := continuous_ofReal.mul continuous_const
  have hscale : Continuous fun β : ℝ => ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hmul
  have hexpArg :
      Continuous fun β : ℝ => (Complex.I : ℂ) * ((2 * Real.pi : ℂ) * ((β : ℂ) * (n : ℂ))) :=
    continuous_const.mul hscale
  simpa [mul_assoc, mul_left_comm, mul_comm] using Complex.continuous_exp.comp hexpArg

private lemma continuous_smallBetaCenteredArchShell_uncurry (N : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaCenteredArchShell N p.1 p.2 := by
  have hK :
      Continuous fun p : ℝ × ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC) :=
    by
      dsimp [Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC,
        Goldbach.Cert.MajorArcStep9CorrelationIntegral.kernelPoly]
      refine continuous_finset_sum _ ?_
      intro k hk
      exact continuous_const.mul
        ((((fourier (T := (1 : ℝ)) k).continuous).comp continuous_coe_UC).comp continuous_snd)
  have hF :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ) :=
    ((fourier (T := (1 : ℝ)) (-(N : ℤ))).continuous).comp (continuous_coe_UC.comp continuous_fst)
  have hVp :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (continuous_fst.add continuous_snd)
  have hVm :
      Continuous fun p : ℝ × ℝ =>
        ∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
          Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n := by
    classical
    refine continuous_finset_sum _ ?_
    intro n hn
    exact (continuous_gExp_real n).comp (continuous_fst.sub continuous_snd)
  change Continuous (fun p : ℝ × ℝ =>
    Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC)
      * (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
      * ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n)))
  have hProd :
      Continuous fun p : ℝ × ℝ =>
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
        (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n) := hVp.mul hVm
  have hFProd :
      Continuous fun p : ℝ × ℝ =>
        (fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
          *
        ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
          *
          (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
            Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n)) := hF.mul hProd
  have hAll :
      Continuous fun p : ℝ × ℝ =>
        Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (p.2 : UC)
          *
        ((fourier (T := (1 : ℝ)) (-(N : ℤ)) (p.1 : UC) : ℂ)
          *
          ((∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 + p.2) n)
            *
            (∑ n ∈ Finset.Ico 4 ((N - 2) + 1),
              Goldbach.Cert.MajorArcStep2ExpSums.gExp (p.1 - p.2) n))) := hK.mul hFProd
  simpa [mul_assoc] using hAll

private lemma continuous_smallBetaRescaledArchShell_uncurry (X N q : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaRescaledArchShell X N q p.2 p.1 := by
  let phi : ℝ × ℝ → ℝ × ℝ := fun p => (p.2 / ((q : ℝ) * (X : ℝ)), p.1)
  have hphi : Continuous phi := (continuous_snd.div_const _).prodMk continuous_fst
  simpa [phi, smallBetaRescaledArchShell] using
    (continuous_smallBetaCenteredArchShell_uncurry N).comp hphi

private lemma continuous_smallBetaFrozenRescaledArchShell_uncurry (N : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaFrozenRescaledArchShell N p.2 p.1 := by
  let phi : ℝ × ℝ → ℝ × ℝ := fun p => (0, p.1)
  have hphi : Continuous phi := continuous_const.prodMk continuous_fst
  simpa [phi, smallBetaFrozenRescaledArchShell] using
    (continuous_smallBetaCenteredArchShell_uncurry N).comp hphi

private lemma continuous_smallBetaPhaseCorrectedFrozenRescaledArchShellQ1_uncurry
    (X N : ℕ) :
    Continuous fun p : ℝ × ℝ => smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N p.2 p.1 := by
  have hphase : Continuous fun p : ℝ × ℝ =>
      Goldbach.Cert.MajorArcExponential.e (2 * p.2 / (X : ℝ)) := by
    unfold Goldbach.Cert.MajorArcExponential.e
    have hreal : Continuous fun p : ℝ × ℝ =>
        2 * Real.pi * (2 * p.2 / (X : ℝ)) := by
      continuity
    have harg : Continuous fun p : ℝ × ℝ =>
        (Complex.I : ℂ) * ((2 * Real.pi * (2 * p.2 / (X : ℝ)) : ℝ) : ℂ) := by
      exact continuous_const.mul (continuous_ofReal.comp hreal)
    simpa using Complex.continuous_exp.comp harg
  simpa [smallBetaPhaseCorrectedFrozenRescaledArchShellQ1]
    using hphase.mul (continuous_smallBetaFrozenRescaledArchShell_uncurry N)

private lemma integral_indicator_centeredUnitSet_one_smallBetaRescaledArchShell_eq_intervalIntegral
    (X N q : ℕ) (β : ℝ) :
    (∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaRescaledArchShell X N q u β) u)
      =
    ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N q u β := by
  have hcont : Continuous fun u : ℝ => smallBetaRescaledArchShell X N q u β := by
    let psi : ℝ → ℝ × ℝ := fun u => (β, u)
    have hpsi : Continuous psi := continuous_const.prodMk continuous_id
    simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N q).comp hpsi
  rw [centeredUnitSet_one_eq_Icc]
  calc
    (∫ u : ℝ, (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator
        (fun u => smallBetaRescaledArchShell X N q u β) u)
      =
    ∫ u in Set.Icc (-1 : ℝ) (1 : ℝ), smallBetaRescaledArchShell X N q u β := by
      simpa using
        (MeasureTheory.integral_indicator (μ := volume)
          (s := Set.Icc (-1 : ℝ) (1 : ℝ))
          (f := fun u : ℝ => smallBetaRescaledArchShell X N q u β) measurableSet_Icc)
    _ = ∫ u in Set.Ioc (-1 : ℝ) (1 : ℝ), smallBetaRescaledArchShell X N q u β := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := volume) (f := fun u : ℝ => smallBetaRescaledArchShell X N q u β)
          (x := (-1 : ℝ)) (y := (1 : ℝ)))
    _ = ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N q u β := by
      simpa using
        (intervalIntegral.integral_of_le (μ := volume)
          (f := fun u : ℝ => smallBetaRescaledArchShell X N q u β)
          (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 1)).symm

private lemma integral_indicator_centeredUnitSet_one_smallBetaFrozenRescaledArchShell_eq_intervalIntegral
    (N : ℕ) (β : ℝ) :
    (∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaFrozenRescaledArchShell N u β) u)
      =
    ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
  rw [centeredUnitSet_one_eq_Icc]
  calc
    (∫ u : ℝ, (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator
        (fun u => smallBetaFrozenRescaledArchShell N u β) u)
      =
    ∫ u in Set.Icc (-1 : ℝ) (1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
      simpa using
        (MeasureTheory.integral_indicator (μ := volume)
          (s := Set.Icc (-1 : ℝ) (1 : ℝ))
          (f := fun u : ℝ => smallBetaFrozenRescaledArchShell N u β) measurableSet_Icc)
    _ = ∫ u in Set.Ioc (-1 : ℝ) (1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := volume) (f := fun u : ℝ => smallBetaFrozenRescaledArchShell N u β)
          (x := (-1 : ℝ)) (y := (1 : ℝ)))
    _ = ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
      simpa using
        (intervalIntegral.integral_of_le (μ := volume)
          (f := fun u : ℝ => smallBetaFrozenRescaledArchShell N u β)
          (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 1)).symm

private lemma integral_indicator_centeredUnitSet_one_smallBetaRescaledShellGap_eq_intervalIntegral
    (X N q : ℕ) (β : ℝ) :
    (∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaRescaledShellGap X N q u β) u)
      =
    ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledShellGap X N q u β := by
  rw [centeredUnitSet_one_eq_Icc]
  calc
    (∫ u : ℝ, (Set.Icc (-1 : ℝ) (1 : ℝ)).indicator
        (fun u => smallBetaRescaledShellGap X N q u β) u)
      =
    ∫ u in Set.Icc (-1 : ℝ) (1 : ℝ), smallBetaRescaledShellGap X N q u β := by
      simpa using
        (MeasureTheory.integral_indicator (μ := volume)
          (s := Set.Icc (-1 : ℝ) (1 : ℝ))
          (f := fun u : ℝ => smallBetaRescaledShellGap X N q u β) measurableSet_Icc)
    _ = ∫ u in Set.Ioc (-1 : ℝ) (1 : ℝ), smallBetaRescaledShellGap X N q u β := by
      simpa using
        (MeasureTheory.integral_Icc_eq_integral_Ioc
          (μ := volume) (f := fun u : ℝ => smallBetaRescaledShellGap X N q u β)
          (x := (-1 : ℝ)) (y := (1 : ℝ)))
    _ = ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledShellGap X N q u β := by
      simpa using
        (intervalIntegral.integral_of_le (μ := volume)
          (f := fun u : ℝ => smallBetaRescaledShellGap X N q u β)
          (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 1)).symm

private lemma integral_indicator_centeredUnitSet_one_smallBetaRescaledShellGap_eq_sub
    (X N q : ℕ) (β : ℝ) :
    (∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaRescaledShellGap X N q u β) u)
      =
    (∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaRescaledArchShell X N q u β) u)
      -
    (∫ u : ℝ, (centeredUnitSet (1 : ℝ)).indicator
        (fun u => smallBetaFrozenRescaledArchShell N u β) u) := by
  have hcent :
      IntervalIntegrable (fun u : ℝ => smallBetaRescaledArchShell X N q u β)
        volume (-1 : ℝ) (1 : ℝ) := by
    have hcont : Continuous fun u : ℝ => smallBetaRescaledArchShell X N q u β := by
      let psi : ℝ → ℝ × ℝ := fun u => (β, u)
      have hpsi : Continuous psi := continuous_const.prodMk continuous_id
      simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N q).comp hpsi
    exact hcont.intervalIntegrable _ _
  have hfroz :
      IntervalIntegrable (fun u : ℝ => smallBetaFrozenRescaledArchShell N u β)
        volume (-1 : ℝ) (1 : ℝ) := by
    have hcont : Continuous fun u : ℝ => smallBetaFrozenRescaledArchShell N u β := by
      let psi : ℝ → ℝ × ℝ := fun u => (β, u)
      have hpsi : Continuous psi := continuous_const.prodMk continuous_id
      simpa [psi] using (continuous_smallBetaFrozenRescaledArchShell_uncurry N).comp hpsi
    exact hcont.intervalIntegrable _ _
  rw [integral_indicator_centeredUnitSet_one_smallBetaRescaledShellGap_eq_intervalIntegral,
    integral_indicator_centeredUnitSet_one_smallBetaRescaledArchShell_eq_intervalIntegral,
    integral_indicator_centeredUnitSet_one_smallBetaFrozenRescaledArchShell_eq_intervalIntegral]
  calc
    (∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledShellGap X N q u β)
      =
    ∫ u in (-1 : ℝ)..(1 : ℝ),
      (smallBetaRescaledArchShell X N q u β - smallBetaFrozenRescaledArchShell N u β) := by
        refine intervalIntegral.integral_congr_ae ?_
        exact Filter.Eventually.of_forall <| fun u _ =>
          smallBetaRescaledShellGap_eq_sub X N q u β
    _ =
    (∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N q u β)
      - ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
        rw [intervalIntegral.integral_sub hcent hfroz]

private lemma continuous_beta_intervalIntegral_smallBetaRescaledArchShell_one
    (X N q : ℕ) :
    Continuous fun β : ℝ =>
      ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N q u β := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u => smallBetaRescaledArchShell X N q u β)
      (hf := by
        simpa [Function.uncurry] using continuous_smallBetaRescaledArchShell_uncurry X N q)
      (-1 : ℝ) (1 : ℝ))

private lemma continuous_beta_intervalIntegral_smallBetaFrozenRescaledArchShell_one
    (N : ℕ) :
    Continuous fun β : ℝ =>
      ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u => smallBetaFrozenRescaledArchShell N u β)
      (hf := by
        simpa [Function.uncurry] using continuous_smallBetaFrozenRescaledArchShell_uncurry N)
      (-1 : ℝ) (1 : ℝ))

private lemma intervalIntegrable_betaSmall_indicator_inner_smallBetaRescaledArchShell_one
    (X N q : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u : ℝ,
              (centeredUnitSet (1 : ℝ)).indicator
                (fun u => smallBetaRescaledArchShell X N q u β) u) β)
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ =>
          ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N q u β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_smallBetaRescaledArchShell_one X N q).intervalIntegrable _ _
  have hEq :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u : ℝ,
              (centeredUnitSet (1 : ℝ)).indicator
                (fun u => smallBetaRescaledArchShell X N q u β) u) β)
        =
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N q u β) β) := by
    funext β
    simp [integral_indicator_centeredUnitSet_one_smallBetaRescaledArchShell_eq_intervalIntegral]
  rw [hEq]
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

private lemma intervalIntegrable_betaSmall_indicator_inner_smallBetaFrozenRescaledArchShell_one
    (N : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u : ℝ,
              (centeredUnitSet (1 : ℝ)).indicator
                (fun u => smallBetaFrozenRescaledArchShell N u β) u) β)
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ =>
          ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_smallBetaFrozenRescaledArchShell_one N).intervalIntegrable _ _
  have hEq :
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u : ℝ,
              (centeredUnitSet (1 : ℝ)).indicator
                (fun u => smallBetaFrozenRescaledArchShell N u β) u) β)
        =
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ =>
            ∫ u in (-1 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β) β) := by
    funext β
    simp [integral_indicator_centeredUnitSet_one_smallBetaFrozenRescaledArchShell_eq_intervalIntegral]
  rw [hEq]
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

private lemma continuous_beta_intervalIntegral_smallBetaRescaledArchShell_halfQ1
    (X N : ℕ) :
    Continuous fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u => smallBetaRescaledArchShell X N 1 u β)
      (hf := by
        simpa [Function.uncurry] using continuous_smallBetaRescaledArchShell_uncurry X N 1)
      (0 : ℝ) (1 : ℝ))

private lemma continuous_beta_intervalIntegral_smallBetaFrozenRescaledArchShell_halfQ1
    (N : ℕ) :
    Continuous fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u => smallBetaFrozenRescaledArchShell N u β)
      (hf := by
        simpa [Function.uncurry] using continuous_smallBetaFrozenRescaledArchShell_uncurry N)
      (0 : ℝ) (1 : ℝ))

private lemma intervalIntegrable_betaSmall_indicator_inner_smallBetaRescaledArchShell_halfQ1
    (X N : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_smallBetaRescaledArchShell_halfQ1 X N).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

private lemma intervalIntegrable_betaSmall_indicator_inner_smallBetaFrozenRescaledArchShell_halfQ1
    (N : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β) β)
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_smallBetaFrozenRescaledArchShell_halfQ1 N).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

private lemma continuous_beta_intervalIntegral_smallBetaPhaseCorrectedFrozenRescaledArchShell_halfQ1
    (X N : ℕ) :
    Continuous fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β := by
  simpa using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β u => smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β)
      (hf := by
        simpa [Function.uncurry] using
          continuous_smallBetaPhaseCorrectedFrozenRescaledArchShellQ1_uncurry X N)
      (0 : ℝ) (1 : ℝ))

private lemma intervalIntegrable_betaSmall_indicator_inner_smallBetaPhaseCorrectedFrozenRescaledArchShell_halfQ1
    (X N : ℕ) :
    IntervalIntegrable
      (fun β : ℝ =>
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator
          (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β) β)
      volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ := by
  have hInt :
      IntervalIntegrable
        (fun β : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β)
        volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ :=
    (continuous_beta_intervalIntegral_smallBetaPhaseCorrectedFrozenRescaledArchShell_halfQ1 X N).intervalIntegrable _ _
  exact
    Goldbach.Cert.MajorArcModules.BetaLocalization.intervalIntegrable_indicator_of_intervalIntegrable
      (a := Goldbach.Cert.MajorArcModules.BetaInterval.aβ)
      (b := Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
      (s := Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet)
      Goldbach.Cert.MajorArcModules.BetaLocalization.measurableSet_betaSmallSet
      hInt

theorem smallBetaRescaledGapExtractedArc_eq_sub
    (X N q : ℕ) :
    smallBetaRescaledGapExtractedArc X N q (1 : ℝ)
      =
    smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)
      - smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ) := by
  refine smallBetaRescaledGapExtractedArc_eq_sub_of_intervalIntegrable ?_ ?_ ?_
  · exact intervalIntegrable_betaSmall_indicator_inner_smallBetaRescaledArchShell_one X N q
  · exact intervalIntegrable_betaSmall_indicator_inner_smallBetaFrozenRescaledArchShell_one N
  · intro β
    exact integral_indicator_centeredUnitSet_one_smallBetaRescaledShellGap_eq_sub X N q β

theorem smallBetaRescaledGapExtractedArcHalfQ1_eq_sub
    (X N : ℕ) :
    smallBetaRescaledGapExtractedArcHalfQ1 X N
      =
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)
      -
    smallBetaFrozenArchExtractedArcRescaledHalfQ1 N := by
  unfold smallBetaRescaledGapExtractedArcHalfQ1 smallBetaFrozenArchExtractedArcRescaledHalfQ1
  have hcentu :
      ∀ β : ℝ,
        IntervalIntegrable (fun u : ℝ => smallBetaRescaledArchShell X N 1 u β)
          volume (0 : ℝ) (1 : ℝ) := by
    intro β
    have hcont : Continuous fun u : ℝ => smallBetaRescaledArchShell X N 1 u β := by
      let psi : ℝ → ℝ × ℝ := fun u => (β, u)
      have hpsi : Continuous psi := continuous_const.prodMk continuous_id
      simpa [psi] using (continuous_smallBetaRescaledArchShell_uncurry X N 1).comp hpsi
    exact hcont.intervalIntegrable _ _
  have hfrozu :
      ∀ β : ℝ,
        IntervalIntegrable (fun u : ℝ => smallBetaFrozenRescaledArchShell N u β)
          volume (0 : ℝ) (1 : ℝ) := by
    intro β
    have hcont : Continuous fun u : ℝ => smallBetaFrozenRescaledArchShell N u β := by
      let psi : ℝ → ℝ × ℝ := fun u => (β, u)
      have hpsi : Continuous psi := continuous_const.prodMk continuous_id
      simpa [psi] using (continuous_smallBetaFrozenRescaledArchShell_uncurry N).comp hpsi
    exact hcont.intervalIntegrable _ _
  calc
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledShellGap X N 1 u β) β
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β
        -
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β) β) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun β _ => by
            by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
            · simp [hβ]
              calc
                ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledShellGap X N 1 u β
                  =
                ∫ u in (0 : ℝ)..(1 : ℝ),
                  (smallBetaRescaledArchShell X N 1 u β
                    - smallBetaFrozenRescaledArchShell N u β) := by
                      refine intervalIntegral.integral_congr_ae ?_
                      exact Filter.Eventually.of_forall <| fun u _ =>
                        smallBetaRescaledShellGap_eq_sub X N 1 u β
                _ =
                (∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β)
                  - ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β := by
                      rw [intervalIntegral.integral_sub (hcentu β) (hfrozu β)]
            · simp [hβ]
    _ =
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)
      -
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaFrozenRescaledArchShell N u β) β) := by
          rw [intervalIntegral.integral_sub
            (intervalIntegrable_betaSmall_indicator_inner_smallBetaRescaledArchShell_halfQ1 X N)
            (intervalIntegrable_betaSmall_indicator_inner_smallBetaFrozenRescaledArchShell_halfQ1 N)]

theorem AqLocalC_q1_sub_AqFrozenHalfQ1C_eq_inv_weight_mass_mul_inv_X_mul_halfGap
    (X N : ℕ) (hX : 2 ≤ X) :
    AqLocalC X N 1 - AqFrozenHalfQ1C X N
      =
    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
      * ((((X : ℝ) : ℂ))⁻¹)
      * smallBetaRescaledGapExtractedArcHalfQ1 X N := by
  rw [AqLocalC_q1_eq_inv_weight_mass_mul_inv_X_mul_rescaled_half X N hX,
    AqFrozenHalfQ1C_eq_inv_weight_mass_mul_inv_X_mul_frozenBetaScalarC]
  rw [← smallBetaFrozenArchExtractedArcRescaledHalfQ1_eq_frozenBetaScalarC]
  rw [smallBetaRescaledGapExtractedArcHalfQ1_eq_sub]
  ring

theorem smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_sub
    (X N : ℕ) :
    smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      =
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)
      -
    smallBetaPhaseCorrectedFrozenArchExtractedArcRescaledHalfQ1 X N := by
  unfold smallBetaRescaledGapExtractedArcHalfQ1Corrected
    smallBetaPhaseCorrectedFrozenArchExtractedArcRescaledHalfQ1
  have hcorru :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun u : ℝ => smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β)
          volume (0 : ℝ) (1 : ℝ) := by
    intro β
    have hcont : Continuous fun u : ℝ => smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β := by
      let psi : ℝ → ℝ × ℝ := fun u => (β, u)
      have hpsi : Continuous psi := continuous_const.prodMk continuous_id
      simpa [psi] using
        (continuous_smallBetaPhaseCorrectedFrozenRescaledArchShellQ1_uncurry X N).comp hpsi
    exact hcont.intervalIntegrable _ _
  calc
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ),
          (smallBetaRescaledArchShell X N 1 u β
            - smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β)) β
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      (Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β
        -
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β) β) := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun β _ => by
            by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
            · simp [hβ]
              rw [intervalIntegral.integral_sub
                (by
                  have hcont : Continuous fun u : ℝ => smallBetaRescaledArchShell X N 1 u β := by
                    let psi : ℝ → ℝ × ℝ := fun u => (β, u)
                    have hpsi : Continuous psi := continuous_const.prodMk continuous_id
                    simpa [psi] using
                      (continuous_smallBetaRescaledArchShell_uncurry X N 1).comp hpsi
                  exact hcont.intervalIntegrable _ _)
                (hcorru β)]
            · simp [hβ]
    _ =
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaRescaledArchShell X N 1 u β) β)
      -
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), smallBetaPhaseCorrectedFrozenRescaledArchShellQ1 X N u β) β) := by
          rw [intervalIntegral.integral_sub
            (intervalIntegrable_betaSmall_indicator_inner_smallBetaRescaledArchShell_halfQ1 X N)
            (intervalIntegrable_betaSmall_indicator_inner_smallBetaPhaseCorrectedFrozenRescaledArchShell_halfQ1 X N)]

/--
Exact integral rewrite of the corrected principal-arc half-gap through the shell-level double-sum
defect.

This is the principal-arc endpoint before any norm estimate: the half-gap is literally the
`β`-integral of the `u`-integral of the kernel-weighted midpoint-corrected double-sum defect.
-/
theorem smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_integral_doubleSumDefect
    (X N : ℕ) :
    smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X N u β) β := by
  unfold smallBetaRescaledGapExtractedArcHalfQ1Corrected
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun β _ => by
    by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
    · simp [hβ]
      refine intervalIntegral.integral_congr_ae ?_
      exact Filter.Eventually.of_forall <| fun u _ =>
        smallBetaRescaledArchShell_q1_sub_phaseCorrectedFrozen_eq_kernel_mul_double_sum
          (X := X) (N := N) (u := u) (β := β)
    · simp [hβ]

/--
Twice the corrected principal-arc half-gap is the `β`/`u` integral of the paired two-sided-shift
`q = 1` shell defect.
-/
theorem two_mul_smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_integral_twoSided
    (X N : ℕ) :
    (2 : ℂ) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      =
    ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
            * (∑ j ∈ Finset.range (N - 5),
                ∑ k ∈ Finset.range (N - 5),
                  q1TwoSidedShiftRangeTerm X N u β j k)) β := by
  calc
    (2 : ℂ) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
        =
      (2 : ℂ)
        * ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              ∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X N u β) β := by
          rw [smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_integral_doubleSumDefect
            (X := X) (N := N)]
    _ =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          (2 : ℂ)
            * Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
                ∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X N u β) β := by
          rw [intervalIntegral.integral_const_mul]
    _ =
      ∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ),
              (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                * (∑ j ∈ Finset.range (N - 5),
                    ∑ k ∈ Finset.range (N - 5),
                      q1TwoSidedShiftRangeTerm X N u β j k)) β := by
          refine intervalIntegral.integral_congr_ae ?_
          exact Filter.Eventually.of_forall <| fun β _ => by
            by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
            · simp [hβ]
              have hinner :
                  ∫ u in (0 : ℝ)..(1 : ℝ), (2 : ℂ) * q1PhaseCorrectedDoubleSumShellDefect X N u β
                    =
                  ∫ u in (0 : ℝ)..(1 : ℝ),
                    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
                      * (∑ j ∈ Finset.range (N - 5),
                          ∑ k ∈ Finset.range (N - 5),
                            q1TwoSidedShiftRangeTerm X N u β j k) := by
                refine intervalIntegral.integral_congr_ae ?_
                exact Filter.Eventually.of_forall <| fun u _ =>
                  two_mul_q1PhaseCorrectedDoubleSumShellDefect_eq_kernel_mul_twoSided
                    (X := X) (N := N) (u := u) (β := β)
              simpa [intervalIntegral.integral_const_mul] using hinner
            · simp [hβ]

theorem AqLocalC_q1_sub_AqFrozenHalfQ1CorrectedC_eq_inv_weight_mass_mul_inv_X_mul_halfGapCorrected
    (X N : ℕ) (hX : 2 ≤ X) :
    AqLocalC X N 1 - AqFrozenHalfQ1CorrectedC X N
      =
    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
      * ((((X : ℝ) : ℂ))⁻¹)
      * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N := by
  rw [AqLocalC_q1_eq_inv_weight_mass_mul_inv_X_mul_rescaled_half X N hX]
  unfold AqFrozenHalfQ1CorrectedC
  rw [smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_sub]
  ring

/-- The `q = 1` phase factor is exactly `1`. -/
private lemma qPhaseFactor_one (N : ℕ) : qPhaseFactor 1 N = 1 := by
  unfold qPhaseFactor
  simp [Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop, Goldbach.Cert.MajorArcExponential.e]

/--
The weighted `q ≥ 2` freeze defect kept as a single summed object, before taking norms.
-/
noncomputable def weightedFreezeDefectGe2C (X N : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
    (AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N

/--
Exact `q ≥ 2` rewrite of the weighted freeze defect through the rescaled archimedean family.

This keeps the already-weighted defect as a single summed object, but replaces `AqLocalC` by the
honest rescaled scalar `AqCRescaled` on the range where that identification is exact.
-/
theorem weightedFreezeDefectGe2C_eq_sum_AqCRescaled_sub_AqFrozenC
    (X N : ℕ) (hX : 2 ≤ X) :
    weightedFreezeDefectGe2C X N
      =
    ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
      (AqCRescaled X N q (1 : ℝ) - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N := by
  unfold weightedFreezeDefectGe2C
  refine Finset.sum_congr rfl ?_
  intro q hq
  rw [AqLocalC_eq_AqCRescaled_of_two_le hX (Finset.mem_Icc.mp hq).1]

/--
The corrected frozen weighted endpoint: the principal arc uses the phase-corrected half comparator,
while the `q ≥ 2` arcs keep the usual frozen model.
-/
noncomputable def frozenWeightedMainTermQ1CorrectedC (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
    * (AqFrozenHalfQ1CorrectedC X N
        + ∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqFrozenC X N q (1 : ℝ) * qPhaseFactor q N)

/--
Exact weighted freeze decomposition against the corrected principal-arc endpoint.

This is the right algebraic surface for the next quantitative work: the `q = 1` defect is isolated
from the already weighted `q ≥ 2` sum before any norm or triangle inequality is applied.
-/
theorem smallBetaModelWeightedQC_sub_frozenWeightedMainTermQ1CorrectedC_eq
    (X N : ℕ) :
    smallBetaModelWeightedQC AqLocalC X N - frozenWeightedMainTermQ1CorrectedC X N
      =
    (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
      * ((AqLocalC X N 1 - AqFrozenHalfQ1CorrectedC X N)
          + weightedFreezeDefectGe2C X N) := by
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  have hsplitLocal :
      ∑ q ∈ Finset.Icc (1 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N
        =
      AqLocalC X N 1 * qPhaseFactor 1 N
        + ∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N := by
    have hsplit :
        Finset.Icc (1 : ℕ) Q0 = insert 1 (Finset.Icc (2 : ℕ) Q0) := by
      ext q
      simp [Nat.succ_le_iff]
      omega
    have hnotmem : 1 ∉ Finset.Icc (2 : ℕ) Q0 := by simp
    rw [hsplit, Finset.sum_insert hnotmem]
  have hsplitFrozen :
      ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
          (AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N
        =
      (∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N)
        -
      (∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqFrozenC X N q (1 : ℝ) * qPhaseFactor q N) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro q hq
    ring
  calc
    smallBetaModelWeightedQC AqLocalC X N - frozenWeightedMainTermQ1CorrectedC X N
      =
    w * (AqLocalC X N 1 * qPhaseFactor 1 N
          + ∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N)
      - w * (AqFrozenHalfQ1CorrectedC X N
          + ∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqFrozenC X N q (1 : ℝ) * qPhaseFactor q N) := by
          unfold smallBetaModelWeightedQC frozenWeightedMainTermQ1CorrectedC
          rw [hsplitLocal]
    _ =
    w * ((AqLocalC X N 1 * qPhaseFactor 1 N - AqFrozenHalfQ1CorrectedC X N)
          + ((∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N)
              -
             (∑ q ∈ Finset.Icc (2 : ℕ) Q0, AqFrozenC X N q (1 : ℝ) * qPhaseFactor q N))) := by
          ring
    _ =
    w * ((AqLocalC X N 1 * qPhaseFactor 1 N - AqFrozenHalfQ1CorrectedC X N)
          + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
              (AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N) := by
          rw [hsplitFrozen]
    _ =
    w * ((AqLocalC X N 1 - AqFrozenHalfQ1CorrectedC X N)
          + weightedFreezeDefectGe2C X N) := by
          rw [qPhaseFactor_one]
          simp [weightedFreezeDefectGe2C]

/--
The same exact weighted freeze decomposition with the corrected `q = 1` term rewritten through the
half-gap object.
-/
theorem smallBetaModelWeightedQC_sub_frozenWeightedMainTermQ1CorrectedC_eq_inv_X_mul_halfGap_add
    (X N : ℕ) (hX : 2 ≤ X) :
    smallBetaModelWeightedQC AqLocalC X N - frozenWeightedMainTermQ1CorrectedC X N
      =
    ((((X : ℝ) : ℂ))⁻¹) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      + (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * weightedFreezeDefectGe2C X N := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_two_le hX
  have hwneR : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0 := ne_of_gt hwpos
  have hwneC : (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hwneR
  let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  calc
    smallBetaModelWeightedQC AqLocalC X N - frozenWeightedMainTermQ1CorrectedC X N
      = w * ((AqLocalC X N 1 - AqFrozenHalfQ1CorrectedC X N)
            + weightedFreezeDefectGe2C X N) := by
            simpa [w] using
              smallBetaModelWeightedQC_sub_frozenWeightedMainTermQ1CorrectedC_eq (X := X) (N := N)
    _ = w * (((w⁻¹ * ((((X : ℝ) : ℂ))⁻¹)
              * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N))
            + weightedFreezeDefectGe2C X N) := by
            rw [AqLocalC_q1_sub_AqFrozenHalfQ1CorrectedC_eq_inv_weight_mass_mul_inv_X_mul_halfGapCorrected
              (X := X) (N := N) hX]
    _ = w * (w⁻¹ * ((((X : ℝ) : ℂ))⁻¹) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N)
          + w * weightedFreezeDefectGe2C X N := by
            rw [mul_add]
    _ = ((((X : ℝ) : ℂ))⁻¹) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
          + w * weightedFreezeDefectGe2C X N := by
            congr 1
            calc
              w * (w⁻¹ * ((((X : ℝ) : ℂ))⁻¹) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N)
                = (w * w⁻¹) * ((((X : ℝ) : ℂ))⁻¹)
                    * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N := by
                      ring
              _ = ((((X : ℝ) : ℂ))⁻¹) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N := by
                      rw [mul_inv_cancel₀ hwneC]
                      simp

/--
Exact top-level split of the corrected frozen defect into the honest `q = 1` double-sum integral
and the already-weighted `q ≥ 2` defect.

This is the right endpoint before any norm estimate: both live pieces are now on their exact
cancellation surfaces.
-/
theorem smallBetaModelWeightedQC_sub_frozenWeightedMainTermQ1CorrectedC_eq_integral_doubleSumDefect_add_weightedGe2
    (X N : ℕ) (hX : 2 ≤ X) :
    smallBetaModelWeightedQC AqLocalC X N - frozenWeightedMainTermQ1CorrectedC X N
      =
    ((((X : ℝ) : ℂ))⁻¹)
      * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
          Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
            ∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X N u β) β)
      + (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
          * (∑ q ∈ Finset.Icc (2 : ℕ) Q0,
              (AqCRescaled X N q (1 : ℝ) - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N) := by
  rw [smallBetaModelWeightedQC_sub_frozenWeightedMainTermQ1CorrectedC_eq_inv_X_mul_halfGap_add
      (X := X) (N := N) hX]
  rw [smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_integral_doubleSumDefect]
  rw [weightedFreezeDefectGe2C_eq_sum_AqCRescaled_sub_AqFrozenC (X := X) (N := N) hX]

theorem AqFrozenC_eq_inv_weight_mass_mul_inv_qX_mul_frozenRawScalarC
    (X N q : ℕ) (Δ : ℝ) :
    AqFrozenC X N q Δ
      =
    ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
      * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
      * frozenRawScalarC N Δ := by
  unfold AqFrozenC
  rw [smallBetaFrozenArchExtractedArcRescaled_eq_frozenRawScalarC]

/-- The exact post-freeze `q`-sum kernel on the weighted small-`β` model. -/
noncomputable def frozenQKernelC (X N : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N

/--
The honest post-freeze weighted arithmetic kernel.

This is the surviving `q`-sum after pulling the global `1 / X` normalization out of the
centered-arc geometry.
-/
noncomputable def kappaLeQ0C (N : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ((((q : ℝ) : ℂ))⁻¹) * qPhaseFactor q N

theorem frozenQKernelC_eq_inv_X_mul_kappaLeQ0C
    (X N : ℕ) (hX : 1 ≤ X) :
    frozenQKernelC X N = (((X : ℝ) : ℂ)⁻¹) * kappaLeQ0C N := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hXneR : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  have hXneC : (((X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hXneR
  unfold frozenQKernelC kappaLeQ0C
  calc
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N
      =
    ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      ((((X : ℝ) : ℂ)⁻¹) * ((((q : ℝ) : ℂ))⁻¹)) * qPhaseFactor q N := by
        refine Finset.sum_congr rfl ?_
        intro q hq
        have hqpos : (0 : ℝ) < (q : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1)
        have hqneR : (q : ℝ) ≠ 0 := ne_of_gt hqpos
        have hqneC : (((q : ℝ) : ℂ)) ≠ 0 := by
          exact_mod_cast hqneR
        have hcast :
            (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ)))
              = (((q : ℝ) : ℂ) * (((X : ℝ) : ℂ))) := by
          norm_num
        rw [hcast, mul_inv_rev]
    _ =
    (((X : ℝ) : ℂ)⁻¹)
      * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ((((q : ℝ) : ℂ))⁻¹) * qPhaseFactor q N := by
        calc
          ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((X : ℝ) : ℂ)⁻¹) * ((((q : ℝ) : ℂ))⁻¹) * qPhaseFactor q N
            =
          ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
            (((X : ℝ) : ℂ)⁻¹) * (((((q : ℝ) : ℂ))⁻¹) * qPhaseFactor q N) := by
              refine Finset.sum_congr rfl ?_
              intro q hq
              ring
          _ =
          (((X : ℝ) : ℂ)⁻¹)
            * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, ((((q : ℝ) : ℂ))⁻¹) * qPhaseFactor q N := by
              exact
                (Finset.mul_sum
                  (s := Finset.Icc (1 : ℕ) Q0)
                  (a := (((X : ℝ) : ℂ)⁻¹))
                  (f := fun q : ℕ => ((((q : ℝ) : ℂ))⁻¹) * qPhaseFactor q N)).symm

theorem smallBetaModelWeightedQC_AqFrozenC_eq_frozenRawScalarC_mul_frozenQKernelC
    (X N : ℕ) (hX : 2 ≤ X) :
    smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N
      =
    frozenRawScalarC N (1 : ℝ) * frozenQKernelC X N := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_two_le hX
  have hwneR : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0 := ne_of_gt hwpos
  have hwneC : (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hwneR
  unfold smallBetaModelWeightedQC frozenQKernelC
  set w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
  calc
    w * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, AqFrozenC X N q (1 : ℝ) * qPhaseFactor q N
      =
    w * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      ((w⁻¹ * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * frozenRawScalarC N (1 : ℝ))
        * qPhaseFactor q N) := by
          refine congrArg (fun z : ℂ => w * z) ?_
          refine Finset.sum_congr rfl ?_
          intro q hq
          rw [AqFrozenC_eq_inv_weight_mass_mul_inv_qX_mul_frozenRawScalarC]
    _ =
    w * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
      (w⁻¹ * frozenRawScalarC N (1 : ℝ))
        * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹ * qPhaseFactor q N) := by
          refine congrArg (fun z : ℂ => w * z) ?_
          refine Finset.sum_congr rfl ?_
          intro q hq
          ring
    _ =
    w * ((w⁻¹ * frozenRawScalarC N (1 : ℝ))
      * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N) := by
          rw [← Finset.mul_sum]
    _ =
    (w * (w⁻¹ * frozenRawScalarC N (1 : ℝ)))
      * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N := by
        ring
    _ =
    frozenRawScalarC N (1 : ℝ)
      * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N := by
        calc
          (w * (w⁻¹ * frozenRawScalarC N (1 : ℝ)))
              * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N
            =
          ((w * w⁻¹) * frozenRawScalarC N (1 : ℝ))
              * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N := by
                ring
          _ =
          (1 * frozenRawScalarC N (1 : ℝ))
              * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N := by
                rw [mul_inv_cancel₀ hwneC]
          _ =
          frozenRawScalarC N (1 : ℝ)
              * ∑ q ∈ Finset.Icc (1 : ℕ) Q0, (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹) * qPhaseFactor q N := by
                simp

theorem norm_AqCRescaled_sub_AqFrozenC_le_of_rescaled_gap
    {X N q : ℕ} {Δ η : ℝ}
    (hX : 2 ≤ X)
    (hq : 1 ≤ q)
    (hgap :
      ‖smallBetaCenteredArchExtractedArcRescaled X N q Δ
          - smallBetaFrozenArchExtractedArcRescaled X N q Δ‖ ≤ η) :
    ‖AqCRescaled X N q Δ - AqFrozenC X N q Δ‖
      ≤ (Goldbach.AO_WeightMass.weight_mass X)⁻¹ * (((q : ℝ) * (X : ℝ))⁻¹) * η := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_two_le hX
  have hwneR : (Goldbach.AO_WeightMass.weight_mass X : ℝ) ≠ 0 := ne_of_gt hwpos
  have hwneC : (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hwneR
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hX)
  have hqXpos : 0 < (q : ℝ) * (X : ℝ) := by positivity
  have hqXneR : ((q : ℝ) * (X : ℝ) : ℝ) ≠ 0 := ne_of_gt hqXpos
  have hqXneC : (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))) ≠ 0 := by
    exact_mod_cast hqXneR
  have hsplit :
      AqCRescaled X N q Δ - AqFrozenC X N q Δ
        =
      ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
        * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
        * (smallBetaCenteredArchExtractedArcRescaled X N q Δ
            - smallBetaFrozenArchExtractedArcRescaled X N q Δ) := by
    unfold AqCRescaled AqFrozenC
    ring
  calc
    ‖AqCRescaled X N q Δ - AqFrozenC X N q Δ‖
      =
    ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
        * (((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)
        * (smallBetaCenteredArchExtractedArcRescaled X N q Δ
            - smallBetaFrozenArchExtractedArcRescaled X N q Δ)‖ := by
          simpa [hsplit]
    _ =
    ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)‖
      * ‖(((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)‖
      * ‖smallBetaCenteredArchExtractedArcRescaled X N q Δ
          - smallBetaFrozenArchExtractedArcRescaled X N q Δ‖ := by
            rw [norm_mul, norm_mul]
    _ ≤
    ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)‖
      * ‖(((((q : ℝ) * (X : ℝ) : ℝ) : ℂ))⁻¹)‖
      * η := by
            gcongr
    _ =
    (Goldbach.AO_WeightMass.weight_mass X)⁻¹ * (((q : ℝ) * (X : ℝ))⁻¹) * η := by
          rw [norm_inv, norm_inv]
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos, abs_of_pos hqXpos]

private lemma norm_smallBetaCenteredArchExtractedArcRescaled_sub_frozen_le_linear_q_inv
    {X N q : ℕ}
    (hX : 4 ≤ X) (hq : 2 ≤ q) :
    ‖smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)
        - smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)‖
      ≤
    (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
            * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
                * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))))) / 3 := by
  rw [← smallBetaRescaledGapExtractedArc_eq_sub X N q]
  exact norm_smallBetaRescaledGapExtractedArc_le_linear_q_inv hX hq

theorem norm_AqCRescaled_sub_AqFrozenC_le_linear_q_inv_of_two_le
    {X N q : ℕ}
    (hX : 4 ≤ X) (hq : 2 ≤ q) :
    ‖AqCRescaled X N q (1 : ℝ) - AqFrozenC X N q (1 : ℝ)‖
      ≤
    (Goldbach.AO_WeightMass.weight_mass X)⁻¹
      * (((q : ℝ) * (X : ℝ))⁻¹)
      * ((Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
              * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
                  * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))))) / 3) := by
  exact
    norm_AqCRescaled_sub_AqFrozenC_le_of_rescaled_gap
      (X := X) (N := N) (q := q) (Δ := (1 : ℝ))
      (η := (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
            * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
                * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))))) / 3)
      (show 2 ≤ X by omega) (show 1 ≤ q by omega)
      (norm_smallBetaCenteredArchExtractedArcRescaled_sub_frozen_le_linear_q_inv hX hq)

noncomputable def etaLinearRescaledGap (X N q : ℕ) : ℝ :=
  (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
    * (((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2
        * (((N : ℝ) + 2 * ((N - 2 : ℕ) : ℝ))
            * (4 * Real.pi * (((q : ℝ) * (X : ℝ))⁻¹))))) / 3

noncomputable def etaFreezeTrivial (X N : ℕ) : ℝ :=
  (Goldbach.AO_WeightMass.weight_mass X)⁻¹
    * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)

private lemma norm_smallBetaCenteredArchExtractedArcRescaled_le_one_third_kernelCap_card_sq
    (X N q : ℕ) :
    ‖smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)‖
      ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by
  unfold smallBetaCenteredArchExtractedArcRescaled
  refine le_trans
    (norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six
      (C := 2
        * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2))
      (hC := by
        have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
        positivity)
      (hg := ?_))
    ?_
  · intro β hβ
    exact norm_integral_indicator_centeredUnitSet_one_le
      (C := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)
      (hC := by
        have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
        positivity)
      (hf := fun u hu => norm_smallBetaRescaledArchShell_le X N q u β)
  · ring_nf
    nlinarith

private lemma norm_smallBetaLocalArchShell_le
    (X N q a : ℕ) (α β : ℝ) :
    ‖smallBetaLocalArchShell X N q a α β‖
      ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
  have hrewrite :
      smallBetaLocalArchShell X N q a α β
        =
      smallBetaCenteredArchShell N (localShift q a α) β := by
    unfold smallBetaLocalArchShell smallBetaCenteredArchShell
    simp only
      [Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaV1,
        Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaV2,
        Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.betaPlusResidual,
        Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.betaMinusResidual,
        localShift, sub_eq_add_neg]
  rw [hrewrite]
  exact norm_smallBetaCenteredArchShell_le N (localShift q a α) β

private lemma norm_smallBetaLocalArchExtractedArc_q1_le_one_sixth_kernelCap_card_sq
    (X N : ℕ) (hX : 2 ≤ X) :
    ‖smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)‖
      ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 6 := by
  unfold smallBetaLocalArchExtractedArc
  refine le_trans
    (norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six
      (C := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)
      (hC := by
        have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
        positivity)
      (hg := ?_))
    le_rfl
  intro β hβ
  refine le_trans
    (Goldbach.Cert.MajorArcModules.ArcSetBounds.norm_intervalIntegral_indicator_arcSetTextbook_le
      (X := X) (q := 1) (a := 0) (Δ := (1 : ℝ))
      (C := Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
        * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)
      (hΔ := by norm_num)
      (hq := by norm_num)
      (hX := by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hX))
      (hC := by
        have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
        positivity)
      (hf := fun α hα => norm_smallBetaLocalArchShell_le X N 1 0 α β))
    ?_
  have hhalf :
      2 * ((1 : ℝ) / (((1 : ℝ) * (X : ℝ)))) ≤ (1 : ℝ) := by
    field_simp [show (X : ℝ) ≠ 0 by positivity]
    have hXreal : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    nlinarith
  have hnonneg :
      0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
    have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    positivity
  simpa using mul_le_mul_of_nonneg_left hhalf hnonneg

private lemma norm_smallBetaRescaledGapExtractedArc_le_two_thirds_kernelCap_card_sq
    (X N q : ℕ) :
    ‖smallBetaRescaledGapExtractedArc X N q (1 : ℝ)‖
      ≤ (2 : ℝ)
          * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by
  refine norm_smallBetaRescaledGapExtractedArc_le_one_third_of_pointwise_bound
    (X := X) (N := N) (q := q)
    (Cshell := 2
      * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2))
    (hCshell := by
      have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
        Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
      positivity) ?_
  intro β hβ u hu
  exact norm_smallBetaRescaledShellGap_le X N q u β

private lemma norm_frozenBetaScalarC_le_one_sixth_kernelCap_card_sq
    (N : ℕ) :
    ‖frozenBetaScalarC N‖
      ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 6 := by
  refine norm_intervalIntegral_betaSmallSet_indicator_le_one_div_six ?_ ?_
  · have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
        Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    positivity
  · intro β hβ
    exact norm_smallBetaCenteredArchShell_le N 0 β

private lemma norm_frozenRawScalarC_le_one_third_kernelCap_card_sq
    (N : ℕ) :
    ‖frozenRawScalarC N (1 : ℝ)‖
      ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by
  rw [frozenRawScalarC_eq_two_mul_frozenBetaScalarC]
  calc
    ‖(2 : ℂ) * frozenBetaScalarC N‖
      = (2 : ℝ) * ‖frozenBetaScalarC N‖ := by simp [norm_mul]
    _ ≤ (2 : ℝ)
        * ((Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 6) := by
          gcongr
          exact norm_frozenBetaScalarC_le_one_sixth_kernelCap_card_sq N
    _ = (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by ring



/--
If the `q = 1` scalar and the rescaled `q ≥ 2` scalars are uniformly close to the frozen family,
then the honest local family `AqLocalC` is uniformly close to that frozen family on all
`q ∈ [1,Q0]`.

This is the honest post-oscillation theorem surface. Any later `q`-collapse must be proved from
properties of `AqFrozenC`, not hidden in the oscillation step itself.
-/
theorem AqLocalC_uniform_freeze_of_q1_and_rescaled_ge2
    {X N : ℕ} {ηA : ℝ}
    (hX : 2 ≤ X)
    (hq1 :
      ‖AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)‖ ≤ ηA)
    (hge2 :
      ∀ q ∈ Finset.Icc (2 : ℕ) Q0, ‖AqCRescaled X N q (1 : ℝ) - AqFrozenC X N q (1 : ℝ)‖ ≤ ηA) :
    ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ ≤ ηA := by
  intro q hq
  rcases Nat.eq_or_lt_of_le (Finset.mem_Icc.mp hq).1 with rfl | hqgt
  · exact hq1
  · have hq2 : 2 ≤ q := by omega
    have hq' : q ∈ Finset.Icc (2 : ℕ) Q0 := by
      exact Finset.mem_Icc.mpr ⟨hq2, (Finset.mem_Icc.mp hq).2⟩
    rw [AqLocalC_eq_AqCRescaled_of_two_le hX hq2]
    exact hge2 q hq'

private lemma norm_AqCRescaled_sub_AqFrozenC_le_etaFreezeTrivial_of_two_le
    (X N q : ℕ) (hX : 2 ≤ X) (hq : 2 ≤ q) :
    ‖AqCRescaled X N q (1 : ℝ) - AqFrozenC X N q (1 : ℝ)‖ ≤ etaFreezeTrivial X N := by
  have hgap :
      ‖smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)
          - smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)‖
        ≤ (2 : ℝ)
          * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by
    calc
      ‖smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)
          - smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)‖
        ≤ ‖smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)‖
            + ‖smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)‖ := norm_sub_le _ _
      _ ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3
            + (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by
            gcongr
            · exact norm_smallBetaCenteredArchExtractedArcRescaled_le_one_third_kernelCap_card_sq X N q
            · rw [smallBetaFrozenArchExtractedArcRescaled_eq_frozenRawScalarC]
              exact norm_frozenRawScalarC_le_one_third_kernelCap_card_sq N
      _ = (2 : ℝ)
          * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by ring
  have hmain :=
    norm_AqCRescaled_sub_AqFrozenC_le_of_rescaled_gap
      (X := X) (N := N) (q := q) (Δ := (1 : ℝ))
      (η := (2 : ℝ)
        * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
            * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3)
      hX (by omega) hgap
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_two_le hX
  have hfactor :
      (((q : ℝ) * (X : ℝ))⁻¹) * ((2 : ℝ) / 3) ≤ (1 : ℝ) := by
    field_simp [show ((q : ℝ) * (X : ℝ)) ≠ 0 by positivity]
    have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hXreal : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    nlinarith
  have hnonneg :
      0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
    have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
      Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
    positivity
  refine le_trans hmain ?_
  calc
    (Goldbach.AO_WeightMass.weight_mass X)⁻¹ * (((q : ℝ) * (X : ℝ))⁻¹)
      * ((2 : ℝ)
          * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
              * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3)
      =
    (Goldbach.AO_WeightMass.weight_mass X)⁻¹
      * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)
      * ((((q : ℝ) * (X : ℝ))⁻¹) * ((2 : ℝ) / 3)) := by ring
    _ ≤
    (Goldbach.AO_WeightMass.weight_mass X)⁻¹
      * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2)
      * 1 := by
        gcongr
    _ = etaFreezeTrivial X N := by
        unfold etaFreezeTrivial
        ring

private lemma norm_AqLocalC_one_sub_AqFrozenC_one_le_etaFreezeTrivial
    (X N : ℕ) (hX : 2 ≤ X) :
    ‖AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)‖ ≤ etaFreezeTrivial X N := by
  have hwpos : 0 < Goldbach.AO_WeightMass.weight_mass X := weight_mass_pos_of_two_le hX
  have hsplit :
      AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)
        =
      ((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
        * (smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)
            - ((((X : ℝ) : ℂ))⁻¹) * frozenRawScalarC N (1 : ℝ)) := by
    unfold AqLocalC AqFrozenC
    rw [smallBetaFrozenArchExtractedArcRescaled_eq_frozenRawScalarC]
    simp
    ring
  calc
    ‖AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)‖
      = ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)
          * (smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)
              - ((((X : ℝ) : ℂ))⁻¹) * frozenRawScalarC N (1 : ℝ))‖ := by
            simpa [hsplit]
    _ ≤ ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)‖
          * (‖smallBetaLocalArchExtractedArc X N 1 0 (1 : ℝ)‖
              + ‖((((X : ℝ) : ℂ))⁻¹) * frozenRawScalarC N (1 : ℝ)‖) := by
            rw [norm_mul]
            gcongr
            exact norm_sub_le _ _
    _ ≤ ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)‖
          * ((Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 6
              + ((Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 6)) := by
            gcongr
            · exact norm_smallBetaLocalArchExtractedArc_q1_le_one_sixth_kernelCap_card_sq X N hX
            · calc
                ‖((((X : ℝ) : ℂ))⁻¹) * frozenRawScalarC N (1 : ℝ)‖
                  = ((X : ℝ)⁻¹) * ‖frozenRawScalarC N (1 : ℝ)‖ := by
                      rw [norm_mul, norm_inv]
                      simp [abs_of_pos (show (0 : ℝ) < X by positivity)]
                _ ≤ ((X : ℝ)⁻¹)
                      * ((Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                          * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3) := by
                            gcongr
                            exact norm_frozenRawScalarC_le_one_third_kernelCap_card_sq N
                _ ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                      * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 6 := by
                            have hXhalf : (X : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
                              field_simp [show (X : ℝ) ≠ 0 by positivity]
                              have hXreal : (2 : ℝ) ≤ X := by exact_mod_cast hX
                              nlinarith
                            have hnonneg :
                                0 ≤ (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                                  * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3 := by
                              have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
                                Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
                              positivity
                            have hmul :=
                              mul_le_mul_of_nonneg_right hXhalf hnonneg
                            nlinarith
    _ = ‖((((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))⁻¹)‖
          * ((Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2) / 3) := by ring
    _ ≤ etaFreezeTrivial X N := by
          unfold etaFreezeTrivial
          rw [norm_inv]
          simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos]
          have hw0 : 0 ≤ (Goldbach.AO_WeightMass.weight_mass X)⁻¹ := by positivity
          have hnonneg :
              0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                  * ((Finset.Ico 4 ((N - 2) + 1)).card : ℝ) ^ 2 := by
            have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
              Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
            positivity
          have hthirdnum : ((1 : ℝ) / 3) ≤ 1 := by norm_num
          ring_nf
          have hbase0 :
              0 ≤ (Goldbach.BG_Bank.wScale X)⁻¹ ^ 2
                    * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                    * (((N - 2 - 3 : ℕ) : ℝ) ^ 2) := by
            have hsq0 : 0 ≤ (Goldbach.BG_Bank.wScale X)⁻¹ ^ 2 := by
              exact sq_nonneg ((Goldbach.BG_Bank.wScale X)⁻¹)
            have hcap0 : 0 ≤ Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap :=
              Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg
            have hcard0 : 0 ≤ (((N - 2 - 3 : ℕ) : ℝ) ^ 2) := by
              exact sq_nonneg (((N - 2 - 3 : ℕ) : ℝ))
            exact mul_nonneg (mul_nonneg hsq0 hcap0) hcard0
          have hineq :
              ((1 : ℝ) / 3)
                  * ((Goldbach.BG_Bank.wScale X)⁻¹ ^ 2
                      * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                      * (((N - 2 - 3 : ℕ) : ℝ) ^ 2))
                ≤ (Goldbach.BG_Bank.wScale X)⁻¹ ^ 2
                    * Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
                    * (((N - 2 - 3 : ℕ) : ℝ) ^ 2) := by
            simpa using mul_le_mul_of_nonneg_right hthirdnum hbase0
          simpa [mul_assoc, mul_left_comm, mul_comm] using hineq

theorem AqLocalC_uniform_freeze_trivial
    (X N : ℕ) (hX : 2 ≤ X) :
    ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ ≤ etaFreezeTrivial X N := by
  refine AqLocalC_uniform_freeze_of_q1_and_rescaled_ge2 (X := X) (N := N)
    (ηA := etaFreezeTrivial X N) hX
    (norm_AqLocalC_one_sub_AqFrozenC_one_le_etaFreezeTrivial X N hX)
    ?_
  intro q hq
  exact norm_AqCRescaled_sub_AqFrozenC_le_etaFreezeTrivial_of_two_le X N q hX (Finset.mem_Icc.mp hq).1

private lemma norm_qPhaseFactor_le (q N : ℕ) :
    ‖qPhaseFactor q N‖ ≤ Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [qPhaseFactor, Goldbach.AO_OffDiag.TailBlock.muSq]
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_pos_nat : 0 < Nat.totient q := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  have hphi_pos : 0 < (Nat.totient q : ℝ) := by exact_mod_cast hphi_pos_nat
  have hfrac_nonneg : 0 ≤ (1 / ((Nat.totient q : ℝ) ^ 2) : ℝ) := by positivity
  calc
    ‖qPhaseFactor q N‖
        =
      Goldbach.AO_OffDiag.TailBlock.muSq q
        * (1 / ((Nat.totient q : ℝ) ^ 2))
        * ‖∑ r ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
            Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (r : ℝ) / q))‖ := by
          rw [qPhaseFactor, norm_mul, norm_mul]
          rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.moebius_sq_cast_eq_muSq]
          simp [abs_of_nonneg hmu_nonneg, mul_assoc]
    _ ≤ Goldbach.AO_OffDiag.TailBlock.muSq q
          * (1 / ((Nat.totient q : ℝ) ^ 2))
          * (Nat.totient q : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (by
                calc
                  ‖∑ r ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
                      Goldbach.Cert.MajorArcExponential.e (-((N : ℝ) * (r : ℝ) / q))‖
                    = ‖star (Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC q N)‖ := by
                        rw [Goldbach.Cert.MajorArcStep24MainTermIdentification.phaseSum_neg_eq_star_ramanujanSumC]
                  _ = ‖Goldbach.Cert.MajorArcStep23RamanujanSum.ramanujanSumC q N‖ := by simp
                  _ ≤ (Nat.totient q : ℝ) := by
                        exact Goldbach.Cert.MajorArcStep23RamanujanSum.norm_ramanujanSumC_le_totient q N)
              (mul_nonneg hmu_nonneg hfrac_nonneg)
    _ = Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
          field_simp [show (Nat.totient q : ℝ) ≠ 0 by positivity]

private lemma qaPhaseUpperConst_nonneg :
    0 ≤ Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst := by
  unfold Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst
  refine Finset.sum_nonneg ?_
  intro q hq
  have hmu_nonneg : 0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q := by
    by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq]
  have hphi_nonneg : 0 ≤ (Nat.totient q : ℝ) := by positivity
  exact div_nonneg hmu_nonneg hphi_nonneg

/-- Uniform local freeze control lifts directly to the weighted small-`β` model. -/
theorem norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_weighted_freeze
    {X N : ℕ} {ηAq : ℕ → ℝ}
    (hfreeze :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ ≤ ηAq q) :
    ‖smallBetaModelWeightedQC AqLocalC X N
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
  have hwm_nonneg : 0 ≤ Goldbach.AO_WeightMass.weight_mass X := by
    have hs : 0 ≤ Goldbach.BG_Bank.wScale X := Goldbach.BG_Bank.wScale_nonneg X
    simpa [Goldbach.AO_WeightMass.weight_mass, pow_two] using mul_nonneg hs hs
  calc
    ‖smallBetaModelWeightedQC AqLocalC X N
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      =
    ‖(((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
        * (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
            (AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N)‖ := by
          let w : ℂ := (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ))
          have hsplit :
              smallBetaModelWeightedQC AqLocalC X N
                - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N
                =
              w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                    (AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N) := by
            unfold smallBetaModelWeightedQC
            calc
              w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N)
                  - w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0, AqFrozenC X N q (1 : ℝ) * qPhaseFactor q N)
                =
              w * ((∑ q ∈ Finset.Icc (1 : ℕ) Q0, AqLocalC X N q * qPhaseFactor q N)
                    - (∑ q ∈ Finset.Icc (1 : ℕ) Q0, AqFrozenC X N q (1 : ℝ) * qPhaseFactor q N)) := by
                      ring
              _ =
              w * (∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                    (AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N) := by
                      refine congrArg (fun z : ℂ => w * z) ?_
                      rw [← Finset.sum_sub_distrib]
                      refine Finset.sum_congr rfl ?_
                      intro q hq
                      ring
          simpa [w] using congrArg norm hsplit
    _ = Goldbach.AO_WeightMass.weight_mass X
          * ‖∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              (AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N‖ := by
            rw [norm_mul]
            simp [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              ‖(AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N‖ := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
            gcongr with q hq
            calc
              ‖(AqLocalC X N q - AqFrozenC X N q (1 : ℝ)) * qPhaseFactor q N‖
                  = ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ * ‖qPhaseFactor q N‖ := by
                      rw [norm_mul]
              _ ≤ ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖
                    * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
                      exact mul_le_mul_of_nonneg_left (norm_qPhaseFactor_le q N) (norm_nonneg _)
              _ ≤ ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
                      have hterm_nonneg :
                          0 ≤ Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ) := by
                        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
                        have hphi_pos : 0 < (Nat.totient q : ℝ) := by
                          exact_mod_cast Nat.totient_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hq1)
                        exact div_nonneg
                          (by
                            by_cases hsq : Squarefree q <;> simp [Goldbach.AO_OffDiag.TailBlock.muSq, hsq])
                          (le_of_lt hphi_pos)
                      have hη_nonneg : 0 ≤ ηAq q := by
                        exact le_trans (norm_nonneg _) (hfreeze q hq)
                      exact mul_le_mul_of_nonneg_right (hfreeze q hq) hterm_nonneg

/--
Weighted frozen-model comparison with `q = 1` handled separately and `q ≥ 2` controlled through
the rescaled extracted-gap family.

This is the first useful sharpened theorem surface after the trivial route fails: it keeps the
actual `q`-weighted model norm and pushes the explicit `1 / (qX)` factor from
`AqCRescaled - AqFrozenC` all the way to the final summed bound.
-/
theorem norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_q1_and_weighted_rescaled_gap
    {X N : ℕ} {ηA1 : ℝ} {ηgap : ℕ → ℝ}
    (hX : 2 ≤ X)
    (hq1 :
      ‖AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)‖ ≤ ηA1)
    (hge2 :
      ∀ q ∈ Finset.Icc (2 : ℕ) Q0,
        ‖smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)
            - smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)‖ ≤ ηgap q) :
    ‖smallBetaModelWeightedQC AqLocalC X N
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X
          * (ηA1
              + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                  (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                      * (((q : ℝ) * (X : ℝ))⁻¹) * ηgap q))
                    * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ))) := by
  let ηAq : ℕ → ℝ := fun q =>
    if q = 1 then ηA1
    else (Goldbach.AO_WeightMass.weight_mass X)⁻¹ * (((q : ℝ) * (X : ℝ))⁻¹) * ηgap q
  have hfreeze :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ ≤ ηAq q := by
    intro q hq
    rcases Nat.eq_or_lt_of_le (Finset.mem_Icc.mp hq).1 with rfl | hqgt
    · simp [ηAq, hq1]
    · have hq2 : 2 ≤ q := by omega
      have hq' : q ∈ Finset.Icc (2 : ℕ) Q0 := by
        exact Finset.mem_Icc.mpr ⟨hq2, (Finset.mem_Icc.mp hq).2⟩
      rw [AqLocalC_eq_AqCRescaled_of_two_le hX hq2]
      have hmain :=
        norm_AqCRescaled_sub_AqFrozenC_le_of_rescaled_gap
          (X := X) (N := N) (q := q) (Δ := (1 : ℝ)) (η := ηgap q)
          hX (by omega) (hge2 q hq')
      simpa [ηAq, Nat.ne_of_gt hqgt]
        using hmain
  calc
    ‖smallBetaModelWeightedQC AqLocalC X N
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
          exact norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_weighted_freeze
            (X := X) (N := N) (ηAq := ηAq) hfreeze
    _ =
      Goldbach.AO_WeightMass.weight_mass X
        * ((ηAq 1) * (Goldbach.AO_OffDiag.TailBlock.muSq 1 / (Nat.totient 1 : ℝ))
            + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ))) := by
          have hsplit :
              Finset.Icc (1 : ℕ) Q0 = insert 1 (Finset.Icc (2 : ℕ) Q0) := by
            ext q
            simp [Nat.succ_le_iff]
            omega
          have hnotmem : 1 ∉ Finset.Icc (2 : ℕ) Q0 := by simp
          rw [hsplit, Finset.sum_insert hnotmem]
    _ =
      Goldbach.AO_WeightMass.weight_mass X
        * (ηA1
            + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                    * (((q : ℝ) * (X : ℝ))⁻¹) * ηgap q))
                  * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ))) := by
          have hsum :
              (∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                  ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)))
                =
              ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                  (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                      * (((q : ℝ) * (X : ℝ))⁻¹) * ηgap q))
                    * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            have hqne : q ≠ 1 := by
              have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
              omega
            simp [ηAq, hqne]
          rw [hsum]
          have hη1 : ηAq 1 = ηA1 := by simp [ηAq]
          have hmu1 : Goldbach.AO_OffDiag.TailBlock.muSq 1 = 1 := by
            simp [Goldbach.AO_OffDiag.TailBlock.muSq]
          norm_num [hη1, hmu1]


/--
Weighted frozen-model comparison for the small-`β` major term, with `q = 1` handled separately and
`q ≥ 2` controlled through the rescaled extracted-gap family.
-/
theorem norm_corr_integral_major_Q0_small_sub_frozenModel_le_of_residual_q1_weighted_rescaled_gap
    {X N : ℕ} {ηres ηA1 : ℝ} {ηgap : ℕ → ℝ}
    (hX : 2 ≤ X)
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hres :
      ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖
        ≤ ηres)
    (hq1 :
      ‖AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)‖ ≤ ηA1)
    (hge2 :
      ∀ q ∈ Finset.Icc (2 : ℕ) Q0,
        ‖smallBetaCenteredArchExtractedArcRescaled X N q (1 : ℝ)
            - smallBetaFrozenArchExtractedArcRescaled X N q (1 : ℝ)‖ ≤ ηgap q) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ ηres
          + Goldbach.AO_WeightMass.weight_mass X
              * (ηA1
                  + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                      (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                          * (((q : ℝ) * (X : ℝ))⁻¹) * ηgap q))
                        * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ))) := by
  have hmain :
      ‖smallBetaModelWeightedQC AqLocalC X N
          - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
        ≤ Goldbach.AO_WeightMass.weight_mass X
            * (ηA1
                + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                    (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                        * (((q : ℝ) * (X : ℝ))⁻¹) * ηgap q))
                      * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ))) := by
    exact norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_q1_and_weighted_rescaled_gap
      (X := X) (N := N) (ηA1 := ηA1) (ηgap := ηgap) hX hq1 hge2
  calc
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ ηres
          + ‖smallBetaModelWeightedQC AqLocalC X N
              - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖ := by
            have hbase :
                ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                    - smallBetaModelWeightedQC AqLocalC X N‖ ≤ ηres := by
              rw [Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.corr_integral_major_Q0_small_eq_extracted_add_residual
                (X := X) (N := N) (Δ := (1 : ℝ)) hsep hInner hOuter]
              calc
                ‖(Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
                    + Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ))
                    - smallBetaModelWeightedQC AqLocalC X N‖
                  =
                ‖(Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
                      - smallBetaModelWeightedQC AqLocalC X N)
                    + Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖ := by
                      ring_nf
                _ ≤ ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
                        - smallBetaModelWeightedQC AqLocalC X N‖
                      + ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖ := by
                        simpa using
                          norm_add_le
                            (Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
                              - smallBetaModelWeightedQC AqLocalC X N)
                            (Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ))
                _ ≤ 0 + ηres := by
                        have hextract :
                            ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
                                - smallBetaModelWeightedQC AqLocalC X N‖ ≤ 0 := by
                          rw [smallBetaExtractedWeighted_eq_smallBetaModelWeightedQC_AqLocalC (X := X) (N := N) hX]
                          simp
                        exact add_le_add hextract hres
                _ = ηres := by ring
            calc
              ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                  - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
                ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                      - smallBetaModelWeightedQC AqLocalC X N‖
                    + ‖smallBetaModelWeightedQC AqLocalC X N
                      - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖ := by
                        calc
                          ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                              - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
                            =
                          ‖(Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                                - smallBetaModelWeightedQC AqLocalC X N)
                              + (smallBetaModelWeightedQC AqLocalC X N
                                - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N)‖ := by
                                  ring_nf
                          _ ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                                  - smallBetaModelWeightedQC AqLocalC X N‖
                                + ‖smallBetaModelWeightedQC AqLocalC X N
                                  - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖ := by
                                    simpa using
                                      norm_add_le
                                        (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                                          - smallBetaModelWeightedQC AqLocalC X N)
                                        (smallBetaModelWeightedQC AqLocalC X N
                                          - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N)
              _ ≤ ηres
                    + ‖smallBetaModelWeightedQC AqLocalC X N
                      - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖ := by
                        exact add_le_add_right hbase _
    _ ≤ ηres
          + Goldbach.AO_WeightMass.weight_mass X
              * (ηA1
                  + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                      (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                          * (((q : ℝ) * (X : ℝ))⁻¹) * ηgap q))
                        * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ))) := by
          exact add_le_add_left hmain ηres

/-- Uniform local freeze control lifts directly to the weighted small-`β` model. -/
theorem norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_uniform_freeze
    {X N : ℕ} {ηA : ℝ}
    (hfreeze :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ ≤ ηA) :
    ‖smallBetaModelWeightedQC AqLocalC X N
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X
          * (ηA * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := by
  calc
    ‖smallBetaModelWeightedQC AqLocalC X N
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X
          * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
              ηA * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
            exact norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_weighted_freeze
              (X := X) (N := N) (ηAq := fun _ => ηA) hfreeze
    _ = Goldbach.AO_WeightMass.weight_mass X
          * (ηA * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := by
          rw [← Finset.mul_sum]
          simp [Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst,
            mul_assoc, mul_left_comm, mul_comm]

/-- The exact small-`β` integral is close to the frozen weighted model under residual and freeze bounds. -/
theorem norm_corr_integral_major_Q0_small_sub_frozenModel_le_of_residual_weighted_freeze
    {X N : ℕ} {ηres : ℝ} {ηAq : ℕ → ℝ}
    (hX : 2 ≤ X)
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hres : ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖ ≤ ηres)
    (hfreeze :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ ≤ ηAq q) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ ηres
          + Goldbach.AO_WeightMass.weight_mass X
              * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                  ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
  have hmain :
      ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
          - smallBetaModelWeightedQC AqLocalC X N‖ ≤ ηres := by
    rw [Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.corr_integral_major_Q0_small_eq_extracted_add_residual
      (X := X) (N := N) (Δ := (1 : ℝ)) hsep hInner hOuter]
    calc
      ‖(Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
          + Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ))
          - smallBetaModelWeightedQC AqLocalC X N‖
        =
      ‖(Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
            - smallBetaModelWeightedQC AqLocalC X N)
          + Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖ := by
            ring_nf
      _ ≤ ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
              - smallBetaModelWeightedQC AqLocalC X N‖
            + ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖ := by
              simpa using
                norm_add_le
                  (Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
                    - smallBetaModelWeightedQC AqLocalC X N)
                  (Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ))
      _ ≤ 0 + ηres := by
              have hextract :
                  ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaExtractedWeighted X N (1 : ℝ)
                      - smallBetaModelWeightedQC AqLocalC X N‖ ≤ 0 := by
                    rw [smallBetaExtractedWeighted_eq_smallBetaModelWeightedQC_AqLocalC (X := X) (N := N) hX]
                    simp
              exact add_le_add hextract hres
      _ = ηres := by ring
  calc
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
            - smallBetaModelWeightedQC AqLocalC X N‖
          + ‖smallBetaModelWeightedQC AqLocalC X N
              - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖ := by
            calc
              ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                  - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
                =
              ‖(Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                    - smallBetaModelWeightedQC AqLocalC X N)
                  + (smallBetaModelWeightedQC AqLocalC X N
                    - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N)‖ := by
                    ring_nf
              _ ≤ ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                      - smallBetaModelWeightedQC AqLocalC X N‖
                    + ‖smallBetaModelWeightedQC AqLocalC X N
                      - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖ := by
                        simpa using
                          norm_add_le
                            (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
                              - smallBetaModelWeightedQC AqLocalC X N)
                            (smallBetaModelWeightedQC AqLocalC X N
                              - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N)
    _ ≤ ηres
          + Goldbach.AO_WeightMass.weight_mass X
              * ∑ q ∈ Finset.Icc (1 : ℕ) Q0,
                  ηAq q * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)) := by
          exact add_le_add hmain
            (norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_weighted_freeze
              (X := X) (N := N) hfreeze)

/-- The exact small-`β` integral is close to the frozen weighted model under residual and freeze bounds. -/
theorem norm_corr_integral_major_Q0_small_sub_frozenModel_le_of_residual_freeze
    {X N : ℕ} {ηres ηA : ℝ}
    (hX : 2 ≤ X)
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hres : ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖ ≤ ηres)
    (hfreeze :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ‖AqLocalC X N q - AqFrozenC X N q (1 : ℝ)‖ ≤ ηA) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ ηres
          + Goldbach.AO_WeightMass.weight_mass X
              * (ηA * Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst) := by
  simpa [Finset.mul_sum,
    Goldbach.BankPieces.Cert.ProjectedConstGapBridge.qaPhaseUpperConst,
    mul_assoc, mul_left_comm, mul_comm] using
    (norm_corr_integral_major_Q0_small_sub_frozenModel_le_of_residual_weighted_freeze
      (X := X) (N := N) (ηres := ηres) (ηAq := fun _ => ηA)
      hX hsep hInner hOuter hres hfreeze)

/--
Sharpened weighted frozen-model comparison using the explicit `1 / (qX)` oscillation gain for
`q ≥ 2`, while still handling `q = 1` separately.
-/
theorem norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_q1_and_linear_rescaled_gap
    {X N : ℕ} {ηA1 : ℝ}
    (hX : 4 ≤ X)
    (hq1 :
      ‖AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)‖ ≤ ηA1) :
    ‖smallBetaModelWeightedQC AqLocalC X N
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ Goldbach.AO_WeightMass.weight_mass X
          * (ηA1
              + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                  (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                      * (((q : ℝ) * (X : ℝ))⁻¹) * etaLinearRescaledGap X N q)
                    * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)))) := by
  refine
    norm_smallBetaModelWeightedQC_sub_AqFrozenC_le_of_q1_and_weighted_rescaled_gap
      (X := X) (N := N) (ηA1 := ηA1) (ηgap := etaLinearRescaledGap X N)
      (show 2 ≤ X by omega) hq1 ?_
  intro q hq
  simpa [etaLinearRescaledGap] using
    norm_smallBetaCenteredArchExtractedArcRescaled_sub_frozen_le_linear_q_inv hX
    ((Finset.mem_Icc.mp hq).1)

/--
Sharpened small-`β` major-term comparison using the explicit `1 / (qX)` oscillation gain for
`q ≥ 2`, while still handling `q = 1` separately.
-/
theorem norm_corr_integral_major_Q0_small_sub_frozenModel_le_of_residual_q1_linear_rescaled_gap
    {X N : ℕ} {ηres ηA1 : ℝ}
    (hX : 4 ≤ X)
    (hsep : Goldbach.Cert.MajorArcStep24IntegralExtraction.SepQ0 X (1 : ℝ))
    (hInner :
      ∀ β : ℝ,
        IntervalIntegrable
          (fun α : ℝ => Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α)
          volume (0 : ℝ) (1 : ℝ))
    (hOuter :
      ∀ q ∈ Finset.Icc (1 : ℕ) Q0, ∀ a ∈ Goldbach.Cert.MajorArcStep23RamanujanSum.Rcop q,
        IntervalIntegrable
          (fun β : ℝ =>
            Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
              Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC) *
                (∫ α in (0 : ℝ)..(1 : ℝ),
                  (Goldbach.Cert.MajorArcStep24IntegralExtraction.arcSetTextbook X q a (1 : ℝ)).indicator
                    (fun α =>
                      Goldbach.Cert.MajorArcModules.IntegralPipeline.innerIntegrand X N β α) α)) β)
          volume Goldbach.Cert.MajorArcModules.BetaInterval.aβ
            Goldbach.Cert.MajorArcModules.BetaInterval.bβ)
    (hres :
      ‖Goldbach.BankPieces.Cert.RawScaleSmallBetaExtracted.smallBetaResidualWeighted X N (1 : ℝ)‖
        ≤ ηres)
    (hq1 :
      ‖AqLocalC X N 1 - AqFrozenC X N 1 (1 : ℝ)‖ ≤ ηA1) :
    ‖Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.corr_integral_major_Q0_small X N (1 : ℝ)
        - smallBetaModelWeightedQC (fun X N q => AqFrozenC X N q (1 : ℝ)) X N‖
      ≤ ηres
          + Goldbach.AO_WeightMass.weight_mass X
              * (ηA1
                  + ∑ q ∈ Finset.Icc (2 : ℕ) Q0,
                      (((Goldbach.AO_WeightMass.weight_mass X)⁻¹
                          * (((q : ℝ) * (X : ℝ))⁻¹) * etaLinearRescaledGap X N q)
                        * (Goldbach.AO_OffDiag.TailBlock.muSq q / (Nat.totient q : ℝ)))) := by
  refine
    norm_corr_integral_major_Q0_small_sub_frozenModel_le_of_residual_q1_weighted_rescaled_gap
      (X := X) (N := N) (ηres := ηres) (ηA1 := ηA1) (ηgap := etaLinearRescaledGap X N)
      (show 2 ≤ X by omega) hsep hInner hOuter hres hq1 ?_
  intro q hq
  simpa [etaLinearRescaledGap] using
    norm_smallBetaCenteredArchExtractedArcRescaled_sub_frozen_le_linear_q_inv hX
    ((Finset.mem_Icc.mp hq).1)

end

end Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
