import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm
import Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
import Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
import Goldbach.Cert.MajorArcModules.Q0FinitePairwiseEnergy

namespace Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets

open scoped BigOperators

open Complex
open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

open Goldbach.BankPieces.Cert.RawScaleSmallBetaFreeze
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassLowRankMainTerm
open Goldbach.Cert.MajorArcModules.Q0MajorWindowBounds
open Goldbach.Cert.MajorArcModules.Q0MinorHalfMassShellRecentering
open Goldbach.Cert.MajorArcModules.Q0FinitePairwiseEnergy

noncomputable section

private abbrev UC : Type := Goldbach.Cert.MajorArcStep7FourierOrthogonality.UC

private lemma card_evenIn_ne_zero {X : ℕ} (hX : X0 ≤ X) :
    (EvenIn X H).card ≠ 0 := by
  exact Finset.card_ne_zero.mpr ⟨canonicalEvenWindowPoint X, canonicalEvenWindowPoint_mem_even_window hX⟩

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

private lemma sum_mem_const_eq_card_mul
    (s : Finset ℕ) (c : ℝ) :
    (∑ n ∈ s, c) = (s.card : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]

private lemma sum_mem_const_eq_card_mul_complex
    (s : Finset ℕ) (c : ℂ) :
    (∑ n ∈ s, c) = (s.card : ℂ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The exact corrected `q = 1` integral defect block at the freeze seam. -/
noncomputable def canonicalCorrectedFreezeIntegralDoubleSumDefect
    (X N : ℕ) : ℂ :=
  ((((X : ℝ) : ℂ))⁻¹)
    * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X N u β) β)

/-- The exact weighted `q ≥ 2` freeze defect block. -/
noncomputable def canonicalCorrectedFreezeWeightedGe2Defect
    (X N : ℕ) : ℂ :=
  (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * weightedFreezeDefectGe2C X N

/-- Centered corrected `q = 1` integral defect on the canonical even window. -/
noncomputable def centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect
    (X N : ℕ) : ℂ :=
  canonicalCorrectedFreezeIntegralDoubleSumDefect X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalCorrectedFreezeIntegralDoubleSumDefect X M

/-- Centered weighted `q ≥ 2` freeze defect on the canonical even window. -/
noncomputable def centeredCanonicalCorrectedFreezeWeightedGe2Defect
    (X N : ℕ) : ℂ :=
  canonicalCorrectedFreezeWeightedGe2Defect X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalCorrectedFreezeWeightedGe2Defect X M

/-- Centered corrected principal half-gap on the canonical even window. -/
noncomputable def centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected
    (X N : ℕ) : ℂ :=
  smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M

/-- Window energy of the centered corrected `q = 1` integral defect. -/
noncomputable def centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N‖ ^ 2

/-- Window energy of the centered weighted `q ≥ 2` freeze defect. -/
noncomputable def centeredCanonicalCorrectedFreezeWeightedGe2DefectWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalCorrectedFreezeWeightedGe2Defect X N‖ ^ 2

/-- Window energy of the centered corrected principal half-gap. -/
noncomputable def centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖ ^ 2

/-- Pairwise window energy of the raw corrected principal half-gap. -/
noncomputable def canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H, ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      - smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ ^ 2

/-- Pairwise-difference local principal-arc half integral. -/
noncomputable def canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff
    (X N M : ℕ) : ℂ :=
  (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ),
          Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X N 1 u β) β)
    -
  (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
      Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ),
          Goldbach.BankPieces.Cert.RawScaleSmallBetaLocalFactor.smallBetaRescaledArchShell X M 1 u β) β)

/-- Pairwise-difference corrected frozen principal-arc half integral. -/
noncomputable def canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff
    (X N M : ℕ) : ℂ :=
  smallBetaPhaseCorrectedFrozenArchExtractedArcRescaledHalfQ1 X N
    - smallBetaPhaseCorrectedFrozenArchExtractedArcRescaledHalfQ1 X M

/-- The paired two-sided-shift `q = 1` box sum on the shifted square `range (N - 5)^2`. -/
noncomputable def canonicalQ1TwoSidedShiftRangeSquareSum
    (X N : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N - 5),
    ∑ k ∈ Finset.range (N - 5), q1TwoSidedShiftRangeTerm X N u β j k

/--
The common-square part of the difference between the two-sided-shift boxes for `N ≤ M`.

This is the exact interior contribution on the shared square `range (N - 5)^2`.
-/
noncomputable def canonicalQ1TwoSidedShiftCommonSquareDiff
    (X N M : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N - 5),
    ∑ k ∈ Finset.range (N - 5),
      (q1TwoSidedShiftRangeTerm X N u β j k - q1TwoSidedShiftRangeTerm X M u β j k)

/-- The outer `j`-strip added when enlarging `range (N - 5)^2` to `range (M - 5)^2`. -/
noncomputable def canonicalQ1TwoSidedShiftOuterJStrip
    (X N M : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.Ico (N - 5) (M - 5),
    ∑ k ∈ Finset.range (M - 5), q1TwoSidedShiftRangeTerm X M u β j k

/-- The outer `k`-strip added when enlarging `range (N - 5)^2` to `range (M - 5)^2`. -/
noncomputable def canonicalQ1TwoSidedShiftOuterKStrip
    (X N M : ℕ) (u β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N - 5),
    ∑ k ∈ Finset.Ico (N - 5) (M - 5), q1TwoSidedShiftRangeTerm X M u β j k

/-- Pairwise window energy of the local principal-arc half integral. -/
noncomputable def canonicalSmallBetaRescaledArchHalfQ1PairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H, ‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M‖ ^ 2

/-- Pairwise window energy of the corrected frozen principal-arc half integral. -/
noncomputable def canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H,
    ∑ M ∈ EvenIn X H, ‖canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖ ^ 2

/-- Coarse uniform pointwise upper for the corrected principal half-gap on the even window. -/
noncomputable def canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper
    (X : ℕ) : ℝ :=
  Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
    * ((((X + H : ℕ) : ℝ) ^ 2) * (((2 * Real.pi * ((101 : ℝ) / 100)) ^ 2))) / 12

/-- Local centered alias for the corrected freeze discrepancy. -/
noncomputable def centeredCanonicalCorrectedFreezeDiscrepancyAux
    (X N : ℕ) : ℂ :=
  canonicalCorrectedFreezeDiscrepancy X N
    - ((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, canonicalCorrectedFreezeDiscrepancy X M

/-- Local window energy for the centered corrected freeze discrepancy. -/
noncomputable def centeredCanonicalCorrectedFreezeDiscrepancyAuxWindowEnergy
    (X : ℕ) : ℝ :=
  ∑ N ∈ EvenIn X H, ‖centeredCanonicalCorrectedFreezeDiscrepancyAux X N‖ ^ 2

theorem canonicalCorrectedFreezeIntegralDoubleSumDefect_eq_Xinv_mul_gap
    (X N : ℕ) :
    canonicalCorrectedFreezeIntegralDoubleSumDefect X N
      =
    ((((X : ℝ) : ℂ))⁻¹) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N := by
  unfold canonicalCorrectedFreezeIntegralDoubleSumDefect
  rw [smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_integral_doubleSumDefect]

theorem centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect_eq_Xinv_mul_gap
    (X N : ℕ) :
    centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N
      =
    ((((X : ℝ) : ℂ))⁻¹) * centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N := by
  unfold centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected
  rw [canonicalCorrectedFreezeIntegralDoubleSumDefect_eq_Xinv_mul_gap]
  have hsum :
      ∑ M ∈ EvenIn X H, canonicalCorrectedFreezeIntegralDoubleSumDefect X M
        =
      ((((X : ℝ) : ℂ))⁻¹)
        * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M := by
    calc
      ∑ M ∈ EvenIn X H, canonicalCorrectedFreezeIntegralDoubleSumDefect X M
          =
        ∑ M ∈ EvenIn X H,
          ((((X : ℝ) : ℂ))⁻¹) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X M := by
            refine Finset.sum_congr rfl ?_
            intro M hM
            rw [canonicalCorrectedFreezeIntegralDoubleSumDefect_eq_Xinv_mul_gap]
      _ =
        ((((X : ℝ) : ℂ))⁻¹)
          * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M := by
            rw [Finset.mul_sum]
  rw [hsum]
  ring_nf

theorem norm_canonicalCorrectedFreezeIntegralDoubleSumDefect_le_quadratic
    (X N : ℕ) :
    ‖canonicalCorrectedFreezeIntegralDoubleSumDefect X N‖
      ≤
    ‖(((X : ℝ) : ℂ))⁻¹‖
      * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2)) / 12) := by
  rw [canonicalCorrectedFreezeIntegralDoubleSumDefect_eq_Xinv_mul_gap, norm_mul]
  gcongr
  exact norm_smallBetaRescaledGapExtractedArcHalfQ1Corrected_le_quadratic (X := X) (N := N)

theorem norm_smallBetaRescaledGapExtractedArcHalfQ1Corrected_le_pointwiseUpper
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖
      ≤
    canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X := by
  have hraw := norm_smallBetaRescaledGapExtractedArcHalfQ1Corrected_le_quadratic (X := X) (N := N)
  have hNle : (N : ℝ) ≤ ((X + H : ℕ) : ℝ) := by
    exact_mod_cast le_X_add_H_of_mem_EvenIn (X := X) (N := N) hN
  have hXleN : (X : ℝ) ≤ N := by
    exact_mod_cast X_le_of_mem_EvenIn (X := X) (N := N) hN
  have hNge5 : (5 : ℕ) ≤ N := by
    exact le_trans (by decide : 5 ≤ X0) (le_trans hX (X_le_of_mem_EvenIn (X := X) (N := N) hN))
  have hsubsq :
      ((N - 5 : ℝ) ^ 2) ≤ (((X + H : ℕ) : ℝ) ^ 2) := by
    have hsuble : (N - 5 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N 5
    have hsubnonneg : 0 ≤ (N - 5 : ℝ) := by
      have hNge5R : (5 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hNge5
      linarith
    have hNsq : ((N - 5 : ℝ) ^ 2) ≤ (N : ℝ) ^ 2 := by
      nlinarith
    have hNsq_le : (N : ℝ) ^ 2 ≤ (((X + H : ℕ) : ℝ) ^ 2) := by
      have hXHnonneg : 0 ≤ (((X + H : ℕ) : ℝ)) := by positivity
      nlinarith
    exact le_trans hNsq hNsq_le
  have hratio :
      (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2) ≤ ((2 * Real.pi * ((101 : ℝ) / 100)) ^ 2) := by
    have hfrac := N_div_X_le_101_over_100 (X := X) (N := N) hX hN
    have hXpos : 0 < (X : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by decide : 0 < X0) hX
    have hfrac_nonneg : 0 ≤ (N : ℝ) / (X : ℝ) := by
      exact div_nonneg (by positivity) hXpos.le
    have hmul :
        ((2 * Real.pi * (N : ℝ)) / (X : ℝ))
          ≤
        (2 * Real.pi) * ((101 : ℝ) / 100) := by
      calc
        ((2 * Real.pi * (N : ℝ)) / (X : ℝ))
            = (2 * Real.pi) * ((N : ℝ) / (X : ℝ)) := by
                rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
        _ ≤ (2 * Real.pi) * ((101 : ℝ) / 100) := by
              exact mul_le_mul_of_nonneg_left hfrac (by positivity)
    have hleft_nonneg : 0 ≤ ((2 * Real.pi * (N : ℝ)) / (X : ℝ)) := by
      positivity
    have hright_nonneg : 0 ≤ (2 * Real.pi) * ((101 : ℝ) / 100) := by
      positivity
    have habs :
        |((2 * Real.pi * (N : ℝ)) / (X : ℝ))|
          ≤
        |(2 * Real.pi) * ((101 : ℝ) / 100)| := by
      rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
      exact hmul
    exact sq_le_sq.mpr habs
  unfold canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper
  have hprod :
      ((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2)
        ≤
      (((X + H : ℕ) : ℝ) ^ 2) * ((2 * Real.pi * ((101 : ℝ) / 100)) ^ 2) := by
    exact mul_le_mul hsubsq hratio (by positivity) (by positivity)
  have hmid :
      (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * (((N - 5 : ℝ) ^ 2) * (((2 * Real.pi * (N : ℝ)) / (X : ℝ)) ^ 2))) / 12
        ≤
      (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((((X + H : ℕ) : ℝ) ^ 2) * ((2 * Real.pi * ((101 : ℝ) / 100)) ^ 2))) / 12 := by
    exact
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod
          Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap_nonneg)
        (by positivity)
  exact le_trans hraw hmid

theorem sum_centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_zero
    (X : ℕ) :
    ∑ N ∈ EvenIn X H, centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N = 0 := by
  unfold centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected
  by_cases hcard : (EvenIn X H).card = 0
  · have hempty : EvenIn X H = ∅ := Finset.card_eq_zero.mp hcard
    simp [hempty]
  · have hcardC : ((EvenIn X H).card : ℂ) ≠ 0 := by
      exact_mod_cast hcard
    rw [Finset.sum_sub_distrib]
    rw [sum_mem_const_eq_card_mul_complex]
    calc
      ∑ N ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
          -
        ((EvenIn X H).card : ℂ)
          * (((EvenIn X H).card : ℂ)⁻¹
              * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M)
        =
      ∑ N ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
          -
        ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M := by
            field_simp [hcardC]
      _ = 0 := by ring

theorem centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected_sub_eq_raw_sub
    (X N M : ℕ) :
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      - centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X M
        =
    smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      - smallBetaRescaledGapExtractedArcHalfQ1Corrected X M := by
  unfold centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected
  ring

theorem smallBetaRescaledGapExtractedArcHalfQ1Corrected_sub_eq_pairwiseDiff
    (X N M : ℕ) :
    smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
      - smallBetaRescaledGapExtractedArcHalfQ1Corrected X M
        =
    canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M
      - canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M := by
  rw [smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_sub (X := X) (N := N)]
  rw [smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_sub (X := X) (N := M)]
  unfold canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff
    canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff
  ring_nf

theorem two_mul_smallBetaRescaledGapExtractedArcHalfQ1Corrected_sub_eq_twoSidedIntegral_sub
    (X N M : ℕ) :
    (2 : ℂ)
      * (smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
          - smallBetaRescaledGapExtractedArcHalfQ1Corrected X M)
        =
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
            * canonicalQ1TwoSidedShiftRangeSquareSum X N u β) β)
      -
    (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
        Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
      Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
        ∫ u in (0 : ℝ)..(1 : ℝ),
          (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
            * canonicalQ1TwoSidedShiftRangeSquareSum X M u β) β) := by
  calc
    (2 : ℂ) * (smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
          - smallBetaRescaledGapExtractedArcHalfQ1Corrected X M)
        =
      (2 : ℂ) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
        - (2 : ℂ) * smallBetaRescaledGapExtractedArcHalfQ1Corrected X M := by ring
    _ =
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ),
            (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
              * canonicalQ1TwoSidedShiftRangeSquareSum X N u β) β)
      -
      (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
          Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
        Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
          ∫ u in (0 : ℝ)..(1 : ℝ),
            (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC ((β : ℝ) : UC))
              * canonicalQ1TwoSidedShiftRangeSquareSum X M u β) β) := by
          simp [canonicalQ1TwoSidedShiftRangeSquareSum,
            two_mul_smallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_integral_twoSided]

private theorem double_sum_range_square_sub_eq_common_minus_strips
    (f g : ℕ → ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, f j k)
      -
    (∑ j ∈ Finset.range b, ∑ k ∈ Finset.range b, g j k)
      =
    (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, (f j k - g j k))
      -
    (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k)
      -
    (∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico a b, g j k) := by
  have hsplit :
      (∑ j ∈ Finset.range b, ∑ k ∈ Finset.range b, g j k)
        =
      (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, g j k)
        +
      (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k)
        +
      (∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico a b, g j k) := by
    calc
      (∑ j ∈ Finset.range b, ∑ k ∈ Finset.range b, g j k)
          =
        (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range b, g j k)
          + (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k) := by
            rw [← Finset.sum_range_add_sum_Ico _ hab]
      _ =
        (∑ j ∈ Finset.range a, ((∑ k ∈ Finset.range a, g j k)
          + (∑ k ∈ Finset.Ico a b, g j k)))
          + (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k) := by
            refine congrArg (fun z : ℂ => z + (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k)) ?_
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [← Finset.sum_range_add_sum_Ico _ hab]
      _ =
        ((∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, g j k)
          + (∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico a b, g j k))
          + (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k) := by
            rw [Finset.sum_add_distrib]
      _ =
        (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, g j k)
          + (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k)
          + (∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico a b, g j k) := by
            ring
  have hdiff :
      (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, f j k)
        - (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, g j k)
        =
      ∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, (f j k - g j k) := by
        calc
          (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, f j k)
              - (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, g j k)
              =
            ∑ j ∈ Finset.range a,
              ((∑ k ∈ Finset.range a, f j k) - (∑ k ∈ Finset.range a, g j k)) := by
                rw [Finset.sum_sub_distrib]
          _ =
            ∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, (f j k - g j k) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [Finset.sum_sub_distrib]
  rw [hsplit]
  calc
    (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, f j k) -
        ((∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, g j k)
          + (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k)
          + (∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico a b, g j k))
        =
      ((∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, f j k)
          - (∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, g j k))
        - (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k)
        - (∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico a b, g j k) := by
            ring
    _ =
      ∑ j ∈ Finset.range a, ∑ k ∈ Finset.range a, (f j k - g j k)
        - (∑ j ∈ Finset.Ico a b, ∑ k ∈ Finset.range b, g j k)
        - (∑ j ∈ Finset.range a, ∑ k ∈ Finset.Ico a b, g j k) := by
            rw [hdiff]

theorem canonicalQ1TwoSidedShiftRangeSquareSum_sub_eq_common_minus_strips
    {X N M : ℕ} (hNM : N ≤ M) (u β : ℝ) :
    canonicalQ1TwoSidedShiftRangeSquareSum X N u β
      - canonicalQ1TwoSidedShiftRangeSquareSum X M u β
        =
    canonicalQ1TwoSidedShiftCommonSquareDiff X N M u β
      - canonicalQ1TwoSidedShiftOuterJStrip X N M u β
      - canonicalQ1TwoSidedShiftOuterKStrip X N M u β := by
  unfold canonicalQ1TwoSidedShiftRangeSquareSum
    canonicalQ1TwoSidedShiftCommonSquareDiff
    canonicalQ1TwoSidedShiftOuterJStrip
    canonicalQ1TwoSidedShiftOuterKStrip
  exact double_sum_range_square_sub_eq_common_minus_strips
    (f := fun j k => q1TwoSidedShiftRangeTerm X N u β j k)
    (g := fun j k => q1TwoSidedShiftRangeTerm X M u β j k)
    (hab := Nat.sub_le_sub_right hNM 5)

theorem kernel_mul_canonicalQ1TwoSidedShiftRangeSquareSum_sub_eq_common_minus_strips
    {X N M : ℕ} (hNM : N ≤ M) (u β : ℝ) :
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftRangeSquareSum X N u β
      -
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftRangeSquareSum X M u β
        =
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftCommonSquareDiff X N M u β
      -
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftOuterJStrip X N M u β
      -
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
        * canonicalQ1TwoSidedShiftOuterKStrip X N M u β := by
  rw [← mul_sub]
  rw [canonicalQ1TwoSidedShiftRangeSquareSum_sub_eq_common_minus_strips hNM]
  ring

theorem canonicalQ1TwoSidedShiftBoundaryUIntegralDiff_eq_common_minus_strips
    {X N M : ℕ} (hNM : N ≤ M) (β : ℝ) :
    (∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftRangeSquareSum X N u β
        -
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftRangeSquareSum X M u β)
      =
    (∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonSquareDiff X N M u β
        -
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftOuterJStrip X N M u β
        -
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftOuterKStrip X N M u β) := by
  refine intervalIntegral.integral_congr_ae ?_
  exact Filter.Eventually.of_forall <| fun u _ => by
    rw [kernel_mul_canonicalQ1TwoSidedShiftRangeSquareSum_sub_eq_common_minus_strips hNM]

theorem canonicalQ1TwoSidedShiftBoundaryBetaIntegrandDiff_eq_common_minus_strips
    {X N M : ℕ} (hNM : N ≤ M) (β : ℝ) :
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftRangeSquareSum X N u β
        -
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftRangeSquareSum X M u β) β
      =
    Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
      ∫ u in (0 : ℝ)..(1 : ℝ),
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftCommonSquareDiff X N M u β
        -
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftOuterJStrip X N M u β
        -
        (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
          * canonicalQ1TwoSidedShiftOuterKStrip X N M u β) β := by
  by_cases hβ : β ∈ Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet
  · simp [hβ, canonicalQ1TwoSidedShiftBoundaryUIntegralDiff_eq_common_minus_strips, hNM]
  · simp [hβ]

noncomputable def canonicalQ1TwoSidedShiftBoundaryCommonUIntegral
    (X N M : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftCommonSquareDiff X N M u β

noncomputable def canonicalQ1TwoSidedShiftBoundaryOuterJUIntegral
    (X N M : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftOuterJStrip X N M u β

noncomputable def canonicalQ1TwoSidedShiftBoundaryOuterKUIntegral
    (X N M : ℕ) (β : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..(1 : ℝ),
    (Goldbach.Cert.MajorArcStep10RLSmoothIntegral.kernelPolyC (β : UC))
      * canonicalQ1TwoSidedShiftOuterKStrip X N M u β

noncomputable def canonicalQ1TwoSidedShiftBoundaryBetaIntegrandUpper
    (X N M : ℕ) (β : ℝ) : ℝ :=
  ‖canonicalQ1TwoSidedShiftBoundaryCommonUIntegral X N M β‖
    + ‖canonicalQ1TwoSidedShiftBoundaryOuterJUIntegral X N M β‖
    + ‖canonicalQ1TwoSidedShiftBoundaryOuterKUIntegral X N M β‖

noncomputable def canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseUpper
    (X N M : ℕ) : ℝ :=
  2 * ‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M‖ ^ 2
    + 2 * ‖canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖ ^ 2

private theorem canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwise_sq_le
    (X N M : ℕ) :
    ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
        - smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ ^ 2
      ≤ canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseUpper X N M := by
  rw [smallBetaRescaledGapExtractedArcHalfQ1Corrected_sub_eq_pairwiseDiff]
  unfold canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseUpper
  have hnorm :=
    norm_add_le
      (canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M)
      (-canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M)
  have hsq1 :
      ‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M
          - canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖ ^ 2
        ≤
      (‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M‖
          + ‖canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖) ^ 2 := by
    have habs :
        |‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M
            - canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖|
          ≤
        |‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M‖
            + ‖canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖| := by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
      simpa [sub_eq_add_neg, norm_neg] using hnorm
    exact sq_le_sq.mpr habs
  have hsq2 :
      (‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M‖
          + ‖canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖) ^ 2
        ≤
      2 * ‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M‖ ^ 2
        + 2 * ‖canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖ ^ 2 := by
    have hnonneg :
        0 ≤
          (‖canonicalSmallBetaRescaledArchHalfQ1PairwiseDiff X N M‖
            - ‖canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseDiff X N M‖) ^ 2 := by
      exact sq_nonneg _
    nlinarith
  exact le_trans hsq1 hsq2

theorem canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy_eq
    (X : ℕ) :
    canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy X
      =
    2 * (((EvenIn X H).card : ℝ)
      * centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X) := by
  unfold canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy
  calc
    ∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H, ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
          - smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ ^ 2
      =
    ∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H, ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N
          - centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro N hN
            refine Finset.sum_congr rfl ?_
            intro M hM
            rw [centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected_sub_eq_raw_sub]
  _ =
    2 * (((EvenIn X H).card : ℝ)
      * ∑ N ∈ EvenIn X H, ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖ ^ 2) := by
          exact
            sum_pairwise_norm_sq_eq_two_card_mul_sum_norm_sq_of_sum_eq_zero
              (s := EvenIn X H)
              (f := fun N => centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N)
              (hzero := sum_centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected_eq_zero X)

theorem canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy_le
    (X : ℕ) :
    canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy X
      ≤
    2 * canonicalSmallBetaRescaledArchHalfQ1PairwiseWindowEnergy X
      + 2 * canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseWindowEnergy X := by
  calc
    canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy X
        ≤
      ∑ N ∈ EvenIn X H,
        ∑ M ∈ EvenIn X H,
          canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseUpper X N M := by
            unfold canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy
            refine Finset.sum_le_sum ?_
            intro N hN
            refine Finset.sum_le_sum ?_
            intro M hM
            exact canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwise_sq_le X N M
    _ =
      2 * canonicalSmallBetaRescaledArchHalfQ1PairwiseWindowEnergy X
        + 2 * canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseWindowEnergy X := by
          unfold canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseUpper
            canonicalSmallBetaRescaledArchHalfQ1PairwiseWindowEnergy
            canonicalSmallBetaPhaseCorrectedFrozenArchHalfQ1PairwiseWindowEnergy
          simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

private theorem norm_centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected_le_two_mul
    {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H)
    {B : ℝ}
    (hB : ∀ {M : ℕ}, M ∈ EvenIn X H →
      ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ ≤ B) :
    ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖ ≤ 2 * B := by
  have hBnonneg : 0 ≤ B := le_trans (norm_nonneg _) (hB hN)
  have havg :
      ‖((EvenIn X H).card : ℂ)⁻¹
          * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖
        ≤ B := by
    have hcard_nat : (EvenIn X H).card ≠ 0 := card_evenIn_ne_zero hX
    have hcardR : (((EvenIn X H).card : ℝ)) ≠ 0 := by
      exact_mod_cast hcard_nat
    have hsum_norm :
        ‖∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖
          ≤
        ∑ M ∈ EvenIn X H, ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ := by
      simpa using
        (norm_sum_le (s := EvenIn X H)
          (f := fun M => smallBetaRescaledGapExtractedArcHalfQ1Corrected X M))
    have hsum_bound :
        ∑ M ∈ EvenIn X H, ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖
          ≤
        ((EvenIn X H).card : ℝ) * B := by
      calc
        ∑ M ∈ EvenIn X H, ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖
            ≤
          ∑ _M ∈ EvenIn X H, B := by
              refine Finset.sum_le_sum ?_
              intro M hM
              exact hB hM
        _ = ((EvenIn X H).card : ℝ) * B := by
              rw [sum_mem_const_eq_card_mul]
    calc
      ‖((EvenIn X H).card : ℂ)⁻¹
          * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖
          =
        ‖((EvenIn X H).card : ℂ)⁻¹‖
          * ‖∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ := by
            rw [norm_mul]
      _ ≤
        ‖((EvenIn X H).card : ℂ)⁻¹‖
          * ∑ M ∈ EvenIn X H, ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ := by
            exact mul_le_mul_of_nonneg_left hsum_norm (norm_nonneg _)
      _ ≤
        ‖((EvenIn X H).card : ℂ)⁻¹‖ * (((EvenIn X H).card : ℝ) * B) := by
            exact mul_le_mul_of_nonneg_left hsum_bound (norm_nonneg _)
      _ = B := by
            rw [norm_inv, Complex.norm_natCast]
            calc
              (((EvenIn X H).card : ℝ)⁻¹) * (((EvenIn X H).card : ℝ) * B)
                  = ((((EvenIn X H).card : ℝ)⁻¹) * ((EvenIn X H).card : ℝ)) * B := by ring
              _ = 1 * B := by rw [inv_mul_cancel₀ hcardR]
              _ = B := by ring
  have hmain := norm_sub_le
      (smallBetaRescaledGapExtractedArcHalfQ1Corrected X N)
      (((EvenIn X H).card : ℂ)⁻¹
        * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M)
  have hrawN := hB hN
  calc
    ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖
        =
      ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X N
        - ((EvenIn X H).card : ℂ)⁻¹
            * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ := by
          rfl
    _ ≤
      ‖smallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖
        +
      ‖((EvenIn X H).card : ℂ)⁻¹
          * ∑ M ∈ EvenIn X H, smallBetaRescaledGapExtractedArcHalfQ1Corrected X M‖ := hmain
    _ ≤ B + B := add_le_add hrawN havg
    _ = 2 * B := by ring

theorem centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy_le_card_mul_pointwiseUpper_sq
    {X : ℕ} (hX : X0 ≤ X) :
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X
      ≤
    ((EvenIn X H).card : ℝ)
      * (2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X) ^ 2 := by
  calc
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X
        ≤
      ∑ N ∈ EvenIn X H,
        (2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X) ^ 2 := by
          unfold centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy
          refine Finset.sum_le_sum ?_
          intro N hN
          have hpt :
              ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖
                ≤
              2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X := by
            apply norm_centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected_le_two_mul
              (hX := hX) (hN := hN)
            intro M hM
            exact norm_smallBetaRescaledGapExtractedArcHalfQ1Corrected_le_pointwiseUpper hX hM
          nlinarith [hpt, norm_nonneg (centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N)]
    _ =
      ((EvenIn X H).card : ℝ)
        * (2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X) ^ 2 := by
          rw [sum_mem_const_eq_card_mul]

theorem centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy_le_H_add_one_mul_pointwiseUpper_sq
    {X : ℕ} (hX : X0 ≤ X) :
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X
      ≤
    ((H + 1 : ℕ) : ℝ)
      * (2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X) ^ 2 := by
  have hmain :=
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy_le_card_mul_pointwiseUpper_sq
      (X := X) hX
  have hcard : ((EvenIn X H).card : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by
    exact_mod_cast card_evenIn_le_H_add_one X
  have hsq_nonneg : 0 ≤ (2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X) ^ 2 := by
    exact sq_nonneg _
  calc
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X
        ≤
      ((EvenIn X H).card : ℝ)
        * (2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X) ^ 2 := hmain
    _ ≤
      ((H + 1 : ℕ) : ℝ)
        * (2 * canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper X) ^ 2 := by
          exact mul_le_mul_of_nonneg_right hcard hsq_nonneg

theorem centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy_le_H_add_one_mul_explicit
    {X : ℕ} (hX : X0 ≤ X) :
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X
      ≤
    ((H + 1 : ℕ) : ℝ)
      * (2 * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((((X + H : ℕ) : ℝ) ^ 2) * ((2 * Real.pi * ((101 : ℝ) / 100)) ^ 2)) / 12)) ^ 2 := by
  simpa [canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPointwiseUpper] using
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy_le_H_add_one_mul_pointwiseUpper_sq
      (X := X) hX

theorem centeredCanonicalCorrectedFreezeDiscrepancyAux_eq_integral_doubleSumDefect_add_weightedGe2
    (X N : ℕ) (hX : 2 ≤ X) :
    centeredCanonicalCorrectedFreezeDiscrepancyAux X N
      =
    centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N
      + centeredCanonicalCorrectedFreezeWeightedGe2Defect X N := by
  unfold centeredCanonicalCorrectedFreezeDiscrepancyAux
    centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect
    centeredCanonicalCorrectedFreezeWeightedGe2Defect
    canonicalCorrectedFreezeIntegralDoubleSumDefect
    canonicalCorrectedFreezeWeightedGe2Defect
  rw [canonicalCorrectedFreezeDiscrepancy_eq_integral_doubleSumDefect_add_weightedGe2
    (X := X) (N := N) hX]
  rw [← weightedFreezeDefectGe2C_eq_sum_AqCRescaled_sub_AqFrozenC (X := X) (N := N) hX]
  have hsum :
      ∑ M ∈ EvenIn X H, canonicalCorrectedFreezeDiscrepancy X M
        =
      ∑ M ∈ EvenIn X H,
        (((((X : ℝ) : ℂ))⁻¹)
          * (∫ β in Goldbach.Cert.MajorArcModules.BetaInterval.aβ..
                Goldbach.Cert.MajorArcModules.BetaInterval.bβ,
              Goldbach.Cert.MajorArcModules.BetaLocalization.betaSmallSet.indicator (fun β : ℝ =>
                ∫ u in (0 : ℝ)..(1 : ℝ), q1PhaseCorrectedDoubleSumShellDefect X M u β) β)
          + (((Goldbach.AO_WeightMass.weight_mass X : ℝ) : ℂ)) * weightedFreezeDefectGe2C X M) := by
    refine Finset.sum_congr rfl ?_
    intro M hM
    rw [canonicalCorrectedFreezeDiscrepancy_eq_integral_doubleSumDefect_add_weightedGe2
      (X := X) (N := M) hX]
    rw [← weightedFreezeDefectGe2C_eq_sum_AqCRescaled_sub_AqFrozenC (X := X) (N := M) hX]
  rw [hsum, Finset.sum_add_distrib]
  ring_nf

/-- Pointwise quadratic upper bound for the freeze discrepancy split. -/
noncomputable def canonicalCorrectedFreezeDiscrepancyUpper
    (X N : ℕ) : ℝ :=
  2 * ‖centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N‖ ^ 2
    + 2 * ‖centeredCanonicalCorrectedFreezeWeightedGe2Defect X N‖ ^ 2

private theorem centeredCanonicalCorrectedFreezeDiscrepancy_sq_le
    (X N : ℕ) (hX : 2 ≤ X) :
    ‖centeredCanonicalCorrectedFreezeDiscrepancyAux X N‖ ^ 2
      ≤
    canonicalCorrectedFreezeDiscrepancyUpper X N := by
  rw [centeredCanonicalCorrectedFreezeDiscrepancyAux_eq_integral_doubleSumDefect_add_weightedGe2
    (X := X) (N := N) hX]
  unfold canonicalCorrectedFreezeDiscrepancyUpper
  have hnorm :=
    norm_add_le
      (centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N)
      (centeredCanonicalCorrectedFreezeWeightedGe2Defect X N)
  have hsq1 :
      ‖centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N
          + centeredCanonicalCorrectedFreezeWeightedGe2Defect X N‖ ^ 2
        ≤
      (‖centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N‖
          + ‖centeredCanonicalCorrectedFreezeWeightedGe2Defect X N‖) ^ 2 := by
    nlinarith [hnorm,
      norm_nonneg (centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N),
      norm_nonneg (centeredCanonicalCorrectedFreezeWeightedGe2Defect X N),
      norm_nonneg
        (centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N
          + centeredCanonicalCorrectedFreezeWeightedGe2Defect X N)]
  have hsq2 :
      (‖centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N‖
          + ‖centeredCanonicalCorrectedFreezeWeightedGe2Defect X N‖) ^ 2
        ≤
      2 * ‖centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N‖ ^ 2
        + 2 * ‖centeredCanonicalCorrectedFreezeWeightedGe2Defect X N‖ ^ 2 := by
    have hnonneg :
        0 ≤
          (‖centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect X N‖
            - ‖centeredCanonicalCorrectedFreezeWeightedGe2Defect X N‖) ^ 2 := by
      exact sq_nonneg _
    nlinarith
  exact le_trans hsq1 hsq2

theorem centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy_le
    (X : ℕ) (hX : 2 ≤ X) :
    centeredCanonicalCorrectedFreezeDiscrepancyAuxWindowEnergy X
      ≤
    2 * centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
      + 2 * centeredCanonicalCorrectedFreezeWeightedGe2DefectWindowEnergy X := by
  calc
    centeredCanonicalCorrectedFreezeDiscrepancyAuxWindowEnergy X
        ≤
      ∑ N ∈ EvenIn X H, canonicalCorrectedFreezeDiscrepancyUpper X N := by
            unfold centeredCanonicalCorrectedFreezeDiscrepancyAuxWindowEnergy
            exact Finset.sum_le_sum (fun N hN =>
              centeredCanonicalCorrectedFreezeDiscrepancy_sq_le X N hX)
    _ =
      2 * centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
        + 2 * centeredCanonicalCorrectedFreezeWeightedGe2DefectWindowEnergy X := by
          unfold canonicalCorrectedFreezeDiscrepancyUpper
            centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy
            centeredCanonicalCorrectedFreezeWeightedGe2DefectWindowEnergy
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Route-sized target for the centered corrected `q = 1` integral defect. -/
structure CenteredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Route-sized target for the centered corrected principal half-gap.

This is the natural first freeze-side block: the `q = 1` integral defect is exactly `X⁻¹`
times this object, so any theorem-sized window estimate should first be proved here and then
transported to the integral-defect form.
-/
structure CenteredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

/--
Pairwise-difference target for the raw corrected principal half-gap.

This is the exact boundary-style proof surface for the `q = 1` block after eliminating the window
average. Any route-sized bound for these raw pairwise differences upgrades automatically to the
centered window-energy target.
-/
structure CanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy X
        ≤
      2 * (((EvenIn X H).card : ℝ)
        * (C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)))

/-- Route-sized target for the centered weighted `q ≥ 2` freeze defect. -/
structure CenteredCanonicalCorrectedFreezeWeightedGe2DefectWindowTarget
    (C3 : ℝ) : Prop where
  C3_nonneg : 0 ≤ C3
  bound :
    ∀ {X : ℕ}, X0 ≤ X →
      centeredCanonicalCorrectedFreezeWeightedGe2DefectWindowEnergy X
        ≤
      C3 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)

theorem centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowTarget_of_gap
    {CQ1 : ℝ}
    (hGap : CenteredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowTarget CQ1) :
    CenteredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowTarget CQ1 where
  C3_nonneg := hGap.C3_nonneg
  bound := by
    intro X hX0
    have hXneq : (((X : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show X ≠ 0 from ne_of_gt (lt_of_lt_of_le (by decide : 0 < X0) hX0))
    have hXle_one : ‖(((X : ℝ) : ℂ))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      have hXge_one : (1 : ℝ) ≤ ‖(((X : ℝ) : ℂ))‖ := by
        have hXge_one_nat : 1 ≤ X := le_trans (by decide : 1 ≤ X0) hX0
        simp [RCLike.norm_ofReal, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ (X : ℝ) by positivity), hXge_one_nat]
      exact inv_le_one_of_one_le₀ hXge_one
    calc
      centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
          = ∑ N ∈ EvenIn X H,
              ‖((((X : ℝ) : ℂ))⁻¹)
                  * centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖ ^ 2 := by
                unfold centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy
                refine Finset.sum_congr rfl ?_
                intro N hN
                rw [centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect_eq_Xinv_mul_gap]
      _ ≤ ∑ N ∈ EvenIn X H, ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖ ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro N hN
            rw [norm_mul]
            let z := ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖
            have hz : 0 ≤ z := norm_nonneg _
            have hsq :
                (‖(((X : ℝ) : ℂ))⁻¹‖ * z) ^ 2 ≤ z ^ 2 := by
              have hcoeffsq : ‖(((X : ℝ) : ℂ))⁻¹‖ ^ 2 ≤ 1 := by
                nlinarith [hXle_one, norm_nonneg ((((X : ℝ) : ℂ))⁻¹)]
              calc
                (‖(((X : ℝ) : ℂ))⁻¹‖ * z) ^ 2
                    = (‖(((X : ℝ) : ℂ))⁻¹‖ ^ 2) * (z ^ 2) := by ring
                _ ≤ (1 : ℝ) * (z ^ 2) := by
                    gcongr
                _ = z ^ 2 := by ring
            simpa using hsq
      _ = centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X := by
            rfl
      _ ≤ CQ1 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := hGap.bound hX0

theorem centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowTarget_of_pairwise
    {CQ1 : ℝ}
    (hPair : CanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowTarget CQ1) :
    CenteredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowTarget CQ1 where
  C3_nonneg := hPair.C3_nonneg
  bound := by
    intro X hX
    have hcard_nat : (EvenIn X H).card ≠ 0 := card_evenIn_ne_zero hX
    have hcardR_nonneg : 0 ≤ ((EvenIn X H).card : ℝ) := by
      exact_mod_cast Nat.zero_le (EvenIn X H).card
    have hcardR_ne : ((EvenIn X H).card : ℝ) ≠ 0 := by
      exact_mod_cast hcard_nat
    have hcardR_pos : 0 < ((EvenIn X H).card : ℝ) := by
      exact lt_of_le_of_ne hcardR_nonneg (Ne.symm hcardR_ne)
    have hpair := hPair.bound (X := X) hX
    rw [canonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedPairwiseWindowEnergy_eq] at hpair
    nlinarith

theorem centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy_le_gap
    {X : ℕ} (hX0 : X0 ≤ X) :
    centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
      ≤
    centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X := by
  have hXneq : (((X : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 from ne_of_gt (lt_of_lt_of_le (by decide : 0 < X0) hX0))
  have hXle_one : ‖(((X : ℝ) : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    have hXge_one : (1 : ℝ) ≤ ‖(((X : ℝ) : ℂ))‖ := by
      have hXge_one_nat : 1 ≤ X := le_trans (by decide : 1 ≤ X0) hX0
      simp [hXge_one_nat]
    exact inv_le_one_of_one_le₀ hXge_one
  calc
    centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
        = ∑ N ∈ EvenIn X H,
            ‖((((X : ℝ) : ℂ))⁻¹)
                * centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖ ^ 2 := by
              unfold centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy
              refine Finset.sum_congr rfl ?_
              intro N hN
              rw [centeredCanonicalCorrectedFreezeIntegralDoubleSumDefect_eq_Xinv_mul_gap]
    _ ≤ ∑ N ∈ EvenIn X H, ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖ ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro N hN
          rw [norm_mul]
          let z := ‖centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1Corrected X N‖
          have hsq :
              (‖(((X : ℝ) : ℂ))⁻¹‖ * z) ^ 2 ≤ z ^ 2 := by
            have hcoeffsq : ‖(((X : ℝ) : ℂ))⁻¹‖ ^ 2 ≤ 1 := by
              nlinarith [hXle_one, norm_nonneg ((((X : ℝ) : ℂ))⁻¹)]
            calc
              (‖(((X : ℝ) : ℂ))⁻¹‖ * z) ^ 2
                  = (‖(((X : ℝ) : ℂ))⁻¹‖ ^ 2) * (z ^ 2) := by ring
              _ ≤ (1 : ℝ) * (z ^ 2) := by
                  gcongr
              _ = z ^ 2 := by ring
          simpa using hsq
    _ = centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy X := by
          rfl

theorem centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy_le_H_add_one_mul_explicit
    {X : ℕ} (hX0 : X0 ≤ X) :
    centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
      ≤
    ((H + 1 : ℕ) : ℝ)
      * (2 * (Goldbach.Cert.MajorArcModules.Q0MajorBoundSplit.kernelCap
          * ((((X + H : ℕ) : ℝ) ^ 2) * ((2 * Real.pi * ((101 : ℝ) / 100)) ^ 2)) / 12)) ^ 2 := by
  exact le_trans
    (centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy_le_gap (X := X) hX0)
    (centeredCanonicalSmallBetaRescaledGapExtractedArcHalfQ1CorrectedWindowEnergy_le_H_add_one_mul_explicit
      (X := X) hX0)

theorem centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy_bound_of_q1_and_weightedGe2
    {CQ1 CGe2 : ℝ}
    (hQ1 : CenteredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowTarget CQ1)
    (hGe2 : CenteredCanonicalCorrectedFreezeWeightedGe2DefectWindowTarget CGe2)
    {X : ℕ} (hX0 : X0 ≤ X) :
    centeredCanonicalCorrectedFreezeDiscrepancyAuxWindowEnergy X
      ≤
    (2 * CQ1 + 2 * CGe2)
      / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
  have hX : 2 ≤ X := le_trans (by decide : 2 ≤ X0) hX0
  have hmain := centeredCanonicalCorrectedFreezeDiscrepancyWindowEnergy_le X hX
  have h1 := hQ1.bound hX0
  have h2 := hGe2.bound hX0
  calc
    centeredCanonicalCorrectedFreezeDiscrepancyAuxWindowEnergy X
        ≤
      2 * centeredCanonicalCorrectedFreezeIntegralDoubleSumDefectWindowEnergy X
        + 2 * centeredCanonicalCorrectedFreezeWeightedGe2DefectWindowEnergy X := hmain
    _ ≤
      2 * (CQ1 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2))
        + 2 * (CGe2 / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2)) := by
          gcongr
    _ =
      (2 * CQ1 + 2 * CGe2)
        / ((H : ℝ) * ((Goldbach.AO_OffDiag.TailBlock.Q0 : ℕ) : ℝ) ^ 2) := by
          field_simp

end

end Goldbach.Cert.MajorArcModules.Q0MinorHalfMassFreezeWindowTargets
