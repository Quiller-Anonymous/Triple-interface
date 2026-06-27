import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record coverage facts for PeriodicMainNonzeroRecordPairsChunk238, JSON indices [23800,23900). -/

def PeriodicMainNonzeroRecordPairsChunk238 : Finset (ℕ × ℕ) :=
  ([
    (1603, 14),
    (1603, 229),
    (1603, 458),
    (1603, 687),
    (1603, 3206),
    (1603, 4809),
    (1605, 5),
    (1605, 10),
    (1605, 15),
    (1605, 30),
    (1605, 107),
    (1605, 214),
    (1605, 321),
    (1605, 535),
    (1605, 642),
    (1605, 1070),
    (1605, 3210),
    (1606, 11),
    (1606, 22),
    (1606, 33),
    (1606, 66),
    (1606, 73),
    (1606, 146),
    (1606, 219),
    (1606, 438),
    (1606, 803),
    (1606, 2409),
    (1606, 4818),
    (1607, 3214),
    (1609, 3218),
    (1610, 5),
    (1610, 7),
    (1610, 10),
    (1610, 14),
    (1610, 15),
    (1610, 23),
    (1610, 30),
    (1610, 35),
    (1610, 46),
    (1610, 69),
    (1610, 70),
    (1610, 105),
    (1610, 115),
    (1610, 138),
    (1610, 161),
    (1610, 210),
    (1610, 230),
    (1610, 322),
    (1610, 345),
    (1610, 483),
    (1610, 690),
    (1610, 805),
    (1610, 966),
    (1610, 2415),
    (1610, 4830),
    (1613, 3226),
    (1613, 4839),
    (1614, 269),
    (1614, 538),
    (1614, 807),
    (1615, 5),
    (1615, 10),
    (1615, 15),
    (1615, 17),
    (1615, 19),
    (1615, 34),
    (1615, 38),
    (1615, 57),
    (1615, 85),
    (1615, 95),
    (1615, 170),
    (1615, 190),
    (1615, 255),
    (1615, 285),
    (1615, 323),
    (1615, 646),
    (1615, 969),
    (1615, 3230),
    (1615, 4845),
    (1618, 809),
    (1619, 3238),
    (1621, 3242),
    (1622, 811),
    (1623, 3246),
    (1626, 813),
    (1627, 3254),
    (1630, 5),
    (1630, 10),
    (1630, 15),
    (1630, 30),
    (1630, 163),
    (1630, 326),
    (1630, 489),
    (1630, 815),
    (1630, 978),
    (1630, 2445),
    (1630, 4890),
    (1631, 7),
    (1631, 14),
    (1631, 233)
  ] : List (ℕ × ℕ)).toFinset

theorem PeriodicMainNonzeroRecordPairsChunk238_card :
    PeriodicMainNonzeroRecordPairsChunk238.card = 100 := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk238_subset_fullBlockExplicit :
    PeriodicMainNonzeroRecordPairsChunk238 ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  simp [PeriodicMainNonzeroRecordPairsChunk238] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst p
    have hqCoeff : 1603 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 14 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1603 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 14 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1603 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 229 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1603 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 229 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1603 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 458 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1603 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 458 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1603 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 687 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1603 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 687 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1603 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3206 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1603 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3206 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1603 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4809 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1603 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4809 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 5 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 10 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 15 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 15 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 30 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 30 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 107 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 107 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 214 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 214 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 321 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 321 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 535 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 535 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 642 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 642 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1070 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1070 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1605 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3210 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1605 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3210 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 11 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 11 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 22 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 22 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 33 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 33 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 66 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 66 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 73 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 73 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 146 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 146 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 219 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 219 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 438 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 438 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 803 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 803 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2409 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2409 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1606 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4818 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1606 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4818 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1607 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3214 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1607 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3214 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1609 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3218 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1609 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3218 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 5 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 7 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 10 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 14 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 14 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 15 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 15 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 23 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 23 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 30 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 30 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 35 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 35 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 46 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 46 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 69 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 69 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 70 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 70 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 105 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 105 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 115 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 115 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 138 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 138 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 161 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 161 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 210 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 210 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 230 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 230 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 322 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 322 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 345 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 345 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 483 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 483 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 690 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 690 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 805 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 805 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 966 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 966 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2415 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2415 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1610 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4830 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1610 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4830 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1613 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3226 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1613 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3226 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1613 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4839 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1613 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4839 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1614 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 269 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1614 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 269 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1614 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 538 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1614 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 538 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1614 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 807 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1614 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 807 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 5 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 10 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 15 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 15 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 17 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 17 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 19 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 19 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 34 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 34 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 38 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 38 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 57 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 57 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 85 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 85 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 95 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 95 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 170 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 170 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 190 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 190 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 255 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 255 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 285 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 285 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 323 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 323 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 646 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 646 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 969 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 969 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3230 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3230 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1615 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4845 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1615 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4845 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1618 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 809 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1618 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 809 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1619 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3238 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1619 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3238 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1621 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3242 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1621 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3242 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1622 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 811 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1622 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 811 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1623 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3246 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1623 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3246 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1626 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 813 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1626 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 813 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1627 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3254 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1627 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3254 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 5 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 10 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 15 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 15 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 30 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 30 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 163 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 163 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 326 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 326 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 489 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 489 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 815 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 815 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 978 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 978 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2445 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2445 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1630 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4890 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1630 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4890 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1631 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1631 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 7 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1631 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 14 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1631 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 14 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1631 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 233 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1631 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 233 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩

theorem PeriodicMainNonzeroRecordPairsChunk238_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsChunk238 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [← PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact PeriodicMainNonzeroRecordPairsChunk238_subset_fullBlockExplicit hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
