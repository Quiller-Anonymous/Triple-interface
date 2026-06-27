import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record coverage facts for PeriodicMainNonzeroRecordPairsChunk176, JSON indices [17600,17700). -/

def PeriodicMainNonzeroRecordPairsChunk176 : Finset (ℕ × ℕ) :=
  ([
    (430, 15),
    (430, 22),
    (430, 30),
    (430, 35),
    (430, 43),
    (430, 55),
    (430, 70),
    (430, 86),
    (430, 110),
    (430, 215),
    (430, 301),
    (430, 473),
    (430, 602),
    (430, 645),
    (430, 946),
    (430, 1290),
    (430, 1505),
    (430, 2365),
    (430, 3010),
    (430, 4730),
    (431, 5),
    (431, 7),
    (431, 10),
    (431, 11),
    (431, 862),
    (431, 1293),
    (431, 2155),
    (431, 2586),
    (431, 3017),
    (431, 4310),
    (431, 4741),
    (433, 5),
    (433, 7),
    (433, 10),
    (433, 11),
    (433, 866),
    (433, 2165),
    (433, 3031),
    (433, 4330),
    (433, 4763),
    (434, 5),
    (434, 7),
    (434, 10),
    (434, 11),
    (434, 14),
    (434, 22),
    (434, 31),
    (434, 35),
    (434, 62),
    (434, 70),
    (434, 77),
    (434, 93),
    (434, 154),
    (434, 155),
    (434, 186),
    (434, 217),
    (434, 310),
    (434, 341),
    (434, 651),
    (434, 682),
    (434, 1085),
    (434, 1302),
    (434, 2170),
    (434, 2387),
    (434, 4774),
    (435, 5),
    (435, 7),
    (435, 10),
    (435, 11),
    (435, 15),
    (435, 29),
    (435, 30),
    (435, 33),
    (435, 35),
    (435, 55),
    (435, 58),
    (435, 87),
    (435, 105),
    (435, 145),
    (435, 165),
    (435, 174),
    (435, 203),
    (435, 290),
    (435, 319),
    (435, 609),
    (435, 870),
    (435, 957),
    (435, 1015),
    (435, 1595),
    (435, 3045),
    (435, 4785),
    (437, 5),
    (437, 7),
    (437, 10),
    (437, 11),
    (437, 19),
    (437, 23),
    (437, 38),
    (437, 46),
    (437, 57)
  ] : List (ℕ × ℕ)).toFinset

theorem PeriodicMainNonzeroRecordPairsChunk176_card :
    PeriodicMainNonzeroRecordPairsChunk176.card = 100 := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk176_subset_fullBlockExplicit :
    PeriodicMainNonzeroRecordPairsChunk176 ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  simp [PeriodicMainNonzeroRecordPairsChunk176] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst p
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 15 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 22 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 30 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 35 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 43 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 43 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 55 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 55 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 70 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 86 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 86 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 110 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 110 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 215 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 215 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 301 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 301 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 473 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 473 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 602 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 602 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 645 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 645 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 946 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 946 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1290 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1290 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1505 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1505 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2365 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2365 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3010 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3010 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4730 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4730 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 11 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 862 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 862 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1293 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1293 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2155 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2155 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2586 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2586 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3017 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3017 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4310 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4310 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4741 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4741 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 11 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 866 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 866 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2165 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2165 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3031 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3031 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4330 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4330 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4763 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 433 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4763 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 11 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 14 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 22 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 31 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 31 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 35 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 62 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 62 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 70 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 77 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 77 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 93 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 93 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 154 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 154 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 155 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 155 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 186 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 186 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 217 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 217 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 310 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 310 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 341 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 341 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 651 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 651 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 682 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 682 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1085 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1085 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1302 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1302 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2170 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2170 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2387 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2387 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4774 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4774 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 11 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 15 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 29 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 29 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 30 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 33 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 35 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 55 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 55 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 58 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 58 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 87 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 87 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 105 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 145 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 145 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 165 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 165 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 174 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 174 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 203 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 203 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 290 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 290 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 319 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 319 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 609 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 609 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 870 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 870 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 957 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 957 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1015 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1015 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1595 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1595 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3045 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3045 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4785 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4785 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 5 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 7 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 10 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 11 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 19 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 23 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 38 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 46 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 57 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 437 ∈ PeriodicMainActiveSupportExplicit := by
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

theorem PeriodicMainNonzeroRecordPairsChunk176_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsChunk176 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [← PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact PeriodicMainNonzeroRecordPairsChunk176_subset_fullBlockExplicit hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
