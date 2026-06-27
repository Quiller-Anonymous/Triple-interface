import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record coverage facts for PeriodicMainNonzeroRecordPairsChunk055, JSON indices [5500,5600). -/

def PeriodicMainNonzeroRecordPairsChunk055 : Finset (ℕ × ℕ) :=
  ([
    (26, 322),
    (26, 326),
    (26, 330),
    (26, 334),
    (26, 346),
    (26, 354),
    (26, 358),
    (26, 362),
    (26, 366),
    (26, 370),
    (26, 374),
    (26, 377),
    (26, 382),
    (26, 390),
    (26, 403),
    (26, 429),
    (26, 442),
    (26, 455),
    (26, 481),
    (26, 494),
    (26, 533),
    (26, 546),
    (26, 559),
    (26, 598),
    (26, 611),
    (26, 663),
    (26, 689),
    (26, 715),
    (26, 741),
    (26, 754),
    (26, 767),
    (26, 793),
    (26, 806),
    (26, 858),
    (26, 871),
    (26, 897),
    (26, 910),
    (26, 923),
    (26, 949),
    (26, 962),
    (26, 1001),
    (26, 1027),
    (26, 1066),
    (26, 1079),
    (26, 1105),
    (26, 1118),
    (26, 1131),
    (26, 1157),
    (26, 1209),
    (26, 1222),
    (26, 1235),
    (26, 1261),
    (26, 1313),
    (26, 1326),
    (26, 1339),
    (26, 1365),
    (26, 1378),
    (26, 1391),
    (26, 1417),
    (26, 1430),
    (26, 1443),
    (26, 1469),
    (26, 1482),
    (26, 1495),
    (26, 1534),
    (26, 1547),
    (26, 1586),
    (26, 1599),
    (26, 1651),
    (26, 1677),
    (26, 1703),
    (26, 1729),
    (26, 1742),
    (26, 1781),
    (26, 1794),
    (26, 1807),
    (26, 1833),
    (26, 1846),
    (26, 1885),
    (26, 1898),
    (26, 1937),
    (26, 1963),
    (26, 2002),
    (26, 2015),
    (26, 2041),
    (26, 2054),
    (26, 2067),
    (26, 2093),
    (26, 2119),
    (26, 2145),
    (26, 2158),
    (26, 2171),
    (26, 2210),
    (26, 2249),
    (26, 2262),
    (26, 2301),
    (26, 2314),
    (26, 2327),
    (26, 2353),
    (26, 2379)
  ] : List (ℕ × ℕ)).toFinset

theorem PeriodicMainNonzeroRecordPairsChunk055_card :
    PeriodicMainNonzeroRecordPairsChunk055.card = 100 := by
  native_decide

theorem PeriodicMainNonzeroRecordPairsChunk055_subset_fullBlockExplicit :
    PeriodicMainNonzeroRecordPairsChunk055 ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  simp [PeriodicMainNonzeroRecordPairsChunk055] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst p
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 322 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 326 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 330 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 330 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 334 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 334 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 346 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 346 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 354 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 354 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 358 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 358 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 362 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 362 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 366 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 366 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 370 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 370 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 374 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 374 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 377 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 377 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 382 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 382 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 390 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 390 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 403 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 403 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 429 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 429 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 442 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 442 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 455 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 455 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 481 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 481 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 494 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 494 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 533 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 533 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 546 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 546 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 559 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 559 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 598 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 598 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 611 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 611 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 663 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 663 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 689 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 689 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 715 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 715 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 741 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 741 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 754 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 754 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 767 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 767 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 793 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 793 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 806 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 806 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 858 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 858 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 871 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 871 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 897 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 897 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 910 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 910 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 923 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 923 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 949 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 949 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 962 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 962 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1001 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1001 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1027 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1027 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1066 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1066 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1079 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1079 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1105 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1105 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1118 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1118 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1131 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1131 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1157 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1157 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1209 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1209 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1222 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1222 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1235 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1235 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1261 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1261 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1313 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1313 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1326 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1326 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1339 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1339 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1365 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1365 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1378 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1378 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1391 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1391 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1417 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1417 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1430 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1443 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1443 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1469 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1469 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1482 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1482 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1495 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1495 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1534 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1534 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1547 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1547 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1586 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1586 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1599 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1599 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1651 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1651 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1677 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1677 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1703 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1703 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1729 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1729 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1742 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1742 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1781 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1781 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1794 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1794 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1807 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1807 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1833 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1833 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1846 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1846 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1885 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1885 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1898 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1898 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1937 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1937 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1963 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1963 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2002 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2002 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2015 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2015 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2041 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2041 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2054 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2054 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2067 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2067 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2093 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2093 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2119 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2119 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2145 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2145 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2158 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2158 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2171 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2171 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2210 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2210 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2249 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2249 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2262 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2262 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2301 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2301 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2314 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2314 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2327 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2327 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2353 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2353 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 26 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2379 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 26 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2379 ∈ PeriodicMainActiveSupportExplicit := by
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

theorem PeriodicMainNonzeroRecordPairsChunk055_subset_fullBlockSquarefreeExplicit :
    PeriodicMainNonzeroRecordPairsChunk055 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [← PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact PeriodicMainNonzeroRecordPairsChunk055_subset_fullBlockExplicit hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
