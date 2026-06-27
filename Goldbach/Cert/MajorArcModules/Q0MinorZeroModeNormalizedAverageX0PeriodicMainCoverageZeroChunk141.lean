import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record coverage facts for PeriodicMainZeroRecordPairsChunk141, JSON indices [14100,14200). -/

def PeriodicMainZeroRecordPairsChunk141 : Finset (ℕ × ℕ) :=
  ([
    (1486, 1),
    (1486, 2),
    (1486, 3),
    (1486, 6),
    (1487, 1),
    (1487, 2),
    (1487, 3),
    (1487, 4461),
    (1489, 1),
    (1489, 2),
    (1489, 3),
    (1490, 1),
    (1490, 2),
    (1490, 3),
    (1490, 6),
    (1491, 1),
    (1491, 2),
    (1491, 3),
    (1491, 6),
    (1491, 21),
    (1491, 42),
    (1493, 1),
    (1493, 2),
    (1493, 3),
    (1495, 1),
    (1495, 2),
    (1495, 3),
    (1497, 1),
    (1497, 2),
    (1497, 3),
    (1497, 6),
    (1498, 1),
    (1498, 2),
    (1498, 3),
    (1498, 6),
    (1498, 21),
    (1498, 42),
    (1499, 1),
    (1499, 2),
    (1499, 3),
    (1499, 4497),
    (1501, 1),
    (1501, 2),
    (1501, 3),
    (1501, 237),
    (1502, 1),
    (1502, 2),
    (1502, 3),
    (1502, 6),
    (1505, 1),
    (1505, 2),
    (1505, 3),
    (1505, 21),
    (1505, 129),
    (1506, 1),
    (1506, 2),
    (1506, 3),
    (1506, 6),
    (1507, 1),
    (1507, 2),
    (1507, 3),
    (1509, 1),
    (1509, 2),
    (1509, 3),
    (1509, 6),
    (1509, 503),
    (1509, 1006),
    (1510, 1),
    (1510, 2),
    (1510, 3),
    (1510, 6),
    (1510, 453),
    (1510, 906),
    (1511, 1),
    (1511, 2),
    (1511, 3),
    (1513, 1),
    (1513, 2),
    (1513, 3),
    (1513, 51),
    (1513, 267),
    (1513, 4539),
    (1514, 1),
    (1514, 2),
    (1514, 3),
    (1514, 6),
    (1515, 1),
    (1515, 2),
    (1515, 3),
    (1515, 6),
    (1517, 1),
    (1517, 2),
    (1517, 3),
    (1517, 111),
    (1518, 1),
    (1518, 2),
    (1518, 3),
    (1518, 6),
    (1522, 1),
    (1522, 2)
  ] : List (ℕ × ℕ)).toFinset

theorem PeriodicMainZeroRecordPairsChunk141_card :
    PeriodicMainZeroRecordPairsChunk141.card = 100 := by
  native_decide

theorem PeriodicMainZeroRecordPairsChunk141_subset_fullBlockExplicit :
    PeriodicMainZeroRecordPairsChunk141 ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  simp [PeriodicMainZeroRecordPairsChunk141] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst p
    have hqCoeff : 1486 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1486 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1486 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1486 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1486 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1486 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1486 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1486 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1487 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1487 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1487 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1487 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1487 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1487 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1487 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4461 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1487 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4461 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1489 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1489 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1489 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1489 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1489 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1489 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1490 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1490 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1490 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1490 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1490 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1490 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1490 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1490 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1491 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1491 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1491 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1491 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1491 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1491 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1491 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1491 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1491 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 21 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1491 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 21 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1491 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 42 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1491 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 42 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1493 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1493 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1493 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1493 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1493 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1493 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1495 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1495 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1495 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1495 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1495 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1495 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1497 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1497 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1497 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1497 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1497 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1497 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1497 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1497 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1498 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1498 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1498 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1498 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1498 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1498 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1498 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1498 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1498 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 21 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1498 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 21 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1498 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 42 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1498 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 42 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1499 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1499 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1499 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1499 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1499 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1499 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1499 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4497 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1499 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4497 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1501 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1501 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1501 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1501 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1501 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1501 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1501 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 237 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1501 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 237 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1502 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1502 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1502 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1502 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1502 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1502 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1502 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1502 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1505 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1505 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1505 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1505 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1505 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1505 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1505 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 21 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1505 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 21 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1505 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 129 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1505 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 129 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1506 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1506 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1506 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1506 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1506 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1506 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1506 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1506 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1507 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1507 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1507 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1507 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1507 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1507 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1509 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1509 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1509 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1509 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1509 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1509 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1509 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1509 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1509 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 503 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1509 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 503 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1509 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1006 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1509 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1006 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1510 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1510 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1510 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1510 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1510 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1510 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1510 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1510 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1510 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 453 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1510 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 453 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1510 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 906 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1510 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 906 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1511 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1511 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1511 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1511 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1511 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1511 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1513 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1513 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1513 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1513 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1513 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1513 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1513 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 51 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1513 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 51 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1513 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 267 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1513 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 267 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1513 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 4539 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1513 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 4539 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1514 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1514 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1514 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1514 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1514 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1514 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1514 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1514 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1515 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1515 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1515 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1515 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1515 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1515 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1515 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1515 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1517 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1517 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1517 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1517 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1517 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1517 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1517 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 111 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1517 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 111 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1518 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1518 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1518 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1518 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1518 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 3 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1518 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 3 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1518 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 6 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1518 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 6 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1522 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 1 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1522 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 1 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 1522 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 1522 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩

theorem PeriodicMainZeroRecordPairsChunk141_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsChunk141 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [← PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact PeriodicMainZeroRecordPairsChunk141_subset_fullBlockExplicit hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
