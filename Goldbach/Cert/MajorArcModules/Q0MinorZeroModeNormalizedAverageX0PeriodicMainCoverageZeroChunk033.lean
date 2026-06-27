import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMain

set_option maxHeartbeats 0

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/- Generated periodic-main ordered-record coverage facts for PeriodicMainZeroRecordPairsChunk033, JSON indices [3300,3400). -/

def PeriodicMainZeroRecordPairsChunk033 : Finset (ℕ × ℕ) :=
  ([
    (2, 429),
    (2, 430),
    (2, 431),
    (2, 433),
    (2, 434),
    (2, 435),
    (2, 437),
    (2, 438),
    (2, 439),
    (2, 442),
    (2, 443),
    (2, 445),
    (2, 446),
    (2, 447),
    (2, 449),
    (2, 451),
    (2, 453),
    (2, 454),
    (2, 455),
    (2, 457),
    (2, 458),
    (2, 461),
    (2, 462),
    (2, 463),
    (2, 465),
    (2, 466),
    (2, 467),
    (2, 469),
    (2, 470),
    (2, 471),
    (2, 473),
    (2, 474),
    (2, 478),
    (2, 479),
    (2, 481),
    (2, 482),
    (2, 483),
    (2, 485),
    (2, 487),
    (2, 489),
    (2, 491),
    (2, 493),
    (2, 494),
    (2, 497),
    (2, 498),
    (2, 499),
    (2, 501),
    (2, 502),
    (2, 503),
    (2, 505),
    (2, 506),
    (2, 509),
    (2, 510),
    (2, 511),
    (2, 514),
    (2, 515),
    (2, 517),
    (2, 518),
    (2, 519),
    (2, 521),
    (2, 523),
    (2, 526),
    (2, 527),
    (2, 530),
    (2, 533),
    (2, 534),
    (2, 535),
    (2, 537),
    (2, 538),
    (2, 541),
    (2, 542),
    (2, 543),
    (2, 545),
    (2, 546),
    (2, 547),
    (2, 551),
    (2, 553),
    (2, 554),
    (2, 555),
    (2, 557),
    (2, 559),
    (2, 561),
    (2, 562),
    (2, 563),
    (2, 565),
    (2, 566),
    (2, 569),
    (2, 570),
    (2, 571),
    (2, 573),
    (2, 574),
    (2, 577),
    (2, 579),
    (2, 581),
    (2, 582),
    (2, 583),
    (2, 586),
    (2, 587),
    (2, 589),
    (2, 590)
  ] : List (ℕ × ℕ)).toFinset

theorem PeriodicMainZeroRecordPairsChunk033_card :
    PeriodicMainZeroRecordPairsChunk033.card = 100 := by
  native_decide

theorem PeriodicMainZeroRecordPairsChunk033_subset_fullBlockExplicit :
    PeriodicMainZeroRecordPairsChunk033 ⊆ PeriodicMainFullBlockOrderedPairSupportExplicit := by
  intro p hp
  simp [PeriodicMainZeroRecordPairsChunk033] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 429 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 430 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 430 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 431 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 431 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 433 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 433 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 434 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 434 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 435 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 435 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 437 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 437 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 438 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 439 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 439 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 442 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 443 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 443 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 445 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 445 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 446 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 446 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 447 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 447 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 449 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 449 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 451 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 451 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 453 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 454 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 454 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 455 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 457 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 457 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 458 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 461 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 461 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 462 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 462 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 463 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 463 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 465 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 465 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 466 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 466 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 467 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 467 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 469 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 469 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 470 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 470 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 471 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 471 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 473 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 474 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 474 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 478 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 478 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 479 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 479 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 481 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 482 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 482 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 483 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 485 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 485 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 487 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 487 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 489 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 491 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 491 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 493 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 493 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 494 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 497 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 497 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 498 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 498 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 499 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 499 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 501 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 501 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 502 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 502 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 503 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 505 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 505 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 506 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 506 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 509 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 509 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 510 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 510 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 511 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 511 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 514 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 514 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 515 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 515 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 517 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 517 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 518 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 518 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 519 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 519 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 521 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 521 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 523 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 523 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 526 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 526 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 527 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 527 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 530 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 530 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 533 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 534 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 534 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 535 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 537 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 537 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 538 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 541 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 541 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 542 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 542 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 543 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 543 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 545 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 545 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 546 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 547 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 547 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 551 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 551 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 553 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 553 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 554 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 554 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 555 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 555 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 557 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 557 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 559 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
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
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 561 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 561 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 562 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 562 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 563 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 563 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 565 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 565 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 566 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 566 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 569 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 569 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 570 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 570 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 571 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 571 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 573 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 573 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 574 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 574 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 577 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 577 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 579 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 579 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 581 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 581 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 582 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 582 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 583 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 583 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 586 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 586 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 587 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 587 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 589 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 589 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩
  · subst p
    have hqCoeff : 2 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hq2Coeff : 590 ∈ PeriodicMainCoeffSupportExplicit := by
      unfold PeriodicMainCoeffSupportExplicit
      exact mem_normalizedSigmaTruncSummandCoeffSupportUpToQ0_iff.mpr ⟨by norm_num, by native_decide⟩
    have hqActive : 2 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hqCoeff, by norm_num [H]⟩
    have hq2Active : 590 ∈ PeriodicMainActiveSupportExplicit := by
      unfold PeriodicMainActiveSupportExplicit
      exact Finset.mem_filter.mpr ⟨hq2Coeff, by norm_num [H]⟩
    unfold PeriodicMainFullBlockOrderedPairSupportExplicit
    exact Finset.mem_filter.mpr ⟨by
      unfold PeriodicMainActiveOrderedPairSupportExplicit
      exact Finset.mem_product.mpr ⟨hqActive, hq2Active⟩,
      by
        constructor
        · norm_num
        · norm_num [centeredRamanujanPairBlockPeriod, H]
    ⟩

theorem PeriodicMainZeroRecordPairsChunk033_subset_fullBlockSquarefreeExplicit :
    PeriodicMainZeroRecordPairsChunk033 ⊆ PeriodicMainFullBlockOrderedPairSupportSquarefreeExplicit := by
  intro p hp
  rw [← PeriodicMainFullBlockOrderedPairSupportExplicit_eq_squarefreeExplicit]
  exact PeriodicMainZeroRecordPairsChunk033_subset_fullBlockExplicit hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
