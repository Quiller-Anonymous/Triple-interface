import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk000
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk001
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk002
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk003
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk004
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk005
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk006
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk007
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk008
import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeNonCoprimeCoreRawChunk009

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Final non-coprime-core base-zero proof for `bothThree`.

This consumes the 10 raw-core range chunks and the shared side-average
certificate to prove `bothThreeBaseFullBlockZeroAtX0` for every non-coprime
odd-core record.
-/

theorem bothThreeNonCoprimeCoreRawCorePairGood_of_mem
    {ab : ℕ × ℕ} (hab : ab ∈ bothThreeNonCoprimeCoreRawCorePairs) :
    bothThreeNonCoprimeCoreRawCorePairGood ab := by
  have hlt : ab.1 < 2000 :=
    bothThreeNonCoprimeCoreRawCore_left_lt_2000_of_mem hab
  by_cases h25 : ab.1 < 25
  · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
      bothThreeNonCoprimeCoreRawCoreBadPairsChunk000_card hab (by omega) h25
  · by_cases h50 : ab.1 < 50
    · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
        bothThreeNonCoprimeCoreRawCoreBadPairsChunk001_card hab (by omega) h50
    · by_cases h75 : ab.1 < 75
      · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
          bothThreeNonCoprimeCoreRawCoreBadPairsChunk002_card hab (by omega) h75
      · by_cases h100 : ab.1 < 100
        · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
            bothThreeNonCoprimeCoreRawCoreBadPairsChunk003_card hab (by omega) h100
        · by_cases h150 : ab.1 < 150
          · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
              bothThreeNonCoprimeCoreRawCoreBadPairsChunk004_card hab (by omega) h150
          · by_cases h250 : ab.1 < 250
            · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
                bothThreeNonCoprimeCoreRawCoreBadPairsChunk005_card hab (by omega) h250
            · by_cases h500 : ab.1 < 500
              · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
                  bothThreeNonCoprimeCoreRawCoreBadPairsChunk006_card hab (by omega) h500
              · by_cases h800 : ab.1 < 800
                · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
                    bothThreeNonCoprimeCoreRawCoreBadPairsChunk007_card hab (by omega) h800
                · by_cases h1200 : ab.1 < 1200
                  · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
                      bothThreeNonCoprimeCoreRawCoreBadPairsChunk008_card hab (by omega) h1200
                  · exact bothThreeNonCoprimeCoreRawCorePairGood_of_badPairsInLeftRange_card_zero
                      bothThreeNonCoprimeCoreRawCoreBadPairsChunk009_card hab (by omega) hlt

theorem bothThreeNonCoprimeCoreRawCorePairGood_of_record_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs) :
    rawEvenRamanujanPairBlockSumRat X0
      (bothThreeOddCore p.1) (bothThreeOddCore p.2) = 0 := by
  have hmem :
      (bothThreeOddCore p.1, bothThreeOddCore p.2)
        ∈ bothThreeNonCoprimeCoreRawCorePairs := by
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  exact bothThreeNonCoprimeCoreRawCorePairGood_of_mem hmem

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_coreBlockPeriod_coprime_three
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs) :
    Nat.Coprime
      (centeredRamanujanPairBlockPeriod (bothThreeOddCore p.1) (bothThreeOddCore p.2))
      3 := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_mem_bothThree
      p hp
  exact centeredRamanujanPairBlockPeriod_coprime_three_of_not_dvd_three
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hpBoth)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_basePairRawBlockSum_eq_zero_of_core
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs)
    (hcore :
      rawEvenRamanujanPairBlockSum X0
        (bothThreeOddCore p.1) (bothThreeOddCore p.2) = 0) :
    rawEvenRamanujanPairBlockSum X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
      =
    0 := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_mem_bothThree
      p hp
  rw [rawEvenRamanujanPairBlockSum_three_mul_both_eq_six_mul
    (X := X0) (q := bothThreeOddCore p.1) (q' := bothThreeOddCore p.2)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_coreBlockPeriod_coprime_three
      hp)]
  rw [hcore]
  ring

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_baseLeftRawBlockSum_eq_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs) :
    rawEvenRamanujanBlockSum X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
        (3 * bothThreeOddCore p.1)
      =
    0 := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_mem_bothThree
      p hp
  exact rawEvenRamanujanBlockSum_three_mul_both_eq_zero
    (X := X0) (q := bothThreeOddCore p.1) (q' := bothThreeOddCore p.2)
    (q0 := bothThreeOddCore p.1)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_coreBlockPeriod_coprime_three
      hp)
    (by
      unfold centeredRamanujanPairBlockPeriod
      exact dvd_mul_of_dvd_right
        (dvd_lcm_left (bothThreeOddCore p.1) (bothThreeOddCore p.2)) 2)

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_baseRightRawBlockSum_eq_zero
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs) :
    rawEvenRamanujanBlockSum X0
        (3 * bothThreeOddCore p.1) (3 * bothThreeOddCore p.2)
        (3 * bothThreeOddCore p.2)
      =
    0 := by
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_mem_bothThree
      p hp
  exact rawEvenRamanujanBlockSum_three_mul_both_eq_zero
    (X := X0) (q := bothThreeOddCore p.1) (q' := bothThreeOddCore p.2)
    (q0 := bothThreeOddCore p.2)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_not_dvd_three
      p hpBoth)
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_coreBlockPeriod_coprime_three
      hp)
    (by
      unfold centeredRamanujanPairBlockPeriod
      exact dvd_mul_of_dvd_right
        (dvd_lcm_right (bothThreeOddCore p.1) (bothThreeOddCore p.2)) 2)

theorem bothThreeBaseFullBlockZeroAtX0_of_nonCoprimeCore_mem
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs)
    (hvalue :
      ∀ a ∈ bothThreeCoprimeCoreAverageZeroCores,
        bothThreeCoprimeCoreAverageZeroCoreValueGood a) :
    bothThreeBaseFullBlockZeroAtX0 p := by
  let a := bothThreeOddCore p.1
  let b := bothThreeOddCore p.2
  have hpBoth :
      p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_mem_bothThree
      p hp
  have hcoreRat :
      rawEvenRamanujanPairBlockSumRat X0 a b = 0 := by
    simpa [a, b] using bothThreeNonCoprimeCoreRawCorePairGood_of_record_mem hp
  have hcoreReal :
      rawEvenRamanujanPairBlockSum X0 a b = 0 := by
    rw [rawEvenRamanujanPairBlockSum_eq_ratCast]
    rw [hcoreRat]
    norm_num
  have hapos : 1 ≤ 3 * a := by
    have ha0 : 0 < a := by
      simpa [a] using
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_core_pos
          hpBoth
    omega
  have hbpos : 1 ≤ 3 * b := by
    have hb0 : 0 < b := by
      simpa [b] using
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_core_pos
          hpBoth
    omega
  have havgRat :
      ramanujanWindowAverageByGcdRat X0 (3 * a) = 0
        ∨ ramanujanWindowAverageByGcdRat X0 (3 * b) = 0 := by
    simpa [bothThreeCoprimeCoreAverageGood, a, b] using
      bothThreeNonCoprimeCoreAverageGood_of_mem hp hvalue
  have havgReal :
      ramanujanWindowAverage X0 (3 * a) = 0
        ∨ ramanujanWindowAverage X0 (3 * b) = 0 := by
    rcases havgRat with havgLeft | havgRight
    · left
      rw [ramanujanWindowAverage_eq_ratCast_ramanujanWindowAverageByGcdRat
        (X := X0) (q := 3 * a) hapos]
      rw [havgLeft]
      norm_num
    · right
      rw [ramanujanWindowAverage_eq_ratCast_ramanujanWindowAverageByGcdRat
        (X := X0) (q := 3 * b) hbpos]
      rw [havgRight]
      norm_num
  unfold bothThreeBaseFullBlockZeroAtX0
  change centeredRamanujanPairFullEvenBlockSum X0 (3 * a) (3 * b) = 0
  rw [centeredRamanujanPairFullEvenBlockSum_eq_rawBlock_decomposition]
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_basePairRawBlockSum_eq_zero_of_core
    hp (by simpa [a, b] using hcoreReal)]
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_baseLeftRawBlockSum_eq_zero
    hp]
  rw [PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_nonCoprimeCore_baseRightRawBlockSum_eq_zero
    hp]
  rcases havgReal with havgLeft | havgRight
  · rw [havgLeft]
    ring
  · rw [havgRight]
    ring

theorem bothThreeBaseFullBlockZeroAtX0_of_nonCoprimeCore_mem_of_averageValueCert
    (cert : BothThreeCoprimeCoreAverageValueCertificateAtX0)
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs) :
    bothThreeBaseFullBlockZeroAtX0 p :=
  bothThreeBaseFullBlockZeroAtX0_of_nonCoprimeCore_mem hp cert.value_on_zero_cores

theorem bothThreeBaseFullBlockZeroAtX0_of_nonCoprimeCore_mem_certified
    {p : ℕ × ℕ}
    (hp : p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs) :
    bothThreeBaseFullBlockZeroAtX0 p :=
  bothThreeBaseFullBlockZeroAtX0_of_nonCoprimeCore_mem_of_averageValueCert
    bothThreeCoprimeCoreAverageValueCert_true hp

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
