import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainSymmetry

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-- Rational one-variable Ramanujan average over the fixed even window. -/
def ramanujanObservableWindowAverageRat (X q : ℕ) : ℚ :=
  ∑ g ∈ q.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassWindowAverageRat X q g

/-- Coefficient-weighted one-variable complete-period block sum. -/
def rawRamanujanPeriodicBlockSumRat (X q q' q0 : ℕ) : ℚ :=
  ∑ g ∈ q0.divisors,
    ramanujanGcdClassCoeffRat q0 g
      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q0 g

/-- Coefficient-weighted two-variable complete-period block sum. -/
def rawRamanujanPeriodicPairBlockSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q q' g h

/-- Coefficient-weighted left one-sided correction over one complete period. -/
def rawRamanujanPeriodicLeftCorrectionSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * ramanujanGcdClassWindowAverageRat X q' h
      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q g

/-- Coefficient-weighted right one-sided correction over one complete period. -/
def rawRamanujanPeriodicRightCorrectionSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * ramanujanGcdClassWindowAverageRat X q g
      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q' h

/-- Coefficient-weighted mean-product correction over one complete period. -/
def rawRamanujanPeriodicMeanCorrectionSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * ramanujanGcdClassWindowAverageRat X q g
      * ramanujanGcdClassWindowAverageRat X q' h
      * evenRamanujanBlockCountRat q q'

/-- Scaled coefficient-weighted two-variable complete-period block sum. -/
def scaledRawRamanujanPeriodicPairBlockSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * rawEvenRamanujanGcdClassPairBlockResolvedCountRat X q q' g h

/-- Scaled coefficient-weighted left one-sided correction. -/
def scaledRawRamanujanPeriodicLeftCorrectionSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * ramanujanGcdClassWindowAverageRat X q' h
      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q g

/-- Scaled coefficient-weighted right one-sided correction. -/
def scaledRawRamanujanPeriodicRightCorrectionSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * ramanujanGcdClassWindowAverageRat X q g
      * rawEvenRamanujanGcdClassBlockPeriodicCountRat X q q' q' h

/-- Scaled coefficient-weighted mean-product correction. -/
def scaledRawRamanujanPeriodicMeanCorrectionSumRat (X q q' : ℕ) : ℚ :=
  ∑ g ∈ q.divisors, ∑ h ∈ q'.divisors,
    ramanujanGcdClassCoeffRat q g * ramanujanGcdClassCoeffRat q' h
      * (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * ramanujanGcdClassWindowAverageRat X q g
      * ramanujanGcdClassWindowAverageRat X q' h
      * evenRamanujanBlockCountRat q q'

theorem scaledRawRamanujanPeriodicPairBlockSumRat_comm
    (X q q' : ℕ) :
    scaledRawRamanujanPeriodicPairBlockSumRat X q q'
      =
    scaledRawRamanujanPeriodicPairBlockSumRat X q' q := by
  unfold scaledRawRamanujanPeriodicPairBlockSumRat
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [centeredRamanujanPairBlockPeriod_comm]
  rw [rawEvenRamanujanGcdClassPairBlockResolvedCountRat_comm]
  ring

theorem scaledRawRamanujanPeriodicLeftCorrectionSumRat_comm_right
    (X q q' : ℕ) :
    scaledRawRamanujanPeriodicLeftCorrectionSumRat X q q'
      =
    scaledRawRamanujanPeriodicRightCorrectionSumRat X q' q := by
  unfold scaledRawRamanujanPeriodicLeftCorrectionSumRat
    scaledRawRamanujanPeriodicRightCorrectionSumRat
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro g _hg
  rw [centeredRamanujanPairBlockPeriod_comm]
  rw [rawEvenRamanujanGcdClassBlockPeriodicCountRat_comm X q q' q g]
  ring

theorem scaledRawRamanujanPeriodicRightCorrectionSumRat_comm_left
    (X q q' : ℕ) :
    scaledRawRamanujanPeriodicRightCorrectionSumRat X q q'
      =
    scaledRawRamanujanPeriodicLeftCorrectionSumRat X q' q := by
  simpa using (scaledRawRamanujanPeriodicLeftCorrectionSumRat_comm_right X q' q).symm

/-- Reusable one-variable weight in the non-dyadic mean-product compression. -/
def surrogatePeriodicMainMeanProductWeightRat (X q : ℕ) : ℚ :=
  surrogateNormalizedSigmaTruncSummandCoeffRat q
    * ramanujanObservableWindowAverageRat X q

/-- Pair scalar left after the one-variable weights have been factored out. -/
def surrogatePeriodicMainMeanProductPairScalarRat (q q' : ℕ) : ℚ :=
  (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
    * evenRamanujanBlockCountRat q q'

theorem scaledRawRamanujanPeriodicMeanCorrectionSumRat_eq_mean_product
    (X q q' : ℕ) :
    scaledRawRamanujanPeriodicMeanCorrectionSumRat X q q'
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * ramanujanObservableWindowAverageRat X q
      * ramanujanObservableWindowAverageRat X q'
      * evenRamanujanBlockCountRat q q' := by
  unfold scaledRawRamanujanPeriodicMeanCorrectionSumRat
    ramanujanObservableWindowAverageRat
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro g _hg
  ring

theorem scaledRawRamanujanPeriodicLeftCorrectionSumRat_eq_block_sum_mul_average
    (X q q' : ℕ) :
    scaledRawRamanujanPeriodicLeftCorrectionSumRat X q q'
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * rawRamanujanPeriodicBlockSumRat X q q' q
      * ramanujanObservableWindowAverageRat X q' := by
  unfold scaledRawRamanujanPeriodicLeftCorrectionSumRat
    rawRamanujanPeriodicBlockSumRat
    ramanujanObservableWindowAverageRat
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro g _hg
  ring

theorem scaledRawRamanujanPeriodicRightCorrectionSumRat_eq_average_mul_block_sum
    (X q q' : ℕ) :
    scaledRawRamanujanPeriodicRightCorrectionSumRat X q q'
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * ramanujanObservableWindowAverageRat X q
      * rawRamanujanPeriodicBlockSumRat X q q' q' := by
  unfold scaledRawRamanujanPeriodicRightCorrectionSumRat
    rawRamanujanPeriodicBlockSumRat
    ramanujanObservableWindowAverageRat
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro h _hh
  refine Finset.sum_congr rfl ?_
  intro g _hg
  ring

theorem centeredRamanujanPairPeriodicMainTermRat_eq_aggregate_components
    (X q q' : ℕ) :
    centeredRamanujanPairPeriodicMainTermRat X q q'
      =
    scaledRawRamanujanPeriodicPairBlockSumRat X q q'
      - scaledRawRamanujanPeriodicLeftCorrectionSumRat X q q'
      - scaledRawRamanujanPeriodicRightCorrectionSumRat X q q'
      + scaledRawRamanujanPeriodicMeanCorrectionSumRat X q q' := by
  unfold centeredRamanujanPairPeriodicMainTermRat
    scaledRawRamanujanPeriodicPairBlockSumRat
    scaledRawRamanujanPeriodicLeftCorrectionSumRat
    scaledRawRamanujanPeriodicRightCorrectionSumRat
    scaledRawRamanujanPeriodicMeanCorrectionSumRat
  simp only [nsmul_eq_mul]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  abel_nf
  simp only [mul_assoc]

theorem centeredRamanujanPairPeriodicMainTermRat_eq_mean_product_of_aggregate_zeros
    {X q q' : ℕ}
    (hRaw : scaledRawRamanujanPeriodicPairBlockSumRat X q q' = 0)
    (hLeft : scaledRawRamanujanPeriodicLeftCorrectionSumRat X q q' = 0)
    (hRight : scaledRawRamanujanPeriodicRightCorrectionSumRat X q q' = 0) :
    centeredRamanujanPairPeriodicMainTermRat X q q'
      =
    (((H + 1) / centeredRamanujanPairBlockPeriod q q' : ℕ) : ℚ)
      * ramanujanObservableWindowAverageRat X q
      * ramanujanObservableWindowAverageRat X q'
      * evenRamanujanBlockCountRat q q' := by
  rw [centeredRamanujanPairPeriodicMainTermRat_eq_aggregate_components]
  rw [hRaw, hLeft, hRight,
    scaledRawRamanujanPeriodicMeanCorrectionSumRat_eq_mean_product]
  ring

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_weight_product_of_aggregate_zeros
    {X q q' : ℕ}
    (hneq : q ≠ q')
    (hRaw : scaledRawRamanujanPeriodicPairBlockSumRat X q q' = 0)
    (hLeft : scaledRawRamanujanPeriodicLeftCorrectionSumRat X q q' = 0)
    (hRight : scaledRawRamanujanPeriodicRightCorrectionSumRat X q q' = 0) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X (q, q')
      =
    surrogatePeriodicMainMeanProductPairScalarRat q q'
      * surrogatePeriodicMainMeanProductWeightRat X q
      * surrogatePeriodicMainMeanProductWeightRat X q' := by
  unfold surrogatePeriodicMainActiveOrderedPairSummandRat
  simp [hneq]
  rw [centeredRamanujanPairPeriodicMainTermRat_eq_mean_product_of_aggregate_zeros
    hRaw hLeft hRight]
  unfold surrogatePeriodicMainMeanProductPairScalarRat
    surrogatePeriodicMainMeanProductWeightRat
  ring

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
