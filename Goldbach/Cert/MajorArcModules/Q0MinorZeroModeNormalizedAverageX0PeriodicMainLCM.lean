import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainMeanProduct

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-- The reusable pair value after the non-dyadic periodic-main LCM compression. -/
def surrogatePeriodicMainLCMCompressedPairValueRat
    (X : ℕ) (p : ℕ × ℕ) : ℚ :=
  surrogatePeriodicMainMeanProductPairScalarRat p.1 p.2
    * surrogatePeriodicMainMeanProductWeightRat X p.1
    * surrogatePeriodicMainMeanProductWeightRat X p.2

/-- The three aggregate component zeros needed to collapse an active pair to its mean-product value. -/
def surrogatePeriodicMainAggregateComponentsZeroRat
    (X : ℕ) (p : ℕ × ℕ) : Prop :=
  scaledRawRamanujanPeriodicPairBlockSumRat X p.1 p.2 = 0
    ∧ scaledRawRamanujanPeriodicLeftCorrectionSumRat X p.1 p.2 = 0
    ∧ scaledRawRamanujanPeriodicRightCorrectionSumRat X p.1 p.2 = 0

abbrev surrogatePeriodicMainAggregateComponentsZeroAtX0Rat
    (p : ℕ × ℕ) : Prop :=
  surrogatePeriodicMainAggregateComponentsZeroRat X0 p

theorem surrogatePeriodicMainLCMCompressedPairValueRat_eq_of_weight_scalar
    {X : ℕ} {p : ℕ × ℕ} {weight : ℕ → ℚ} {scalar : ℕ → ℚ}
    (hscalar :
      surrogatePeriodicMainMeanProductPairScalarRat p.1 p.2
        = scalar (Nat.lcm p.1 p.2))
    (hleft : surrogatePeriodicMainMeanProductWeightRat X p.1 = weight p.1)
    (hright : surrogatePeriodicMainMeanProductWeightRat X p.2 = weight p.2) :
    surrogatePeriodicMainLCMCompressedPairValueRat X p
      =
    scalar (Nat.lcm p.1 p.2) * weight p.1 * weight p.2 := by
  simp [surrogatePeriodicMainLCMCompressedPairValueRat, hscalar, hleft, hright]

theorem surrogatePeriodicMainLCMCompressedPairValueRat_eq_pairValue_of_weight_scalar
    {X : ℕ} {p : ℕ × ℕ} {weight : ℕ → ℚ} {scalar : ℕ → ℚ} {pairValue : ℕ × ℕ → ℚ}
    (hpair :
      pairValue p = scalar (Nat.lcm p.1 p.2) * weight p.1 * weight p.2)
    (hscalar :
      surrogatePeriodicMainMeanProductPairScalarRat p.1 p.2
        = scalar (Nat.lcm p.1 p.2))
    (hleft : surrogatePeriodicMainMeanProductWeightRat X p.1 = weight p.1)
    (hright : surrogatePeriodicMainMeanProductWeightRat X p.2 = weight p.2) :
    surrogatePeriodicMainLCMCompressedPairValueRat X p = pairValue p := by
  rw [surrogatePeriodicMainLCMCompressedPairValueRat_eq_of_weight_scalar
    (X := X) (p := p) (weight := weight) (scalar := scalar) hscalar hleft hright]
  exact hpair.symm

theorem surrogatePeriodicMainAggregateComponentsZeroRat_swap
    {X q q' : ℕ}
    (hzero : surrogatePeriodicMainAggregateComponentsZeroRat X (q, q')) :
    surrogatePeriodicMainAggregateComponentsZeroRat X (q', q) := by
  rcases hzero with ⟨hRaw, hLeft, hRight⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← scaledRawRamanujanPeriodicPairBlockSumRat_comm X q q']
    exact hRaw
  · rw [← scaledRawRamanujanPeriodicRightCorrectionSumRat_comm_left X q q']
    exact hRight
  · rw [← scaledRawRamanujanPeriodicLeftCorrectionSumRat_comm_right X q q']
    exact hLeft

theorem surrogatePeriodicMainAggregateComponentsZeroAtX0Rat_swap
    {q q' : ℕ}
    (hzero : surrogatePeriodicMainAggregateComponentsZeroAtX0Rat (q, q')) :
    surrogatePeriodicMainAggregateComponentsZeroAtX0Rat (q', q) :=
  surrogatePeriodicMainAggregateComponentsZeroRat_swap (X := X0) hzero

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_eq_lcmCompressedPairValue_of_componentZeros
    {X : ℕ} {p : ℕ × ℕ}
    (hneq : p.1 ≠ p.2)
    (hzero : surrogatePeriodicMainAggregateComponentsZeroRat X p) :
    surrogatePeriodicMainActiveOrderedPairSummandRat X p
      =
    surrogatePeriodicMainLCMCompressedPairValueRat X p := by
  rcases p with ⟨q, q'⟩
  exact
    surrogatePeriodicMainActiveOrderedPairSummandRat_eq_weight_product_of_aggregate_zeros
      (X := X) (q := q) (q' := q') hneq hzero.1 hzero.2.1 hzero.2.2

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_sum_eq_lcmCompressedPairValue_sum_of_componentZeros
    {X : ℕ} (pairs : Finset (ℕ × ℕ))
    (hneq : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hzero : ∀ p ∈ pairs, surrogatePeriodicMainAggregateComponentsZeroRat X p) :
    (∑ p ∈ pairs, surrogatePeriodicMainActiveOrderedPairSummandRat X p)
      =
    (∑ p ∈ pairs, surrogatePeriodicMainLCMCompressedPairValueRat X p) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact
    surrogatePeriodicMainActiveOrderedPairSummandRat_eq_lcmCompressedPairValue_of_componentZeros
      (X := X) (p := p) (hneq p hp) (hzero p hp)

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_sum_eq_lcmCompressedTotal_of_componentZeros
    {X : ℕ} {pairs : Finset (ℕ × ℕ)} {total : ℚ}
    (hneq : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hzero : ∀ p ∈ pairs, surrogatePeriodicMainAggregateComponentsZeroRat X p)
    (hsum :
      (∑ p ∈ pairs, surrogatePeriodicMainLCMCompressedPairValueRat X p) = total) :
    (∑ p ∈ pairs, surrogatePeriodicMainActiveOrderedPairSummandRat X p) = total := by
  rw [surrogatePeriodicMainActiveOrderedPairSummandRat_sum_eq_lcmCompressedPairValue_sum_of_componentZeros
    pairs hneq hzero]
  exact hsum

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_sum_eq_certifiedTotal_of_componentZeros
    {X : ℕ} {pairs : Finset (ℕ × ℕ)} {pairValue : ℕ × ℕ → ℚ} {total : ℚ}
    (hneq : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hzero : ∀ p ∈ pairs, surrogatePeriodicMainAggregateComponentsZeroRat X p)
    (hvalue :
      ∀ p ∈ pairs,
        surrogatePeriodicMainLCMCompressedPairValueRat X p = pairValue p)
    (hsum : (∑ p ∈ pairs, pairValue p) = total) :
    (∑ p ∈ pairs, surrogatePeriodicMainActiveOrderedPairSummandRat X p) = total := by
  calc
    (∑ p ∈ pairs, surrogatePeriodicMainActiveOrderedPairSummandRat X p)
        = ∑ p ∈ pairs, surrogatePeriodicMainLCMCompressedPairValueRat X p :=
          surrogatePeriodicMainActiveOrderedPairSummandRat_sum_eq_lcmCompressedPairValue_sum_of_componentZeros
            pairs hneq hzero
    _ = ∑ p ∈ pairs, pairValue p := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact hvalue p hp
    _ = total := hsum

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_sum_eq_lcmCompressedTotal_of_componentZeros
    {pairs : Finset (ℕ × ℕ)} {total : ℚ}
    (hneq : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hzero : ∀ p ∈ pairs, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p)
    (hsum :
      (∑ p ∈ pairs, surrogatePeriodicMainLCMCompressedPairValueRat X0 p) = total) :
    (∑ p ∈ pairs, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = total :=
  surrogatePeriodicMainActiveOrderedPairSummandRat_sum_eq_lcmCompressedTotal_of_componentZeros
    (X := X0) hneq hzero hsum

theorem surrogatePeriodicMainActiveOrderedPairSummandRat_X0_sum_eq_certifiedTotal_of_componentZeros
    {pairs : Finset (ℕ × ℕ)} {pairValue : ℕ × ℕ → ℚ} {total : ℚ}
    (hneq : ∀ p ∈ pairs, p.1 ≠ p.2)
    (hzero : ∀ p ∈ pairs, surrogatePeriodicMainAggregateComponentsZeroAtX0Rat p)
    (hvalue :
      ∀ p ∈ pairs,
        surrogatePeriodicMainLCMCompressedPairValueRat X0 p = pairValue p)
    (hsum : (∑ p ∈ pairs, pairValue p) = total) :
    (∑ p ∈ pairs, surrogatePeriodicMainActiveOrderedPairSummandRat X0 p) = total :=
  surrogatePeriodicMainActiveOrderedPairSummandRat_sum_eq_certifiedTotal_of_componentZeros
    (X := X0) hneq hzero hvalue hsum

theorem Finset.pair_disjoint_of_lcm_eq
    {pairsA pairsB : Finset (ℕ × ℕ)} {lcmA lcmB : ℕ}
    (hA : ∀ p ∈ pairsA, Nat.lcm p.1 p.2 = lcmA)
    (hB : ∀ p ∈ pairsB, Nat.lcm p.1 p.2 = lcmB)
    (hne : lcmA ≠ lcmB) :
    Disjoint pairsA pairsB := by
  rw [Finset.disjoint_left]
  intro p hpA hpB
  exact hne ((hA p hpA).symm.trans (hB p hpB))

theorem Finset.pair_disjoint_of_lcm_mem
    {pairsA pairsB : Finset (ℕ × ℕ)} {lcmsA lcmsB : Finset ℕ}
    (hA : ∀ p ∈ pairsA, Nat.lcm p.1 p.2 ∈ lcmsA)
    (hB : ∀ p ∈ pairsB, Nat.lcm p.1 p.2 ∈ lcmsB)
    (hdisj : Disjoint lcmsA lcmsB) :
    Disjoint pairsA pairsB := by
  rw [Finset.disjoint_left] at hdisj ⊢
  intro p hpA hpB
  exact hdisj (hA p hpA) (hB p hpB)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
