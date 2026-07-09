import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualBothThreeCoreSplit

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Dyadic-shape split for the `bothThree` residual.

Every record in this bucket has each modulus equal to either `3 * oddCore` or
`6 * oddCore`.  The coprime-core/non-coprime-core split is therefore still too
coarse for transport: the proof needs separate `3/3`, `3/6`, `6/3`, and `6/6`
surfaces.
-/

def bothThreeDyadicShape33 (p : ℕ × ℕ) : Prop :=
  p.1 = 3 * bothThreeOddCore p.1 ∧ p.2 = 3 * bothThreeOddCore p.2

def bothThreeDyadicShape36 (p : ℕ × ℕ) : Prop :=
  p.1 = 3 * bothThreeOddCore p.1 ∧ p.2 = 6 * bothThreeOddCore p.2

def bothThreeDyadicShape63 (p : ℕ × ℕ) : Prop :=
  p.1 = 6 * bothThreeOddCore p.1 ∧ p.2 = 3 * bothThreeOddCore p.2

def bothThreeDyadicShape66 (p : ℕ × ℕ) : Prop :=
  p.1 = 6 * bothThreeOddCore p.1 ∧ p.2 = 6 * bothThreeOddCore p.2

instance instDecidableBothThreeDyadicShape33
    (p : ℕ × ℕ) : Decidable (bothThreeDyadicShape33 p) := by
  unfold bothThreeDyadicShape33
  infer_instance

instance instDecidableBothThreeDyadicShape36
    (p : ℕ × ℕ) : Decidable (bothThreeDyadicShape36 p) := by
  unfold bothThreeDyadicShape36
  infer_instance

instance instDecidableBothThreeDyadicShape63
    (p : ℕ × ℕ) : Decidable (bothThreeDyadicShape63 p) := by
  unfold bothThreeDyadicShape63
  infer_instance

instance instDecidableBothThreeDyadicShape66
    (p : ℕ × ℕ) : Decidable (bothThreeDyadicShape66 p) := by
  unfold bothThreeDyadicShape66
  infer_instance

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape33Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    bothThreeDyadicShape33

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape36Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    bothThreeDyadicShape36

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape63Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    bothThreeDyadicShape63

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape66Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs.filter
    bothThreeDyadicShape66

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape33Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs.filter
    bothThreeDyadicShape33

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape36Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs.filter
    bothThreeDyadicShape36

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape63Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs.filter
    bothThreeDyadicShape63

def PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape66Pairs :
    Finset (ℕ × ℕ) :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs.filter
    bothThreeDyadicShape66

structure PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShapeZeroCertificateAtX0 :
    Prop where
  shape33_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape33Pairs,
      bothThreeDyadicShape33 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  shape36_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape36Pairs,
      bothThreeDyadicShape36 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  shape63_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape63Pairs,
      bothThreeDyadicShape63 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  shape66_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShape66Pairs,
      bothThreeDyadicShape66 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

structure PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShapeZeroCertificateAtX0 :
    Prop where
  shape33_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape33Pairs,
      bothThreeDyadicShape33 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  shape36_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape36Pairs,
      bothThreeDyadicShape36 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  shape63_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape63Pairs,
      bothThreeDyadicShape63 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0
  shape66_value_on_records :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShape66Pairs,
      bothThreeDyadicShape66 p →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_value_on_records_of_shapeSplit
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShapeZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCorePairs,
      Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2) →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp _hcop
  have hpBoth :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_mem_bothThree
      p hp
  rcases
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_eq_three_or_six_mul_core
        p hpBoth with hleft | hleft
  · rcases
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core
          p hpBoth with hright | hright
    · exact cert.shape33_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩
    · exact cert.shape36_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩
  · rcases
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core
          p hpBoth with hright | hright
    · exact cert.shape63_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩
    · exact cert.shape66_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_value_on_records_of_shapeSplit
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShapeZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCorePairs,
      ¬ Nat.Coprime (bothThreeOddCore p.1) (bothThreeOddCore p.2) →
        surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 := by
  intro p hp _hcop
  have hpBoth :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_mem_bothThree
      p hp
  rcases
      PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_left_eq_three_or_six_mul_core
        p hpBoth with hleft | hleft
  · rcases
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core
          p hpBoth with hright | hright
    · exact cert.shape33_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩
    · exact cert.shape36_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩
  · rcases
        PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_right_eq_three_or_six_mul_core
          p hpBoth with hright | hright
    · exact cert.shape63_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩
    · exact cert.shape66_value_on_records p
        (Finset.mem_filter.mpr ⟨hp, hleft, hright⟩)
        ⟨hleft, hright⟩

structure PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeShapeSplitZeroCertificateAtX0 :
    Prop where
  coprimeCore_shape_cert :
    PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCoreShapeZeroCertificateAtX0
  nonCoprimeCore_shape_cert :
    PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCoreShapeZeroCertificateAtX0

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coreSplit_of_shapeSplit
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeShapeSplitZeroCertificateAtX0) :
    PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeCoreSplitZeroCertificateAtX0 where
  coprimeCore_value_on_records :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeCoprimeCore_value_on_records_of_shapeSplit
      cert.coprimeCore_shape_cert
  nonCoprimeCore_value_on_records :=
    PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreeNonCoprimeCore_value_on_records_of_shapeSplit
      cert.nonCoprimeCore_shape_cert

theorem PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_of_shapeSplit
    (cert :
      PeriodicMainDyadicExceptionNonCoprimeCoreResidualBothThreeShapeSplitZeroCertificateAtX0) :
    ∀ p ∈ PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThreePairs,
      surrogatePeriodicMainActiveOrderedPairSummandRat X0 p = 0 :=
  PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_value_on_records_of_coreSplit
    (PeriodicMainZeroDyadicExceptionNonCoprimeCoreResidualBothThree_coreSplit_of_shapeSplit cert)

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
