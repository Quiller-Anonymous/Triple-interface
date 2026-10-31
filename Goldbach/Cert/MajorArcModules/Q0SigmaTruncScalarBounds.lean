import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum
import Goldbach.Cert.MajorArcModules.DivisorWindowDiscrepancy

/-!
Exact rational scalar bounds for the fixed `Q = 30000` truncation on even inputs.
The computable totient expression is proved equal to `Nat.totient`; no approximate
arithmetic is used by the certificate.
-/

namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds

open scoped BigOperators ArithmeticFunction.Moebius

def cutoff : ℕ := 30000

/-- Euler's finite product computes the totient without enumerating all residues. -/
def totientFast (n : ℕ) : ℕ :=
  (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1)

theorem totientFast_eq (n : ℕ) : totientFast n = Nat.totient n :=
  (Nat.totient_eq_div_primeFactors_mul n).symm

/-- The multiplicity obtained by grouping odd modulus `r` with modulus `2*r`. -/
def evenMultiplicity (r : ℕ) : ℚ := if 2 * r ≤ cutoff then 2 else 1

def oddWeightRat (r : ℕ) : ℚ :=
  if Odd r ∧ Squarefree r then evenMultiplicity r / (totientFast r : ℚ) ^ 2 else 0

/-- Full-even-period variance of the unnormalized truncation. -/
def varianceRat : ℚ :=
  ∑ r ∈ Finset.Icc 2 cutoff,
    if Odd r ∧ Squarefree r then
      (evenMultiplicity r) ^ 2 / (totientFast r : ℚ) ^ 3
    else 0

/-- The value of the unnormalized truncation at a common multiple of its moduli. -/
def valueAtZeroRat : ℚ :=
  ∑ r ∈ Finset.Icc 1 cutoff,
    if Odd r ∧ Squarefree r then evenMultiplicity r / (totientFast r : ℚ) else 0

/-- Divisor coefficient after restricting the raw truncation to even inputs. -/
def divisorCoefficientRat (d : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc 1 cutoff,
    if d ∣ r then oddWeightRat r * d * (μ (r / d) : ℚ) else 0

structure ScalarPacket where
  variance : ℚ
  valueAtZero : ℚ
  B1 : ℚ
  B3 : ℚ
  B5 : ℚ

def scalarPacket : ScalarPacket where
  variance := varianceRat
  valueAtZero := valueAtZeroRat
  B1 := divisorCoefficientRat 1
  B3 := divisorCoefficientRat 3
  B5 := divisorCoefficientRat 5

theorem scalarPacket_bounds :
    let s := scalarPacket
    s.variance < (601924 : ℚ) / 1000000 ∧
    2 ≤ s.valueAtZero ∧ s.valueAtZero < (11642 : ℚ) / 1000 ∧
    (13203 : ℚ) / 10000 < s.B1 ∧ s.B1 < (1321 : ℚ) / 1000 ∧
    (13203 : ℚ) / 10000 < s.B3 ∧ s.B3 < (1321 : ℚ) / 1000 ∧
    (4401 : ℚ) / 10000 < s.B5 ∧ s.B5 < (441 : ℚ) / 1000 := by
  native_decide

theorem varianceRat_lt : varianceRat < (601924 : ℚ) / 1000000 :=
  scalarPacket_bounds.1

theorem varianceRat_nonneg : 0 ≤ varianceRat := by
  apply Finset.sum_nonneg
  intro r hr
  split_ifs
  · exact div_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  · norm_num

theorem valueAtZeroRat_bounds :
    2 ≤ valueAtZeroRat ∧ valueAtZeroRat < (11642 : ℚ) / 1000 :=
  ⟨scalarPacket_bounds.2.1, scalarPacket_bounds.2.2.1⟩

theorem divisorCoefficientRat_one_bounds :
    (13203 : ℚ) / 10000 < divisorCoefficientRat 1 ∧
      divisorCoefficientRat 1 < (1321 : ℚ) / 1000 :=
  ⟨scalarPacket_bounds.2.2.2.1, scalarPacket_bounds.2.2.2.2.1⟩

theorem divisorCoefficientRat_three_bounds :
    (13203 : ℚ) / 10000 < divisorCoefficientRat 3 ∧
      divisorCoefficientRat 3 < (1321 : ℚ) / 1000 :=
  ⟨scalarPacket_bounds.2.2.2.2.2.1, scalarPacket_bounds.2.2.2.2.2.2.1⟩

theorem divisorCoefficientRat_five_bounds :
    (4401 : ℚ) / 10000 < divisorCoefficientRat 5 ∧
      divisorCoefficientRat 5 < (441 : ℚ) / 1000 :=
  ⟨scalarPacket_bounds.2.2.2.2.2.2.2.1, scalarPacket_bounds.2.2.2.2.2.2.2.2⟩

theorem three_five_le_twice_mean_gap :
    divisorCoefficientRat 3 ≤ 2 * (2 - divisorCoefficientRat 1) ∧
    divisorCoefficientRat 5 ≤ 2 * (2 - divisorCoefficientRat 1) := by
  obtain ⟨_, hb1⟩ := divisorCoefficientRat_one_bounds
  obtain ⟨_, hb3⟩ := divisorCoefficientRat_three_bounds
  obtain ⟨_, hb5⟩ := divisorCoefficientRat_five_bounds
  constructor <;> linarith

theorem oddWeightRat_cast (r : ℕ) :
    (oddWeightRat r : ℝ) =
      if Odd r ∧ Squarefree r then
        ((if 2 * r ≤ cutoff then 2 else 1) : ℝ) / (Nat.totient r : ℝ) ^ 2
      else 0 := by
  by_cases hr : Odd r ∧ Squarefree r <;>
    by_cases hcut : 2 * r ≤ cutoff <;>
    simp [oddWeightRat, evenMultiplicity, hr, hcut, totientFast_eq]

theorem divisorCoefficientRat_cast (d : ℕ) :
    (divisorCoefficientRat d : ℝ) =
      ∑ r ∈ Finset.Icc 1 cutoff,
        if d ∣ r then (oddWeightRat r : ℝ) * d * (μ (r / d) : ℝ) else 0 := by
  rw [divisorCoefficientRat, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : d ∣ r <;> simp [h]

/-- The elementary coefficient bound after retaining the cancellations at `d=3,5`. -/
def twoTermL1BoundRat : ℚ :=
  (2 + valueAtZeroRat - 2 * divisorCoefficientRat 1) ^ 2
    - 2 * ((divisorCoefficientRat 3) ^ 2 + (divisorCoefficientRat 5) ^ 2)

theorem twoTermL1BoundRat_le : twoTermL1BoundRat ≤ (11715704176 : ℚ) / 100000000 := by
  obtain ⟨hglo, hghi⟩ := valueAtZeroRat_bounds
  obtain ⟨hb1lo, hb1hi⟩ := divisorCoefficientRat_one_bounds
  obtain ⟨hb3lo, hb3hi⟩ := divisorCoefficientRat_three_bounds
  obtain ⟨hb5lo, hb5hi⟩ := divisorCoefficientRat_five_bounds
  let t := 2 + valueAtZeroRat - 2 * divisorCoefficientRat 1
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have hthi : t ≤ (55007 : ℚ) / 5000 := by dsimp [t]; linarith
  have htprod : 0 ≤ ((55007 : ℚ) / 5000 - t) * ((55007 : ℚ) / 5000 + t) :=
    mul_nonneg (by linarith) (by linarith)
  have hb3prod : 0 ≤ (divisorCoefficientRat 3 - (13203 : ℚ) / 10000) *
      (divisorCoefficientRat 3 + (13203 : ℚ) / 10000) :=
    mul_nonneg (by linarith) (by linarith)
  have hb5prod : 0 ≤ (divisorCoefficientRat 5 - (4401 : ℚ) / 10000) *
      (divisorCoefficientRat 5 + (4401 : ℚ) / 10000) :=
    mul_nonneg (by linarith) (by linarith)
  change t ^ 2 - 2 * ((divisorCoefficientRat 3) ^ 2 + (divisorCoefficientRat 5) ^ 2)
    ≤ (11715704176 : ℚ) / 100000000
  nlinarith

/-- The scalar budget is strictly below `1795`; the remaining task is the analytic bridge. -/
theorem twoTerm_normalized_budget_lt_1795 :
    (5001 * varianceRat + twoTermL1BoundRat) / ((33 : ℚ) / 25) ^ 2 < 1795 := by
  apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < ((33 : ℚ) / 25) ^ 2)).2
  have hv := varianceRat_lt
  have hL1 := twoTermL1BoundRat_le
  nlinarith

end Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds
