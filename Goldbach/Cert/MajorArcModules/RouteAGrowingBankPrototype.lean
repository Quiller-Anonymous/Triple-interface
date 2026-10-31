import Goldbach.BG_Bank
import Mathlib.NumberTheory.Bertrand

/-!
# Growing-bank prototype for Route A

This module is deliberately separate from `BG_Bank.wX`.  Replacing that definition in place would
invalidate the existing certificate graph before the replacement has passed its mathematical
feasibility checks.

The prototype uses a support interval whose width grows linearly with `X`, normalizes by its exact
prime mass, and grows the admissible pair-difference band with `X`.  Bertrand's theorem then gives
an unconditional prime and diagonal-pair coverage theorem on the dyadic output interval `(X,2X]`.

That coverage is weaker than the short-window positivity needed by the current Route A endpoint.
The distinction is intentional: proving coverage in `[X,X+H]` for every `X` would require a new
prime-pair theorem, not merely a different normalization.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAGrowingBankPrototype

open scoped BigOperators

open Goldbach

noncomputable section

/-- A scale-growing prime support, wide enough for Bertrand's theorem to apply. -/
def growingPrimeSupport (X : ℕ) : Finset ℕ :=
  Finset.Icc (X / 2 + 1) X

/-- A matching scale-growing pair-difference band. -/
def growingPairBand (X : ℕ) : Finset ℤ :=
  Finset.Icc (-(X : ℤ)) (X : ℤ)

/-- Total von Mangoldt mass on the growing support. -/
noncomputable def growingPrimeMass (X : ℕ) : ℝ :=
  ∑ n ∈ growingPrimeSupport X, Goldbach.BG_Bank.Λ n

/--
Prime coefficient normalized by the exact mass on the growing support.

The total coefficient mass is one.  Thus coefficient control comes from normalization rather than
from keeping the support width bounded independently of `X`.
-/
noncomputable def growingPrimeCoefficient (X n : ℕ) : ℝ :=
  if n ∈ growingPrimeSupport X then
    Goldbach.BG_Bank.Λ n / growingPrimeMass X
  else
    0

lemma Lambda_nonneg (n : ℕ) : 0 ≤ Goldbach.BG_Bank.Λ n := by
  unfold Goldbach.BG_Bank.Λ
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · exact le_rfl

lemma Lambda_pos_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 < Goldbach.BG_Bank.Λ p := by
  have hpcast : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  simpa [Goldbach.BG_Bank.Λ, hp] using Real.log_pos hpcast

/-- Bertrand coverage: the growing support contains a prime at every scale `X >= 2`. -/
theorem exists_prime_mem_growingPrimeSupport
    {X : ℕ} (hX : 2 ≤ X) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∈ growingPrimeSupport X := by
  have hhalf : X / 2 ≠ 0 := by omega
  rcases Nat.exists_prime_lt_and_le_two_mul (X / 2) hhalf with ⟨p, hp, hlo, hhi⟩
  refine ⟨p, hp, ?_⟩
  rw [growingPrimeSupport, Finset.mem_Icc]
  constructor <;> omega

/-- The exact normalizing mass is positive at every nontrivial scale. -/
theorem growingPrimeMass_pos
    {X : ℕ} (hX : 2 ≤ X) :
    0 < growingPrimeMass X := by
  rcases exists_prime_mem_growingPrimeSupport hX with ⟨p, hp, hpS⟩
  unfold growingPrimeMass
  exact Finset.sum_pos' (fun n hn => Lambda_nonneg n) ⟨p, hpS, Lambda_pos_of_prime hp⟩

lemma growingPrimeCoefficient_nonneg
    {X : ℕ} (hX : 2 ≤ X) (n : ℕ) :
    0 ≤ growingPrimeCoefficient X n := by
  unfold growingPrimeCoefficient
  split_ifs
  · exact div_nonneg (Lambda_nonneg n) (le_of_lt (growingPrimeMass_pos hX))
  · exact le_rfl

/-- The normalized growing coefficients have exact total mass one. -/
theorem growingPrimeCoefficient_sum_eq_one
    {X : ℕ} (hX : 2 ≤ X) :
    ∑ n ∈ growingPrimeSupport X, growingPrimeCoefficient X n = 1 := by
  have hmass_ne : growingPrimeMass X ≠ 0 := ne_of_gt (growingPrimeMass_pos hX)
  calc
    ∑ n ∈ growingPrimeSupport X, growingPrimeCoefficient X n
        = ∑ n ∈ growingPrimeSupport X,
            Goldbach.BG_Bank.Λ n / growingPrimeMass X := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [growingPrimeCoefficient, hn]
    _ = growingPrimeMass X / growingPrimeMass X := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          rfl
    _ = 1 := div_self hmass_ne

/-- The absolute coefficient mass is uniformly one despite the growing support. -/
theorem growingPrimeCoefficient_l1Mass_eq_one
    {X : ℕ} (hX : 2 ≤ X) :
    ∑ n ∈ growingPrimeSupport X, |growingPrimeCoefficient X n| = 1 := by
  calc
    ∑ n ∈ growingPrimeSupport X, |growingPrimeCoefficient X n|
        = ∑ n ∈ growingPrimeSupport X, growingPrimeCoefficient X n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [abs_of_nonneg (growingPrimeCoefficient_nonneg hX n)]
    _ = 1 := growingPrimeCoefficient_sum_eq_one hX

lemma zero_mem_growingPairBand (X : ℕ) : (0 : ℤ) ∈ growingPairBand X := by
  simp [growingPairBand]

/--
Explicit dyadic pair coverage for the redesigned support and pair band.

The witness is the diagonal pair `(p,p)` supplied by Bertrand.  Its sum lies in `(X,2X]` and its
difference is zero, hence it survives the growing pair band.
-/
theorem exists_diagonal_prime_pair_dyadic_coverage
    {X : ℕ} (hX : 2 ≤ X) :
    ∃ p N : ℕ,
      Nat.Prime p
        ∧ p ∈ growingPrimeSupport X
        ∧ N = 2 * p
        ∧ Even N
        ∧ N ∈ Finset.Ioc X (2 * X)
        ∧ ((p : ℤ) - (p : ℤ)) ∈ growingPairBand X := by
  rcases exists_prime_mem_growingPrimeSupport hX with ⟨p, hp, hpS⟩
  refine ⟨p, 2 * p, hp, hpS, rfl, even_two_mul p, ?_, ?_⟩
  · rw [Finset.mem_Ioc]
    have hpBounds := Finset.mem_Icc.mp hpS
    constructor <;> omega
  · simpa using zero_mem_growingPairBand X

/--
Coverage contract still missing from the current Route A endpoint: every short output window must
contain enough prime-pair mass.  The growing-bank theorem above establishes only dyadic coverage.
-/
def ShortWindowPairCoverage
    (support : ℕ → Finset ℕ) (windowRadius : ℕ) : Prop :=
  ∀ X : ℕ, 2 ≤ X →
    ∃ p q N : ℕ,
      Nat.Prime p
        ∧ Nat.Prime q
        ∧ p ∈ support X
        ∧ q ∈ support X
        ∧ N = p + q
        ∧ N ∈ Finset.Icc X (X + windowRadius)

end

end Goldbach.Cert.MajorArcModules.RouteAGrowingBankPrototype
