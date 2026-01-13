import Goldbach.AO_OffDiag.TailBlock

/-!
S2 algebra for the truncated σ-model `TailBlock.sigma_trunc_Q0`.

This file is intended to support the global “S2” route for `SigmaLowerOnWindow`:

1. On the locus where an even `N` has no odd prime divisor `≤ Q0`, the truncation is constant:
   `sigma_trunc_Q0 N = sigma_trunc_Q0 2`.

This is pure arithmetic: it uses only the closed-form definition of the Ramanujan sum
`TailBlock.ramanujanZ q N := μ(q/d) * φ(d)` with `d = gcd(q,N)`, together with the fact that
`TailBlock.muSq q` kills non-squarefree moduli.
-/

namespace Goldbach.Cert.SigmaTruncQ0_S2Algebra

open Goldbach
open Goldbach.AO_OffDiag

open scoped BigOperators

noncomputable section

/-- Predicate: `N` has no odd prime divisor `≤ Q0`. -/
def NoOddPrimeFactorUpToQ0 (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ TailBlock.Q0 → ¬ p ∣ N

private lemma gcd_eq_gcd_two_of_noOddPrimeFactor
    {q N : ℕ} (hq1 : 1 ≤ q) (hqQ : q ≤ TailBlock.Q0) (hN2 : 2 ∣ N)
    (hNo : NoOddPrimeFactorUpToQ0 N) (hqSq : Squarefree q) :
    Nat.gcd q N = Nat.gcd q 2 := by
  classical
  -- Both gcds are squarefree, so we can use `Squarefree.ext_iff`.
  have hsq1 : Squarefree (Nat.gcd q N) :=
    hqSq.squarefree_of_dvd (Nat.gcd_dvd_left q N)
  have hsq2 : Squarefree (Nat.gcd q 2) :=
    Nat.squarefree_two.squarefree_of_dvd (Nat.gcd_dvd_right q 2)

  refine (Nat.Squarefree.ext_iff hsq1 hsq2).2 ?_
  intro r hr
  constructor
  · intro hr_d1
    have hrq : r ∣ q := dvd_trans hr_d1 (Nat.gcd_dvd_left q N)
    have hrN : r ∣ N := dvd_trans hr_d1 (Nat.gcd_dvd_right q N)
    have hqpos : 0 < q := Nat.lt_of_lt_of_le (Nat.succ_pos 0) hq1
    have hr_le_q : r ≤ q := Nat.le_of_dvd hqpos hrq
    have hr_le_Q0 : r ≤ TailBlock.Q0 := le_trans hr_le_q hqQ
    by_cases hr2 : r = 2
    · -- If `r = 2`, then `2` divides `gcd q 2` whenever it divides `q`.
      subst hr2
      exact Nat.dvd_gcd hrq (by simp)
    · -- If `r ≠ 2`, then `r ≥ 3` (since `r` is prime), contradicting `hNo`.
      have h2lt : 2 < r := lt_of_le_of_ne hr.two_le (Ne.symm hr2)
      have hr_ge_3 : 3 ≤ r := (Nat.succ_le_iff).2 h2lt
      have : ¬ r ∣ N := hNo r hr hr_ge_3 hr_le_Q0
      exact (this hrN).elim
  · intro hr_d2
    have hr2 : r = 2 := by
      have hr_dvd_2 : r ∣ 2 := dvd_trans hr_d2 (Nat.gcd_dvd_right q 2)
      -- `r` is prime and divides the prime `2`, hence `r = 2`.
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hr_dvd_2
    subst hr2
    have h2q : 2 ∣ q := dvd_trans hr_d2 (Nat.gcd_dvd_left q 2)
    exact Nat.dvd_gcd h2q hN2

private lemma muSq_mul_ramanujanR_eq_of_noOddPrimeFactor
    {q N : ℕ} (hq1 : 1 ≤ q) (hqQ : q ≤ TailBlock.Q0) (hN2 : 2 ∣ N)
    (hNo : NoOddPrimeFactorUpToQ0 N) :
    TailBlock.muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * TailBlock.ramanujanR q N
      =
    TailBlock.muSq q * (1 / ((Nat.totient q : ℝ) ^ 2)) * TailBlock.ramanujanR q 2 := by
  classical
  by_cases hqSq : Squarefree q
  · have hgcd :
        Nat.gcd q N = Nat.gcd q 2 :=
      gcd_eq_gcd_two_of_noOddPrimeFactor (q := q) (N := N) hq1 hqQ hN2 hNo hqSq
    have hramZ : TailBlock.ramanujanZ q N = TailBlock.ramanujanZ q 2 := by
      -- `ramanujanZ` is definitional in terms of `gcd q N`.
      simp [TailBlock.ramanujanZ, hgcd]
    -- Now unfold the casts and use `muSq q = 1` in the squarefree case.
    simp [TailBlock.muSq, hqSq, TailBlock.ramanujanR, hramZ]
  · simp [TailBlock.muSq, hqSq]

/-- On the “coprime-to-small-odd-primes” locus, the truncation `sigma_trunc_Q0` is constant. -/
theorem sigma_trunc_Q0_eq_at2_of_noOddPrimeFactor
    {N : ℕ} (hN2 : 2 ∣ N) (hNo : NoOddPrimeFactorUpToQ0 N) :
    TailBlock.sigma_trunc_Q0 N = TailBlock.sigma_trunc_Q0 2 := by
  classical
  -- Expand the truncation as a finite sum and compare summands.
  simp [TailBlock.sigma_trunc_Q0]
  refine Finset.sum_congr rfl ?_
  intro q hq
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqQ : q ≤ TailBlock.Q0 := (Finset.mem_Icc.mp hq).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    muSq_mul_ramanujanR_eq_of_noOddPrimeFactor (q := q) (N := N) hq1 hqQ hN2 hNo

end

end Goldbach.Cert.SigmaTruncQ0_S2Algebra
