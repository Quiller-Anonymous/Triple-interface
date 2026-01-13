import Goldbach.Cert.SigmaTruncQ0_S2Toggle

/-!
Certificate checker scaffolding for the S2 σ-lower project.

The global S2 reduction (`Goldbach/Cert/SigmaTruncQ0_S2Reduction.lean`) isolates a single missing
ingredient:

  `BpAlt p N ≥ 0` for all primes `3 ≤ p ≤ Q0`, all even `N`, with `p ∤ N`.

This file provides:

* a convenient predicate `BpAltNonneg p` for fixed `p`;
* a small, purely algebraic lemma that discharges the *large prime* range where `Q0/p ≤ 2`,
  so only `p = 3,5,7,...` need nontrivial certificate work.

The generated per-prime certificate modules should import this file and provide the remaining
small-prime proofs.
-/

namespace Goldbach.Cert.BpCertChecker

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.Cert.SigmaTruncQ0_S2Toggle

open scoped BigOperators

noncomputable section

/-- The fixed-`p` certificate goal: `BpAlt p N ≥ 0` for all even `N` with `p ∤ N`. -/
def BpAltNonneg (p : ℕ) : Prop :=
  ∀ N : ℕ, Even N → ¬ p ∣ N → 0 ≤ BpAlt p N

private lemma ramanujanR_one (N : ℕ) : TailBlock.ramanujanR 1 N = 1 := by
  simp [TailBlock.ramanujanR, TailBlock.ramanujanZ]

private lemma ramanujanR_two_of_even {N : ℕ} (hN : Even N) : TailBlock.ramanujanR 2 N = 1 := by
  have h2 : 2 ∣ N := (even_iff_two_dvd).1 hN
  have hgcd : Nat.gcd 2 N = 2 := Nat.gcd_eq_left h2
  simp [TailBlock.ramanujanR, TailBlock.ramanujanZ, hgcd]

private lemma muSq_nonneg (q : ℕ) : 0 ≤ TailBlock.muSq q := by
  by_cases hsq : Squarefree q <;> simp [TailBlock.muSq, hsq]

private lemma inv_totient_sq_nonneg (q : ℕ) : 0 ≤ ((Nat.totient q : ℝ) ^ 2)⁻¹ := by
  exact inv_nonneg.2 (sq_nonneg (Nat.totient q : ℝ))

/-- If the cutoff is tiny (`Q0 / p ≤ 2`), `BpAlt p N` is explicitly a sum of nonnegative terms. -/
theorem bpAltNonneg_of_Q0_div_p_le_two
    {p : ℕ} (_hp : p.Prime) (_hp3 : 3 ≤ p) (hsmall : TailBlock.Q0 / p ≤ 2) :
    BpAltNonneg p := by
  classical
  intro N hN _hpN
  -- Unfold the definition of `BpAlt` and show each summand is nonnegative.
  unfold BpAlt
  refine Finset.sum_nonneg ?_
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr_le2 : r ≤ 2 := le_trans (Finset.mem_Icc.mp hr).2 hsmall
  -- The cutoff forces `r = 1` or `r = 2` (and the latter only occurs when `Q0/p = 2`).
  cases r with
  | zero =>
      -- Contradiction with `1 ≤ r`.
      exact (Nat.not_succ_le_zero 0 hr1).elim
  | succ r =>
      cases r with
      | zero =>
          -- r = 1
          have hR : TailBlock.ramanujanR 1 N = 1 := ramanujanR_one N
          have hmu : 0 ≤ TailBlock.muSq (p * 1) := muSq_nonneg (p * 1)
          have htot : 0 ≤ ((Nat.totient (p * 1) : ℝ) ^ 2)⁻¹ := inv_totient_sq_nonneg (p * 1)
          have hRnonneg : 0 ≤ TailBlock.ramanujanR 1 N := by simpa [hR]
          exact mul_nonneg (mul_nonneg hmu htot) hRnonneg
      | succ r =>
          cases r with
          | zero =>
              -- r = 2
              have hR : TailBlock.ramanujanR 2 N = 1 := ramanujanR_two_of_even hN
              have hmu : 0 ≤ TailBlock.muSq (p * 2) := muSq_nonneg (p * 2)
              have htot : 0 ≤ ((Nat.totient (p * 2) : ℝ) ^ 2)⁻¹ := inv_totient_sq_nonneg (p * 2)
              have hRnonneg : 0 ≤ TailBlock.ramanujanR 2 N := by simpa [hR]
              exact mul_nonneg (mul_nonneg hmu htot) hRnonneg
          | succ r =>
              -- r ≥ 3 contradicts `r ≤ 2`.
              have h2lt : (2 : ℕ) < Nat.succ (Nat.succ (Nat.succ r)) := by
                exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ r))
              exact (Nat.not_le_of_gt h2lt hr_le2).elim

end

end Goldbach.Cert.BpCertChecker
