import Mathlib.Data.Nat.Factorization.Basic
import Goldbach.Cert.SigmaTruncQ0_S2Algebra
import Goldbach.Cert.SigmaTruncQ0_S2Toggle
import Goldbach.Cert.SigmaTruncQ0At2Cert

/-!
Global S2 reduction for the truncated singular series `TailBlock.sigma_trunc_Q0`.

This file packages the **pure Lean** part of the global “S2” strategy:

* `sigma_trunc_Q0` is constant on the coprime/parity locus (proved in
  `Goldbach/Cert/SigmaTruncQ0_S2Algebra.lean`).
* A prime-toggle identity describes the change `sigma_trunc_Q0 (p*N) - sigma_trunc_Q0 N`
  (proved in `Goldbach/Cert/SigmaTruncQ0_S2Toggle.lean`).

Assuming a nonnegativity input for the toggle short sum `BpAlt`, we derive the global lower bound
`sigma_trunc_Q0 N ≥ sigma_trunc_Q0 2` for all even `N`, and hence a concrete bound
`sigma_trunc_Q0 N ≥ 33/25`.

This is designed to be the *Lean-side checker* that consumes generated certificates for `BpAlt`.
-/

namespace Goldbach.Cert.SigmaTruncQ0_S2Reduction

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.TailBlock

open scoped BigOperators

noncomputable section

namespace S2

open Goldbach.Cert.SigmaTruncQ0_S2Algebra
open Goldbach.Cert.SigmaTruncQ0_S2Toggle

/-- The “certificate interface”: nonnegativity of the S2 toggle sum `BpAlt` for primes `≤ Q0`. -/
def BpAltNonnegUpToQ0 : Prop :=
  ∀ p : ℕ,
    p.Prime → 3 ≤ p → p ≤ TailBlock.Q0 →
      ∀ N : ℕ, Even N → ¬ p ∣ N → 0 ≤ BpAlt p N

private lemma sigma_trunc_Q0_eq_mul_ordCompl
    {p N : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    TailBlock.sigma_trunc_Q0 N = TailBlock.sigma_trunc_Q0 (p * ordCompl[p] N) := by
  classical
  -- Expand the truncation as a finite sum; compare summands via `ramanujanZ`'s gcd-closed form.
  simp [TailBlock.sigma_trunc_Q0]
  refine Finset.sum_congr rfl ?_
  intro q hq
  by_cases hqSq : Squarefree q
  · -- On squarefree moduli, `ramanujanZ q _` depends only on `gcd q _`, and exponents are irrelevant.
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : q ≤ TailBlock.Q0 := (Finset.mem_Icc.mp hq).2
    -- Show `gcd q N = gcd q (p * ordCompl[p] N)` by prime-divisor extensionality (since `q` is squarefree).
    have hsq1 : Squarefree (Nat.gcd q N) :=
      hqSq.squarefree_of_dvd (Nat.gcd_dvd_left q N)
    have hsq2 : Squarefree (Nat.gcd q (p * ordCompl[p] N)) :=
      hqSq.squarefree_of_dvd (Nat.gcd_dvd_left q (p * ordCompl[p] N))
    have hgcd :
        Nat.gcd q N = Nat.gcd q (p * ordCompl[p] N) := by
      refine (Nat.Squarefree.ext_iff hsq1 hsq2).2 ?_
      intro r hr
      constructor
      · intro hr_d1
        have hrq : r ∣ q := dvd_trans hr_d1 (Nat.gcd_dvd_left q N)
        have hrN : r ∣ N := dvd_trans hr_d1 (Nat.gcd_dvd_right q N)
        have hNfac : ordProj[p] N * ordCompl[p] N = N :=
          Nat.ordProj_mul_ordCompl_eq_self N p
        by_cases hrp : r = p
        · subst r
          exact Nat.dvd_gcd hrq (dvd_mul_of_dvd_left (dvd_refl p) _)
        · have hr_prod : r ∣ ordProj[p] N * ordCompl[p] N := by
            simpa [hNfac] using hrN
          have hr_not_ordProj : ¬ r ∣ ordProj[p] N := by
            intro hrd
            have : r ∣ p := by
              -- `ordProj[p] N = p^(N.factorization p)`
              exact hr.dvd_of_dvd_pow (by simpa using hrd)
            have : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 this
            exact hrp this
          have hr_ordCompl : r ∣ ordCompl[p] N := by
            rcases (hr.dvd_mul.mp hr_prod) with h | h
            · exact (hr_not_ordProj h).elim
            · exact h
          exact Nat.dvd_gcd hrq (dvd_mul_of_dvd_right hr_ordCompl p)
      · intro hr_d2
        have hrq : r ∣ q := dvd_trans hr_d2 (Nat.gcd_dvd_left q (p * ordCompl[p] N))
        have hrpN : r ∣ p * ordCompl[p] N :=
          dvd_trans hr_d2 (Nat.gcd_dvd_right q (p * ordCompl[p] N))
        by_cases hrp : r = p
        · subst hrp
          exact Nat.dvd_gcd hrq hpN
        · have hr_ordCompl : r ∣ ordCompl[p] N := by
            rcases (hr.dvd_mul.mp hrpN) with h | h
            · have : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 h
              exact (hrp this).elim
            · exact h
          have hrN : r ∣ N := dvd_trans hr_ordCompl (Nat.ordCompl_dvd N p)
          exact Nat.dvd_gcd hrq hrN
    have hramZ : TailBlock.ramanujanZ q N = TailBlock.ramanujanZ q (p * ordCompl[p] N) := by
      simp [TailBlock.ramanujanZ, hgcd]
    simp [TailBlock.muSq, hqSq, TailBlock.ramanujanR, hramZ]
  · -- If `q` is not squarefree, `muSq q = 0` so the term is `0` on both sides.
    simp [TailBlock.muSq, hqSq]

private lemma ordCompl_even_of_even_of_three_le_prime
    {p N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hN : Even N) :
    Even (ordCompl[p] N) := by
  classical
  have hp_ne_two : p ≠ 2 := by
    have : 2 < p := lt_of_lt_of_le (by decide : 2 < 3) hp3
    exact ne_of_gt this
  have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
  have hord_odd : Odd (ordProj[p] N) := by
    -- `ordProj[p] N = p^(N.factorization p)`
    simpa using (hp_odd.pow (n := Nat.factorization N p))
  have hcop : Nat.Coprime 2 (ordProj[p] N) := (Nat.coprime_two_left).2 hord_odd
  have h2 : 2 ∣ N := (even_iff_two_dvd).1 hN
  have hmul : 2 ∣ ordProj[p] N * ordCompl[p] N := by
    simpa [Nat.ordProj_mul_ordCompl_eq_self N p] using h2
  have : 2 ∣ ordCompl[p] N :=
    (Nat.Coprime.dvd_mul_left (m := ordProj[p] N) (n := ordCompl[p] N) hcop).1 hmul
  exact (even_iff_two_dvd).2 this

private def smallOddPrimeDivisors (N : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun p => 3 ≤ p ∧ p ≤ TailBlock.Q0

private lemma noOddPrimeFactorUpToQ0_of_smallOddPrimeDivisors_empty
    {N : ℕ} (hN0 : N ≠ 0) (hS : smallOddPrimeDivisors N = ∅) :
    NoOddPrimeFactorUpToQ0 N := by
  intro p hp hp3 hpQ0 hp_dvd
  have hp_mem_pf : p ∈ N.primeFactors :=
    (Nat.mem_primeFactors_of_ne_zero hN0).2 ⟨hp, hp_dvd⟩
  have hpQ0' : p ≤ TailBlock.Q0 := by simpa using hpQ0
  have hp_mem_S : p ∈ smallOddPrimeDivisors N :=
    Finset.mem_filter.2 ⟨hp_mem_pf, ⟨hp3, hpQ0'⟩⟩
  simpa [hS] using hp_mem_S

private lemma smallOddPrimeDivisors_ordCompl_subset
    {p N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpQ0 : p ≤ TailBlock.Q0) (hN0 : N ≠ 0)
    (hp_mem : p ∈ smallOddPrimeDivisors N) :
    smallOddPrimeDivisors (ordCompl[p] N) ⊆ (smallOddPrimeDivisors N).erase p := by
  classical
  intro q hq
  have hq' : q ∈ (ordCompl[p] N).primeFactors := by
    exact (Finset.mem_filter.mp hq).1
  have hq_range : 3 ≤ q ∧ q ≤ TailBlock.Q0 := (Finset.mem_filter.mp hq).2
  have hq_fac : q.Prime ∧ q ∣ ordCompl[p] N :=
    (Nat.mem_primeFactors_of_ne_zero (Nat.ordCompl_pos p hN0).ne').1 hq'
  have hq_dvd_N : q ∣ N := dvd_trans hq_fac.2 (Nat.ordCompl_dvd N p)
  have hq_mem_pf : q ∈ N.primeFactors := by
    exact (Nat.mem_primeFactors_of_ne_zero hN0).2 ⟨hq_fac.1, hq_dvd_N⟩
  have hqQ0 : q ≤ TailBlock.Q0 := by simpa using hq_range.2
  have hq_mem_S : q ∈ smallOddPrimeDivisors N :=
    Finset.mem_filter.2 ⟨hq_mem_pf, ⟨hq_range.1, hqQ0⟩⟩
  have hq_ne_p : q ≠ p := by
    intro hqp
    subst q
    have : ¬ p ∣ ordCompl[p] N := Nat.not_dvd_ordCompl hp hN0
    exact (this hq_fac.2).elim
  exact Finset.mem_erase.2 ⟨hq_ne_p, hq_mem_S⟩

private lemma sigma_trunc_Q0_ge_of_remove_one_prime
    (hBp : BpAltNonnegUpToQ0)
    {p N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpQ0 : p ≤ TailBlock.Q0)
    (hN0 : N ≠ 0) (hN_even : Even N) (hp_dvd : p ∣ N) :
    TailBlock.sigma_trunc_Q0 (ordCompl[p] N) ≤ TailBlock.sigma_trunc_Q0 N := by
  have hN_eq : TailBlock.sigma_trunc_Q0 N = TailBlock.sigma_trunc_Q0 (p * ordCompl[p] N) :=
    sigma_trunc_Q0_eq_mul_ordCompl (hp := hp) hp_dvd
  have hp_not : ¬ p ∣ ordCompl[p] N := Nat.not_dvd_ordCompl hp hN0
  have hEven' : Even (ordCompl[p] N) :=
    ordCompl_even_of_even_of_three_le_prime (hp := hp) hp3 hN_even
  have hBp' : 0 ≤ BpAlt p (ordCompl[p] N) :=
    hBp p hp hp3 hpQ0 (ordCompl[p] N) hEven' hp_not
  have hdiff_nonneg :
      0 ≤ TailBlock.sigma_trunc_Q0 (p * ordCompl[p] N) - TailBlock.sigma_trunc_Q0 (ordCompl[p] N) := by
    -- Use the toggle identity, then nonnegativity of `BpAlt`.
    rw [sigma_trunc_Q0_toggle_eq (hp := hp) (hpN := hp_not)]
    exact mul_nonneg (Nat.cast_nonneg p) hBp'
  have hle :
      TailBlock.sigma_trunc_Q0 (ordCompl[p] N) ≤ TailBlock.sigma_trunc_Q0 (p * ordCompl[p] N) :=
    (sub_nonneg).1 hdiff_nonneg
  -- Rewrite the RHS back to `sigma_trunc_Q0 N`.
  simpa [hN_eq] using hle

theorem sigma_trunc_Q0_ge_at2_of_BpAltNonnegUpToQ0
    (hBp : BpAltNonnegUpToQ0) :
    ∀ {N : ℕ}, N ≠ 0 → Even N → TailBlock.sigma_trunc_Q0 2 ≤ TailBlock.sigma_trunc_Q0 N := by
  classical
  -- Induction on the number of odd prime divisors `≤ Q0`.
  intro N hN0 hN_even
  -- Prove the stronger statement: `card S ≤ k → σ(2) ≤ σ(N)` by induction on `k`.
  have main :
      ∀ k : ℕ,
        ∀ {n : ℕ}, n ≠ 0 → Even n →
          (smallOddPrimeDivisors n).card ≤ k →
            TailBlock.sigma_trunc_Q0 2 ≤ TailBlock.sigma_trunc_Q0 n := by
    intro k
    induction k with
    | zero =>
        intro n hn0 hn_even hk
        have hcard0 : (smallOddPrimeDivisors n).card = 0 := Nat.le_zero.1 hk
        have hEmpty : smallOddPrimeDivisors n = ∅ := Finset.card_eq_zero.mp hcard0
        have hNo : NoOddPrimeFactorUpToQ0 n :=
          noOddPrimeFactorUpToQ0_of_smallOddPrimeDivisors_empty (N := n) hn0 hEmpty
        have h2 : 2 ∣ n := (even_iff_two_dvd).1 hn_even
        -- On this locus, the truncation is constant and equals the value at `2`.
        have hEq : TailBlock.sigma_trunc_Q0 n = TailBlock.sigma_trunc_Q0 2 :=
          sigma_trunc_Q0_eq_at2_of_noOddPrimeFactor (N := n) h2 hNo
        simpa [hEq]
    | succ k ih =>
        intro n hn0 hn_even hk'
        by_cases hk : (smallOddPrimeDivisors n).card ≤ k
        · exact ih hn0 hn_even hk
        · -- Then `card = k+1` and the set is nonempty; remove one prime factor and recurse.
          have hcard_eq : (smallOddPrimeDivisors n).card = k.succ := by omega
          have hS_nonempty : (smallOddPrimeDivisors n).Nonempty := by
            have : 0 < (smallOddPrimeDivisors n).card := by
              simpa [hcard_eq] using Nat.succ_pos k
            exact Finset.card_pos.mp this
          rcases hS_nonempty with ⟨p, hp_mem⟩
          have hp_mem_pf : p ∈ n.primeFactors := (Finset.mem_filter.mp hp_mem).1
          have hp_range : 3 ≤ p ∧ p ≤ TailBlock.Q0 := (Finset.mem_filter.mp hp_mem).2
          have hp' : p.Prime ∧ p ∣ n := (Nat.mem_primeFactors_of_ne_zero hn0).1 hp_mem_pf
          have hn_le :
              TailBlock.sigma_trunc_Q0 2 ≤ TailBlock.sigma_trunc_Q0 (ordCompl[p] n) := by
            -- `ordCompl[p] n` removes `p` and does not introduce new small odd primes, so the measure drops.
            have hsub :
                smallOddPrimeDivisors (ordCompl[p] n) ⊆ (smallOddPrimeDivisors n).erase p :=
              smallOddPrimeDivisors_ordCompl_subset (p := p) (N := n)
                hp'.1 hp_range.1 hp_range.2 hn0 hp_mem
            have hcard_le' :
                (smallOddPrimeDivisors (ordCompl[p] n)).card ≤ k := by
              have hcard_le_erase :
                  (smallOddPrimeDivisors (ordCompl[p] n)).card ≤ ((smallOddPrimeDivisors n).erase p).card :=
                Finset.card_le_card hsub
              have hcard_erase :
                  ((smallOddPrimeDivisors n).erase p).card = k := by
                -- `card (erase p S) = card S - 1` and `card S = k+1`
                have : (smallOddPrimeDivisors n).card = k.succ := hcard_eq
                simpa [this] using (Finset.card_erase_of_mem hp_mem)
              simpa [hcard_erase] using hcard_le_erase
            have hn_even' : Even (ordCompl[p] n) :=
              ordCompl_even_of_even_of_three_le_prime (p := p) (N := n) hp'.1 hp_range.1 hn_even
            exact ih (Nat.ordCompl_pos p hn0).ne' hn_even' hcard_le'
          have hstep :
              TailBlock.sigma_trunc_Q0 (ordCompl[p] n) ≤ TailBlock.sigma_trunc_Q0 n :=
            sigma_trunc_Q0_ge_of_remove_one_prime hBp (p := p) (N := n)
              hp'.1 hp_range.1 hp_range.2 hn0 hn_even hp'.2
          exact le_trans hn_le hstep

  -- Apply the induction with `k = card S`.
  exact main (smallOddPrimeDivisors N).card hN0 hN_even le_rfl

theorem sigma_trunc_Q0_ge_33_25_of_BpAltNonnegUpToQ0
    (hBp : BpAltNonnegUpToQ0) :
    ∀ {N : ℕ}, N ≠ 0 → Even N → (33 : ℝ) / 25 ≤ TailBlock.sigma_trunc_Q0 N := by
  intro N hN0 hN_even
  have h_at2 : (33 : ℝ) / 25 ≤ TailBlock.sigma_trunc_Q0 2 :=
    Goldbach.Cert.SigmaTruncQ0At2Cert.sigma_trunc_Q0_two_ge_33_25
  have hmin : TailBlock.sigma_trunc_Q0 2 ≤ TailBlock.sigma_trunc_Q0 N :=
    sigma_trunc_Q0_ge_at2_of_BpAltNonnegUpToQ0 hBp hN0 hN_even
  exact le_trans h_at2 hmin

end S2

end

end Goldbach.Cert.SigmaTruncQ0_S2Reduction
