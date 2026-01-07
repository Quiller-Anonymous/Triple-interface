import Mathlib
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Goldbach.AO_OffDiag.TailBlock
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Goldbach.Utils.TsumTail
import Mathlib.Algebra.Order.Field.Basic

namespace Goldbach.AO_OffDiag

open scoped BigOperators
open Real
open Goldbach.Utils

noncomputable section

/-- The squared Möbius function indicator: 1 if squarefree, 0 otherwise. -/
noncomputable def muSq (n : ℕ) : ℝ :=
  if Squarefree n then 1 else 0

/-- The basic totient-reciprocal weight in `ENNReal`. -/
noncomputable def invTotENN (n : ℕ) : ENNReal :=
  ENNReal.ofReal (1 / (Nat.totient n : ℝ))

/-- ENNReal weight `muSq(d)/φ(d)` (nonnegative). -/
noncomputable def W (d : ℕ) : ENNReal :=
  ENNReal.ofReal (muSq d * (1 / (Nat.totient d : ℝ)))

/-- The global constant
`Cstar = ∑_{d,e≥1} muSq(d) muSq(e) / (φ(d) φ(e) lcm(d,e))`,
packaged in `ENNReal` for Tonelli-friendly manipulation. -/
noncomputable def Cstar : ENNReal :=
  ∑' d : ℕ, ∑' e : ℕ,
    W d * W e * ENNReal.ofReal (1 / (Nat.lcm d e : ℝ))

/- Step 1 (still to be proved): divisor expansion for `n/φ(n)` with `muSq`. -/
/-!
## Conventional axioms in this file

We isolate “literature facts” here so the rest of the pipeline stays axiom-free/bespoke-free.

* `totient_divisor_expansion`: a standard identity expressing `n/φ(n)` as a divisor sum with a
  squarefree indicator. This should be provable from Mathlib’s arithmetic function API, but may
  require some setup work in this toolchain snapshot.

* `Cstar_le_45`: a global bound on the Euler-product-style constant `Cstar`. The intended proof
  is conventional analytic number theory (Euler product + exponential bound), but it is not
  expected to be present in Mathlib in the exact numeric form we want.
-/
private lemma inv_totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 / (Nat.totient (∏ p ∈ s, p) : ℝ)) = ∏ p ∈ s, (1 / ((p - 1 : ℕ) : ℝ)) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro hs
    simp
  · intro p s hp_not_mem ih hs
    have hp_prime : p.Prime := hs p (by simp [hp_not_mem])
    have hs_prime : ∀ q ∈ s, q.Prime := by
      intro q hq
      exact hs q (by simp [hq, hp_not_mem])

    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      -- `p` is coprime to every distinct prime factor in `s`, hence to their product.
      refine (Nat.coprime_prod_right_iff (x := p) (t := s) (s := fun q : ℕ => q)).2 ?_
      intro q hq
      have hq_prime : q.Prime := hs_prime q hq
      have hpq_ne : p ≠ q := by
        intro h
        subst h
        exact hp_not_mem hq
      refine (hp_prime.coprime_iff_not_dvd).2 ?_
      intro hp_dvd_q
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).1 hp_dvd_q
      exact hpq_ne this

    have htot : Nat.totient (p * (∏ q ∈ s, q)) = Nat.totient p * Nat.totient (∏ q ∈ s, q) :=
      Nat.totient_mul hcop

    have htot' :
        (Nat.totient (p * (∏ q ∈ s, q)) : ℝ) =
          (Nat.totient p : ℝ) * (Nat.totient (∏ q ∈ s, q) : ℝ) := by
      exact_mod_cast htot

    have hphi_p : (Nat.totient p : ℝ) = (p - 1 : ℕ) := by
      simpa [Nat.totient_prime hp_prime]

    calc
      (1 / (Nat.totient (∏ q ∈ insert p s, q) : ℝ))
          =
        1 / (Nat.totient (p * (∏ q ∈ s, q)) : ℝ) := by
          simp [Finset.prod_insert, hp_not_mem, mul_comm, mul_left_comm, mul_assoc]
      _ = (1 / (Nat.totient p : ℝ)) * (1 / (Nat.totient (∏ q ∈ s, q) : ℝ)) := by
          -- rewrite `φ(p*s)=φ(p)*φ(s)` and invert
          simp [one_div, htot', mul_assoc, mul_left_comm, mul_comm]
      _ = (1 / ((p - 1 : ℕ) : ℝ)) * ∏ q ∈ s, (1 / ((q - 1 : ℕ) : ℝ)) := by
          simp [hphi_p, ih hs_prime]
      _ = ∏ q ∈ insert p s, (1 / ((q - 1 : ℕ) : ℝ)) := by
          simp [Finset.prod_insert, hp_not_mem, mul_assoc, mul_left_comm, mul_comm]

theorem totient_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
  (n : ℝ) / (Nat.totient n : ℝ) =
    (Nat.divisors n).sum (fun d => muSq d * (1 / (Nat.totient d : ℝ))) := by
  classical
  -- Rewrite the divisor sum as a sum over squarefree divisors.
  have hsq :
      (Nat.divisors n).sum (fun d => muSq d * (1 / (Nat.totient d : ℝ)))
        =
      ∑ d ∈ n.divisors with Squarefree d, (1 / (Nat.totient d : ℝ)) := by
    -- `muSq d` is `1` on squarefree `d`, else `0`.
    simpa [muSq] using
      (Finset.sum_filter (s := n.divisors) (p := Squarefree) (f := fun d => (1 / (Nat.totient d : ℝ)))).symm

  -- Enumerate squarefree divisors by subsets of prime factors.
  have hpow :
      (∑ d ∈ n.divisors with Squarefree d, (1 / (Nat.totient d : ℝ)))
        =
      ∑ s ∈ n.primeFactors.powerset, (1 / (Nat.totient (∏ p ∈ s, p) : ℝ)) := by
    have h0 :=
      (Nat.sum_divisors_filter_squarefree (n := n) hn (f := fun d : ℕ => (1 / (Nat.totient d : ℝ))))
    -- Identify the `toFinset` of normalized factors with `n.primeFactors`.
    have hS : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
      ext p
      -- Avoid simp loops around `Nat.primeFactors`; expand memberships manually.
      change (p ∈ (UniqueFactorizationMonoid.normalizedFactors n).toFinset) ↔
        p ∈ n.primeFactorsList.toFinset
      constructor
      · intro hp
        have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors n := by
          -- membership in `toFinset` is membership in the multiset
          simpa using (Multiset.mem_toFinset (a := p) (s := UniqueFactorizationMonoid.normalizedFactors n)).1 hp
        have hp'' : p ∈ (n.primeFactorsList : Multiset ℕ) := by
          simpa [Nat.factors_eq n] using hp'
        have hpList : p ∈ n.primeFactorsList := by
          simpa using hp''
        exact List.mem_toFinset.2 hpList
      · intro hp
        have hpList : p ∈ n.primeFactorsList := List.mem_toFinset.1 hp
        have hp'' : p ∈ (n.primeFactorsList : Multiset ℕ) := by
          simpa using hpList
        have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors n := by
          simpa [Nat.factors_eq n] using hp''
        exact (Multiset.mem_toFinset (a := p) (s := UniqueFactorizationMonoid.normalizedFactors n)).2 hp'
    -- Rewrite the RHS along `hS`, and rewrite `s.val.prod` as `∏ p ∈ s, p`.
    simpa [hS] using h0

  -- Turn `1/φ(∏ p)` into `∏ 1/(p-1)` on every subset.
  let g : ℕ → ℝ := fun p => 1 / ((p - 1 : ℕ) : ℝ)
  have hterm :
      (∑ s ∈ n.primeFactors.powerset, (1 / (Nat.totient (∏ p ∈ s, p) : ℝ)))
        =
      ∑ s ∈ n.primeFactors.powerset, ∏ p ∈ s, g p := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    -- every `p ∈ s` is a prime factor of `n`
    have hs_primes : ∀ p ∈ s, p.Prime := by
      intro p hp
      have : p ∈ n.primeFactors := by
        exact (Finset.mem_powerset.mp hs) hp
      exact Nat.prime_of_mem_primeFactors this
    simpa [g] using (inv_totient_prod_primes s hs_primes)

  -- Subset expansion: the sum equals the product over prime factors.
  have hprod :
      (∑ s ∈ n.primeFactors.powerset, ∏ p ∈ s, g p) =
        ∏ p ∈ n.primeFactors, (1 + g p) := by
    simpa using (Finset.prod_one_add (s := n.primeFactors) (f := g)).symm

  -- Compute the ratio `n/φ(n)` as `∏ p|n (p/(p-1)) = ∏ (1 + 1/(p-1))`.
  have hphi_pos : 0 < Nat.totient n := Nat.totient_pos.2 (Nat.pos_of_ne_zero hn)
  have hphi_ne : (Nat.totient n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hphi_pos)

  have hQ_ne :
      (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) ≠ 0 := by
    have hQ_pos :
        0 < (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
      refine Finset.prod_pos ?_
      intro p hp
      have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact_mod_cast Nat.sub_pos_of_lt hp'.one_lt
    exact ne_of_gt hQ_pos

  have hEuler :
      (Nat.totient n : ℝ) * (∏ p ∈ n.primeFactors, (p : ℝ)) =
        (n : ℝ) * (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
    -- Cast Euler's product formula in a controlled way.
    have hNat := Nat.totient_mul_prod_primeFactors n
    have hCast :
        ((Nat.totient n * ∏ p ∈ n.primeFactors, p : ℕ) : ℝ) =
          ((n * ∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    -- Push casts through `*` and `∏`.
    simpa [Nat.cast_mul, Nat.cast_prod, mul_assoc, mul_left_comm, mul_comm] using hCast

  have hratio :
      (n : ℝ) / (Nat.totient n : ℝ) =
        (∏ p ∈ n.primeFactors, (1 + g p)) := by
    -- First, express `n/φ(n)` as `P/Q` using `φ(n)*P = n*Q`.
    have hPQ :
        (n : ℝ) / (Nat.totient n : ℝ) =
          (∏ p ∈ n.primeFactors, (p : ℝ)) /
            (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
      field_simp [hphi_ne, hQ_ne]
      -- after clearing denominators, this is exactly Euler's product formula.
      simpa [mul_assoc, mul_left_comm, mul_comm] using hEuler.symm

    -- Next, rewrite `P/Q` as a product of `p/(p-1)` and then as `∏ (1 + 1/(p-1))`.
    have hP :
        (∏ p ∈ n.primeFactors, (p : ℝ)) /
            (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ))
          =
        ∏ p ∈ n.primeFactors, (1 + g p) := by
      -- `P/Q = ∏ (p/(p-1))`
      have hdiv :
          (∏ p ∈ n.primeFactors, (p : ℝ)) /
              (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ))
            =
          ∏ p ∈ n.primeFactors, (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
        simpa using (Finset.prod_div_distrib (s := n.primeFactors) (f := fun p => (p : ℝ))
          (g := fun p => ((p - 1 : ℕ) : ℝ))).symm
      -- and `p/(p-1) = 1 + 1/(p-1)`
      have hpoint :
          ∀ p ∈ n.primeFactors,
            (p : ℝ) / ((p - 1 : ℕ) : ℝ) = 1 + g p := by
        intro p hp
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
          have : (0 : ℕ) < p - 1 := Nat.sub_pos_of_lt hp'.one_lt
          exact_mod_cast (ne_of_gt this)
        have hp_pos : 1 ≤ p := Nat.succ_le_of_lt hp'.pos
        have hsplit : (p : ℝ) = ((p - 1 : ℕ) : ℝ) + 1 := by
          -- `p = (p-1)+1` for `p ≥ 1`
          exact_mod_cast (Nat.sub_add_cancel hp_pos).symm
        calc
          (p : ℝ) / ((p - 1 : ℕ) : ℝ)
              = (((p - 1 : ℕ) : ℝ) + 1) / ((p - 1 : ℕ) : ℝ) := by
                  simpa [hsplit]
          _ = 1 + (1 / ((p - 1 : ℕ) : ℝ)) := by
                -- `(a+1)/a = 1 + 1/a` for `a ≠ 0`
                simp [add_div, hne, div_self]
          _ = 1 + g p := by
                simp [g]
      -- finish by pointwise rewrite under the product
      calc
        (∏ p ∈ n.primeFactors, (p : ℝ)) / (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ))
            = ∏ p ∈ n.primeFactors, (p : ℝ) / ((p - 1 : ℕ) : ℝ) := hdiv
        _ = ∏ p ∈ n.primeFactors, (1 + g p) := by
              refine Finset.prod_congr rfl ?_
              intro p hp
              simpa using (hpoint p hp)

    exact hPQ.trans hP

  -- Assemble everything.
  calc
    (n : ℝ) / (Nat.totient n : ℝ)
        = ∏ p ∈ n.primeFactors, (1 + g p) := hratio
    _ = (∑ s ∈ n.primeFactors.powerset, ∏ p ∈ s, g p) := by
          simpa [hprod] using hprod.symm
    _ = (∑ s ∈ n.primeFactors.powerset, (1 / (Nat.totient (∏ p ∈ s, p) : ℝ))) := by
          simpa [hterm] using hterm.symm
    _ = (∑ d ∈ n.divisors with Squarefree d, (1 / (Nat.totient d : ℝ))) := by
          simpa [hpow] using hpow.symm
    _ = (Nat.divisors n).sum (fun d => muSq d * (1 / (Nat.totient d : ℝ))) := by
          simpa [hsq] using hsq.symm

/-!
## Step 2: a divisor-expansion bound for `1/φ(n)²`

This is the inequality:
`1/φ(n)^2 ≤ Σ_{d|n} Σ_{e|n} W(d) W(e) / n^2`
in `ENNReal` form.
-/

/--
## Step 2: expand `1/φ(n)^2` into a nonnegative double divisor sum

This proves the lemma you left as `sorry`:

`ENNReal.ofReal (1 / φ(n)^2) ≤ ∑_{d|n} ∑_{e|n} W d * W e * ofReal (1/n^2)`.

We actually prove an *equality* (hence the `≤`), using Step 1
`totient_divisor_expansion` and purely finite-sum algebra.
-/
theorem inv_totient_sq_le_double_divisor_sum (n : ℕ) (hn : n ≠ 0) :
  ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
    ≤
  (Nat.divisors n).sum (fun d =>
    (Nat.divisors n).sum (fun e =>
      W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2))) := by
  classical
  set D : Finset ℕ := Nat.divisors n

  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos

  have hphi_pos : 0 < Nat.totient n := (Nat.totient_pos).2 (Nat.pos_of_ne_zero hn)
  have hphi_pos' : 0 < (Nat.totient n : ℝ) := by exact_mod_cast hphi_pos
  have hphi_ne : (Nat.totient n : ℝ) ≠ 0 := ne_of_gt hphi_pos'

  -- abbreviations in ℝ
  let a : ℕ → ℝ := fun d => muSq d * (1 / (Nat.totient d : ℝ))
  let c : ℝ := (1 / (n : ℝ) ^ 2)

  -- Step 1: n/φ(n) = ∑_{d|n} a(d)
  have hexp : (n : ℝ) / (Nat.totient n : ℝ) = D.sum a := by
    simpa [D, a] using totient_divisor_expansion n hn

  -- Convert the RHS double sum into `(∑ W)^2 * ofReal c`
  have hRHS :
      D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c))
        =
      (D.sum W) * (D.sum W) * ENNReal.ofReal c := by
    -- pull the constant `ofReal c` out of the inner sum, then outer sum
    have h1 :
        D.sum (fun d => D.sum (fun e => (W d * W e) * ENNReal.ofReal c))
          =
        (D.sum (fun d => D.sum (fun e => W d * W e))) * ENNReal.ofReal c := by
      -- inner
      have hinner :
          ∀ d : ℕ, D.sum (fun e => (W d * W e) * ENNReal.ofReal c)
                = (D.sum (fun e => W d * W e)) * ENNReal.ofReal c := by
        intro d
        simpa [Finset.sum_mul]   -- (∑ e, f e) * C = ∑ e, f e * C
      -- outer
      calc
        D.sum (fun d => D.sum (fun e => (W d * W e) * ENNReal.ofReal c))
            = D.sum (fun d => (D.sum (fun e => W d * W e)) * ENNReal.ofReal c) := by
                refine Finset.sum_congr rfl ?_
                intro d hd
                simpa [hinner d]
        _ = (D.sum (fun d => D.sum (fun e => W d * W e))) * ENNReal.ofReal c := by
              simpa [Finset.sum_mul]  -- again

    -- now identify the double sum with `(∑W)*(∑W)` via `sum_mul_sum`
    have hmul :
        (D.sum W) * (D.sum W) =
          D.sum (fun d => D.sum (fun e => W d * W e)) := by
      simpa [Finset.sum_mul_sum]  -- standard lemma

    calc
      D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c))
          = D.sum (fun d => D.sum (fun e => (W d * W e) * ENNReal.ofReal c)) := by
              refine Finset.sum_congr rfl ?_
              intro d hd
              refine Finset.sum_congr rfl ?_
              intro e he
              simp [mul_assoc]
      _ = (D.sum (fun d => D.sum (fun e => W d * W e))) * ENNReal.ofReal c := h1
      _ = ((D.sum W) * (D.sum W)) * ENNReal.ofReal c := by
            rw [← hmul]
      _ = (D.sum W) * (D.sum W) * ENNReal.ofReal c := by
            rfl

  -- Now rewrite the LHS as `(ofReal (n/φ))^2 * ofReal c`, then replace `ofReal (n/φ)` by `∑ W`.
  have hquot0 : 0 ≤ (n : ℝ) / (Nat.totient n : ℝ) := by
    exact div_nonneg (le_of_lt hn_pos) (le_of_lt hphi_pos')

  have hc0 : 0 ≤ c := by
    simp [c]

  have hLHS :
      ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
        =
      ENNReal.ofReal (( (n : ℝ) / (Nat.totient n : ℝ) ) ^ 2) * ENNReal.ofReal c := by
    -- use the real identity: 1/φ(n)^2 = (n/φ(n))^2 * (1/n^2)
    have hreal :
        (1 / (Nat.totient n : ℝ) ^ 2)
          =
        (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2) * c := by
      -- c = 1/n^2
      simp [c]
      -- clear denominators safely
      field_simp [hn_ne, hphi_ne]
    -- push into `ofReal` and split the product
    rw [hreal]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2))]

  -- express `ofReal ((n/φ)^2)` as `(ofReal (n/φ))*(ofReal (n/φ))`
  have hsq :
      ENNReal.ofReal (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2)
        =
      ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) *
        ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) := by
    -- square = mul; then `ofReal_mul`
    rw [pow_two, ENNReal.ofReal_mul hquot0]

  -- replace `ofReal (n/φ)` by `∑ W` using Step 1 + finite sum
  -- replace `ofReal (n/φ)` by `∑ W` using Step 1 + finite sum
  have hsumW :
      D.sum W = ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) := by
    -- helper: each `a d` is nonnegative
    have ha_nonneg : ∀ d, 0 ≤ a d := by
      intro d
      simp only [a, muSq]
      split_ifs <;> positivity

    -- helper: ofReal commutes with *finite* sums of nonnegative reals
    have ofReal_sum_eq :
        ENNReal.ofReal (D.sum a) = D.sum (fun d => ENNReal.ofReal (a d)) := by
      induction D using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        have hx0 : 0 ≤ a x := ha_nonneg x
        have hs_sum0 : 0 ≤ s.sum a := Finset.sum_nonneg (fun y _ => ha_nonneg y)
        simp only [Finset.sum_insert hx]
        rw [ENNReal.ofReal_add hx0 hs_sum0, ih]

    -- now use the helper plus Step 1 (`hexp`)
    calc
      D.sum W
          = D.sum (fun d => ENNReal.ofReal (a d)) := by
              simp [W, a]
      _   = ENNReal.ofReal (D.sum a) := by
              simpa using ofReal_sum_eq.symm
      _   = ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) := by
              simpa [hexp]

  -- Finish: LHS = (∑W)*(∑W)*ofReal c = RHS
  have hEq :
      ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
        =
      D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c)) := by
    calc
      ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2)
          = ENNReal.ofReal (((n : ℝ) / (Nat.totient n : ℝ)) ^ 2) * ENNReal.ofReal c := hLHS
      _ = (ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ)) *
            ENNReal.ofReal ((n : ℝ) / (Nat.totient n : ℝ))) * ENNReal.ofReal c := by
            simp [hsq]
      _ = ((D.sum W) * (D.sum W)) * ENNReal.ofReal c := by
            simp [hsumW, mul_assoc]
      _ = D.sum (fun d => D.sum (fun e => W d * W e * ENNReal.ofReal c)) := by
            rw [← hRHS]

  -- goal is ≤
  exact hEq.le

/-! ## Step 3: tail bound for multiples of `L`

We want the ENNReal version of:

`∑_{n>R, L|n} 1/n^2 ≤ 2/(L*R)`,

which follows from the tail axiom for `∑ 1/m^2` at the real cutoff `t = R/L`.-/

/-!This replaces the `sorry` at `hreindex` and avoids the brittle `linarith` blocks by using the
clean implication `R < L*m → (R/L) < m` (in `ℝ`), plus `Function.Injective.tsum_eq` to reindex.
It also replaces the old `le_antisymm` factoring with `ENNReal.tsum_mul_left`.
-/

theorem tsum_multiples_inv_sq_le (R L : ℕ) (hR : 1 ≤ R) (hL : 1 ≤ L) :
  (∑' n : ℕ,
      if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
  classical

  have hL0 : L ≠ 0 := (Nat.one_le_iff_ne_zero.mp hL)
  have hR0 : R ≠ 0 := (Nat.one_le_iff_ne_zero.mp hR)

  have hL_pos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hL0)
  have hR_pos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hR0)

  -- Define the summand once.
  let f : ℕ → ENNReal := fun n =>
    if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0

  -- Reindex the sum over multiples using `Function.Injective.tsum_eq`.
  have hinj : Function.Injective (fun m : ℕ => L * m) := by
    intro a b hab
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hL0) hab

  have hsupport : Function.support f ⊆ Set.range (fun m : ℕ => L * m) := by
    intro n hn
    -- `hn : f n ≠ 0`, so the `if`-condition must hold, hence `L ∣ n`.
    have hn' : R < n ∧ L ∣ n := by
      by_contra hcond
      -- if the condition fails then `f n = 0`, contradiction
      simpa [f, hcond] using hn
    refine ⟨n / L, ?_⟩
    -- `L * (n / L) = n` since `L ∣ n`
    simpa using (Nat.mul_div_cancel' (n := L) (m := n) hn'.2)

  have hreindex :
      (∑' n : ℕ,
          if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
        =
      ∑' m : ℕ,
        if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0 := by
    -- `Function.Injective.tsum_eq` gives: ∑ m, f(L*m) = ∑ n, f(n)
    have h := (Function.Injective.tsum_eq hinj (f := f) hsupport).symm
    -- simplify `f (L*m)` using `L ∣ L*m`
    simpa [f, Nat.dvd_mul_right] using h

  -- Start from the reindexed form.
  rw [hreindex]

  -- Key implication: `R < L*m` (in `ℕ`) forces `(R/L) < m` (in `ℝ`), for `L>0`.
  have himp : ∀ m : ℕ, R < L * m → (↑R / ↑L : ℝ) < (m : ℝ) := by
    intro m hRm
    have hRm' : (R : ℝ) < (L : ℝ) * (m : ℝ) := by
      exact_mod_cast hRm
    -- rewrite RHS as m * L to match `div_lt_iff`
    have hRm'' : (R : ℝ) < (m : ℝ) * (L : ℝ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hRm'
    -- now divide by L > 0
    exact (div_lt_iff₀ hL_pos).2 hRm''

  -- Cut: replace `R < L*m` by the weaker real cutoff `(R/L) < m`.
  have hcut : ∀ m : ℕ,
      (if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
        ≤
      if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0 := by
    intro m
    by_cases hlt : (↑R / ↑L : ℝ) < (m : ℝ)
    · by_cases hRm : R < L * m
      · simp [hRm, hlt, Nat.cast_mul, mul_assoc]
      · simp [hRm, hlt]
    · have hRm : ¬ R < L * m := by
        intro hRm
        exact hlt (himp m hRm)
      simp [hRm, hlt]

  have hle :
      (∑' m : ℕ,
          if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
        ≤
      ∑' m : ℕ,
        if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0 := by
    exact ENNReal.tsum_le_tsum hcut

  -- Factor out `1/L^2` on the RHS using `ENNReal.tsum_mul_left`.
  have hfactor :
      (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0)
        =
      ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
        ∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0 := by
    have hpoint :
        ∀ m : ℕ,
          (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0)
            =
          ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
            (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := by
      intro m
      by_cases htm : (↑R / ↑L : ℝ) < (m : ℝ)
      · have hreal :
            (1 / (↑L * (m : ℝ)) ^ 2) =
              (1 / (↑L : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
          -- purely algebraic in ℝ, with `L ≠ 0`
          field_simp [pow_two, hL_pos.ne']
        simp [htm, hreal, ENNReal.ofReal_mul, mul_assoc]
      · simp [htm]

    calc
      (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0)
          =
        ∑' m : ℕ,
          ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
            (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := by
          refine tsum_congr ?_
          intro m
          simpa using (hpoint m)
      _ =
        ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
          ∑' m : ℕ,
            (if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := by
          -- pull out the constant
          rw [ENNReal.tsum_mul_left]

  -- Apply the tail axiom at `t = R/L`.
  have ht : 0 < (↑R / ↑L : ℝ) := div_pos hR_pos hL_pos
  have htail :
      (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0)
        ≤ ENNReal.ofReal (2 / (↑R / ↑L : ℝ)) := by
    simpa using tsum_tail_inv_sq_le (t := (↑R / ↑L : ℝ)) ht

  -- Now chain everything.
  have : (∑' m : ℕ,
            if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
        ≤ ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
    calc
      (∑' m : ℕ,
          if R < L * m then ENNReal.ofReal (1 / (↑(L * m) : ℝ) ^ 2) else 0)
          ≤
        (∑' m : ℕ,
          if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (↑L * (m : ℝ)) ^ 2) else 0) := hle
      _ =
        ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) *
          (∑' m : ℕ,
            if (↑R / ↑L : ℝ) < (m : ℝ) then ENNReal.ofReal (1 / (m : ℝ) ^ 2) else 0) := hfactor
      _ ≤
        ENNReal.ofReal (1 / (↑L : ℝ) ^ 2) * ENNReal.ofReal (2 / (↑R / ↑L : ℝ)) := by
          exact mul_le_mul_left' htail _
      _ = ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
        -- arithmetic in ℝ, then push through `ofReal`
        have hreal :
            (1 / (↑L : ℝ) ^ 2) * (2 / (↑R / ↑L : ℝ)) = 2 / ((L : ℝ) * (R : ℝ)) := by
          field_simp [hL_pos.ne', hR_pos.ne', pow_two]
        -- both factors are ≥ 0, so `ofReal_mul` is safe to use
        have h1 : (0 : ℝ) ≤ 1 / (↑L : ℝ) ^ 2 := by positivity
        rw [← ENNReal.ofReal_mul h1, hreal]

  exact this

/-!
## Step 4: prime-free bound `Cstar ≤ 45`
-/
/-- Step 4 (temporary): global numeric bound for `Cstar`.

Mathematically, one proves
`Cstar = ∏' p, (1 + 2/(p*(p-1)) + 1/(p*(p-1)^2)) ≤ exp(3) < 45`.
-/
private def CstarTerm (d e : ℕ) : ENNReal :=
  W d * W e * ENNReal.ofReal (1 / (Nat.lcm d e : ℝ))

private def CstarTermPair (x : ℕ × ℕ) : ENNReal :=
  CstarTerm x.1 x.2

private lemma Cstar_eq_tsum_term : Cstar = ∑' x : ℕ × ℕ, CstarTermPair x := by
  simpa [Cstar, CstarTermPair, CstarTerm] using
    (ENNReal.tsum_prod (f := fun d e : ℕ =>
      W d * W e * ENNReal.ofReal (1 / (Nat.lcm d e : ℝ)))).symm

private lemma W_eq_zero_of_not_squarefree {d : ℕ} (hd : ¬ Squarefree d) : W d = 0 := by
  simp [W, muSq, hd]

private lemma CstarTerm_eq_zero_of_not_squarefree_left {d e : ℕ} (hd : ¬ Squarefree d) :
    CstarTerm d e = 0 := by
  simp [CstarTerm, W_eq_zero_of_not_squarefree hd]

private lemma CstarTerm_eq_zero_of_not_squarefree_right {d e : ℕ} (he : ¬ Squarefree e) :
    CstarTerm d e = 0 := by
  simp [CstarTerm, W_eq_zero_of_not_squarefree he]

private noncomputable def factorR (p : ℕ) : ℝ :=
  1 + 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)

private noncomputable def factorENN (p : ℕ) : ENNReal :=
  ENNReal.ofReal (factorR p)

private noncomputable def prodOf (s : Finset ℕ) : ℕ :=
  ∏ p ∈ s, p

private lemma prodOf_eq (s : Finset ℕ) : prodOf s = ∏ p ∈ s, p := by
  rfl

private lemma primeFactors_prodOf {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Nat.primeFactors (prodOf s) = s := by
  simpa [prodOf] using (Nat.primeFactors_prod (s := s) hs)

private lemma squarefree_prodOf {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (prodOf s) := by
  classical
  -- `prodOf s` is a product of pairwise-coprime squarefree terms (primes), hence squarefree.
  have hs_pairwise : Set.Pairwise (s : Set ℕ) (fun a b : ℕ => IsRelPrime a b) := by
    intro a ha b hb hab
    have ha' : a.Prime := hs a ha
    have hb' : b.Prime := hs b hb
    -- distinct primes are coprime
    refine (Nat.coprime_iff_isRelPrime).1 ?_
    exact (ha'.coprime_iff_not_dvd).2 (by
      intro h
      have : a = b := (Nat.prime_dvd_prime_iff_eq ha' hb').1 h
      exact hab this)
  have hs_sq : ∀ p ∈ s, Squarefree p := by
    intro p hp
    exact (hs p hp).squarefree
  have hs_pairwise' : Set.Pairwise (s : Set ℕ) (fun a b : ℕ => IsRelPrime (a : ℕ) (b : ℕ)) := hs_pairwise
  -- apply the general lemma on `Finset` products
  simpa [prodOf] using
    (Finset.squarefree_prod_of_pairwise_isCoprime (s := s) (f := fun p : ℕ => p) hs_pairwise' hs_sq)

private lemma factorR_nonneg {p : ℕ} : 0 ≤ factorR p := by
  -- holds for all `p` by monotonicity of `ofReal`; in usage we only apply it at primes (`p ≥ 2`)
  dsimp [factorR]
  positivity

private lemma prodOf_insert {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) :
    prodOf (insert p s) = p * prodOf s := by
  classical
  simp [prodOf, Finset.prod_insert, hp, mul_assoc, mul_left_comm, mul_comm]

private lemma prime_not_dvd_lcm_of_not_dvd {p d e : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    ¬ p ∣ Nat.lcm d e := by
  intro h
  have hlcm_dvd : Nat.lcm d e ∣ d * e := by
    -- `lcm` divides `gcd * lcm = d * e`
    have : Nat.lcm d e ∣ Nat.gcd d e * Nat.lcm d e := dvd_mul_left _ _
    simpa [Nat.gcd_mul_lcm] using this
  have : p ∣ d * e := dvd_trans h hlcm_dvd
  rcases hp.dvd_mul.mp this with h | h
  · exact hpd h
  · exact hpe h

private lemma coprime_prime_lcm_of_not_dvd {p d e : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    Nat.Coprime p (Nat.lcm d e) :=
  (hp.coprime_iff_not_dvd).2 (prime_not_dvd_lcm_of_not_dvd hp hpd hpe)

private lemma lcm_mul_prime_right {p d e : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    Nat.lcm d (p * e) = p * Nat.lcm d e := by
  refine Nat.dvd_antisymm ?_ ?_
  · -- `lcm d (p*e)` divides `p*lcm d e` since that is a common multiple
    refine Nat.lcm_dvd ?_ ?_
    · exact dvd_mul_of_dvd_right (Nat.dvd_lcm_left d e) p
    · exact (Nat.mul_dvd_mul_left p (Nat.dvd_lcm_right d e))
  · -- `p*lcm d e` divides `lcm d (p*e)` by coprimality + two divisibilities
    have hcop : Nat.Coprime p (Nat.lcm d e) := coprime_prime_lcm_of_not_dvd hp hpd hpe
    refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
    · -- `p ∣ lcm d (p*e)`
      exact dvd_trans (dvd_mul_right p e) (Nat.dvd_lcm_right d (p * e))
    · -- `lcm d e ∣ lcm d (p*e)` since it divides any common multiple of `d` and `e`
      refine Nat.lcm_dvd ?_ ?_
      · exact Nat.dvd_lcm_left d (p * e)
      ·
        -- `e ∣ p*e`, hence `e ∣ lcm d (p*e)`
        refine dvd_trans ?_ (Nat.dvd_lcm_right d (p * e))
        exact ⟨p, by simpa [Nat.mul_comm]⟩

private lemma lcm_mul_prime_left {p d e : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    Nat.lcm (p * d) e = p * Nat.lcm d e := by
  simpa [mul_assoc, mul_left_comm, mul_comm, Nat.lcm_comm] using
    (lcm_mul_prime_right (p := p) (d := e) (e := d) hp hpe hpd)

private lemma W_mul_prime_right {p e : ℕ} (hp : p.Prime) (he : Squarefree e) (hpe : ¬ p ∣ e) :
    W (p * e) = W e * ENNReal.ofReal (1 / ((p - 1 : ℕ) : ℝ)) := by
  have hcop : Nat.Coprime p e := (hp.coprime_iff_not_dvd).2 hpe
  have hsf : Squarefree (p * e) := (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, he⟩
  have htot : Nat.totient (p * e) = Nat.totient p * Nat.totient e := Nat.totient_mul hcop
  have htot' : (Nat.totient (p * e) : ℝ) = (Nat.totient p : ℝ) * (Nat.totient e : ℝ) := by
    exact_mod_cast htot
  have hphi_p : (Nat.totient p : ℝ) = (p - 1 : ℕ) := by
    simpa [Nat.totient_prime hp]
  have hnonneg : (0 : ℝ) ≤ 1 / ((p - 1 : ℕ) : ℝ) := by positivity
  -- expand `W` on both sides; `muSq` is `1` for squarefree arguments
  simp [W, muSq, hsf, he, htot', hphi_p, ENNReal.ofReal_mul hnonneg, mul_assoc, mul_left_comm,
    mul_comm, one_div, div_eq_mul_inv]

private lemma W_mul_prime_left {p d : ℕ} (hp : p.Prime) (hd : Squarefree d) (hpd : ¬ p ∣ d) :
    W (p * d) = W d * ENNReal.ofReal (1 / ((p - 1 : ℕ) : ℝ)) := by
  simpa [mul_comm] using W_mul_prime_right (p := p) (e := d) hp hd hpd

private lemma CstarTerm_mul_prime_right {p d e : ℕ} (hp : p.Prime)
    (hd : Squarefree d) (he : Squarefree e) (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    CstarTerm d (p * e) =
      CstarTerm d e * ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
  have hlcm : Nat.lcm d (p * e) = p * Nat.lcm d e := lcm_mul_prime_right (p := p) (d := d) (e := e) hp hpd hpe
  have hW : W (p * e) = W e * ENNReal.ofReal (1 / ((p - 1 : ℕ) : ℝ)) :=
    W_mul_prime_right (p := p) (e := e) hp he hpe
  have hnonneg1 : (0 : ℝ) ≤ 1 / ((p - 1 : ℕ) : ℝ) := by positivity
  have hnonneg2 : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by positivity
  -- rewrite everything and regroup
  simp [CstarTerm, hW, hlcm, ENNReal.ofReal_mul hnonneg1, ENNReal.ofReal_mul hnonneg2,
    mul_assoc, mul_left_comm, mul_comm]

private lemma CstarTerm_mul_prime_left {p d e : ℕ} (hp : p.Prime)
    (hd : Squarefree d) (he : Squarefree e) (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    CstarTerm (p * d) e =
      CstarTerm d e * ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
  have hlcm : Nat.lcm (p * d) e = p * Nat.lcm d e :=
    lcm_mul_prime_left (p := p) (d := d) (e := e) hp hpd hpe
  have hW : W (p * d) = W d * ENNReal.ofReal (1 / ((p - 1 : ℕ) : ℝ)) :=
    W_mul_prime_left (p := p) (d := d) hp hd hpd
  have hnonneg1 : (0 : ℝ) ≤ 1 / ((p - 1 : ℕ) : ℝ) := by positivity
  have hnonneg2 : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by positivity
  simp [CstarTerm, hW, hlcm, ENNReal.ofReal_mul hnonneg1, ENNReal.ofReal_mul hnonneg2,
    mul_assoc, mul_left_comm, mul_comm]

private lemma CstarTerm_mul_prime_both {p d e : ℕ} (hp : p.Prime)
    (hd : Squarefree d) (he : Squarefree e) (hpd : ¬ p ∣ d) (hpe : ¬ p ∣ e) :
    CstarTerm (p * d) (p * e) =
      CstarTerm d e * ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) := by
  have hlcm : Nat.lcm (p * d) (p * e) = p * Nat.lcm d e := by
    refine Nat.dvd_antisymm ?_ ?_
    · refine Nat.lcm_dvd ?_ ?_
      · exact Nat.mul_dvd_mul_left p (Nat.dvd_lcm_left d e)
      · exact Nat.mul_dvd_mul_left p (Nat.dvd_lcm_right d e)
    · have hcop : Nat.Coprime p (Nat.lcm d e) := coprime_prime_lcm_of_not_dvd hp hpd hpe
      refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
      · exact dvd_trans (dvd_mul_right p d) (Nat.dvd_lcm_left (p * d) (p * e))
      · refine Nat.lcm_dvd ?_ ?_
        · exact (Nat.dvd_mul_left d p).trans (Nat.dvd_lcm_left (p * d) (p * e))
        · exact (Nat.dvd_mul_left e p).trans (Nat.dvd_lcm_right (p * d) (p * e))
  have hWl : W (p * d) = W d * ENNReal.ofReal (1 / ((p - 1 : ℕ) : ℝ)) := W_mul_prime_left hp hd hpd
  have hWr : W (p * e) = W e * ENNReal.ofReal (1 / ((p - 1 : ℕ) : ℝ)) := W_mul_prime_right hp he hpe
  have hnonnegP : (0 : ℝ) ≤ 1 / ((p - 1 : ℕ) : ℝ) := by positivity
  have hnonneg : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hpos' : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    have : 0 < (p - 1 : ℕ) := Nat.sub_pos_of_lt hp.one_lt
    exact_mod_cast this
  have hx : ((p - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos'
  have hsq :
      ENNReal.ofReal (((p - 1 : ℕ) : ℝ)⁻¹) * ENNReal.ofReal (((p - 1 : ℕ) : ℝ)⁻¹) =
        ENNReal.ofReal ((((p - 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    have hnonnegInv : (0 : ℝ) ≤ (((p - 1 : ℕ) : ℝ)⁻¹) := by positivity
    have hreal : (((p - 1 : ℕ) : ℝ)⁻¹) * (((p - 1 : ℕ) : ℝ)⁻¹) = (((p - 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
      field_simp [pow_two, hx]
    calc
      ENNReal.ofReal (((p - 1 : ℕ) : ℝ)⁻¹) * ENNReal.ofReal (((p - 1 : ℕ) : ℝ)⁻¹)
          = ENNReal.ofReal ((((p - 1 : ℕ) : ℝ)⁻¹) * (((p - 1 : ℕ) : ℝ)⁻¹)) := by
              simpa using (ENNReal.ofReal_mul hnonnegInv (b := ((p - 1 : ℕ) : ℝ)⁻¹)).symm
      _ = ENNReal.ofReal ((((p - 1 : ℕ) : ℝ) ^ 2)⁻¹) := by simpa [hreal]
  -- expand and regroup; the factor is `1/p` from the lcm and `1/(p-1)^2` from `W` twice
  simp [CstarTerm, hWl, hWr, hlcm, ENNReal.ofReal_mul hnonnegP, ENNReal.ofReal_mul hnonneg,
    mul_assoc, mul_left_comm, mul_comm]
  -- collapse the two `(p-1)⁻¹` factors into `((p-1)^2)⁻¹`
  have hCCX :
      ENNReal.ofReal (↑(p - 1))⁻¹ * (ENNReal.ofReal (↑(p - 1))⁻¹ * (W d * W e)) =
        (ENNReal.ofReal (↑(p - 1))⁻¹ * ENNReal.ofReal (↑(p - 1))⁻¹) * (W d * W e) := by
    simpa [mul_assoc]
  -- now it is a direct rewrite
  rw [hCCX, hsq]

private lemma exp_three_le_45 : Real.exp 3 ≤ (45 : ℝ) := by
  -- A very safe numeric upper bound:
  -- from `1 + x ≤ exp x` at `x = -3/10`, we get `exp(3/10) ≤ 10/7`,
  -- hence `exp 3 = (exp(3/10))^10 ≤ (10/7)^10 < 45`.
  have hpos : (0 : ℝ) < (1 - (3 / 10 : ℝ)) := by norm_num
  have hlin : (1 - (3 / 10 : ℝ)) ≤ Real.exp (-(3 / 10 : ℝ)) := by
    -- `add_one_le_exp` is stated as `x + 1 ≤ exp x`.
    -- Convert `(-3/10) + 1` into `1 - 3/10`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (Real.add_one_le_exp (-(3 / 10 : ℝ)))
  have hinv : (1 / Real.exp (-(3 / 10 : ℝ))) ≤ (1 / (1 - (3 / 10 : ℝ))) :=
    one_div_le_one_div_of_le hpos hlin
  have hexp_small : Real.exp (3 / 10 : ℝ) ≤ (10 / 7 : ℝ) := by
    calc
      Real.exp (3 / 10 : ℝ) = 1 / Real.exp (-(3 / 10 : ℝ)) := by
        simp [Real.exp_neg]
      _ ≤ 1 / (1 - (3 / 10 : ℝ)) := hinv
      _ = (10 / 7 : ℝ) := by norm_num
  have hexp3 : Real.exp (3 : ℝ) ≤ (10 / 7 : ℝ) ^ (10 : ℕ) := by
    calc
      Real.exp (3 : ℝ) = Real.exp ((10 : ℕ) * (3 / 10 : ℝ)) := by norm_num
      _ = (Real.exp (3 / 10 : ℝ)) ^ (10 : ℕ) := by
        -- `exp (n*x) = (exp x)^n`
        simpa using (exp_nat_mul (x := (3 / 10 : ℝ)) (n := (10 : ℕ)))
      _ ≤ (10 / 7 : ℝ) ^ (10 : ℕ) := by
        exact pow_le_pow_left₀ (by positivity) hexp_small _
  have hrat : ((10 / 7 : ℝ) ^ (10 : ℕ)) ≤ (45 : ℝ) := by
    -- purely numeric
    norm_num
  exact le_trans hexp3 hrat

/-!
The main analytic/numerical content is to show `Cstar` is bounded by the finite-prime
products `∏_{p∈S} (1 + 2/(p(p-1)) + 1/(p(p-1)^2))`, hence by `exp 3`, hence by `45`.

We isolate the remaining bookkeeping into a single lemma `Cstar_le_exp_three` below.
It is conventional analytic number theory (Euler-product style), but the argument is completely
finite: it bounds every finite partial sum of the defining `tsum`.
-/
private def fullSum (S : Finset ℕ) : ENNReal :=
  ∑ d ∈ S.powerset, ∑ e ∈ S.powerset, CstarTerm (prodOf d) (prodOf e)

private lemma fullSum_eq_sum_product (S : Finset ℕ) :
    fullSum S =
      ∑ x ∈ S.powerset.product S.powerset, CstarTerm (prodOf x.1) (prodOf x.2) := by
  classical
  simp [fullSum, Finset.sum_product]

/-- A small wrapper for rewriting a sum over an `image` along an injective map.

We keep this local because (in this toolchain snapshot) it is easy to get argument-order
inference wrong when using `Finset.sum_image` directly inside `simp`/`simpa`.
-/
private lemma sum_image_eq_of_injOn {α β γ : Type*} [DecidableEq β] [AddCommMonoid γ]
    (s : Finset α) (f : α → β) (g : β → γ)
    (hinj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) :
    (s.image f).sum g = s.sum (fun a => g (f a)) := by
  classical
  revert hinj
  refine Finset.induction_on s ?_ ?_
  · intro _hinj
    simp
  · intro a s ha_not_mem ih hinj
    have hinj_s : ∀ b₁ ∈ s, ∀ b₂ ∈ s, f b₁ = f b₂ → b₁ = b₂ := by
      intro b₁ hb₁ b₂ hb₂ hEq
      exact hinj b₁ (by simp [hb₁, ha_not_mem]) b₂ (by simp [hb₂, ha_not_mem]) hEq
    have ih' : (s.image f).sum g = s.sum (fun b => g (f b)) := ih hinj_s
    have hfa_not_mem : f a ∉ s.image f := by
      intro hmem
      rcases Finset.mem_image.1 hmem with ⟨b, hb, hfb⟩
      have hab : a = b := hinj a (by simp [ha_not_mem]) b (by simp [hb, ha_not_mem]) hfb.symm
      exact ha_not_mem (hab ▸ hb)
    simp [Finset.image_insert, Finset.sum_insert, ha_not_mem, hfa_not_mem, ih']

private lemma not_dvd_prodOf_of_not_mem {p : ℕ} {s : Finset ℕ}
    (hp : p.Prime) (hs : ∀ q ∈ s, q.Prime) (hp_not : p ∉ s) :
    ¬ p ∣ prodOf s := by
  classical
  -- Use the generic `Prime.not_dvd_finset_prod` lemma.
  refine Prime.not_dvd_finset_prod (pp := hp.prime) (S := s) (g := fun q : ℕ => q) ?_
  intro q hq
  have hqP : q.Prime := hs q hq
  intro hpq
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqP).1 hpq
  exact hp_not (this ▸ hq)

private lemma fullSum_insert {s : Finset ℕ} {p : ℕ} (hp : p.Prime) (hp_not_mem : p ∉ s)
    (hs : ∀ q ∈ s, q.Prime) :
    fullSum (insert p s) = fullSum s * factorENN p := by
  classical
  let A : Finset (Finset ℕ) := s.powerset
  let B : Finset (Finset ℕ) := A.image (insert p)
  have hPow : (insert p s).powerset = A ∪ B := by
    simpa [A, B] using (Finset.powerset_insert s p)
  have hdisj : Disjoint A B := by
    refine Finset.disjoint_left.2 ?_
    intro t htA htB
    -- `t ⊆ s`, so `p ∉ t`; but `t = insert p u` implies `p ∈ t`.
    have hp_not_t : p ∉ t := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := t) htA hp_not_mem
    rcases Finset.mem_image.1 htB with ⟨u, huA, rfl⟩
    exact hp_not_t (Finset.mem_insert_self p u)

  -- Abbreviate the term to reduce rewriting noise.
  let F : Finset ℕ → Finset ℕ → ENNReal :=
    fun d e => CstarTerm (prodOf d) (prodOf e)

  -- The two “single prime” coefficients that appear in the split.
  let α : ENNReal := ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))
  let β : ENNReal := ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2))

  have hαβ : factorENN p = (1 : ENNReal) + 2 * α + β := by
    have h0 : (0 : ℝ) ≤ (2 : ℝ) := by positivity
    have hαr : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by positivity
    have hβr : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2) := by positivity
    -- `2/(p*(p-1))` as `2 * (1/(p*(p-1)))`, so `ofReal` matches `2 * α`.
    have h2 : ENNReal.ofReal (2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) = 2 * α := by
      -- `2/x = 2 * (1/x)` and `ofReal` respects products of nonneg reals.
      simpa [α, div_eq_mul_inv, ENNReal.ofReal_mul h0, mul_assoc, mul_left_comm, mul_comm]
    -- Now unfold `factorENN`/`factorR` and convert the `ofReal` of a sum.
    dsimp [factorENN, factorR, α, β]
    -- `ofReal (1 + a + b) = ofReal (1 + a) + ofReal b = 1 + ofReal a + ofReal b`.
    have hsum1 :
        ENNReal.ofReal
            (1 + 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) =
          (1 : ENNReal)
            + ENNReal.ofReal (2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))
            + ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) := by
      -- Associate as `(1 + a) + b`.
      have h1a : (0 : ℝ) ≤ 1 + 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by positivity
      have hA : (0 : ℝ) ≤ 1 := by positivity
      have hB : (0 : ℝ) ≤ 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by positivity
      calc
        ENNReal.ofReal ((1 + 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) =
            ENNReal.ofReal (1 + 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) +
              ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) := by
            simpa [add_assoc] using (ENNReal.ofReal_add h1a hβr)
        _ = (ENNReal.ofReal (1 : ℝ) + ENNReal.ofReal (2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) +
              ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) := by
            -- expand `ofReal (1 + a)`
            simpa using
              congrArg
                (fun x =>
                  x + ENNReal.ofReal (((p - 1 : ℕ) ^ 2 : ℝ)⁻¹) * ENNReal.ofReal ((p : ℝ)⁻¹))
                (ENNReal.ofReal_add hA hB)
        _ = (1 : ENNReal) + ENNReal.ofReal (2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) +
              ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) := by
            simp [add_assoc]
    -- Finish: rewrite `ofReal 1 = 1`, `ofReal(...) = β`, and the `2/(...)` term.
    calc
      ENNReal.ofReal
          (1 + 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) +
            1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) =
          (1 : ENNReal) + ENNReal.ofReal (2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) +
            ENNReal.ofReal (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) := hsum1
      _ = (1 : ENNReal) + 2 * α + β := by
          simp [h2, β, add_assoc, add_left_comm, add_comm]

  -- Unfold `fullSum` at the inserted set and split the two powersets.
  have hSplit :
      fullSum (insert p s) =
        (∑ d ∈ A, ∑ e ∈ A, F d e) +
        (∑ d ∈ A, ∑ e ∈ B, F d e) +
        (∑ d ∈ B, ∑ e ∈ A, F d e) +
        (∑ d ∈ B, ∑ e ∈ B, F d e) := by
    -- Expand both occurrences of `powerset (insert p s)` as `A ∪ B`.
    simp [fullSum, F, hPow, Finset.sum_union hdisj, Finset.sum_add_distrib, add_assoc, add_left_comm,
      add_comm, A, B]

  have hBase : (∑ d ∈ A, ∑ e ∈ A, F d e) = fullSum s := by
    simp [fullSum, F, A]

  -- Convert sums over `B = A.image (insert p)` into sums over `A`, using injectivity of `insert p`
  -- on subsets of `s`.
  have hInsert_inj : ∀ {u v : Finset ℕ}, u ∈ A → v ∈ A → insert p u = insert p v → u = v := by
    intro u v hu hv huv
    have hpu : p ∉ u := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := u) hu hp_not_mem
    have hpv : p ∉ v := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := v) hv hp_not_mem
    -- erase `p` from both sides
    have := congrArg (fun t : Finset ℕ => t.erase p) huv
    simpa [Finset.erase_insert hpu, Finset.erase_insert hpv] using this

  have hAB :
      (∑ d ∈ A, ∑ e ∈ B, F d e) = (fullSum s) * α := by
    -- Rewrite the `e ∈ B` sum as `e = insert p e'` with `e' ∈ A`.
    have hsumE :
        (Finset.sum B (fun e => ∑ d ∈ A, F d e)) =
          Finset.sum A (fun e' => ∑ d ∈ A, F d (insert p e')) := by
      classical
      -- Expand `B = A.image (insert p)` and rewrite the sum via an injective-image lemma.
      simpa [B] using
        (sum_image_eq_of_injOn
          (s := A)
          (f := fun u : Finset ℕ => insert p u)
          (g := fun e : Finset ℕ => ∑ d ∈ A, F d e)
          (hinj := by
            intro u hu v hv huv
            exact hInsert_inj hu hv huv))
    -- Now use the prime-multiplication lemma to factor out `α`.
    -- We proceed by rewriting `F d (insert p e')` as `F d e' * α`, then pulling `α` out.
    have hTerm :
        ∀ d ∈ A, ∀ e' ∈ A, F d (insert p e') = F d e' * α := by
      intro d hd e' he'
      have hdPr : ∀ q ∈ d, q.Prime := by
        intro q hq
        exact hs q ((Finset.mem_powerset.1 hd) hq)
      have hePr : ∀ q ∈ e', q.Prime := by
        intro q hq
        exact hs q ((Finset.mem_powerset.1 he') hq)
      have hdSq : Squarefree (prodOf d) := squarefree_prodOf hdPr
      have heSq : Squarefree (prodOf e') := squarefree_prodOf hePr
      have hpd : p ∉ d := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := d) hd hp_not_mem
      have hpe : p ∉ e' := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := e') he' hp_not_mem
      have hpd' : ¬ p ∣ prodOf d := not_dvd_prodOf_of_not_mem hp hdPr hpd
      have hpe' : ¬ p ∣ prodOf e' := not_dvd_prodOf_of_not_mem hp hePr hpe
      -- Turn `prodOf (insert p e')` into `p * prodOf e'` and apply `CstarTerm_mul_prime_right`.
      have hprod : prodOf (insert p e') = p * prodOf e' := prodOf_insert (p := p) (s := e') hpe
      dsimp [F]
      -- rewrite and apply the lemma
      simpa [hprod, α, mul_assoc, mul_left_comm, mul_comm] using
        (CstarTerm_mul_prime_right (p := p) (d := prodOf d) (e := prodOf e') hp hdSq heSq hpd' hpe')
    -- Put the pieces together and pull out `α` using distributivity.
    -- First swap the order so the factoring lemma applies cleanly.
    calc
      (∑ d ∈ A, ∑ e ∈ B, F d e)
          = ∑ e ∈ B, ∑ d ∈ A, F d e := by
              simpa using
                (Finset.sum_comm :
                  (∑ d ∈ A, ∑ e ∈ B, F d e) = ∑ e ∈ B, ∑ d ∈ A, F d e)
      _ = ∑ e' ∈ A, ∑ d ∈ A, F d (insert p e') := by
              simpa [hsumE]
      _ = ∑ e' ∈ A, ∑ d ∈ A, (F d e') * α := by
              refine Finset.sum_congr rfl ?_
              intro e' he'
              refine Finset.sum_congr rfl ?_
              intro d hd
              exact hTerm d hd e' he'
      _ = (∑ e' ∈ A, ∑ d ∈ A, F d e') * α := by
              simp [Finset.sum_mul, mul_assoc]
      _ = (∑ d ∈ A, ∑ e' ∈ A, F d e') * α := by
              congr 1
              simpa using
                (Finset.sum_comm :
                  (∑ e' ∈ A, ∑ d ∈ A, F d e') = ∑ d ∈ A, ∑ e' ∈ A, F d e')
      _ = (fullSum s) * α := by
              simp [fullSum, F, A, mul_assoc]

  have hBA :
      (∑ d ∈ B, ∑ e ∈ A, F d e) = (fullSum s) * α := by
    -- Symmetric to `hAB` by commutativity of the two sides.
    -- Expand `d ∈ B` as `d = insert p d'` and use `CstarTerm_mul_prime_left`.
    have hsumD :
        (∑ d ∈ B, ∑ e ∈ A, F d e) =
          ∑ d' ∈ A, ∑ e ∈ A, F (insert p d') e := by
      classical
      -- Expand `B = A.image (insert p)` and rewrite the outer sum via an injective-image lemma.
      simpa [B] using
        (sum_image_eq_of_injOn
          (s := A)
          (f := fun u : Finset ℕ => insert p u)
          (g := fun d : Finset ℕ => ∑ e ∈ A, F d e)
          (hinj := by
            intro u hu v hv huv
            exact hInsert_inj hu hv huv))
    have hTerm :
        ∀ d' ∈ A, ∀ e ∈ A, F (insert p d') e = F d' e * α := by
      intro d' hd' e he
      have hdPr : ∀ q ∈ d', q.Prime := by
        intro q hq
        exact hs q ((Finset.mem_powerset.1 hd') hq)
      have hePr : ∀ q ∈ e, q.Prime := by
        intro q hq
        exact hs q ((Finset.mem_powerset.1 he) hq)
      have hdSq : Squarefree (prodOf d') := squarefree_prodOf hdPr
      have heSq : Squarefree (prodOf e) := squarefree_prodOf hePr
      have hpd : p ∉ d' := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := d') hd' hp_not_mem
      have hpe : p ∉ e := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := e) he hp_not_mem
      have hpd' : ¬ p ∣ prodOf d' := not_dvd_prodOf_of_not_mem hp hdPr hpd
      have hpe' : ¬ p ∣ prodOf e := not_dvd_prodOf_of_not_mem hp hePr hpe
      have hprod : prodOf (insert p d') = p * prodOf d' := prodOf_insert (p := p) (s := d') hpd
      dsimp [F]
      simpa [hprod, α, mul_assoc, mul_left_comm, mul_comm] using
        (CstarTerm_mul_prime_left (p := p) (d := prodOf d') (e := prodOf e) hp hdSq heSq hpd' hpe')
    calc
      (∑ d ∈ B, ∑ e ∈ A, F d e)
          = ∑ d ∈ B, ∑ e ∈ A, F d e := rfl
      _ = ∑ d' ∈ A, ∑ e ∈ A, F (insert p d') e := by
            simpa [hsumD]
      _ = ∑ d' ∈ A, ∑ e ∈ A, (F d' e) * α := by
            refine Finset.sum_congr rfl ?_
            intro d' hd'
            refine Finset.sum_congr rfl ?_
            intro e he
            exact hTerm d' hd' e he
      _ = (∑ d' ∈ A, ∑ e ∈ A, F d' e) * α := by
            simp [Finset.sum_mul, mul_assoc]
      _ = (fullSum s) * α := by
            simp [fullSum, F, A, mul_assoc, mul_left_comm, mul_comm]

  have hBB :
      (∑ d ∈ B, ∑ e ∈ B, F d e) = (fullSum s) * β := by
    -- Expand both `d` and `e` from `B` as `insert p d'` and `insert p e'`, and use the `both` lemma.
    have hsumD : (∑ d ∈ B, ∑ e ∈ B, F d e) =
        ∑ d' ∈ A, ∑ e' ∈ A, F (insert p d') (insert p e') := by
      classical
      -- Rewrite both `B`-sums via `B = A.image (insert p)`.
      have houter :
          (∑ d ∈ B, ∑ e ∈ B, F d e) = ∑ d' ∈ A, ∑ e ∈ B, F (insert p d') e := by
        simpa [B] using
          (sum_image_eq_of_injOn
            (s := A)
            (f := fun u : Finset ℕ => insert p u)
            (g := fun d : Finset ℕ => ∑ e ∈ B, F d e)
            (hinj := by
              intro u hu v hv huv
              exact hInsert_inj hu hv huv))
      have hinner :
          ∀ d' ∈ A, (∑ e ∈ B, F (insert p d') e) = ∑ e' ∈ A, F (insert p d') (insert p e') := by
        intro d' _hd'
        simpa [B] using
          (sum_image_eq_of_injOn
            (s := A)
            (f := fun u : Finset ℕ => insert p u)
            (g := fun e : Finset ℕ => F (insert p d') e)
            (hinj := by
              intro u hu v hv huv
              exact hInsert_inj hu hv huv))
      -- Apply the inner rewrite inside the outer sum.
      calc
        (∑ d ∈ B, ∑ e ∈ B, F d e) = ∑ d' ∈ A, ∑ e ∈ B, F (insert p d') e := houter
        _ = ∑ d' ∈ A, ∑ e' ∈ A, F (insert p d') (insert p e') := by
              refine Finset.sum_congr rfl ?_
              intro d' hd'
              exact hinner d' hd'
    have hTerm :
        ∀ d' ∈ A, ∀ e' ∈ A, F (insert p d') (insert p e') = F d' e' * β := by
      intro d' hd' e' he'
      have hdPr : ∀ q ∈ d', q.Prime := by
        intro q hq
        exact hs q ((Finset.mem_powerset.1 hd') hq)
      have hePr : ∀ q ∈ e', q.Prime := by
        intro q hq
        exact hs q ((Finset.mem_powerset.1 he') hq)
      have hdSq : Squarefree (prodOf d') := squarefree_prodOf hdPr
      have heSq : Squarefree (prodOf e') := squarefree_prodOf hePr
      have hpd : p ∉ d' := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := d') hd' hp_not_mem
      have hpe : p ∉ e' := Finset.notMem_of_mem_powerset_of_notMem (s := s) (t := e') he' hp_not_mem
      have hpd' : ¬ p ∣ prodOf d' := not_dvd_prodOf_of_not_mem hp hdPr hpd
      have hpe' : ¬ p ∣ prodOf e' := not_dvd_prodOf_of_not_mem hp hePr hpe
      have hprodD : prodOf (insert p d') = p * prodOf d' := prodOf_insert (p := p) (s := d') hpd
      have hprodE : prodOf (insert p e') = p * prodOf e' := prodOf_insert (p := p) (s := e') hpe
      dsimp [F]
      simpa [hprodD, hprodE, β, mul_assoc, mul_left_comm, mul_comm] using
        (CstarTerm_mul_prime_both (p := p) (d := prodOf d') (e := prodOf e') hp hdSq heSq hpd' hpe')
    calc
      (∑ d ∈ B, ∑ e ∈ B, F d e)
          = ∑ d' ∈ A, ∑ e' ∈ A, F (insert p d') (insert p e') := by
              simpa [hsumD]
      _ = ∑ d' ∈ A, ∑ e' ∈ A, (F d' e') * β := by
              refine Finset.sum_congr rfl ?_
              intro d' hd'
              refine Finset.sum_congr rfl ?_
              intro e' he'
              exact hTerm d' hd' e' he'
      _ = (∑ d' ∈ A, ∑ e' ∈ A, F d' e') * β := by
              simp [Finset.sum_mul, mul_assoc]
      _ = (fullSum s) * β := by
              simp [fullSum, F, A, mul_assoc, mul_left_comm, mul_comm]

  -- Combine the four quadrants and identify the coefficient with `factorENN p`.
  have hsum4 :
      fullSum (insert p s) =
        (fullSum s) + (fullSum s) * α + (fullSum s) * α + (fullSum s) * β := by
    simpa [hBase, hAB, hBA, hBB, add_assoc, add_left_comm, add_comm] using hSplit

  -- Factor out `fullSum s` and rewrite the coefficient.
  calc
    fullSum (insert p s)
        = (fullSum s) * ((1 : ENNReal) + 2 * α + β) := by
            -- `a + a*α + a*α + a*β = a*(1 + 2*α + β)`
            simp [hsum4, mul_add, add_mul, add_assoc, add_left_comm, add_comm, two_mul, mul_assoc]
    _ = (fullSum s) * factorENN p := by
            simpa [hαβ]

private lemma fullSum_eq_prod_factorENN (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    fullSum S = ∏ p ∈ S, factorENN p := by
  classical
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _hS
    -- `powerset ∅ = {∅}` and `prodOf ∅ = 1`, so this is just `CstarTerm 1 1 = 1`.
    simp [fullSum, CstarTerm, W, muSq, prodOf]
  · intro p s hp_not_mem ih hS
    have hpP : p.Prime := hS p (by simp [hp_not_mem])
    have hsP : ∀ q ∈ s, q.Prime := by
      intro q hq
      exact hS q (by simp [hq, hp_not_mem])
    have ih' : fullSum s = ∏ q ∈ s, factorENN q := ih hsP
    -- Expand `fullSum (insert p s)` using the recursion lemma and then simplify.
    calc
      fullSum (insert p s) = fullSum s * factorENN p :=
        fullSum_insert (s := s) (p := p) hpP hp_not_mem hsP
      _ = (∏ q ∈ s, factorENN q) * factorENN p := by simpa [ih']
      _ = factorENN p * ∏ q ∈ s, factorENN q := by simp [mul_comm, mul_left_comm, mul_assoc]
      _ = ∏ q ∈ insert p s, factorENN q := by
            simp [Finset.prod_insert, hp_not_mem, mul_assoc]

private lemma sum_range_inv_mul_sub_eq (B : ℕ) (hB : 2 ≤ B) :
    (∑ n ∈ Finset.range (B + 1), (1 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)))) = 1 - 1 / (B : ℝ) := by
  -- Peel off the `n = 0` and `n = 1` terms (both are `0`), rewrite the remaining sum over
  -- `k = 0..B-2`, and telescope.
  have hB' : 1 ≤ B := le_trans (by decide : (1 : ℕ) ≤ 2) hB

  -- Shift the range sum to start at `n = 2`.
  have hshift :
      (∑ n ∈ Finset.range (B + 1), (1 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ))))
        = ∑ k ∈ Finset.range (B - 1), (1 / (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ))) := by
    -- First shift: drop `n = 0`.
    rw [Finset.sum_range_succ']
    simp
    -- Second shift: drop `n = 1`.
    have hdecomp : B = (B - 1) + 1 := (Nat.sub_add_cancel hB').symm
    -- Rewrite `range B` as `range ((B-1)+1)` and shift again.
    rw [hdecomp, Finset.sum_range_succ']
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    -- The remaining normalization is just `(↑k + 1 + 1) = (↑k + 2)`.
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hcast : ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 := by ring
    simpa [hcast, add_assoc]

  -- Now telescope the shifted sum.
  have htel :
      (∑ k ∈ Finset.range (B - 1), (1 / (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ))))
        = 1 - 1 / (B : ℝ) := by
    have hterm :
        ∀ k : ℕ,
          (1 / (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ))) =
            (1 / ((k + 1 : ℕ) : ℝ)) - (1 / ((k + 2 : ℕ) : ℝ)) := by
      intro k
      have ha : ((k + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
      have hb : ((k + 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (k + 1))
      field_simp [ha, hb]
      -- remaining goal is the simple identity `(k+2) - (k+1) = 1` after casts
      have hdiff :
          (((2 + k : ℕ) : ℝ) - ((1 + k : ℕ) : ℝ)) = (1 : ℝ) := by
        -- rewrite casts to `k + c` in `ℝ` and finish by `ring`
        have : ((k : ℝ) + (2 : ℝ)) - ((k : ℝ) + (1 : ℝ)) = (1 : ℝ) := by ring
        simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using this
      simpa using hdiff.symm
    calc
      (∑ k ∈ Finset.range (B - 1), (1 / (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ))))
          = ∑ k ∈ Finset.range (B - 1),
              ((1 / ((k + 1 : ℕ) : ℝ)) - (1 / ((k + 2 : ℕ) : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [hterm k]
      _ = (1 / ((0 + 1 : ℕ) : ℝ)) - (1 / (((B - 1 : ℕ) + 1 : ℕ) : ℝ)) := by
              -- `sum_range_sub'` telescopes `f k - f(k+1)`.
              simpa [Finset.sum_range_sub', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (Finset.sum_range_sub' (f := fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ))) (n := (B - 1)))
      _ = 1 - 1 / (B : ℝ) := by
              have : (B - 1 : ℕ) + 1 = B := Nat.sub_add_cancel hB'
              simp [this]

  exact hshift.trans htel

private lemma sum_inv_p_mul_sub_le_one (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) ≤ 1 := by
  classical
  by_cases h0 : s = ∅
  · simp [h0]
  · -- Let `B` be the maximum element; since all elements are prime, `B ≥ 2`.
    let B : ℕ := s.max' (Finset.nonempty_iff_ne_empty.2 h0)
    have hBmem : B ∈ s := Finset.max'_mem s (Finset.nonempty_iff_ne_empty.2 h0)
    have hBprime : B.Prime := hs B hBmem
    have hB2 : 2 ≤ B := hBprime.two_le
    have hsub : s ⊆ Finset.range (B + 1) := by
      intro n hn
      have hnle : n ≤ B := Finset.le_max' s n hn
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hnle)
    -- compare the sum over `s` to the sum over the full range.
    have hle :
        (∑ p ∈ s, (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))))
          ≤
        (∑ n ∈ Finset.range (B + 1), (1 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)))) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro n hn hn_not
      positivity
    have hsum :
        (∑ n ∈ Finset.range (B + 1), (1 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)))) = 1 - 1 / (B : ℝ) :=
      sum_range_inv_mul_sub_eq B hB2
    have hpos : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
    -- `1 - 1/B ≤ 1` since `1/B ≥ 0`.
    have hle1 : (1 - 1 / (B : ℝ)) ≤ 1 := by
      simpa using (sub_le_self (1 : ℝ) hpos)
    -- Avoid `simp` rewriting `one_div` into inverses.
    have hrange :
        (∑ n ∈ Finset.range (B + 1), (1 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)))) ≤ 1 := by
      rw [hsum]
      exact hle1
    exact le_trans hle hrange

private lemma factorENN_le_exp (p : ℕ) (hp : p.Prime) :
    factorENN p ≤ ENNReal.ofReal (Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
  -- Bound `factorR p` by `1 + 3/(p(p-1)) ≤ exp(3/(p(p-1)))`.
  have hpos : (0 : ℝ) < ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
    have hp2 : 2 ≤ p := hp.two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ 1) hp2)
    have hm_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      have : 0 < (p - 1 : ℕ) := Nat.sub_pos_of_lt hp.one_lt
      exact_mod_cast this
    nlinarith
  have hle_inv :
      (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)) ≤ (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
    have hpm1 : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ p - 1 := Nat.succ_le_iff.2 (Nat.sub_pos_of_lt hp.one_lt)
      exact_mod_cast this
    have hsq : ((p - 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ 2 := by
      -- `x ≤ x^2` for `x ≥ 1`
      simpa [pow_two] using (mul_le_mul_of_nonneg_left hpm1 (by positivity : (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ)))
    have hden :
        ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) ≤ ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (p : ℝ))
    -- Apply `one_div_le_one_div_of_le` to the denominators.
    -- From `a ≤ b` with `a>0`, we get `1/b ≤ 1/a`.
    have := one_div_le_one_div_of_le hpos hden
    simpa [one_div] using this
  have hX :
      factorR p ≤ 1 + 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
    -- `2/(p(p-1)) + 1/(p(p-1)^2) ≤ 3/(p(p-1))`.
    dsimp [factorR]
    have hx : ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hpos
    have hsum_le :
        2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)
          ≤ 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
      calc
        2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)
            ≤ 2 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) + 1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
                exact add_le_add_left hle_inv _
        _ = 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)) := by
              -- `2/x + 1/x = 3/x`
              -- avoid `simp` leaving `inv`-normal forms behind
              field_simp [hx]
              ring
    -- Add `1` to both sides.
    have := add_le_add_left hsum_le (1 : ℝ)
    -- normalize the associativity/commutativity of addition
    simpa [add_assoc, add_left_comm, add_comm] using this
  have hExp :
      (1 + 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) ≤ Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
    simpa [add_comm] using Real.add_one_le_exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))
  have hR : factorR p ≤ Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := le_trans (le_trans hX hExp) (le_rfl)
  -- Push the inequality through `ENNReal.ofReal`.
  exact (ENNReal.ofReal_le_ofReal hR)

private lemma prod_factorENN_le_exp_three (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, factorENN p) ≤ ENNReal.ofReal (Real.exp 3) := by
  classical
  -- Compare each prime factor to an exponential.
  have hstep :
      (∏ p ∈ S, factorENN p) ≤ ∏ p ∈ S, ENNReal.ofReal (Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
    refine Finset.prod_le_prod' ?_
    intro p hp
    exact factorENN_le_exp p (hS p hp)
  -- Turn the RHS product into `ofReal (exp (sum ...))`.
  have hprodexp :
      (∏ p ∈ S, ENNReal.ofReal (Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))))
        = ENNReal.ofReal (Real.exp (∑ p ∈ S, 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
    have hnonneg :
        ∀ p, p ∈ S → (0 : ℝ) ≤ Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
      intro p hp
      positivity
    -- `ofReal` commutes with finite products of nonnegative reals.
    have h_ofReal_prod :
        (∏ p ∈ S, ENNReal.ofReal (Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))))
          = ENNReal.ofReal (∏ p ∈ S, Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
      -- The lemma is stated in the opposite direction.
      symm
      exact ENNReal.ofReal_prod_of_nonneg (s := S)
        (f := fun p => Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))))
        (by intro p hp; exact hnonneg p hp)
    -- `∏ exp = exp (∑ ...)` for finite `Finset`.
    have h_real :
        (∏ p ∈ S, Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))))
          = Real.exp (∑ p ∈ S, 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
      -- `Real.exp_sum` is `exp (∑ p in S, a p) = ∏ p in S, exp (a p)`.
      simpa using
        (Real.exp_sum (s := S) (f := fun p : ℕ => 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))).symm
    -- Put the two steps together.
    calc
      (∏ p ∈ S, ENNReal.ofReal (Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))))
          = ENNReal.ofReal (∏ p ∈ S, Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := h_ofReal_prod
      _ = ENNReal.ofReal (Real.exp (∑ p ∈ S, 3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
            rw [h_real]
  -- Bound the finite sum of coefficients by `3`.
  have hsumInv : (∑ p ∈ S, (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) ≤ 1 :=
    sum_inv_p_mul_sub_le_one S hS
  have hsum3 :
      (∑ p ∈ S, (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) ≤ 3 := by
    -- rewrite `3/x` as `3 * (1/x)` and pull out the factor `3`
    have hrew :
        (∑ p ∈ S, (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))))
          = (3 : ℝ) * (∑ p ∈ S, (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := by
      -- `3/x = 3 * (1/x)` and `∑ (3 * f p) = 3 * ∑ f p`.
      have : (∑ p ∈ S, (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))))
          = ∑ p ∈ S, (3 : ℝ) * (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      -- Pull out the constant.
      simpa [this, Finset.mul_sum, mul_assoc] using (Finset.mul_sum (a := (3 : ℝ)) (s := S)
        (f := fun p : ℕ => (1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))))).symm
    -- Now bound by `3 * 1`.
    have h3 : (0 : ℝ) ≤ (3 : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hsumInv h3
    simpa [hrew] using this
  -- Finish by monotonicity of `exp`.
  have hexp : Real.exp (∑ p ∈ S, (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) ≤ Real.exp 3 :=
    Real.exp_monotone hsum3
  -- Combine all inequalities in `ENNReal`.
  calc
    (∏ p ∈ S, factorENN p)
        ≤ ∏ p ∈ S, ENNReal.ofReal (Real.exp (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ)))) := hstep
    _ = ENNReal.ofReal (Real.exp (∑ p ∈ S, (3 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ))))) := hprodexp
    _ ≤ ENNReal.ofReal (Real.exp 3) := by
          exact ENNReal.ofReal_le_ofReal hexp

private def primeFactorsPair (x : ℕ × ℕ) : Finset ℕ × Finset ℕ :=
  (x.1.primeFactors, x.2.primeFactors)

private lemma primeFactorsPair_inj {x y : ℕ × ℕ}
    (hx : Squarefree x.1 ∧ Squarefree x.2) (hy : Squarefree y.1 ∧ Squarefree y.2)
    (h : primeFactorsPair x = primeFactorsPair y) : x = y := by
  rcases x with ⟨d1, e1⟩
  rcases y with ⟨d2, e2⟩
  simp [primeFactorsPair] at h
  rcases h with ⟨hd, he⟩
  have hd1 : (∏ p ∈ d1.primeFactors, p) = d1 := Nat.prod_primeFactors_of_squarefree hx.1
  have hd2 : (∏ p ∈ d2.primeFactors, p) = d2 := Nat.prod_primeFactors_of_squarefree hy.1
  have he1 : (∏ p ∈ e1.primeFactors, p) = e1 := Nat.prod_primeFactors_of_squarefree hx.2
  have he2 : (∏ p ∈ e2.primeFactors, p) = e2 := Nat.prod_primeFactors_of_squarefree hy.2
  have hdEq : d1 = d2 := by
    simpa [hd1, hd2] using congrArg (fun s : Finset ℕ => ∏ p ∈ s, p) hd
  have heEq : e1 = e2 := by
    simpa [he1, he2] using congrArg (fun s : Finset ℕ => ∏ p ∈ s, p) he
  simp [hdEq, heEq]

private lemma finite_sum_le_fullSum (t : Finset (ℕ × ℕ)) :
    (∑ x ∈ t, CstarTermPair x) ≤
      fullSum (t.biUnion fun x => x.1.primeFactors ∪ x.2.primeFactors) := by
  classical
  let P : (ℕ × ℕ) → Prop := fun x => Squarefree x.1 ∧ Squarefree x.2
  let tSF : Finset (ℕ × ℕ) := t.filter P
  let S : Finset ℕ := t.biUnion fun x => x.1.primeFactors ∪ x.2.primeFactors
  -- First: restrict to squarefree pairs (other terms are `0`).
  have hrestrict :
      (∑ x ∈ t, CstarTermPair x) = ∑ x ∈ tSF, CstarTermPair x := by
    have hsum_if :
        (∑ x ∈ t, CstarTermPair x) = ∑ x ∈ t, (if P x then CstarTermPair x else 0) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      by_cases hP : P x
      · simp [hP]
      · have : ¬ Squarefree x.1 ∨ ¬ Squarefree x.2 := not_and_or.mp hP
        cases this with
        | inl hd =>
            simp [P, hP, CstarTermPair, CstarTerm_eq_zero_of_not_squarefree_left (d := x.1) (e := x.2) hd]
        | inr he =>
            simp [P, hP, CstarTermPair, CstarTerm_eq_zero_of_not_squarefree_right (d := x.1) (e := x.2) he]
    -- Use `sum_filter` to rewrite the RHS sum over `tSF`.
    simpa [tSF, Finset.sum_filter, hsum_if, P]

  -- Second: reindex the squarefree sum into a sum over pairs of prime-factor sets.
  let u : Finset (Finset ℕ × Finset ℕ) := tSF.image primeFactorsPair
  let g : (Finset ℕ × Finset ℕ) → ENNReal := fun x => CstarTerm (prodOf x.1) (prodOf x.2)

  have hu_eq :
      (∑ x ∈ tSF, CstarTermPair x) = ∑ y ∈ u, g y := by
    -- `primeFactorsPair` is injective on `tSF` (squarefree numbers are determined by their primeFactors).
    have hinj :
        ∀ x1 ∈ tSF, ∀ x2 ∈ tSF, primeFactorsPair x1 = primeFactorsPair x2 → x1 = x2 := by
      intro x1 hx1 x2 hx2 h'
      have hx1' : P x1 := (Finset.mem_filter.1 hx1).2
      have hx2' : P x2 := (Finset.mem_filter.1 hx2).2
      exact primeFactorsPair_inj hx1' hx2' h'
    -- Rewrite the sum over the image.
    have himg :
        (∑ y ∈ u, g y) = ∑ x ∈ tSF, g (primeFactorsPair x) := by
      -- Use a small local lemma to rewrite `sum` over `image` under injectivity.
      -- (We avoid relying on the exact argument order of Mathlib’s `Finset.sum_image`.)
      simpa [u] using (sum_image_eq_of_injOn (s := tSF) (f := primeFactorsPair) (g := g) hinj)
    -- Now show `g (primeFactorsPair x) = CstarTermPair x` on `tSF`.
    have hterm :
        ∀ x ∈ tSF, g (primeFactorsPair x) = CstarTermPair x := by
      intro x hx
      have hxP : P x := (Finset.mem_filter.1 hx).2
      -- rewrite `x.1` and `x.2` as products of their prime factors
      have hd : prodOf x.1.primeFactors = x.1 := by
        simpa [prodOf] using (Nat.prod_primeFactors_of_squarefree hxP.1)
      have he : prodOf x.2.primeFactors = x.2 := by
        simpa [prodOf] using (Nat.prod_primeFactors_of_squarefree hxP.2)
      simp [g, primeFactorsPair, CstarTermPair, CstarTerm, hd, he]
    -- Combine.
    have : (∑ x ∈ tSF, CstarTermPair x) = ∑ x ∈ tSF, g (primeFactorsPair x) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simpa using (hterm x hx).symm
    exact this.trans himg.symm

  -- Third: show `u` sits inside `S.powerset × S.powerset`, and use monotonicity of `sum`.
  have hsubset : u ⊆ S.powerset.product S.powerset := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    have hx_mem : x ∈ t := (Finset.mem_filter.1 hx).1
    have hU : x.1.primeFactors ∪ x.2.primeFactors ⊆ S :=
      Finset.subset_biUnion_of_mem (s := t) (u := fun x => x.1.primeFactors ∪ x.2.primeFactors) hx_mem
    have h1 : x.1.primeFactors ⊆ S := subset_trans Finset.subset_union_left hU
    have h2 : x.2.primeFactors ⊆ S := subset_trans Finset.subset_union_right hU
    refine Finset.mem_product.2 ?_
    exact ⟨Finset.mem_powerset.2 h1, Finset.mem_powerset.2 h2⟩

  have hsum_le :
      (∑ y ∈ u, g y) ≤ ∑ y ∈ S.powerset.product S.powerset, g y := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro y hy hy_not
    exact bot_le

  -- Convert the RHS to `fullSum S`.
  have hfull : (∑ y ∈ S.powerset.product S.powerset, g y) = fullSum S := by
    simpa [fullSum_eq_sum_product, g]

  -- Assemble.
  calc
    (∑ x ∈ t, CstarTermPair x)
        = ∑ x ∈ tSF, CstarTermPair x := hrestrict
    _ = ∑ y ∈ u, g y := hu_eq
    _ ≤ ∑ y ∈ S.powerset.product S.powerset, g y := hsum_le
    _ = fullSum S := hfull

private lemma Cstar_le_exp_three : Cstar ≤ ENNReal.ofReal (Real.exp 3) := by
  classical
  -- Reduce to bounding each finite partial sum.
  rw [Cstar_eq_tsum_term, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le ?_
  intro t
  let S : Finset ℕ := t.biUnion fun x => x.1.primeFactors ∪ x.2.primeFactors
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases Finset.mem_biUnion.1 hp with ⟨x, hx, hp'⟩
    rcases Finset.mem_union.1 hp' with hp' | hp'
    · exact Nat.prime_of_mem_primeFactors hp'
    · exact Nat.prime_of_mem_primeFactors hp'
  have hsum_le : (∑ x ∈ t, CstarTermPair x) ≤ fullSum S := finite_sum_le_fullSum t
  have hfull :
      fullSum S ≤ ENNReal.ofReal (Real.exp 3) := by
    -- `fullSum S = ∏_{p∈S} factorENN p ≤ exp 3`
    have hfac : fullSum S = ∏ p ∈ S, factorENN p := fullSum_eq_prod_factorENN S hS
    have hprod : (∏ p ∈ S, factorENN p) ≤ ENNReal.ofReal (Real.exp 3) := prod_factorENN_le_exp_three S hS
    simpa [hfac] using hprod
  exact le_trans hsum_le hfull

theorem Cstar_le_45 : Cstar ≤ ENNReal.ofReal 45 := by
  have hC : Cstar ≤ ENNReal.ofReal (Real.exp 3) := Cstar_le_exp_three
  have hE : (Real.exp 3 : ℝ) ≤ (45 : ℝ) := exp_three_le_45
  exact le_trans hC (by simpa using ENNReal.ofReal_le_ofReal hE)


--/ ## Main: unconditional totient-squared tail, then filtered corollary-/

theorem tsum_tail_inv_totient_sq_le (R : ℕ) (hR : 1 ≤ R) :
  (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
    ≤ ENNReal.ofReal (2 / (R : ℝ)) * Cstar := by
  classical

  -- First: apply Step 2 pointwise on the tail (note: R < n ⇒ n ≠ 0 since R ≥ 1).
  have hStep2_tsum :
      (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
        ≤
      (∑' n : ℕ,
          if R < n then
            (Nat.divisors n).sum (fun d =>
              (Nat.divisors n).sum (fun e =>
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
          else 0) := by
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    by_cases hRn : R < n
    · have hn0 : n ≠ 0 := by
        apply Nat.ne_of_gt
        exact lt_trans (Nat.lt_of_lt_of_le Nat.zero_lt_one hR) hRn
      simpa [hRn] using (inv_totient_sq_le_double_divisor_sum (n := n) hn0)
    · simp [hRn]

  -- Second: dominate the finite divisor sums by a double tsum with the `lcm`-divisibility test.
  have hDiv_to_tsum :
      (∑' n : ℕ,
          if R < n then
            (Nat.divisors n).sum (fun d =>
              (Nat.divisors n).sum (fun e =>
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
          else 0)
        ≤
      (∑' n : ℕ, ∑' d : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := by
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    by_cases hRn : R < n
    · -- For this n, bound the double Finset sum by the double tsum (Tonelli later).
      have hn0 : n ≠ 0 := by
        apply Nat.ne_of_gt
        exact lt_trans (Nat.lt_of_lt_of_le Nat.zero_lt_one hR) hRn

      -- Inner (over e) bound for each fixed divisor d.
      have hinner (d : ℕ) (hd : d ∈ Nat.divisors n) :
          (Nat.divisors n).sum (fun e =>
              W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2))
            ≤
          (∑' e : ℕ,
              if Nat.lcm d e ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0) := by
        refine le_trans ?_ (ENNReal.sum_le_tsum (Nat.divisors n))
        refine le_of_eq ?_
        refine Finset.sum_congr rfl ?_
        intro e he
        have hd' : d ∣ n := Nat.dvd_of_mem_divisors hd
        have he' : e ∣ n := Nat.dvd_of_mem_divisors he
        have hlcm : Nat.lcm d e ∣ n := (Nat.lcm_dvd_iff).2 ⟨hd', he'⟩
        simp [hlcm]

      -- Outer (over d) bound using the inner bound.
      have houter :
          (Nat.divisors n).sum (fun d =>
              (Nat.divisors n).sum (fun e =>
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
            ≤
          (∑' d : ℕ, ∑' e : ℕ,
              if Nat.lcm d e ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0) := by
        calc (Nat.divisors n).sum (fun d =>
                (Nat.divisors n).sum (fun e =>
                  W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)))
            ≤ (Nat.divisors n).sum (fun d =>
                (∑' e : ℕ,
                    if Nat.lcm d e ∣ n then
                      W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
                    else 0)) := by
                refine Finset.sum_le_sum ?_
                intro d hd
                exact hinner d hd
          _ ≤ ∑' d : ℕ, ∑' e : ℕ,
                if Nat.lcm d e ∣ n then
                  W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
                else 0 := ENNReal.sum_le_tsum (Nat.divisors n)

      -- Now fold the `if R < n` into the big `if` by simp.
      simpa [hRn] using houter
    · simp [hRn]

  -- Now combine the two reductions.
  have hMain :
      (∑' n : ℕ, if R < n then ENNReal.ofReal (1 / (Nat.totient n : ℝ) ^ 2) else 0)
        ≤
      (∑' n : ℕ, ∑' d : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := by
    exact le_trans hStep2_tsum hDiv_to_tsum

  -- Swap order of summation (Tonelli/Fubini for ENNReal): n ↔ d, then n ↔ e.
  -- This lemma name may be `ENNReal.tsum_tsum` in your snapshot.
  have hswap_nd :
      (∑' n : ℕ, ∑' d : ℕ, (∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0))
        =
      (∑' d : ℕ, ∑' n : ℕ, (∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)) := by
    exact ENNReal.tsum_comm

  have hswap_ne (d : ℕ) :
      (∑' n : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)
        =
      (∑' e : ℕ, ∑' n : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := by
    exact ENNReal.tsum_comm

  -- Apply Step 3 on the inner (n)-sum for each (d,e), then recognize Cstar.
  have hBound :
      (∑' n : ℕ, ∑' d : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)
        ≤ ENNReal.ofReal (2 / (R : ℝ)) * Cstar := by
    -- reorder to (d,e,n)
    rw [hswap_nd]
    -- push the second swap inside the outer tsum
    let B : ENNReal :=
      ∑' d : ℕ, ∑' e : ℕ,
        (W d * W e) * ENNReal.ofReal (2 / ((Nat.lcm d e : ℝ) * (R : ℝ)))
    refine le_trans (b := B) ?_ ?_
    · -- show LHS ≤ B using Step 3
      refine ENNReal.tsum_le_tsum (fun d => ?_)
      -- swap (n,e) inside for each d
      have : (∑' n : ℕ, ∑' e : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0)
        =
        (∑' e : ℕ, ∑' n : ℕ,
          if R < n ∧ Nat.lcm d e ∣ n then
            W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
          else 0) := hswap_ne d
      -- use the swapped form
      rw [this]
      -- now bound termwise in e
      refine ENNReal.tsum_le_tsum (fun e => ?_)
      -- factor constants and apply Step 3 with L = lcm d e
      let L : ℕ := Nat.lcm d e
      by_cases hL0 : L = 0
      · -- if L=0 then (L ∣ n) forces n=0, impossible under R<n with R≥1, so tsum is 0
        have hsum_zero : (∑' n : ℕ,
            if R < n ∧ L ∣ n then
              W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
            else 0) = 0 := by
          have hfun_zero : (fun n : ℕ =>
              if R < n ∧ L ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0) = 0 := by
            funext n
            by_cases h : R < n ∧ L ∣ n
            · have : False := by
                have hLn : L ∣ n := h.2
                -- L=0 divides only n=0
                have hn0 : n = 0 := by simpa [hL0] using hLn
                have : ¬ R < n := by simpa [hn0] using (Nat.not_lt_zero R)
                exact this h.1
              exact (False.elim this)
            · simp [h]
          simp only [hfun_zero]
          exact tsum_zero
        -- The goal LHS equals the sum we just proved is 0 (up to definitional equality)
        have heq : (∑' n : ℕ, if R < n ∧ d.lcm e ∣ n then W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0) =
            (∑' n : ℕ, if R < n ∧ L ∣ n then W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0) := by
          rfl
        rw [heq, hsum_zero]
        exact zero_le _
      · have hL : 1 ≤ L := (Nat.one_le_iff_ne_zero).2 hL0
        -- rewrite to pull W d * W e out
        have hfactor :
            (fun n : ℕ =>
              if R < n ∧ L ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0)
              =
            (fun n : ℕ =>
              (W d * W e) *
                (if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)) := by
          funext n
          by_cases h : R < n ∧ L ∣ n <;> simp [h, mul_assoc]
        -- apply Step 3
        have htail :=
          tsum_multiples_inv_sq_le (R := R) (L := L) hR hL
        -- multiply the inequality by (W d * W e)
        have hmul :
            (W d * W e) *
                (∑' n : ℕ, if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)
              ≤
            (W d * W e) * ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := by
          exact mul_le_mul_of_nonneg_left htail (by simp)
        -- finish this (d,e) term
        -- (∑' n, (W d * W e) * ...) = (W d * W e) * (∑' n, ...) by `tsum_mul_left`
        calc
          (∑' n : ℕ,
              if R < n ∧ L ∣ n then
                W d * W e * ENNReal.ofReal (1 / (n : ℝ) ^ 2)
              else 0)
              = (∑' n : ℕ,
                  (W d * W e) *
                    (if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0)) := by
                  simp [hfactor]
          _ = (W d * W e) *
                (∑' n : ℕ, if R < n ∧ L ∣ n then ENNReal.ofReal (1 / (n : ℝ) ^ 2) else 0) := by
                rw [ENNReal.tsum_mul_left]
          _ ≤ (W d * W e) * ENNReal.ofReal (2 / ((L : ℝ) * (R : ℝ))) := hmul
    · -- identify the RHS with (2/R)*Cstar
      -- after the previous step we have exactly the defining double sum for Cstar
      -- up to pulling out the constant (2/R)
      have hR_pos : (0 : ℝ) < (R : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hR))
      -- Rewrite B by factoring out 2/R
      have hB_eq : B = ∑' d : ℕ, ∑' e : ℕ, ENNReal.ofReal (2 / ↑R) * (W d * W e * ENNReal.ofReal (1 / (Nat.lcm d e : ℝ))) := by
        refine tsum_congr (fun d => tsum_congr (fun e => ?_))
        by_cases hL0 : Nat.lcm d e = 0
        · simp [hL0]
        · have hL_pos : (0 : ℝ) < (Nat.lcm d e : ℝ) := by
            exact_mod_cast (Nat.pos_of_ne_zero hL0)
          have harith : (2 : ℝ) / ((Nat.lcm d e : ℝ) * (R : ℝ)) = (2 / ↑R) * (1 / (Nat.lcm d e : ℝ)) := by
            field_simp [hR_pos.ne', hL_pos.ne']
          rw [harith]
          have h2R_nn : (0 : ℝ) ≤ 2 / ↑R := by positivity
          rw [ENNReal.ofReal_mul h2R_nn]
          ring
      rw [hB_eq]
      -- First, show that the LHS equals (2/R) * (double sum of W d * W e * 1/lcm)
      have hfactor_out : (∑' (d : ℕ) (e : ℕ), ENNReal.ofReal (2 / ↑R) * (W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e)))) =
          ENNReal.ofReal (2 / ↑R) * (∑' (d : ℕ) (e : ℕ), W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e))) := by
        have h1 : ∀ d, (∑' e : ℕ, ENNReal.ofReal (2 / ↑R) * (W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e)))) =
            ENNReal.ofReal (2 / ↑R) * (∑' e : ℕ, W d * W e * ENNReal.ofReal (1 / ↑(d.lcm e))) := by
          intro d
          rw [ENNReal.tsum_mul_left]
        simp_rw [h1]
        rw [ENNReal.tsum_mul_left]
      rw [hfactor_out]
      refine mul_le_mul_left' ?_ _
      -- Now show the double sum ≤ Cstar
      unfold Cstar
      refine ENNReal.tsum_le_tsum (fun d => ENNReal.tsum_le_tsum (fun e => ?_))
      by_cases hL0 : Nat.lcm d e = 0
      · simp [hL0]
      · have hL_pos : (0 : ℝ) < (Nat.lcm d e : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hL0)
        have heq : ENNReal.ofReal (1 / (Nat.lcm d e : ℝ)) = ENNReal.ofReal ((Nat.lcm d e : ℝ)⁻¹) := by
          congr 1
          field_simp
        rw [heq]

  -- Put it all together.
  exact le_trans hMain hBound

theorem euler_tail_bound_tsum_ENNReal_of_Cstar_le
    (R N : ℕ) (hR : 1 ≤ R) {C : ℝ} (hC : Cstar ≤ ENNReal.ofReal C) :
    (∑' r : ℕ,
        if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
          ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
        else 0)
      ≤ ENNReal.ofReal (((2 : ℝ) * C) / R) := by
  -- Drop the extra conditions and use the unconditional tail bound, then apply the supplied bound
  -- on `Cstar`.
  have hdrop :
      (∑' r : ℕ,
          if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
            ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
          else 0)
        ≤
      (∑' r : ℕ,
          if R < r then
            ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
          else 0) := by
    refine ENNReal.tsum_le_tsum fun r => ?_
    split_ifs with h1 h2
    · simp
    · exfalso; exact h2 h1.1
    · simp
    · rfl

  have huncond := tsum_tail_inv_totient_sq_le (R := R) hR

  have hmul :
      ENNReal.ofReal (2 / (R : ℝ)) * Cstar
        ≤ ENNReal.ofReal (2 / (R : ℝ)) * ENNReal.ofReal C := by
    exact mul_le_mul_of_nonneg_left hC (by simp)

  have hmain :
      (∑' r : ℕ,
          if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
            ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
          else 0)
        ≤ ENNReal.ofReal (2 / (R : ℝ)) * ENNReal.ofReal C :=
    (hdrop.trans huncond).trans hmul

  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hR)
  have h2R_nonneg : 0 ≤ (2 / (R : ℝ)) := by
    exact div_nonneg (by norm_num) (le_of_lt hRpos)

  have harith : (2 / (R : ℝ)) * C = ((2 : ℝ) * C) / (R : ℝ) := by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

  have hmul_ofReal :
      ENNReal.ofReal (2 / (R : ℝ)) * ENNReal.ofReal C
        = ENNReal.ofReal (((2 : ℝ) * C) / (R : ℝ)) := by
    calc
      ENNReal.ofReal (2 / (R : ℝ)) * ENNReal.ofReal C
          = ENNReal.ofReal ((2 / (R : ℝ)) * C) := by
              simpa using (ENNReal.ofReal_mul h2R_nonneg).symm
      _ = ENNReal.ofReal (((2 : ℝ) * C) / (R : ℝ)) := by
              simp [harith]

  -- Convert the RHS from division by `(R : ℝ)` to division by `R` (via coercions).
  simpa [hmul_ofReal] using hmain

theorem euler_tail_bound_tsum_ENNReal (R N : ℕ) (hR : 1 ≤ R) :
  (∑' r : ℕ,
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
        ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
      else 0)
    ≤ ENNReal.ofReal ((90 : ℝ) / R) := by
  have h :=
    euler_tail_bound_tsum_ENNReal_of_Cstar_le (R := R) (N := N) hR
      (C := (45 : ℝ)) Cstar_le_45
  have h2 : ((2 : ℝ) * (45 : ℝ)) = (90 : ℝ) := by norm_num
  simpa [h2] using h

/-- ℝ-valued Euler tail bound (your original goal statement).

TODO: derive by `toReal` once we have finiteness lemmas (`≠ ⊤`) in place.
-/
theorem euler_tail_bound_tsum (R N : ℕ) (hR : 1 ≤ R) :
  (∑' r : ℕ,
      if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
        (1 / (Nat.totient r : ℝ) ^ 2)
      else 0)
  ≤ (90 : ℝ) / R := by
  classical

  -- Start from the ENNReal version
  have hENN :
      (∑' r : ℕ,
          if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
            ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
          else 0)
        ≤ ENNReal.ofReal ((90 : ℝ) / R) := by
    exact euler_tail_bound_tsum_ENNReal R N hR

  -- Package the summand as an ENNReal function
  let fE : ℕ → ENNReal := fun r =>
    if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
      ENNReal.ofReal (1 / (Nat.totient r : ℝ) ^ 2)
    else 0

  have hENN' : (∑' r : ℕ, fE r) ≤ ENNReal.ofReal ((90 : ℝ) / R) := by
    simpa [fE] using hENN

  -- Needed for `ENNReal.tsum_toReal_eq`
  have hfE : ∀ r : ℕ, fE r ≠ ⊤ := by
    intro r
    by_cases h : (R < r ∧ Squarefree r ∧ Nat.Coprime r N)
    · simp only [fE, if_pos h]
      exact ENNReal.ofReal_ne_top
    · simp [fE, h]

  -- Take `toReal` of both sides, and rewrite `toReal (tsum ...)` as `tsum (toReal ...)`
  have htoReal :
      (∑' r : ℕ, (fE r).toReal) ≤ (90 : ℝ) / R := by
    have hmono :
        (∑' r : ℕ, fE r).toReal ≤ (ENNReal.ofReal ((90 : ℝ) / R)).toReal :=
      ENNReal.toReal_mono (by simp) hENN'

    have htsum :
        (∑' r : ℕ, fE r).toReal = ∑' r : ℕ, (fE r).toReal := by
      simpa using (ENNReal.tsum_toReal_eq (f := fE) hfE)

    have hRpos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mp hR)

    have hRnonneg : 0 ≤ (90 : ℝ) / (R : ℝ) := by
      exact div_nonneg (by norm_num) (le_of_lt hRpos)

    have hRHS : (ENNReal.ofReal ((90 : ℝ) / R)).toReal = (90 : ℝ) / R := by
      simp [ENNReal.toReal_ofReal, hRnonneg]

    -- finish this subgoal
    simpa [htsum, hRHS] using hmono

  -- Identify `(fE r).toReal` with the original real summand, pointwise
  have hterm :
      (fun r : ℕ => (fE r).toReal) =
        fun r : ℕ =>
          if R < r ∧ Squarefree r ∧ Nat.Coprime r N then
            (1 / (Nat.totient r : ℝ) ^ 2)
          else 0 := by
    funext r
    by_cases h : (R < r ∧ Squarefree r ∧ Nat.Coprime r N)
    · simp only [fE, if_pos h]
      rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (Nat.totient r : ℝ) ^ 2)]
    · simp [fE, h]

  simpa [hterm] using htoReal

end
end Goldbach.AO_OffDiag
