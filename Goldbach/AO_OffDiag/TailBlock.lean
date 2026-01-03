import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Squarefree

/-
  Tail block: Ramanujan truncation, block majorant, and the abstract model
  assumptions needed to derive a numeric tail bound on a canonical window.

  HONEST DESIGN (Option B):
  * We do NOT use `Goldbach.AO_Core.sigma` (currently a placeholder `0`).
  * The "true" singular series `sigma` is supplied by a `Model`.
  * The truncation `sigma_trunc_Q0` is defined concretely here.
  * Downstream files (e.g. `SigmaTailReindex`, `SigmaTailEuler`) should build
    an actual `Model` instance by proving the required fields.

  REFACTOR NOTE (2025-12):
  The `Model` is now purely structural:
    • it carries a tail constant `K_tail`,
    • it carries a window bound constant `F_ub`,
    • the final numeric budget is proved separately.
-/

namespace Goldbach
namespace AO_OffDiag
namespace TailBlock

open Real Goldbach.Windows
open scoped BigOperators

noncomputable section

/-- Truncation height for the off-diagonal singular series. -/
@[simp] def Q0 : ℕ := 30000

/-- Möbius arithmetic function. Use `(μ q : ℤ)` for its value at `q`. -/
local notation "μ" => (ArithmeticFunction.moebius : ArithmeticFunction ℤ)

/-- Möbius–squared as a real number (0 or 1): indicator of squarefreeness. -/
noncomputable def muSq (q : ℕ) : ℝ :=
  if Squarefree q then (1 : ℝ) else 0

/-- Ramanujan sum in closed form (integer-valued):
`c_q(N) = μ(q/d) * φ(d)` with `d = gcd(q,N)`. -/
def ramanujanZ (q N : ℕ) : ℤ :=
  let d := Nat.gcd q N
  (μ (q / d) : ℤ) * Int.ofNat (Nat.totient d)

/-- Real-valued Ramanujan sum. -/
noncomputable def ramanujanR (q N : ℕ) : ℝ := (ramanujanZ q N : ℤ)

/-- Truncated singular series at height `Q0`. -/
noncomputable def sigma_trunc_Q0 (N : ℕ) : ℝ :=
  (Finset.Icc (1 : ℕ) Q0).sum (fun q =>
    (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N))

/-- Canonical block majorant used in the tail bound (purely arithmetic). -/
noncomputable def F_block (N : ℕ) : ℝ :=
  ((Nat.factorization N).support).prod (fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1)))

/-- Multiplicative form of `F_block`, recorded separately for clarity. -/
noncomputable def F_block_prod (N : ℕ) : ℝ := F_block N

/-!
### Structural lemmas for `F_block`

These are “pure bookkeeping” facts about the Euler-factor expression used in the off-diagonal
tail bound. They are intended to support later proofs of window-uniform bounds.
-/

private lemma inv_totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 / (Nat.totient (∏ p ∈ s, p) : ℝ)) = ∏ p ∈ s, (1 / ((p - 1 : ℕ) : ℝ)) := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _hs
    simp
  · intro p s hp_not_mem ih hs
    have hp_prime : p.Prime := hs p (by simp [hp_not_mem])
    have hs_prime : ∀ q ∈ s, q.Prime := by
      intro q hq
      exact hs q (by simp [hq, hp_not_mem])

    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      -- `p` is coprime to every distinct prime in `s`, hence to their product.
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
          simp [one_div, htot', mul_assoc, mul_left_comm, mul_comm]
      _ = (1 / ((p - 1 : ℕ) : ℝ)) * ∏ q ∈ s, (1 / ((q - 1 : ℕ) : ℝ)) := by
          simp [hphi_p, ih hs_prime]
      _ = ∏ q ∈ insert p s, (1 / ((q - 1 : ℕ) : ℝ)) := by
          simp [Finset.prod_insert, hp_not_mem, mul_assoc, mul_left_comm, mul_comm]

lemma F_block_eq_sum_squarefree_divisors {N : ℕ} (hN : N ≠ 0) :
    F_block N =
      ∑ d ∈ N.divisors with Squarefree d, (1 / (Nat.totient d : ℝ)) := by
  classical
  set P : Finset ℕ := (Nat.factorization N).support

  -- The primes dividing `N` as a finset can be seen both via `Nat.factorization` and via
  -- `UniqueFactorizationMonoid.normalizedFactors`.
  have hfac : (UniqueFactorizationMonoid.normalizedFactors N).toFinset = P := by
    calc
      (UniqueFactorizationMonoid.normalizedFactors N).toFinset
          = N.primeFactors := by
              -- `normalizedFactors N = primeFactorsList N` (as a multiset), and `primeFactors` is
              -- definitionally `primeFactorsList.toFinset`.
              have h1 :
                  (UniqueFactorizationMonoid.normalizedFactors N).toFinset =
                    ((N.primeFactorsList : List ℕ) : Multiset ℕ).toFinset :=
                congrArg Multiset.toFinset (Nat.factors_eq N)
              have h2 : ((N.primeFactorsList : List ℕ) : Multiset ℕ).toFinset = N.primeFactorsList.toFinset := by
                rfl
              have h3 : N.primeFactorsList.toFinset = N.primeFactors := by
                rfl
              exact h1.trans (h2.trans h3)
      _ = (Nat.factorization N).support := by
              simpa using (Nat.support_factorization N).symm
      _ = P := by rfl

  -- Rewrite the divisor sum as a powerset sum over the prime factors.
  have hsum :
      (∑ d ∈ N.divisors with Squarefree d, (1 / (Nat.totient d : ℝ))) =
        ∑ s ∈ P.powerset, (1 / (Nat.totient (s.val.prod : ℕ) : ℝ)) := by
    simpa [hfac, P] using
      (Nat.sum_divisors_filter_squarefree (n := N) hN (f := fun d => (1 / (Nat.totient d : ℝ))))

  -- Primehood on `P`.
  have hP_prime : ∀ p ∈ P, p.Prime := by
    intro p hp
    have : p.Prime ∧ p ∣ N ∧ N ≠ 0 := by
      -- `P` is (definitionally) `N.primeFactors`.
      simpa [P, Nat.support_factorization, Nat.mem_primeFactors] using hp
    exact this.1

  -- Expand `F_block` as a sum over subsets of the prime factors (powerset expansion),
  -- then rewrite the subset-product as `1/φ(product)` using multiplicativity of `φ` on squarefree products.
  have hF :
      F_block N =
        ∑ s ∈ P.powerset, (1 / (Nat.totient (s.val.prod : ℕ) : ℝ)) := by
    -- `prod_one_add` expansion (kept in `Finset.prod` form to avoid binder-notation hassles).
    have hprod :
        P.prod (fun p : ℕ => (1 : ℝ) + (1 / ((p : ℝ) - 1)))
          =
        ∑ s ∈ P.powerset, s.prod (fun p : ℕ => (1 / ((p : ℝ) - 1))) := by
      simpa using
        (Finset.prod_one_add (s := P) (f := fun p : ℕ => (1 / ((p : ℝ) - 1))))

    -- rewrite each subset product
    have hterm :
        ∀ s : Finset ℕ, s ∈ P.powerset →
          (s.prod (fun p : ℕ => (1 / ((p : ℝ) - 1)))) =
            (1 / (Nat.totient (s.val.prod : ℕ) : ℝ)) := by
      intro s hs
      -- work in the binder-product form so we can reuse `inv_totient_prod_primes`
      change (∏ p ∈ s, (1 / ((p : ℝ) - 1))) = (1 / (Nat.totient (s.val.prod : ℕ) : ℝ))
      have hs_prime : ∀ p ∈ s, p.Prime := by
        intro p hp
        exact hP_prime p ((Finset.mem_powerset.mp hs) hp)
      have hcast : ∀ p : ℕ, p ∈ s → (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
        intro p hp
        have hp1 : 1 ≤ p := Nat.one_le_of_lt (hs_prime p hp).one_lt
        simpa [Nat.cast_sub hp1, Nat.cast_one] using (rfl : ((p : ℝ) - 1) = (p : ℝ) - 1)

      have hφ :
          (1 / (Nat.totient (∏ p ∈ s, p) : ℝ)) = ∏ p ∈ s, (1 / ((p - 1 : ℕ) : ℝ)) := by
        simpa using (inv_totient_prod_primes (s := s) hs_prime)
      have hφ' :
          (1 / (Nat.totient (∏ p ∈ s, p) : ℝ)) = ∏ p ∈ s, (1 / ((p : ℝ) - 1)) := by
        refine hφ.trans ?_
        refine Finset.prod_congr rfl ?_
        intro p hp
        have : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := hcast p hp
        simpa [this]

      have hprod_nat : (∏ p ∈ s, p) = (s.val.prod : ℕ) := by
        -- unfold the finset product and simplify `Multiset.map id`
        change (s.val.map (fun p : ℕ => p)).prod = s.val.prod
        simpa using congrArg Multiset.prod (by simpa using (Multiset.map_id s.val))

      -- rewrite the totient argument and flip the equality to match the goal
      have hφ'' := hφ'
      rw [hprod_nat] at hφ''
      exact hφ''.symm

    -- Put it together
    calc
      F_block N
          = P.prod (fun p : ℕ => (1 : ℝ) + (1 / ((p : ℝ) - 1))) := by
              rfl
      _ = ∑ s ∈ P.powerset, s.prod (fun p : ℕ => (1 / ((p : ℝ) - 1))) := hprod
      _ = ∑ s ∈ P.powerset, (1 / (Nat.totient (s.val.prod : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            exact hterm s hs

  -- Combine the two characterizations.
  exact hF.trans hsum.symm

/--
Tail-block facts packaged as a `Model`.

Analytic inputs live as *fields* to be proved in downstream modules.
-/
structure Model where
  /-- The true singular series. -/
  sigma : ℕ → ℝ
  /-- Majorant factor in the tail bound (often `F_block`). -/
  F : ℕ → ℝ
  /-- Tail constant: analytic estimate produces `(K_tail/Q0) * F(N)`. -/
  K_tail : ℝ
  K_tail_nonneg : 0 ≤ K_tail
  /-- A window bound constant for `F`, used only to derive a concrete numeric bound downstream. -/
  F_ub : ℝ
  F_ub_nonneg : 0 ≤ F_ub
  /-- Uniform bound for `F` on the canonical window. -/
  F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      F N ≤ F_ub
  /-- Tail comparison between `sigma` and the truncation. -/
  sigma_tail_block :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |sigma N - sigma_trunc_Q0 N| ≤ (K_tail : ℝ) / (Q0 : ℝ) * F N

/-- Derived (still-structural) tail bound using the model's `F_ub`. -/
theorem tail_bound_on_window_structural
  (M : Model)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |M.sigma N - sigma_trunc_Q0 N| ≤ (M.K_tail : ℝ) / (Q0 : ℝ) * (M.F_ub : ℝ) := by
  have h1 := M.sigma_tail_block (X:=X) (N:=N) hX hN
  have hF := M.F_bound_on_window (X:=X) (N:=N) hX hN
  have hQpos : (0 : ℝ) < (Q0 : ℝ) := by norm_num [Q0]
  have hcoef_nonneg : 0 ≤ (M.K_tail : ℝ) / (Q0 : ℝ) :=
    div_nonneg M.K_tail_nonneg (le_of_lt hQpos)
  have h2 :
      (M.K_tail : ℝ) / (Q0 : ℝ) * M.F N
        ≤ (M.K_tail : ℝ) / (Q0 : ℝ) * (M.F_ub : ℝ) := by
    exact mul_le_mul_of_nonneg_left hF hcoef_nonneg
  exact h1.trans h2

/--
Numeric consumer lemma: if you have proved the arithmetic squeeze
`(K_tail/Q0) * F_ub ≤ eps`, then you get the uniform tail bound `≤ eps`.
-/
theorem tail_bound_on_window
  (M : Model)
  (eps : ℝ)
  (hbudget : (M.K_tail : ℝ) / (Q0 : ℝ) * (M.F_ub : ℝ) ≤ eps)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |M.sigma N - sigma_trunc_Q0 N| ≤ eps := by
  exact (tail_bound_on_window_structural (M := M) hX hN).trans hbudget

/-
  === Pure math lemmas (non-analytic) ===
-/

/-- Squarefree support of μ² (for our `muSq`). -/
lemma muSq_eq_zero_iff_not_squarefree (q : ℕ) :
    muSq q = 0 ↔ ¬ Squarefree q := by
  by_cases h : Squarefree q <;> simp [muSq, h]

/-- Ramanujan identity (closed form): definitional, no squarefree needed. -/
lemma ramanujan_sqfree (q N : ℕ) (hq : Squarefree q) :
    ramanujanZ q N =
      (μ (q / Nat.gcd q N) : ℤ) * Int.ofNat (Nat.totient (Nat.gcd q N)) := by
  simp [ramanujanZ]

/-- If `q` is squarefree and `d ∣ q`, then `q / d` is squarefree. -/
lemma squarefree_div_of_dvd {q d : ℕ} (hq : Squarefree q) (hd : d ∣ q) :
    Squarefree (q / d) := by
  intro x hx
  have hx' : x * x * d ∣ q := by
    rcases hx with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      q = d * (q / d) := by
            simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hd).symm
      _ = d * (x * x * k) := by
            simpa [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = x * x * d * k := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hx2 : x * x ∣ q := by
    exact dvd_trans (dvd_mul_right (x * x) d) hx'
  exact hq x hx2

/-- If `q` is squarefree, then `gcd(q,N)` is coprime to `q / gcd(q,N)`. -/
lemma coprime_gcd_div_of_squarefree (q N : ℕ) (hq : Squarefree q) :
    (Nat.gcd q N).Coprime (q / Nat.gcd q N) := by
  classical
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne

  set d : ℕ := Nat.gcd q N with hd
  set r : ℕ := q / d with hr
  set g : ℕ := Nat.gcd d r with hg

  have hg_ne_one : g ≠ 1 := by
    simpa [d, r, g, hd, hr, hg] using hne

  have hdq : d ∣ q := by
    simpa [hd] using Nat.gcd_dvd_left q N

  have hqdr : q = d * r := by
    simpa [r, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.mul_div_cancel' hdq).symm

  have hg_d : g ∣ d := by simpa [hg] using Nat.gcd_dvd_left d r
  have hg_r : g ∣ r := by simpa [hg] using Nat.gcd_dvd_right d r

  have hg2_dvd_q : g * g ∣ q := by
    have : g * g ∣ d * r := Nat.mul_dvd_mul hg_d hg_r
    simpa [hqdr] using this

  have hunit_g : IsUnit g := hq g hg2_dvd_q

  have hg_eq_one : g = 1 := by
    simpa [Nat.isUnit_iff] using hunit_g

  exact hg_ne_one hg_eq_one

/-- Termwise bound after splitting q = d*r (squarefree q, q ≠ 0). -/
lemma term_bound_after_split (q N : ℕ) (hq : Squarefree q) (hq0 : q ≠ 0) :
    let d := Nat.gcd q N
    let r := q / d
    |muSq q * (1 / (Nat.totient q : ℝ) ^ 2) * ramanujanR q N|
      = 1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
  classical
  intro d r

  have hd : d ∣ q := Nat.gcd_dvd_left q N
  have hqr_sq : Squarefree (q / d) :=
    squarefree_div_of_dvd (q := q) (d := d) hq hd

  have hmuSq : muSq q = (1 : ℝ) := by
    simp [muSq, hq]

  have hmu_sq : (μ (q / d) : ℤ) ^ 2 = 1 := by
    simpa [hqr_sq] using (ArithmeticFunction.moebius_sq (n := (q / d)))

  have hmu_pm : (μ (q / d) : ℤ) = 1 ∨ (μ (q / d) : ℤ) = -1 := by
    have h0 : ((μ (q / d) : ℤ) - 1) * ((μ (q / d) : ℤ) + 1) = 0 := by
      nlinarith [hmu_sq]
    rcases mul_eq_zero.mp h0 with h | h
    · left; linarith
    · right; linarith

  have hmu_abs : |((μ (q / d) : ℤ) : ℝ)| = 1 := by
    rcases hmu_pm with h | h
    · simp [h]
    · simp [h]

  have hRamAbs : |ramanujanR q N| = (Nat.totient d : ℝ) := by
    simp [ramanujanR, ramanujanZ, d, hmu_abs, abs_mul]

  have hphi : (Nat.totient q : ℝ) = (Nat.totient d : ℝ) * (Nat.totient r : ℝ) := by
    have hqdr : q = d * r := by
      simpa [r, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.mul_div_cancel' hd).symm
    have hcop : d.Coprime r := by
      simpa [d, r] using (coprime_gcd_div_of_squarefree q N hq)
    have ht : Nat.totient (d * r) = Nat.totient d * Nat.totient r := by
      simpa using (Nat.totient_mul (m := d) (n := r) hcop)
    simpa [hqdr, ht, Nat.cast_mul]

  by_cases hdt : (Nat.totient d : ℝ) = 0
  · simp [hmuSq, hRamAbs, hphi, hdt]
  · have hdt' : (Nat.totient d : ℝ) ≠ 0 := hdt
    simp [hmuSq, hRamAbs, hphi, pow_two,
      mul_assoc, mul_left_comm, mul_comm, hdt', mul_inv_cancel, inv_mul_cancel]

/-- The finite product appearing in the block-majorant numeric check (as a rational). -/
def FprodQ : ℚ :=
  ((1 : ℚ) + 1 / ((2 : ℚ) - 1)) *
  ((1 : ℚ) + 1 / ((3 : ℚ) - 1)) *
  ((1 : ℚ) + 1 / ((5 : ℚ) - 1)) *
  ((1 : ℚ) + 1 / ((7 : ℚ) - 1)) *
  ((1 : ℚ) + 1 / ((11 : ℚ) - 1)) *
  ((1 : ℚ) + 1 / ((13 : ℚ) - 1)) *
  ((1 : ℚ) + 1 / ((17 : ℚ) - 1))

lemma numeric_eval_F_block :
    ((FprodQ : ℚ) : ℝ) < (330 : ℝ) := by
  have hQ : FprodQ < (330 : ℚ) := by
    unfold FprodQ
    native_decide
  exact_mod_cast hQ

end
end TailBlock
end AO_OffDiag
end Goldbach
