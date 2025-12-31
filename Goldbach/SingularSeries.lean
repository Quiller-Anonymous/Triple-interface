/-
  Lean 4.26.0-rc2
  Exact Hardy–Littlewood singular series σ for Goldbach (no admits/sorries/axioms).
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.Divisors
import Mathlib

open scoped BigOperators

namespace Goldbach
namespace Singular

/-- The Euler-product constant `C2 = ∏_{p≥3} (1 - 1/(p-1)^2)`.
    We treat it as an abstract positive real carried around as data. -/
structure C2Const where
  C2 : ℝ
  pos : 0 < C2

variable {C : C2Const}

/-- Finite set of **odd primes** dividing `n`. -/
def oddPrimeSupport (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun p => Nat.Prime p ∧ p ≠ 2)

/-- Local factor `(p-1)/(p-2)` for odd primes `p`. -/
noncomputable def oddFactor (p : ℕ) : ℝ := (p - 1 : ℝ) / (p - 2 : ℝ)

/-- The Goldbach singular series σ(n).

    If `n` is odd: `σ(n) = 0`.

    If `n` is even:
    ```
    σ(n) = 2 * C2 * ∏_{p | n, p odd prime} (p-1)/(p-2).
    ```
-/
noncomputable def sigma (C : C2Const) (n : ℕ) : ℝ :=
  if h : Even n then
    (2 : ℝ) * C.C2 * ∏ p ∈ oddPrimeSupport n, oddFactor p
  else
    0

@[simp] lemma sigma_odd {n : ℕ} (hodd : Odd n) : sigma C n = 0 := by
  simp [sigma, Nat.not_even_iff_odd.mpr hodd]

lemma sigma_even_expand {n : ℕ} (he : Even n) :
    sigma C n = (2 : ℝ) * C.C2 * ∏ p ∈ oddPrimeSupport n, oddFactor p := by
  simp [sigma, he]

/-- If `p` is an odd prime then `(p-1)/(p-2) ≥ 1`. -/
lemma oddFactor_ge_one_of_prime_ne_two
    {p : ℕ} (hp : Nat.Prime p) (hne2 : p ≠ 2) : (1 : ℝ) ≤ oddFactor p := by
  -- From `p` prime and `p ≠ 2` we get `2 < p`, hence `1 ≤ p - 2`.
  have h2le : 2 ≤ p := hp.two_le
  have h2lt : 2 < p := lt_of_le_of_ne h2le (by symm; exact hne2)
  have h3le : 3 ≤ p := Nat.succ_le_of_lt h2lt
  -- Turn `1 ≤ p - 2` via `Nat.le_sub_iff_add_le`.
  have h1le : 1 ≤ p - 2 := (Nat.le_sub_iff_add_le h2le).2 (by simpa using h3le)
  have hpos_nat : 0 < p - 2 := (Nat.succ_le_iff).1 h1le
  have hpos : (0 : ℝ) < (p - 2 : ℝ) := by exact_mod_cast hpos_nat
  -- `1 ≤ (p-1)/(p-2)` ↔ `(p-2) ≤ (p-1)` since denominator is positive.
  have num_ge : ((p - 2 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    have : (p : ℝ) - 2 ≤ (p : ℝ) - 1 := by linarith
    have h1le' : 1 ≤ p := le_trans (by decide : 1 ≤ 2) h2le
    simpa [Nat.cast_sub h2le, Nat.cast_sub h1le'] using this
  have : (1 : ℝ) ≤ (p - 1 : ℝ) / (p - 2 : ℝ) :=
    (one_le_div hpos).mpr (by linarith : (p : ℝ) - 2 ≤ (p : ℝ) - 1)
  simpa [oddFactor] using this

/-- No odd prime divides `2^k`. (Key for understanding σ at powers of two.) -/
lemma no_odd_prime_divides_two_pow
    {p k : ℕ} (hp : Nat.Prime p) (hne2 : p ≠ 2) (hdiv : p ∣ 2^k) : False := by
  -- A prime dividing `2^k` divides `2`.
  have hdiv2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
  have hcases : p = 1 ∨ p = 2 := (Nat.dvd_prime (Nat.prime_two)).1 hdiv2
  cases hcases with
  | inl h1 =>
      exact (hp.ne_one h1).elim
  | inr h2 =>
      exact hne2 h2

/-- For any `k ≥ 1`, the odd-prime support of `2^k` is empty. -/
lemma oddPrimeSupport_two_pow_succ (k : ℕ) :
    oddPrimeSupport (2^(k+1)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp_mem
  rcases Finset.mem_filter.mp hp_mem with ⟨hp_div, ⟨hp_prime, hp_ne2⟩⟩
  have hpdvd : p ∣ 2^(k+1) := Nat.dvd_of_mem_divisors hp_div
  exact no_odd_prime_divides_two_pow (p:=p) hp_prime hp_ne2 hpdvd

/-- σ at `2^(k+1)`: the finite product is `1`, hence `σ(2^(k+1)) = 2*C2`. -/
lemma sigma_two_pow_succ (k : ℕ) :
    sigma C (2^(k+1)) = (2 : ℝ) * C.C2 := by
  have he : Even (2^(k+1)) := by
    simpa [pow_succ, Nat.mul_comm] using
      (Nat.even_mul.mpr ⟨by decide, Nat.even_pow.mpr (by decide)⟩)
  have suppEmpty : oddPrimeSupport (2^(k+1)) = ∅ := oddPrimeSupport_two_pow_succ (k)
  simp [sigma_even_expand (C:=C) he, suppEmpty]

end Singular
end Goldbach
