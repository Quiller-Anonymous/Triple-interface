import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Core
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Squarefree

/-
  Tail block: Ramanujan truncation, block majorant, and the abstract model
  assumptions needed to derive the 3e-4 tail bound on the canonical window.
-/

namespace Goldbach
namespace AO_OffDiag
namespace TailBlock

open Real Goldbach.Windows

noncomputable section

/-- Truncation height for the off-diagonal singular series. -/
@[simp] def Q0 : ℕ := 30000

/-- Alias the singular series. -/
abbrev sigma : ℕ → ℝ := AO_Core.sigma

/-- Möbius–squared as a real number (0 or 1). -/
noncomputable def muSq (q : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℤ) ^ 2 : ℤ) : ℝ)

/-- Ramanujan sum via the divisor identity: `c_q(N) = ∑_{d | gcd(q,N)} μ(q/d) * d` (as ℤ). -/
noncomputable def ramanujanZ (q N : ℕ) : ℤ :=
  ((Nat.gcd q N).divisors).sum (fun d => (ArithmeticFunction.moebius (q / d)) * (d : ℤ))

/-- Real-valued Ramanujan sum. -/
noncomputable def ramanujanR (q N : ℕ) : ℝ := (ramanujanZ q N : ℤ)

/-- Truncated singular series at height `Q0`: `σ_{≤Q0}(N) = ∑_{q≤Q0} μ(q)^2/φ(q)^2 * c_q(N)`. -/
noncomputable def sigma_trunc_Q0 (N : ℕ) : ℝ :=
  (Finset.Icc (1 : ℕ) Q0).sum (fun q =>
    (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N))

/-- Canonical block majorant:
    we take the Euler product over primes dividing `N` with local factor `(1 + 1/(p-1))`.
    This matches the numeric window bound `≤ 7.9`. -/
noncomputable def F_block (N : ℕ) : ℝ :=
  ((Nat.factorization N).support).prod (fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1)))

/-- Multiplicative form of `F_block`, recorded separately for clarity. -/
noncomputable def F_block_prod (N : ℕ) : ℝ := F_block N

/-- **Analytic input**: block tail bound on the canonical window (to be supplied). -/
lemma sigma_tail_block_axiom
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |sigma N - sigma_trunc_Q0 N| ≤ (1.02 : ℝ) / (Q0 : ℝ) * F_block N := by
  admit

/-- **Analytic input**: uniform bound for `F_block` on the canonical window (to be supplied). -/
lemma F_block_bound_on_window
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  F_block N ≤ (7.9 : ℝ) := by
  admit

/-- Tail-block facts from the paper, packaged so the final 3e-4 lemma is derivable. -/
structure Model where
  /-- Auxiliary factor `F(N)` in the block majorization. -/
  F : ℕ → ℝ
  /-- Uniform window bound for `F`. -/
  F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      F N ≤ (7.9 : ℝ)
  /-- Block majorization on the canonical window. -/
  sigma_tail_block :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |sigma N - sigma_trunc_Q0 N| ≤ (1.02 : ℝ) / (Q0 : ℝ) * F N

/-- Pure numeric squeeze: `(1.02/30000) * 7.9 ≤ 3e-4`. -/
lemma coef_times_ub_le_3e4 :
  (1.02 : ℝ) / (Q0 : ℝ) * (7.9 : ℝ) ≤ (3e-4 : ℝ) := by
  norm_num [Q0]

/-- Tail bound on the canonical window, derived from the `Model` inputs. -/
theorem tail_bound_on_window
  (M : Model)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |sigma N - sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  have h1 := M.sigma_tail_block (X:=X) (N:=N) hX hN
  have hF := M.F_bound_on_window (X:=X) (N:=N) hX hN
  have hcoef_nonneg : 0 ≤ (1.02 : ℝ) / (Q0 : ℝ) := by
    have : (0 : ℝ) < (Q0 : ℝ) := by norm_num [Q0]
    have hpos : 0 < (1.02 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt hpos) (le_of_lt this)
  have h2 : (1.02 : ℝ) / (Q0 : ℝ) * M.F N ≤ (1.02 : ℝ) / (Q0 : ℝ) * (7.9 : ℝ) :=
    mul_le_mul_of_nonneg_left hF hcoef_nonneg
  exact h1.trans (h2.trans coef_times_ub_le_3e4)

/-- Canonical model instance using the analytic inputs above. -/
noncomputable def canonicalModel : Model where
  F := F_block
  F_bound_on_window := by intro X N hX hN; exact F_block_bound_on_window (X:=X) (N:=N) hX hN
  sigma_tail_block := by intro X N hX hN; exact sigma_tail_block_axiom (X:=X) (N:=N) hX hN

end

end TailBlock
end AO_OffDiag
end Goldbach

namespace Goldbach
namespace AO_OffDiag
namespace TailBlock

open scoped BigOperators
open Real

/-- Squarefree support of μ² (as `muSq`). -/
lemma muSq_eq_zero_iff_not_squarefree (q : ℕ) :
    muSq q = 0 ↔ ¬ Nat.Squarefree q := by
  -- `ArithmeticFunction.moebius q = 0` iff `q` is not squarefree
  -- and `muSq q` is the square of that integer cast to `ℝ`.
  simp [muSq, Nat.squarefree_iff_squarefree]  -- may need small adjustments depending on simp lemmas present

/-
For Ramanujan sums: you defined `ramanujanZ` using the divisor formula already:
  c_q(N) = ∑_{d | gcd(q,N)} μ(q/d) * d.
So we can reason from that formula directly, rather than introducing roots of unity.
The “squarefree closed form” you want is:
  if q squarefree and g = gcd(q,N), then c_q(N) = μ(q/g) * φ(g).
In Mathlib this is available as a lemma about Ramanujan sums; if not,
we can prove it by multiplicativity and prime modulus.
Below is written as a stub-proof pattern; you may need to swap in the exact Mathlib lemma name.
-/

/-- Ramanujan identity for squarefree moduli (as an equality in `ℤ`, then cast to `ℝ`). -/
lemma ramanujan_sqfree (q N : ℕ) (hq : Nat.Squarefree q) :
    ramanujanR q N =
      ((ArithmeticFunction.moebius (q / Nat.gcd q N) : ℤ) * (Nat.totient (Nat.gcd q N) : ℤ) : ℤ) := by
  -- Recommended: replace `ramanujanZ/ramanujanR` with Mathlib's `ramanujanSum` API if available,
  -- then this becomes a one-liner via a library lemma.
  -- For now, keep as an axiom-shaped lemma until wired to the library lemma name.
  -- (I’m avoiding a fake proof here.)
  admit

/-- Absolute value of Ramanujan sum on squarefree moduli. -/
lemma abs_ramanujan_sqfree (q N : ℕ) (hq : Nat.Squarefree q) :
    |ramanujanR q N| = (Nat.totient (Nat.gcd q N) : ℝ) := by
  -- Using `ramanujan_sqfree` and `|μ(…)| = 1` for squarefree arguments.
  admit

/-- GCD decomposition for squarefree `q`: `q = d*r` with `d = gcd(q,N)` and `(r,N)=1`, etc. -/
lemma squarefree_gcd_split (q N : ℕ) (hq : Nat.Squarefree q) :
    let d := Nat.gcd q N
    let r := q / d
    Nat.Squarefree d ∧ Nat.Squarefree r ∧ Nat.Coprime d r ∧
      Nat.totient q = Nat.totient d * Nat.totient r := by
  classical
  intro d r
  -- This is essentially Lemma 3 from your math writeup.
  -- Key facts in Nat:
  -- * gcd_dvd_left/right
  -- * squarefree_of_dvd (a divisor of squarefree is squarefree)
  -- * coprime_div_gcd_div_gcd (or equivalent)
  -- * totient_mul for coprime factors
  admit

/-- Termwise bound after splitting `q = d*r` for squarefree `q`. -/
lemma term_bound_after_split (q N : ℕ) (hq : Nat.Squarefree q) :
    let d := Nat.gcd q N
    let r := q / d
    |muSq q * (1 / (Nat.totient q : ℝ) ^ 2) * ramanujanR q N|
      = (1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2)) := by
  classical
  intro d r
  -- Uses:
  -- * `muSq q = 1` for squarefree q
  -- * `abs_ramanujan_sqfree` gives `|ramanujanR q N| = φ(d)`
  -- * `totient q = totient d * totient r`
  admit

/-
Correct tail formulation: use `tsum` over `r : ℕ` with predicate `R < r`.
We model “sum over squarefree and coprime” by multiplying by an indicator.
-/

/-- Indicator weight for the Euler tail. -/
noncomputable def tailWeight (N : ℕ) (r : ℕ) : ℝ :=
  if Nat.Squarefree r ∧ Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0

/-- Euler-type tail bound (correctly as an infinite tail `tsum`). -/
lemma euler_tail_bound (R N : ℕ) (hR : 3 ≤ R) :
    (∑' r : ℕ, if R < r then tailWeight N r else 0)
      ≤ (45 : ℝ) / R := by
  -- This should be supplied from an explicit inequality of Rosser–Schoenfeld type,
  -- as in your Lemma 5. It's genuinely analytic, so keep as an axiom/`admit` for now.
  admit

/-- Finite product evaluation for the extremal prime set: a simple numeric check. -/
lemma numeric_eval_F_block :
    ((2 : ℝ) + 1 / (2 - 1)) * ((3 : ℝ) + 1 / (3 - 1)) *
      ((5 : ℝ) + 1 / (5 - 1)) * ((7 : ℝ) + 1 / (7 - 1)) *
      ((11 : ℝ) + 1 / (11 - 1)) * ((13 : ℝ) + 1 / (13 - 1)) *
      ((17 : ℝ) + 1 / (17 - 1)) < 330 := by
  norm_num

end TailBlock
end AO_OffDiag
end Goldbach
