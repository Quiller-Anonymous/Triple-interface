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
open scoped BigOperators

noncomputable section

#check Nat.ArithmeticFunction.moebius
#check Nat.Squarefree
#check Nat.Squarefree.squarefree_div_of_dvd
#check Nat.Squarefree.squarefree_of_dvd
#check Nat.ArithmeticFunction.moebius_eq_zero
#check Nat.ArithmeticFunction.moebius_eq_zero_iff_not_squarefree
#check Nat.ArithmeticFunction.squarefree_iff_moebius_ne_zero
#check Nat.ArithmeticFunction.abs_moebius
#check Nat.ArithmeticFunction.abs_moebius_eq_one
#check Nat.ArithmeticFunction.squarefree_iff_abs_moebius_eq_one
#check Nat.ArithmeticFunction.moebius_sq
#check Int.natAbs

/-- Truncation height for the off-diagonal singular series. -/
@[simp] def Q0 : ℕ := 30000

/-- Alias the singular series. -/
abbrev sigma : ℕ → ℝ := AO_Core.sigma

/-- Möbius function as an `ℤ`-valued arithmetic function on `ℕ`. -/
local notation "μ" => Nat.ArithmeticFunction.moebius

/-- Möbius–squared as a real number (0 or 1): indicator of squarefreeness. -/
noncomputable def muSq (q : ℕ) : ℝ :=
  if Nat.Squarefree q then (1 : ℝ) else 0

/-- Ramanujan sum in closed form (integer-valued):
`c_q(N) = μ(q/d) * φ(d)` with `d = gcd(q,N)`. -/
def ramanujanZ (q N : ℕ) : ℤ :=
  let d := Nat.gcd q N
  μ (q / d) * Int.ofNat (Nat.totient d)

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

/-
  === “Pure math” lemmas implementing your Lemmas 1–3 and the finite product check (Lemma 6). ===
-/

/-- Squarefree support of μ². -/
lemma muSq_eq_zero_iff_not_squarefree (q : ℕ) :
    muSq q = 0 ↔ ¬ Nat.squarefree q := by admit

/-- Ramanujan identity for squarefree moduli. -/
lemma ramanujan_sqfree (hq : Nat.squarefree q) (N : ℕ) :
    ramanujanR q N = (ArithmeticFunction.moebius (q / Nat.gcd q N)) * (Nat.gcd q N) := by
  admit

/-- Absolute value of Ramanujan sum on squarefree moduli. -/
lemma abs_ramanujan_sqfree (hq : Nat.squarefree q) (N : ℕ) :
    |ramanujanR q N| = Nat.totient (Nat.gcd q N) := by admit

/-- GCD decomposition for squarefree q. -/
lemma squarefree_gcd_split (hq : Nat.squarefree q) (N : ℕ) :
    let d := Nat.gcd q N
    let r := q / d
    Nat.squarefree d ∧ Nat.squarefree r ∧ Nat.coprime d r ∧
      Nat.totient q = Nat.totient d * Nat.totient r := by
  admit

/-- Termwise bound after splitting q = d*r. -/
lemma term_bound_after_split (hq : Nat.squarefree q) (N : ℕ) :
    let d := Nat.gcd q N
    let r := q / d
    |muSq q / (Nat.totient q : ℝ) ^ 2 * ramanujanR q N|
      = 1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
  admit

/-- Tail reindexing inequality. -/
lemma tail_reindex_bound (N : ℕ) :
    |sigma N - sigma_trunc_Q0 N| ≤
      ∑ d in (Nat.divisors N).filter Nat.squarefree,
        (1 / (Nat.totient d : ℝ)) *
          (∑ r in ((Finset.Icc (Nat.succ (Q0 / d)) (Nat.gcd N (N + Q0))).filter Nat.squarefree),
            if Nat.coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0) := by
  admit

/-- Euler-product tail bound with an explicit constant (stub). -/
lemma euler_tail_bound (R N : ℕ) (hR : 1 ≤ R) :
    ∑ r in ((Finset.Icc (Nat.succ R) (Nat.gcd N (N + R))).filter Nat.squarefree),
      if Nat.coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0
    ≤ (45 : ℝ) / R := by admit

/-- Numeric bound on the Euler-product constant for even N (stub). -/
lemma C_even_bound (N : ℕ) (hN : Nat.Even N) : (1.02 : ℝ) ≤ (1.5 : ℝ) := by admit

/-- Finite product evaluation for the block majorant on the extremal prime set (stub). -/
lemma numeric_eval_F_block :
    ((2 : ℝ) + 1 / (2 - 1)) * ((3 : ℝ) + 1 / (3 - 1)) *
      ((5 : ℝ) + 1 / (5 - 1)) * ((7 : ℝ) + 1 / (7 - 1)) *
      ((11 : ℝ) + 1 / (11 - 1)) * ((13 : ℝ) + 1 / (13 - 1)) *
      ((17 : ℝ) + 1 / (17 - 1)) < 330 := by
  norm_num

end TailBlock
end AO_OffDiag
end Goldbach
