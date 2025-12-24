import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Core
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Squarefree

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

/-- Truncation height for the off-diagonal singular series. -/
@[simp] def Q0 : ℕ := 30000

/-- Alias the singular series. -/
abbrev sigma : ℕ → ℝ := AO_Core.sigma

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

lemma coprime_gcd_left_div (q N : ℕ) :
    (Nat.gcd q N).Coprime (q / Nat.gcd q N) := by
  classical
  set d := Nat.gcd q N with hd
  by_cases hd0 : d = 0
  · subst hd
    -- gcd q N = 0 implies q=0 and N=0; then goal is Coprime 0 (0/0)=Coprime 0 0, true by simp
    simp [Nat.gcd_eq_zero_iff] at hd0
    rcases hd0 with ⟨rfl, rfl⟩
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hdq : d ∣ q := by simpa [hd] using Nat.gcd_dvd_left q N
    -- compute gcd(d, q/d) = 1 via gcd_div
    have hdiv : (q / d).gcd (d / d) = q.gcd d / d := by
      simpa using (Nat.gcd_div (m := q) (n := d) (k := d) hdq (dvd_rfl))
    have hdd : d / d = 1 := Nat.div_self hdpos
    have hqd : q.gcd d = d := Nat.gcd_eq_right hdq
    have : (q / d).gcd 1 = 1 := by
      simpa [hdd, hqd] using hdiv
    -- flip gcd to match `d.Coprime (q/d)`
    -- `Nat.Coprime` is defined by gcd = 1 in ℕ
    simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, hd] using this

/-- Real-valued Ramanujan sum. -/
noncomputable def ramanujanR (q N : ℕ) : ℝ := (ramanujanZ q N : ℤ)

/-- Truncated singular series at height `Q0`: `σ_{≤Q0}(N) = ∑_{q≤Q0} μ(q)^2/φ(q)^2 * c_q(N)`. -/
noncomputable def sigma_trunc_Q0 (N : ℕ) : ℝ :=
  (Finset.Icc (1 : ℕ) Q0).sum (fun q =>
    (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N))

/-- Canonical block majorant. -/
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
  F : ℕ → ℝ
  F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      F N ≤ (7.9 : ℝ)
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
  === Pure math lemmas (non-analytic) ===
-/

/-- Squarefree support of μ² (for our `muSq`). -/
lemma muSq_eq_zero_iff_not_squarefree (q : ℕ) :
    muSq q = 0 ↔ ¬ Squarefree q := by
  by_cases h : Squarefree q <;> simp [muSq, h]

/-- Ramanujan identity (closed form): definitional, no squarefree needed. -/
lemma ramanujan_sqfree (q N : ℕ) (hq : Squarefree q) :
    ramanujanZ q N = (μ (q / Nat.gcd q N) : ℤ) * Int.ofNat (Nat.totient (Nat.gcd q N)) := by
  simp [ramanujanZ]

/-- If `q` is squarefree and `d ∣ q`, then `q / d` is squarefree. -/
lemma squarefree_div_of_dvd {q d : ℕ} (hq : Squarefree q) (hd : d ∣ q) :
    Squarefree (q / d) := by
  -- unfold the `Squarefree` predicate on `ℕ`
  intro x hx
  -- `hx : x*x ∣ q/d`. Multiply by `d` to get `x*x*d ∣ q`.
  have hx' : x * x * d ∣ q := by
    rcases hx with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      q = d * (q / d) := by
            -- q = d*(q/d)
            simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hd).symm
      _ = d * (x * x * k) := by
            simpa [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = x * x * d * k := by
            -- just reassociate/commute
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

  -- Now apply squarefree condition on q:
  -- `hq (x) (x*x ∣ q)` gives `IsUnit x`.
  -- We need `x*x ∣ q`, but we have `x*x*d ∣ q`. Since `x*x ∣ x*x*d`, transitivity gives it.
  have hx2 : x * x ∣ q := by
    exact dvd_trans (dvd_mul_right (x * x) d) hx'
  exact hq x hx2

/-- Termwise bound after splitting q = d*r. -/
lemma term_bound_after_split (q N : ℕ) (hq : Squarefree q) :
    let d := Nat.gcd q N
    let r := q / d
    |muSq q * (1 / (Nat.totient q : ℝ) ^ 2) * ramanujanR q N|
      = 1 / ((Nat.totient d : ℝ) * (Nat.totient r : ℝ) ^ 2) := by
  classical
  intro d r

  have hd : d ∣ q := Nat.gcd_dvd_left q N
  have hqr_sq : Squarefree (q / d) :=
    squarefree_div_of_dvd (q := q) (d := d) hq hd

  -- `muSq q = 1` (since `q` is squarefree)
  have hmuSq : muSq q = (1 : ℝ) := by
    simp [muSq, hq]

  -- From `moebius_sq`, get μ(q/d)^2 = 1 in ℤ
  have hmu_sq : (μ (q / d) : ℤ) ^ 2 = 1 := by
    simpa [hqr_sq] using (ArithmeticFunction.moebius_sq (n := (q / d)))

  -- Hence μ(q/d) = ±1 in ℤ
  have hmu_pm : (μ (q / d) : ℤ) = 1 ∨ (μ (q / d) : ℤ) = -1 := by
    have h0 : ((μ (q / d) : ℤ) - 1) * ((μ (q / d) : ℤ) + 1) = 0 := by
      nlinarith [hmu_sq]
    rcases mul_eq_zero.mp h0 with h | h
    · left; linarith
    · right; linarith

  -- Therefore |μ(q/d)| = 1 after casting to ℝ
  have hmu_abs : |((μ (q / d) : ℤ) : ℝ)| = 1 := by
    rcases hmu_pm with h | h
    · simp [h]
    · simp [h]

  -- Compute |ramanujanR q N| = φ(d)
  have hRamAbs : |ramanujanR q N| = (Nat.totient d : ℝ) := by
    -- ramanujanR q N = ((μ(q/d) * φ(d)) : ℤ) cast to ℝ
    -- so abs = |μ(q/d)| * φ(d) = 1 * φ(d)
    simp [ramanujanR, ramanujanZ, d, hmu_abs, abs_mul]

  -- Structural totient factorization (proved elsewhere / fill in)
  have hphi : (Nat.totient q : ℝ) = (Nat.totient d : ℝ) * (Nat.totient r : ℝ) := by
    have hqdr : q = d * r := by
      simpa [r, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.mul_div_cancel' hd).symm
    have hcop : d.Coprime r := by
      simpa [d, r] using (coprime_gcd_left_div q N)
    have ht : Nat.totient (d * r) = Nat.totient d * Nat.totient r := by
      simpa using (Nat.totient_mul (m := d) (n := r) hcop)
    simpa [hqdr, ht, Nat.cast_mul]

  -- Final algebra: simplify the absolute value expression
  by_cases hdt : (Nat.totient d : ℝ) = 0
  · simp [hmuSq, hRamAbs, hphi, hdt]
  · have hdt' : (Nat.totient d : ℝ) ≠ 0 := hdt
    -- `pow_two` rewrites `x^2` as `x*x`; the remaining goal is cancellation/reassociation.
    simp [hmuSq, hRamAbs, hphi, pow_two,
          mul_assoc, mul_left_comm, mul_comm,
          hdt', mul_inv_cancel, inv_mul_cancel]

/-- Tail reindexing inequality (will be rewritten with `tsum` once `sigma` is nontrivial). -/
lemma tail_reindex_bound (N : ℕ) :
    |sigma N - sigma_trunc_Q0 N| ≤
      ((Nat.divisors N).filter Squarefree).sum (fun d =>
        (1 / (Nat.totient d : ℝ)) *
          (((Finset.Icc (Nat.succ (Q0 / d)) (Nat.gcd N (N + Q0))).filter Squarefree).sum (fun r =>
            if Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0))) := by
  admit

/-- Euler-product tail bound with an explicit constant (Rosser–Schoenfeld input later). -/
lemma euler_tail_bound (R N : ℕ) (hR : 1 ≤ R) :
    ((Finset.Icc (Nat.succ R) (Nat.gcd N (N + R))).filter Squarefree).sum (fun r =>
      if Nat.Coprime r N then 1 / (Nat.totient r : ℝ) ^ 2 else 0)
    ≤ (45 : ℝ) / R := by
  admit

/-- Finite product evaluation for the block majorant on the extremal prime set.
-- The finite product appearing in the block-majorant numeric check (as a rational). -/
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
    -- `native_decide` works fine on rationals here.
    unfold FprodQ
    native_decide
  exact_mod_cast hQ
