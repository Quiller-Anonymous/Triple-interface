import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Squarefree

/-!
Parallel “Tenor-style” refactor scaffold:

The existing off-diagonal tail block (`Goldbach.AO_OffDiag.TailBlock`) hard-codes a truncation
height `Q0`. In Tenor’s main text, the truncation height `Q` depends on the scale `X` (typically
`Q = H^γ` and `H = (log X)^A`).

This file introduces a *purely structural* tail-block interface parameterized by `Q : ℕ → ℕ`
without changing the existing fixed-`Q0` pipeline yet.
-/

namespace Goldbach
namespace AO_OffDiag
namespace TailBlockFun

open Real Goldbach.Windows
open scoped BigOperators

noncomputable section

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

/-- Truncated singular series at a (variable) height `Q`. -/
noncomputable def sigma_trunc (Q : ℕ) (N : ℕ) : ℝ :=
  (Finset.Icc (1 : ℕ) Q).sum (fun q =>
    (muSq q) * (1 / ((Nat.totient q : ℝ) ^ 2)) * (ramanujanR q N))

/-- Canonical block majorant used in the tail bound (purely arithmetic). -/
noncomputable def F_block (N : ℕ) : ℝ :=
  ((Nat.factorization N).support).prod (fun p => (1 : ℝ) + (1 / ((p : ℝ) - 1)))

/--
Tail-block facts packaged as a `Model`, now parameterized by a scale-dependent truncation
height `Q : ℕ → ℕ`.
-/
structure Model where
  /-- Scale-dependent truncation height. -/
  Q : ℕ → ℕ
  /-- On the canonical window, the truncation height is positive. -/
  Q_pos_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) → 1 ≤ Q X
  /-- The true singular series. -/
  sigma : ℕ → ℝ
  /-- Majorant factor in the tail bound (often `F_block`). -/
  F : ℕ → ℝ
  /-- Tail constant: analytic estimate produces `(K_tail/Q X) * F(N)`. -/
  K_tail : ℝ
  K_tail_nonneg : 0 ≤ K_tail
  /-- Tail comparison between `sigma` and the truncation at height `Q X`. -/
  sigma_tail_block :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      |sigma N - sigma_trunc (Q X) N| ≤ (K_tail : ℝ) / (Q X : ℝ) * F N

/--
Consumer lemma: if you have proved the pointwise budget squeeze
`(K_tail/(Q X)) * F(N) ≤ eps` on the window, then you get the uniform tail bound `≤ eps`.
-/
theorem tail_bound_on_window
  (M : Model)
  (eps : ℝ)
  (hbudget :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X BankParams.H →
      (M.K_tail : ℝ) / (M.Q X : ℝ) * (M.F N) ≤ eps)
  {X N : ℕ}
  (hX : BankParams.X0 ≤ X)
  (hN : N ∈ Goldbach.Windows.EvenIn X BankParams.H) :
  |M.sigma N - sigma_trunc (M.Q X) N| ≤ eps := by
  exact (M.sigma_tail_block (X := X) (N := N) hX hN).trans (hbudget hX hN)

/-!
## Pure arithmetic lemmas (reused by reindexing)

These are independent of the choice of truncation height, so they belong in the `Q(X)`-ready layer.
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
  ·
    have hdt' : (Nat.totient d : ℝ) ≠ 0 := hdt
    simp [hmuSq, hRamAbs, hphi, pow_two, mul_assoc, mul_left_comm, mul_comm, hdt', mul_inv_cancel,
      inv_mul_cancel]

end
end TailBlockFun
end AO_OffDiag
end Goldbach
