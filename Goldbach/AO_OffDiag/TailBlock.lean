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

/--
Tail-block facts packaged as a `Model`.

This is the “no-axioms-in-the-file” interface: analytic inputs live as *fields*
to be proved in downstream modules.
-/
structure Model where
  /-- The true singular series. -/
  sigma : ℕ → ℝ
  /-- Majorant factor in the tail bound (often `F_block`). -/
  F : ℕ → ℝ
  /-- Uniform bound for `F` on the canonical window. -/
  F_bound_on_window :
    ∀ {X N : ℕ}, BankParams.X0 ≤ X → N ∈ (Goldbach.Windows.EvenIn X BankParams.H) →
      F N ≤ (7.9 : ℝ)
  /-- Tail comparison between `sigma` and the truncation. -/
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
  |M.sigma N - sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) := by
  have h1 := M.sigma_tail_block (X:=X) (N:=N) hX hN
  have hF := M.F_bound_on_window (X:=X) (N:=N) hX hN
  have hcoef_nonneg : 0 ≤ (1.02 : ℝ) / (Q0 : ℝ) := by
    have : (0 : ℝ) < (Q0 : ℝ) := by norm_num [Q0]
    have hpos : 0 < (1.02 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt hpos) (le_of_lt this)
  have h2 : (1.02 : ℝ) / (Q0 : ℝ) * M.F N ≤ (1.02 : ℝ) / (Q0 : ℝ) * (7.9 : ℝ) :=
    mul_le_mul_of_nonneg_left hF hcoef_nonneg
  exact h1.trans (h2.trans coef_times_ub_le_3e4)

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
