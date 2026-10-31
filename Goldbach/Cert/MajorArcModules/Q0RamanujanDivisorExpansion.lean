import Goldbach.AO_OffDiag.TailBlock

/-!
# Divisor expansion of the finite Ramanujan observable

The closed form in `TailBlock` agrees with the usual Ramanujan divisor sum on squarefree moduli.
Only that case is used by the singular-series truncation.  In particular, no statement below
asserts the unrestricted closed-form identity for nonsquarefree moduli.
-/

namespace Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion

open scoped BigOperators ArithmeticFunction.Moebius
open Goldbach.AO_OffDiag.TailBlock

noncomputable section

/-- Multiplication by two does not change a Ramanujan argument for odd modulus. -/
theorem ramanujanR_two_mul_argument (q n : ℕ) (hq : Odd q) :
    ramanujanR q (2 * n) = ramanujanR q n := by
  have hgcd : Nat.gcd q (2 * n) = Nat.gcd q n :=
    hq.coprime_two_left.gcd_mul_left_cancel_right n
  simp [ramanujanR, ramanujanZ, hgcd]

/-- On even inputs, the odd modulus and twice that modulus have the same Ramanujan value. -/
theorem ramanujanR_two_mul_modulus_two_mul_argument (q n : ℕ) (hq : Odd q) :
    ramanujanR (2 * q) (2 * n) = ramanujanR q n := by
  have hcop : Nat.Coprime 2 (Nat.gcd q n) :=
    hq.coprime_two_left.of_dvd_right (Nat.gcd_dvd_left q n)
  have hphi : Nat.totient (2 * Nat.gcd q n) = Nat.totient (Nat.gcd q n) := by
    rw [Nat.totient_mul hcop]
    norm_num
  have hquot : (2 * q) / (2 * Nat.gcd q n) = q / Nat.gcd q n := by
    exact Nat.mul_div_mul_left q (Nat.gcd q n) (by decide : 0 < 2)
  simp [ramanujanR, ramanujanZ, Nat.gcd_mul_left, hphi, hquot]

theorem totient_eq_sum_divisors_moebius (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℝ) =
      ∑ d ∈ n.divisors, (d : ℝ) * (μ (n / d) : ℝ) := by
  have hsum : ∀ (k : ℕ), k > 0 → ∑ d ∈ k.divisors, (Nat.totient d : ℝ) = (k : ℝ) := by
    intro k hk
    exact_mod_cast Nat.sum_totient k
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun k => (Nat.totient k : ℝ)) (g := fun k => (k : ℝ))).1 hsum n hn
  rw [Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * (b : ℝ))] at hinv
  simpa [mul_comm] using hinv.symm

theorem ramanujanR_eq_sum_divisors_gcd_of_squarefree
    (q N : ℕ) (hq : Squarefree q) :
    ramanujanR q N =
      ∑ d ∈ (Nat.gcd q N).divisors, (d : ℝ) * (μ (q / d) : ℝ) := by
  let g := Nat.gcd q N
  let r := q / g
  have hq0 : q ≠ 0 := hq.ne_zero
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left N (Nat.pos_of_ne_zero hq0)
  have hgdvd : g ∣ q := Nat.gcd_dvd_left q N
  have hqgr : q = g * r := (Nat.mul_div_cancel' hgdvd).symm
  have hcop : Nat.Coprime g r := coprime_gcd_div_of_squarefree q N hq
  have hterm : ∀ d ∈ g.divisors,
      (μ (q / d) : ℝ) = (μ r : ℝ) * (μ (g / d) : ℝ) := by
    intro d hd
    have hdg : d ∣ g := (Nat.mem_divisors.mp hd).1
    have hmul : q / d = r * (g / d) := by
      rw [hqgr, mul_comm g r, Nat.mul_div_assoc r hdg]
    have hrcop : Nat.Coprime r (g / d) :=
      hcop.symm.of_dvd_right (Nat.div_dvd_of_dvd hdg)
    rw [hmul]
    exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hrcop
  calc
    ramanujanR q N = (μ r : ℝ) * (Nat.totient g : ℝ) := by
      simp [ramanujanR, ramanujanZ, g, r]
    _ = (μ r : ℝ) * ∑ d ∈ g.divisors, (d : ℝ) * (μ (g / d) : ℝ) := by
      rw [totient_eq_sum_divisors_moebius g hgpos]
    _ = ∑ d ∈ g.divisors, (d : ℝ) * (μ (q / d) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hterm d hd]
      ring

theorem divisors_gcd_eq_filter (q N : ℕ) (hq0 : q ≠ 0) :
    (Nat.gcd q N).divisors = q.divisors.filter (fun d => d ∣ N) := by
  have hg0 : Nat.gcd q N ≠ 0 := Nat.ne_of_gt
    (Nat.gcd_pos_of_pos_left N (Nat.pos_of_ne_zero hq0))
  ext d
  simp [Nat.mem_divisors, hg0, hq0, Nat.dvd_gcd_iff]

theorem ramanujanR_eq_sum_divisors_indicator_of_squarefree
    (q N : ℕ) (hq : Squarefree q) :
    ramanujanR q N =
      ∑ d ∈ q.divisors, if d ∣ N then (d : ℝ) * (μ (q / d) : ℝ) else 0 := by
  rw [ramanujanR_eq_sum_divisors_gcd_of_squarefree q N hq,
    divisors_gcd_eq_filter q N hq.ne_zero, Finset.sum_filter]

theorem divisors_eq_filter_Icc {q Q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    q.divisors = (Finset.Icc 1 Q).filter (fun d => d ∣ q) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hd
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hq, (Nat.le_of_dvd hq hd.1).trans hqQ⟩, hd.1⟩
  · exact fun hd => ⟨hd.2, Nat.ne_of_gt hq⟩

theorem ramanujanR_eq_sum_Icc_indicator_of_squarefree
    {q Q : ℕ} (N : ℕ) (hq : Squarefree q) (hqQ : q ≤ Q) :
    ramanujanR q N =
      ∑ d ∈ Finset.Icc 1 Q,
        if d ∣ q ∧ d ∣ N then (d : ℝ) * (μ (q / d) : ℝ) else 0 := by
  rw [ramanujanR_eq_sum_divisors_indicator_of_squarefree q N hq,
    divisors_eq_filter_Icc (Nat.pos_of_ne_zero hq.ne_zero) hqQ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdq : d ∣ q <;> by_cases hdN : d ∣ N <;> simp [hdq, hdN]

/-- Divisor coefficient of a finite Ramanujan combination with squarefree support. -/
def divisorCoefficient (Q : ℕ) (w : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q,
    if d ∣ q then w q * (d : ℝ) * (μ (q / d) : ℝ) else 0

theorem sum_ramanujanR_eq_sum_divisorCoefficient
    (Q N : ℕ) (w : ℕ → ℝ)
    (hw : ∀ q ∈ Finset.Icc 1 Q, ¬ Squarefree q → w q = 0) :
    (∑ q ∈ Finset.Icc 1 Q, w q * ramanujanR q N) =
      ∑ d ∈ Finset.Icc 1 Q, if d ∣ N then divisorCoefficient Q w d else 0 := by
  classical
  calc
    (∑ q ∈ Finset.Icc 1 Q, w q * ramanujanR q N) =
        ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 1 Q,
          if d ∣ q ∧ d ∣ N then w q * (d : ℝ) * (μ (q / d) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hsq : Squarefree q
      · rw [ramanujanR_eq_sum_Icc_indicator_of_squarefree N hsq (Finset.mem_Icc.mp hq).2,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases h : d ∣ q ∧ d ∣ N <;> simp [h, mul_assoc]
      · simp [hw q hq hsq]
    _ = ∑ d ∈ Finset.Icc 1 Q, ∑ q ∈ Finset.Icc 1 Q,
          if d ∣ q ∧ d ∣ N then w q * (d : ℝ) * (μ (q / d) : ℝ) else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 Q, if d ∣ N then divisorCoefficient Q w d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdN : d ∣ N <;> simp [hdN, divisorCoefficient]

/-- The rational divisor observable is an exact rewrite of the existing raw truncation. -/
theorem sigma_trunc_Q0_eq_sum_divisorCoefficient (N : ℕ) :
    sigma_trunc_Q0 N =
      ∑ d ∈ Finset.Icc 1 Q0,
        if d ∣ N then
          divisorCoefficient Q0 (fun q => muSq q * (1 / (Nat.totient q : ℝ) ^ 2)) d
        else 0 := by
  apply sum_ramanujanR_eq_sum_divisorCoefficient
  intro q hq hsq
  simp [muSq, hsq]

end
end Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion
