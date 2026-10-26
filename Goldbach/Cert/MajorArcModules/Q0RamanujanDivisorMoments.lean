import Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion

/-!
# Finite divisor orthogonality behind the full-period Ramanujan moments

These identities use Möbius inversion and `sum_totient`.  The full-period divisor density
`1 / lcm(d,e)` turns the product of the two divisor coefficients into the gcd kernel below.
-/

namespace Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorMoments

open scoped BigOperators ArithmeticFunction.Moebius
open Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion

noncomputable section

theorem sum_moebius_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.coe_zeta_mul_moebius
  dsimp only at h
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at h
  exact_mod_cast h

theorem sum_moebius_multiple_divisors (q k : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, if k ∣ d then (μ (q / d) : ℝ) else 0) =
      if k = q then 1 else 0 := by
  classical
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  by_cases hk : k ∣ q
  · have hcomp :
        (∑ d ∈ q.divisors, if k ∣ d then (μ (q / d) : ℝ) else 0) =
          ∑ d ∈ q.divisors, if k ∣ q / d then (μ d : ℝ) else 0 := by
      have h := Nat.sum_div_divisors q
        (fun d => if k ∣ q / d then (μ d : ℝ) else 0)
      refine (Finset.sum_congr rfl ?_).trans h
      intro d hd
      rw [Nat.div_div_self (Nat.mem_divisors.mp hd).1 hq0]
    have hpred : ∀ d ∈ q.divisors, k ∣ q / d ↔ d ∣ q / k := by
      intro d hd
      rw [Nat.dvd_div_iff_mul_dvd (Nat.mem_divisors.mp hd).1,
        Nat.dvd_div_iff_mul_dvd hk, Nat.mul_comm d k]
    have hquot : q / k = 1 ↔ k = q := by
      constructor
      · intro h
        simpa [h] using Nat.mul_div_cancel' hk
      · intro h
        subst k
        exact Nat.div_self hq
    calc
      (∑ d ∈ q.divisors, if k ∣ d then (μ (q / d) : ℝ) else 0) =
          ∑ d ∈ q.divisors, if k ∣ q / d then (μ d : ℝ) else 0 := hcomp
      _ = ∑ d ∈ q.divisors, if d ∣ q / k then (μ d : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [hpred d hd]
      _ = ∑ d ∈ (q / k).divisors, (μ d : ℝ) := by
        rw [← Finset.sum_filter,
          Nat.divisors_filter_dvd_of_dvd hq0 (Nat.div_dvd_of_dvd hk)]
      _ = if k = q then 1 else 0 := by
        simp only [sum_moebius_divisors, hquot]
  · have hkq : k ≠ q := by
      intro h
      subst k
      exact hk (dvd_refl q)
    rw [if_neg hkq]
    apply Finset.sum_eq_zero
    intro d hd
    have hkd : ¬ k ∣ d := fun h => hk (dvd_trans h (Nat.mem_divisors.mp hd).1)
    simp [hkd]

theorem gcd_eq_sum_totient_common_divisors
    (q d e : ℕ) (hq : 0 < q) (hd : d ∈ q.divisors) :
    (Nat.gcd d e : ℝ) =
      ∑ k ∈ q.divisors, if k ∣ d ∧ k ∣ e then (Nat.totient k : ℝ) else 0 := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hg0 : Nat.gcd d e ≠ 0 := Nat.ne_of_gt
    (Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero hd0))
  have hset : (Nat.gcd d e).divisors = q.divisors.filter (fun k => k ∣ d ∧ k ∣ e) := by
    ext k
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · intro h
      have hkd := dvd_trans h.1 (Nat.gcd_dvd_left d e)
      exact ⟨⟨dvd_trans hkd (Nat.mem_divisors.mp hd).1, Nat.ne_of_gt hq⟩,
        hkd, dvd_trans h.1 (Nat.gcd_dvd_right d e)⟩
    · intro h
      exact ⟨Nat.dvd_gcd h.2.1 h.2.2, hg0⟩
  have hsum : (Nat.gcd d e : ℝ) = ∑ k ∈ (Nat.gcd d e).divisors, (Nat.totient k : ℝ) := by
    exact_mod_cast (Nat.sum_totient (Nat.gcd d e)).symm
  rw [hsum, hset, Finset.sum_filter]

theorem moebius_gcd_kernel_orthogonality (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (∑ d ∈ q.divisors, ∑ e ∈ r.divisors,
      (μ (q / d) : ℝ) * (μ (r / e) : ℝ) * (Nat.gcd d e : ℝ)) =
      if q = r then (Nat.totient q : ℝ) else 0 := by
  classical
  calc
    (∑ d ∈ q.divisors, ∑ e ∈ r.divisors,
      (μ (q / d) : ℝ) * (μ (r / e) : ℝ) * (Nat.gcd d e : ℝ)) =
        ∑ d ∈ q.divisors, ∑ e ∈ r.divisors, ∑ k ∈ q.divisors,
          (Nat.totient k : ℝ) *
            (if k ∣ d then (μ (q / d) : ℝ) else 0) *
            (if k ∣ e then (μ (r / e) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [gcd_eq_sum_totient_common_divisors q d e hq hd, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkd : k ∣ d <;> by_cases hke : k ∣ e <;> simp [hkd, hke] <;> ring
    _ = ∑ k ∈ q.divisors,
        (Nat.totient k : ℝ) *
          (∑ d ∈ q.divisors, if k ∣ d then (μ (q / d) : ℝ) else 0) *
          (∑ e ∈ r.divisors, if k ∣ e then (μ (r / e) : ℝ) else 0) := by
      calc
        _ = ∑ d ∈ q.divisors, ∑ k ∈ q.divisors, ∑ e ∈ r.divisors,
            (Nat.totient k : ℝ) *
              (if k ∣ d then (μ (q / d) : ℝ) else 0) *
              (if k ∣ e then (μ (r / e) : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact Finset.sum_comm
        _ = ∑ k ∈ q.divisors, ∑ d ∈ q.divisors, ∑ e ∈ r.divisors,
            (Nat.totient k : ℝ) *
              (if k ∣ d then (μ (q / d) : ℝ) else 0) *
              (if k ∣ e then (μ (r / e) : ℝ) else 0) := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_comm
    _ = ∑ k ∈ q.divisors,
        (Nat.totient k : ℝ) * (if k = q then 1 else 0) * (if k = r then 1 else 0) := by
      simp_rw [sum_moebius_multiple_divisors q _ hq, sum_moebius_multiple_divisors r _ hr]
    _ = if q = r then (Nat.totient q : ℝ) else 0 := by
      rw [Finset.sum_eq_single_of_mem q (Nat.mem_divisors_self q (Nat.ne_of_gt hq))]
      · by_cases hqr : q = r <;> simp [hqr]
      · intro k hk hkq
        simp [hkq]

/-- The full-period density of one Ramanujan divisor expansion. -/
theorem ramanujan_divisor_mean_density (q : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, ((d : ℝ) * (μ (q / d) : ℝ)) / d) =
      if q = 1 then 1 else 0 := by
  calc
    _ = ∑ d ∈ q.divisors, (μ (q / d) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : (d : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      field_simp
    _ = ∑ d ∈ q.divisors, (μ d : ℝ) := Nat.sum_div_divisors q (fun d => (μ d : ℝ))
    _ = _ := sum_moebius_divisors q

/-- CRT gives density `1/lcm(d,e)` for two divisibility conditions.  The resulting
finite divisor kernel is diagonal, with diagonal value `totient q`. -/
theorem ramanujan_divisor_pair_density (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (∑ d ∈ q.divisors, ∑ e ∈ r.divisors,
      ((d : ℝ) * (μ (q / d) : ℝ)) * ((e : ℝ) * (μ (r / e) : ℝ)) /
        (Nat.lcm d e : ℝ)) =
      if q = r then (Nat.totient q : ℝ) else 0 := by
  rw [← moebius_gcd_kernel_orthogonality q r hq hr]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
  have hl0 : (Nat.lcm d e : ℝ) ≠ 0 := by exact_mod_cast Nat.lcm_ne_zero hd0 he0
  have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  apply (div_eq_iff hl0).2
  calc
    _ = (μ (q / d) : ℝ) * (μ (r / e) : ℝ) * ((d : ℝ) * e) := by ring
    _ = _ := by rw [← hgl]; ring

end
end Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorMoments
