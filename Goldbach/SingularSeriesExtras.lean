import Mathlib
import Goldbach.SingularSeries

open scoped BigOperators

namespace Goldbach
namespace Singular

/-- If `p` is an odd prime then `(p-1)/(p-2) ≥ 1`.
lemma oddFactor_ge_one_of_prime_ne_two
    {p : ℕ} (hp : Nat.Prime p) (hne2 : p ≠ 2) :
    (1 : ℝ) ≤ oddFactor p := by
  -- `2 < p` since `p` is prime and `p ≠ 2`.
  have h2le : 2 ≤ p := hp.two_le
  have h2lt : 2 < p := lt_of_le_of_ne h2le (by symm; exact hne2)
  have h1le : 1 ≤ p := le_trans (by decide : 1 ≤ 2) h2le
  -- Denominator positivity: `0 < (p - 2 : ℝ)`.
  have hden_pos_nat : 0 < p - 2 := Nat.sub_pos_of_lt h2lt
  have hden_pos : (0 : ℝ) < (p - 2 : ℝ) := by exact_mod_cast hden_pos_nat
  -- Show `(p-2) ≤ (p-1)` in ℝ and use `one_le_div_iff`.
  have num_ge : ((p - 2 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    have : (p : ℝ) - 2 ≤ (p : ℝ) - 1 := by linarith
    simpa [Nat.cast_sub h2le, Nat.cast_sub h1le] using this
  have : (1 : ℝ) ≤ (p - 1 : ℝ) / (p - 2 : ℝ) := (one_le_div_iff hden_pos).2 num_ge
  simpa [oddFactor] using this

If all factors are ≥ 1, then the real finset product is ≥ 1. -/
private lemma one_le_prod_of_one_le_real {ι : Type} (T : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ T, (1:ℝ) ≤ f i) : (1:ℝ) ≤ T.prod f := by
  apply Finset.prod_induction f (fun x => 1 ≤ x)
  · intro a b ha hb
    have ha0 : 0 ≤ a := le_trans (by norm_num) ha
    nlinarith
  · norm_num
  · exact h


/-- Every factor in the finite product over odd prime divisors is ≥ 1. -/

lemma oddFactor_ge_one_on_support {n p : ℕ}
    (hp : p ∈ oddPrimeSupport n) : (1 : ℝ) ≤ oddFactor p := by
  rcases Finset.mem_filter.mp hp with ⟨_, hpr⟩
  rcases hpr with ⟨hp_prime, hp_ne2⟩
  exact oddFactor_ge_one_of_prime_ne_two hp_prime hp_ne2

/-- The finite product of odd prime local factors is ≥ 1. -/
lemma prod_oddFactor_ge_one (n : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ oddPrimeSupport n, oddFactor p := by
  classical
  -- this is just `Finset.prod` over `oddPrimeSupport n`
  simpa using
    (one_le_prod_of_one_le_real (oddPrimeSupport n) (fun p => oddFactor p) (by
      intro p hp
      exact oddFactor_ge_one_on_support hp))

/-- Uniform positive floor for σ on even `n`: `σ(n) ≥ 2*C2`. -/
lemma sigma_floor_even {C : C2Const} {n : ℕ} (he : Even n) :
  (2 : ℝ) * C.C2 ≤ sigma C n := by
  have hprod := prod_oddFactor_ge_one n
  have hnonneg : 0 ≤ (2 : ℝ) * C.C2 := by
    have : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg this (le_of_lt C.pos)
  have := mul_le_mul_of_nonneg_left hprod hnonneg
  simpa [sigma_even_expand (C:=C) he, mul_assoc, mul_left_comm, mul_comm] using this

/-- Adding an odd prime not already dividing `m` inserts it into the odd-prime support. -/
lemma oddPrimeSupport_mul_prime_of_not_dvd {m p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    oddPrimeSupport (p * m) = insert p (oddPrimeSupport m) := by
  classical
  have hm0 : m ≠ 0 := by
    intro hm0
    exact hpm (hm0.symm ▸ dvd_zero p)
  have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
  ext q
  constructor
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    rcases hq' with ⟨hq_div, hq_prime, hq_ne2⟩
    have hq_dvd : q ∣ p * m := (Nat.mem_divisors.mp hq_div).1
    rcases hq_prime.dvd_mul.mp hq_dvd with hq_p | hq_m
    · exact Finset.mem_insert.mpr <| Or.inl ((Nat.prime_dvd_prime_iff_eq hq_prime hp).1 hq_p)
    · exact Finset.mem_insert.mpr <| Or.inr
        (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hq_m, hm0⟩, hq_prime, hq_ne2⟩)
  · intro hq
    rcases Finset.mem_insert.mp hq with hqeq | hq
    · have hpdvd : q ∣ p * m := by
        simpa [hqeq] using (dvd_mul_right p m)
      have hq_prime : Nat.Prime q := by simpa [hqeq] using hp
      have hq_ne2 : q ≠ 2 := by simpa [hqeq] using hp2
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hpdvd, hpm0⟩, hq_prime, hq_ne2⟩
    ·
      have hq' := Finset.mem_filter.mp hq
      rcases hq' with ⟨hq_div, hq_prime, hq_ne2⟩
      have hq_dvd : q ∣ m := (Nat.mem_divisors.mp hq_div).1
      have hq_dvd_pm : q ∣ p * m := dvd_mul_of_dvd_right hq_dvd p
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hq_dvd_pm, hpm0⟩, hq_prime, hq_ne2⟩

/-- Multiplying by an odd prime already dividing `m` does not change odd-prime support. -/
lemma oddPrimeSupport_mul_prime_of_dvd {m p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpm : p ∣ m) :
    oddPrimeSupport (p * m) = oddPrimeSupport m := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    simp [oddPrimeSupport]
  have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
  ext q
  constructor
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    rcases hq' with ⟨hq_div, hq_prime, hq_ne2⟩
    have hq_dvd_pm : q ∣ p * m := (Nat.mem_divisors.mp hq_div).1
    rcases hq_prime.dvd_mul.mp hq_dvd_pm with hq_p | hq_m
    · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp).1 hq_p
      have hq_dvd_m : q ∣ m := by simpa [hqp] using hpm
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hq_dvd_m, hm0⟩, hq_prime, hq_ne2⟩
    · exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hq_m, hm0⟩, hq_prime, hq_ne2⟩
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    rcases hq' with ⟨hq_div, hq_prime, hq_ne2⟩
    have hq_dvd_m : q ∣ m := (Nat.mem_divisors.mp hq_div).1
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right hq_dvd_m p, hpm0⟩, hq_prime, hq_ne2⟩

/-- Euler-product toggle when adjoining a new odd prime factor. -/
lemma sigma_even_mul_prime_of_not_dvd {C : C2Const} {m p : ℕ}
    (he : Even m) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    sigma C (p * m) = oddFactor p * sigma C m := by
  have hEven_pm : Even (p * m) := by
    exact Nat.even_mul.mpr <| Or.inr he
  have hp_not_mem : p ∉ oddPrimeSupport m := by
    intro hp_mem
    exact hpm ((Nat.mem_divisors.mp (Finset.mem_filter.mp hp_mem).1).1)
  calc
    sigma C (p * m)
        = (2 : ℝ) * C.C2 * ∏ q ∈ oddPrimeSupport (p * m), oddFactor q := by
            simpa using sigma_even_expand (C := C) hEven_pm
    _ = (2 : ℝ) * C.C2 * ∏ q ∈ insert p (oddPrimeSupport m), oddFactor q := by
          rw [oddPrimeSupport_mul_prime_of_not_dvd hp hp2 hpm]
    _ = (2 : ℝ) * C.C2 * (oddFactor p * ∏ q ∈ oddPrimeSupport m, oddFactor q) := by
          simp [Finset.prod_insert, hp_not_mem]
    _ = oddFactor p * sigma C m := by
          rw [sigma_even_expand (C := C) he]
          ring

/-- Adding another copy of an odd prime already dividing `m` leaves `sigma` unchanged. -/
lemma sigma_even_mul_prime_of_dvd {C : C2Const} {m p : ℕ}
    (he : Even m) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpm : p ∣ m) :
    sigma C (p * m) = sigma C m := by
  have hEven_pm : Even (p * m) := Nat.even_mul.mpr <| Or.inr he
  calc
    sigma C (p * m)
        = (2 : ℝ) * C.C2 * ∏ q ∈ oddPrimeSupport (p * m), oddFactor q := by
            simpa using sigma_even_expand (C := C) hEven_pm
    _ = (2 : ℝ) * C.C2 * ∏ q ∈ oddPrimeSupport m, oddFactor q := by
          rw [oddPrimeSupport_mul_prime_of_dvd hp hp2 hpm]
    _ = sigma C m := by
          rw [sigma_even_expand (C := C) he]

end Singular
end Goldbach
