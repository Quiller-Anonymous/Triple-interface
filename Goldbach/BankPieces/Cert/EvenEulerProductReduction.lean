import Goldbach.SingularSeriesExtras

namespace Goldbach.BankPieces.Cert.EvenEulerProductReduction

open Goldbach
open Goldbach.Singular

/--
Local laws sufficient to recover the full Hardy--Littlewood even product formula.

`base_empty` handles the pure powers-of-two case abstractly, while the other two fields encode the
odd-prime toggle and saturation behaviour.
-/
structure EvenLocalProductLaws (f : ℕ → ℝ) (base : ℝ) : Prop where
  base_empty :
    ∀ {n : ℕ}, 0 < n → Even n → oddPrimeSupport n = ∅ → f n = base
  mul_prime_of_not_dvd :
    ∀ {m p : ℕ}, Even m → Nat.Prime p → p ≠ 2 → ¬ p ∣ m →
      f (p * m) = oddFactor p * f m
  mul_prime_of_dvd :
    ∀ {m p : ℕ}, Even m → Nat.Prime p → p ≠ 2 → p ∣ m →
      f (p * m) = f m

/-- The local laws imply the full even-input Hardy--Littlewood product formula. -/
theorem even_formula_of_local_laws {f : ℕ → ℝ} {base : ℝ}
    (hf : EvenLocalProductLaws f base) :
    ∀ {n : ℕ}, 0 < n → Even n →
      f n = base * ∏ p ∈ oddPrimeSupport n, oddFactor p := by
  let P : ℕ → Prop := fun n =>
    0 < n → Even n → f n = base * ∏ p ∈ oddPrimeSupport n, oddFactor p
  have hP : ∀ n : ℕ, P n := by
    intro n
    exact Nat.strong_induction_on n (fun n ih => by
      intro hn_pos hn_even
      by_cases hsupp : oddPrimeSupport n = ∅
      · rw [hsupp, Finset.prod_empty, mul_one]
        exact hf.base_empty hn_pos hn_even hsupp
      · obtain ⟨p, hp_mem⟩ : ∃ p, p ∈ oddPrimeSupport n := by
          simpa [Finset.eq_empty_iff_forall_notMem] using hsupp
        rcases Finset.mem_filter.mp hp_mem with ⟨hp_div, hp_prime, hp_ne2⟩
        have hp_dvd_n : p ∣ n := (Nat.mem_divisors.mp hp_div).1
        let m := n / p
        have hmul : p * m = n := by
          dsimp [m]
          exact Nat.mul_div_cancel' hp_dvd_n
        have hEven_pm : Even (p * m) := by simpa [hmul] using hn_even
        have hp_not_even : ¬ Even p := by
          intro hp_even
          exact hp_ne2 ((Nat.Prime.even_iff hp_prime).1 hp_even)
        have hm_even : Even m := by
          rcases Nat.even_mul.mp hEven_pm with hp_even | hm_even
          · exact (hp_not_even hp_even).elim
          · exact hm_even
        have hm_pos : 0 < m := by
          have hpm_pos : 0 < p * m := by simpa [hmul] using hn_pos
          exact Nat.pos_of_mul_pos_left hpm_pos
        have hm_lt : m < n := by
          dsimp [m]
          exact Nat.div_lt_self hn_pos hp_prime.one_lt
        have ihm := ih m hm_lt hm_pos hm_even
        by_cases hpm : p ∣ m
        · calc
            f n = f (p * m) := by simpa [hmul]
            _ = f m := hf.mul_prime_of_dvd hm_even hp_prime hp_ne2 hpm
            _ = base * ∏ q ∈ oddPrimeSupport m, oddFactor q := ihm
            _ = base * ∏ q ∈ oddPrimeSupport (p * m), oddFactor q := by
                  rw [Goldbach.Singular.oddPrimeSupport_mul_prime_of_dvd hp_prime hp_ne2 hpm]
            _ = base * ∏ q ∈ oddPrimeSupport n, oddFactor q := by simpa [hmul]
        · have hp_not_mem : p ∉ oddPrimeSupport m := by
            intro hp_mem_m
            exact hpm ((Nat.mem_divisors.mp (Finset.mem_filter.mp hp_mem_m).1).1)
          calc
            f n = f (p * m) := by simpa [hmul]
            _ = oddFactor p * f m := hf.mul_prime_of_not_dvd hm_even hp_prime hp_ne2 hpm
            _ = oddFactor p * (base * ∏ q ∈ oddPrimeSupport m, oddFactor q) := by rw [ihm]
            _ = base * (oddFactor p * ∏ q ∈ oddPrimeSupport m, oddFactor q) := by ring
            _ = base * ∏ q ∈ oddPrimeSupport (p * m), oddFactor q := by
                  rw [Goldbach.Singular.oddPrimeSupport_mul_prime_of_not_dvd hp_prime hp_ne2 hpm]
                  simp [Finset.prod_insert, hp_not_mem, mul_assoc, mul_left_comm, mul_comm]
            _ = base * ∏ q ∈ oddPrimeSupport n, oddFactor q := by simpa [hmul])
  intro n hn_pos hn_even
  exact hP n hn_pos hn_even

end Goldbach.BankPieces.Cert.EvenEulerProductReduction
