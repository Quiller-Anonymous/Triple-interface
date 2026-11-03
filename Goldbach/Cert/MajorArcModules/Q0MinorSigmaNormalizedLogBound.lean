import Goldbach.SingularSeriesExtras
import Goldbach.BankParams

/-!
An elementary logarithmic upper bound for the normalized singular series.

The product of `(p - 1) / (p - 2)` over any finite set of distinct integers at
least three is at most the cardinality plus one.  For odd prime divisors of `N`,
the product of the primes divides `N`, so their cardinality is at most `log N`.
No estimate for the distribution of primes is used.
-/

namespace Goldbach.Cert.MajorArcModules.Q0MinorSigmaNormalizedLogBound

open scoped BigOperators
open Goldbach.Singular

noncomputable section

lemma prod_oddFactor_le_card_add_one (s : Finset ℕ)
    (hs : ∀ p ∈ s, 3 ≤ p) :
    (∏ p ∈ s, oddFactor p) ≤ (s.card : ℝ) + 1 := by
  classical
  revert hs
  induction s using Finset.induction_on_max with
  | h0 => intro hs; simp
  | @step a s hmax ih =>
      intro hs
      have ha : 3 ≤ a := hs a (Finset.mem_insert_self a s)
      have hrest : ∀ p ∈ s, 3 ≤ p :=
        fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hnot : a ∉ s := by
        intro ha_mem
        exact (lt_irrefl a) (hmax a ha_mem)
      have hsub : s ⊆ Finset.Ico 3 a := by
        intro p hp
        exact Finset.mem_Ico.mpr ⟨hrest p hp, hmax p hp⟩
      have hcard : s.card + 3 ≤ a := by
        have hh : s.card ≤ a - 3 := by
          simpa using Finset.card_le_card hsub
        omega
      have hcardR : (s.card : ℝ) + 3 ≤ (a : ℝ) := by exact_mod_cast hcard
      have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hden : (0 : ℝ) < (a : ℝ) - 2 := by linarith
      have hfactor_nonneg : 0 ≤ oddFactor a := by
        unfold oddFactor
        exact div_nonneg (by linarith) hden.le
      have hfactor : oddFactor a * ((s.card : ℝ) + 1) ≤ (s.card : ℝ) + 2 := by
        unfold oddFactor
        rw [div_mul_eq_mul_div₀, div_le_iff₀ hden]
        nlinarith
      rw [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
      push_cast
      exact (mul_le_mul_of_nonneg_left (ih hrest) hfactor_nonneg).trans (by
        simpa only [add_assoc, one_add_one_eq_two] using hfactor)

lemma oddPrimeSupport_card_le_log {N : ℕ} (hN : N ≠ 0) :
    ((oddPrimeSupport N).card : ℝ) ≤ Real.log (N : ℝ) := by
  have hthree : ∀ p ∈ oddPrimeSupport N, 3 ≤ p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hprime, hne⟩
    have htwo := hprime.two_le
    omega
  have hsub : oddPrimeSupport N ⊆ N.primeFactors := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp_div, hp_odd⟩
    exact Nat.mem_primeFactors.mpr ⟨hp_odd.1, Nat.dvd_of_mem_divisors hp_div, hN⟩
  have hprod_dvd : (∏ p ∈ oddPrimeSupport N, p) ∣ N :=
    dvd_trans
      (Finset.prod_dvd_prod_of_subset (oddPrimeSupport N) N.primeFactors id hsub)
      (Nat.prod_primeFactors_dvd N)
  have hprod_le : (∏ p ∈ oddPrimeSupport N, p) ≤ N :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hprod_dvd
  have hpow_le : 3 ^ (oddPrimeSupport N).card ≤ N := by
    calc
      3 ^ (oddPrimeSupport N).card = ∏ _p ∈ oddPrimeSupport N, 3 := by simp
      _ ≤ ∏ p ∈ oddPrimeSupport N, p := Finset.prod_le_prod' hthree
      _ ≤ N := hprod_le
  have hpowR : (3 : ℝ) ^ (oddPrimeSupport N).card ≤ (N : ℝ) := by
    exact_mod_cast hpow_le
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 3) _) hpowR
  rw [Real.log_pow] at hlog
  have hexp : Real.exp (1 : ℝ) ≤ 3 := by
    linarith [Real.exp_one_lt_d9]
  have hlogthree : (1 : ℝ) ≤ Real.log 3 := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) hexp
  have hcard_nonneg : (0 : ℝ) ≤ ((oddPrimeSupport N).card : ℝ) := by positivity
  nlinarith

lemma prod_oddFactor_le_one_add_log {N : ℕ} (hN : N ≠ 0) :
    (∏ p ∈ oddPrimeSupport N, oddFactor p) ≤ 1 + Real.log (N : ℝ) := by
  have hthree : ∀ p ∈ oddPrimeSupport N, 3 ≤ p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hprime, hne⟩
    have htwo := hprime.two_le
    omega
  have hprod := prod_oddFactor_le_card_add_one (oddPrimeSupport N) hthree
  have hcard := oddPrimeSupport_card_le_log hN
  linarith

/-- The normalized singular series has an elementary uniform logarithmic bound. -/
theorem abs_normalized_sigma_le_two_mul_log (C : C2Const) {N : ℕ}
    (hN : Goldbach.BankParams.X0 ≤ N) :
    |sigma C N / (2 * C.C2)| ≤ 2 * Real.log (N : ℝ) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < Goldbach.BankParams.X0) hN
  have hNthree : (3 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (le_trans (by decide : 3 ≤ Goldbach.BankParams.X0) hN)
  have hexp : Real.exp (1 : ℝ) ≤ (N : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hlog : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (N : ℝ) := Real.log_le_log (Real.exp_pos 1) hexp
  by_cases he : Even N
  · rw [sigma_even_expand he]
    have hC : (2 : ℝ) * C.C2 ≠ 0 := mul_ne_zero (by norm_num) C.pos.ne'
    rw [mul_div_cancel_left₀ _ hC]
    have hprod_nonneg : (0 : ℝ) ≤ ∏ p ∈ oddPrimeSupport N, oddFactor p :=
      le_trans (by norm_num) (prod_oddFactor_ge_one N)
    rw [abs_of_nonneg hprod_nonneg]
    have hprod := prod_oddFactor_le_one_add_log hNpos.ne'
    linarith
  · simpa [sigma, he] using (show (0 : ℝ) ≤ 2 * Real.log (N : ℝ) by linarith)

end

end Goldbach.Cert.MajorArcModules.Q0MinorSigmaNormalizedLogBound
