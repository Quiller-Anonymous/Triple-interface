import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.AO_OffDiag.TailBlock

namespace Goldbach.BankPieces.Cert.RamanujanOddCancellation

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.TailBlock

noncomputable section

private lemma squarefree_of_two_mul_squarefree {r : ℕ} (hsq : Squarefree (2 * r)) :
    Squarefree r :=
  hsq.squarefree_of_dvd (by simpa [Nat.mul_comm] using (dvd_mul_left r 2))

private lemma two_not_dvd_of_squarefree_two_mul {r : ℕ} (hsq : Squarefree (2 * r)) :
    ¬ 2 ∣ r := by
  intro h2r
  have h4 : 2 * 2 ∣ 2 * r := by
    rcases h2r with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp [hk, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hunit : IsUnit 2 := hsq 2 h4
  norm_num [Nat.isUnit_iff] at hunit

private lemma odd_of_squarefree_two_mul {r : ℕ} (hsq : Squarefree (2 * r)) :
    Odd r := by
  have hnot : ¬ Even r := by
    intro hr_even
    exact two_not_dvd_of_squarefree_two_mul hsq ((even_iff_two_dvd).mp hr_even)
  exact Nat.not_even_iff_odd.mp hnot

private lemma gcd_two_mul_odd_right {r N : ℕ} (hodd : Odd N) :
    Nat.gcd (2 * r) N = Nat.gcd r N := by
  have hcop : Nat.Coprime 2 N := by
    exact (Nat.coprime_two_right).2 hodd |>.symm
  have h :=
    Nat.Coprime.gcd_mul_left_cancel (k := 2) (m := r) (n := N) hcop
  simpa [Nat.mul_comm] using h

private lemma ramanujanZ_two_mul_eq_neg {r N : ℕ}
    (hodd : Odd N) (hsq : Squarefree (2 * r)) :
    TailBlock.ramanujanZ (2 * r) N = -TailBlock.ramanujanZ r N := by
  let d := Nat.gcd r N
  have hd_dvd_r : d ∣ r := by
    simpa [d] using Nat.gcd_dvd_left r N
  have hgcd :
      Nat.gcd (2 * r) N = d := by
    simpa [d] using gcd_two_mul_odd_right (r := r) (N := N) hodd
  have hcop2r : Nat.Coprime 2 r := (Nat.coprime_two_left).2 (odd_of_squarefree_two_mul hsq)
  have hcop2rd : Nat.Coprime 2 (r / d) := by
    exact hcop2r.of_dvd_right (Nat.div_dvd_of_dvd hd_dvd_r)
  have hdiv : (2 * r) / d = 2 * (r / d) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using (Nat.mul_div_assoc 2 hd_dvd_r)
  have hmu :
      (ArithmeticFunction.moebius ((2 * r) / d) : ℤ)
        = (ArithmeticFunction.moebius 2 : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := by
    have hg : Nat.gcd 2 (r / d) = 1 := hcop2rd.gcd_eq_one
    rw [hdiv]
    have hmul :
        ArithmeticFunction.moebius (2 * (r / d))
          = ArithmeticFunction.moebius 2 * ArithmeticFunction.moebius (r / d) :=
      (ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ))
        ArithmeticFunction.isMultiplicative_moebius hg)
    exact hmul
  have hmu2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 := by
    simpa using (ArithmeticFunction.moebius_apply_prime Nat.prime_two)
  have hmu' :
      (ArithmeticFunction.moebius ((2 * r) / d) : ℤ)
        = -(ArithmeticFunction.moebius (r / d) : ℤ) := by
    calc
      (ArithmeticFunction.moebius ((2 * r) / d) : ℤ)
          = (ArithmeticFunction.moebius 2 : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := hmu
      _ = (-1) * (ArithmeticFunction.moebius (r / d) : ℤ) := by simpa [hmu2]
      _ = -(ArithmeticFunction.moebius (r / d) : ℤ) := by simp
  have hleft :
      TailBlock.ramanujanZ (2 * r) N
        = (ArithmeticFunction.moebius ((2 * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := by
    simp [TailBlock.ramanujanZ, hgcd, d]
  have hright :
      TailBlock.ramanujanZ r N
        = (ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d) := by
    simp [TailBlock.ramanujanZ, d]
  calc
    TailBlock.ramanujanZ (2 * r) N
        = (ArithmeticFunction.moebius ((2 * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := hleft
    _ = (-(ArithmeticFunction.moebius (r / d) : ℤ)) * Int.ofNat (Nat.totient d) := by simp [hmu']
    _ = -((ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d)) := by simp [neg_mul]
    _ = -TailBlock.ramanujanZ r N := by simpa [hright]

/--
For odd `N`, the Ramanujan-series summands for `q = r` and `q = 2r` cancel exactly whenever
`2*r` is squarefree.
-/
theorem sigmaTerm_two_mul_eq_neg {r N : ℕ}
    (hodd : Odd N) (hsq : Squarefree (2 * r)) :
    SigmaTailReindex.sigmaTerm (2 * r) N = -SigmaTailReindex.sigmaTerm r N := by
  have hsq_r : Squarefree r := squarefree_of_two_mul_squarefree hsq
  have hodd_r : Odd r := odd_of_squarefree_two_mul hsq
  have hcop : Nat.Coprime 2 r := ((Nat.coprime_two_right).2 hodd_r).symm
  have hphi : Nat.totient (2 * r) = Nat.totient r := by
    simpa using (Nat.totient_mul hcop)
  have hmu2r : AO_OffDiag.muSq (2 * r) = 1 := by
    simp [AO_OffDiag.muSq, hsq]
  have hmur : AO_OffDiag.muSq r = 1 := by
    simp [AO_OffDiag.muSq, hsq_r]
  have hRam :
      TailBlock.ramanujanR (2 * r) N = -TailBlock.ramanujanR r N := by
    unfold TailBlock.ramanujanR
    exact_mod_cast ramanujanZ_two_mul_eq_neg (r := r) (N := N) hodd hsq
  unfold SigmaTailReindex.sigmaTerm
  simp [hmu2r, hmur, hphi, hRam]

private lemma not_squarefree_four_mul (k : ℕ) : ¬ Squarefree (4 * k) := by
  intro hsq
  have h4 : 2 * 2 ∣ 4 * k := by
    refine ⟨k, ?_⟩
    ring
  have hunit : IsUnit 2 := hsq 2 h4
  norm_num [Nat.isUnit_iff] at hunit

/-- The `q = 4k` Ramanujan-series summands vanish identically. -/
theorem sigmaTerm_four_mul_eq_zero {k N : ℕ} :
    SigmaTailReindex.sigmaTerm (4 * k) N = 0 := by
  exact SigmaTailReindex.sigmaTerm_eq_zero_of_not_squarefree
    (q := 4 * k) (N := N) (not_squarefree_four_mul k)

/--
For odd `N`, the `q = 4k+2` and `q = 2k+1` Ramanujan-series summands cancel.

This is the unconditional pointwise form used in the global odd-zero series argument.
-/
theorem sigmaTerm_four_mul_add_two_eq_neg {k N : ℕ} (hodd : Odd N) :
    SigmaTailReindex.sigmaTerm (4 * k + 2) N = -SigmaTailReindex.sigmaTerm (2 * k + 1) N := by
  have hsq_or : Squarefree (2 * (2 * k + 1)) ∨ ¬ Squarefree (2 * (2 * k + 1)) := em _
  rcases hsq_or with hsq | hnsq
  · simpa [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using sigmaTerm_two_mul_eq_neg (r := 2 * k + 1) (N := N) hodd hsq
  · have hzero_left :
        SigmaTailReindex.sigmaTerm (4 * k + 2) N = 0 := by
      have : ¬ Squarefree (4 * k + 2) := by
        simpa [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hnsq
      exact SigmaTailReindex.sigmaTerm_eq_zero_of_not_squarefree
        (q := 4 * k + 2) (N := N) this
    have hsq_odd : ¬ Squarefree (2 * k + 1) := by
      intro hsq_odd
      have hodd_r : Odd (2 * k + 1) := by
        exact Nat.not_even_iff_odd.mp (by simp)
      have hcop : Nat.Coprime 2 (2 * k + 1) := (Nat.coprime_two_left).2 hodd_r
      have hsq_two_mul : Squarefree (2 * (2 * k + 1)) := by
        exact (Nat.squarefree_mul hcop).2 ⟨by simpa using Nat.prime_two.squarefree, hsq_odd⟩
      exact hnsq hsq_two_mul
    have hzero_right :
        SigmaTailReindex.sigmaTerm (2 * k + 1) N = 0 := by
      exact SigmaTailReindex.sigmaTerm_eq_zero_of_not_squarefree
        (q := 2 * k + 1) (N := N) hsq_odd
    simp [hzero_left, hzero_right]

end

end Goldbach.BankPieces.Cert.RamanujanOddCancellation
