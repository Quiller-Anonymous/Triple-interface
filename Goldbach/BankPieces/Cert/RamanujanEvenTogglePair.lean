import Goldbach.AO_OffDiag.SigmaTailReindex
import Goldbach.AO_OffDiag.SigmaTailReindexFun
import Goldbach.SingularSeries

namespace Goldbach.BankPieces.Cert.RamanujanEvenTogglePair

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.SigmaTailReindex
open Goldbach.AO_OffDiag.SigmaTailReindexFun
open Goldbach.AO_OffDiag.TailBlock

open scoped ArithmeticFunction.Moebius

noncomputable section

private lemma sigmaTermFun_eq_sigmaTerm (q N : ℕ) :
    SigmaTailReindexFun.sigmaTerm q N = SigmaTailReindex.sigmaTerm q N := rfl

private lemma sigmaTerm_mul_prime_input_eq
    {q m p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    SigmaTailReindex.sigmaTerm q (p * m) = SigmaTailReindex.sigmaTerm q m := by
  by_cases hqSq : Squarefree q
  · have hpCq : Nat.Coprime p q := (hp.coprime_iff_not_dvd).2 hpq
    have hg :
        Nat.gcd q (p * m) = Nat.gcd q m := by
      have hg' : Nat.gcd (p * m) q = Nat.gcd m q := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpCq.gcd_mul_left_cancel m
      simpa [Nat.gcd_comm] using hg'
    have hRamZ : TailBlock.ramanujanZ q (p * m) = TailBlock.ramanujanZ q m := by
      simp [TailBlock.ramanujanZ, hg]
    have hRamR : TailBlock.ramanujanR q (p * m) = TailBlock.ramanujanR q m := by
      simpa [TailBlock.ramanujanR] using congrArg (fun z : ℤ => (z : ℝ)) hRamZ
    simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hqSq, hRamR]
  · simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hqSq]

private lemma ramanujanZ_mul_prime_eq_neg
    {r m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hpr : ¬ p ∣ r) :
    TailBlock.ramanujanZ (p * r) m = -TailBlock.ramanujanZ r m := by
  set d : ℕ := Nat.gcd r m with hd
  have hpCm : Nat.Coprime p m := (hp.coprime_iff_not_dvd).2 hpm
  have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr
  have hd_dvd_r : d ∣ r := by simpa [hd] using Nat.gcd_dvd_left r m
  have hgcd :
      Nat.gcd (p * r) m = d := by
    have hg' : Nat.gcd (p * r) m = Nat.gcd r m := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpCm.gcd_mul_left_cancel r
    simpa [d, hd] using hg'
  have hmulDiv : (p * r) / d = p * (r / d) := by
    simpa [Nat.mul_assoc] using (Nat.mul_div_assoc p hd_dvd_r)
  have hpCrd : Nat.Coprime p (r / d) := hpCr.of_dvd_right (Nat.div_dvd_of_dvd hd_dvd_r)
  have hmu :
      (ArithmeticFunction.moebius ((p * r) / d) : ℤ)
        = (ArithmeticFunction.moebius p : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := by
    have hg : Nat.gcd p (r / d) = 1 := hpCrd.gcd_eq_one
    rw [hmulDiv]
    exact
      (ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
        (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ))
        ArithmeticFunction.isMultiplicative_moebius hg)
  have hmu_p : (ArithmeticFunction.moebius p : ℤ) = -1 := by
    simpa using (ArithmeticFunction.moebius_apply_prime hp)
  have hmu' :
      (ArithmeticFunction.moebius ((p * r) / d) : ℤ)
        = -(ArithmeticFunction.moebius (r / d) : ℤ) := by
    calc
      (ArithmeticFunction.moebius ((p * r) / d) : ℤ)
          = (ArithmeticFunction.moebius p : ℤ) * (ArithmeticFunction.moebius (r / d) : ℤ) := hmu
      _ = (-1) * (ArithmeticFunction.moebius (r / d) : ℤ) := by simpa [hmu_p]
      _ = -(ArithmeticFunction.moebius (r / d) : ℤ) := by simp
  have hleft :
      TailBlock.ramanujanZ (p * r) m
        = (ArithmeticFunction.moebius ((p * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := by
    simp [TailBlock.ramanujanZ, hgcd, d, hd]
  have hright :
      TailBlock.ramanujanZ r m
        = (ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d) := by
    simp [TailBlock.ramanujanZ, d, hd]
  calc
    TailBlock.ramanujanZ (p * r) m
        = (ArithmeticFunction.moebius ((p * r) / d) : ℤ) * Int.ofNat (Nat.totient d) := hleft
    _ = (-(ArithmeticFunction.moebius (r / d) : ℤ)) * Int.ofNat (Nat.totient d) := by simp [hmu']
    _ = -((ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d)) := by simp [neg_mul]
    _ = -TailBlock.ramanujanZ r m := by simpa [hright]

private lemma ramanujanZ_mul_prime_input_eq_scale
    {r m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (hpr : ¬ p ∣ r) :
    TailBlock.ramanujanZ (p * r) (p * m) = (p - 1 : ℕ) * TailBlock.ramanujanZ r m := by
  set d : ℕ := Nat.gcd r m with hd
  have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr
  have hd_dvd_r : d ∣ r := by simpa [hd] using Nat.gcd_dvd_left r m
  have hgcd : Nat.gcd (p * r) (p * m) = p * d := by
    simpa [d, hd, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.gcd_mul_left p r m
  have hpCd : Nat.Coprime p d := hpCr.of_dvd_right hd_dvd_r
  have hphi : Nat.totient (p * d) = (p - 1) * Nat.totient d := by
    simpa [Nat.totient_prime hp] using (Nat.totient_mul hpCd)
  have hdiv : (p * r) / (p * d) = r / d := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_div_mul_left r d hp.pos
  calc
    TailBlock.ramanujanZ (p * r) (p * m)
        = (ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient (p * d)) := by
            simp [TailBlock.ramanujanZ, hgcd, d, hd, hdiv]
    _ = (ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat ((p - 1) * Nat.totient d) := by
          rw [hphi]
    _ = ((p - 1 : ℕ) : ℤ) * ((ArithmeticFunction.moebius (r / d) : ℤ) * Int.ofNat (Nat.totient d)) := by
          simp [Int.ofNat_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = (p - 1 : ℕ) * TailBlock.ramanujanZ r m := by
          simp [TailBlock.ramanujanZ, d, hd, Int.ofNat_mul, mul_assoc, mul_left_comm, mul_comm]

private lemma sigmaTerm_mul_prime_eq_neg_scale
    {r m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) (hpr : ¬ p ∣ r) :
    SigmaTailReindex.sigmaTerm (p * r) m
      = -((1 : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2)) * SigmaTailReindex.sigmaTerm r m := by
  by_cases hsq_r : Squarefree r
  · have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr
    have hsq_pr : Squarefree (p * r) := by
      exact (Nat.squarefree_mul hpCr).2 ⟨by simpa using hp.squarefree, hsq_r⟩
    have hphi : Nat.totient (p * r) = Nat.totient p * Nat.totient r := Nat.totient_mul hpCr
    have hphi_p : Nat.totient p = p - 1 := Nat.totient_prime hp
    have hRamZ : TailBlock.ramanujanZ (p * r) m = -TailBlock.ramanujanZ r m :=
      ramanujanZ_mul_prime_eq_neg hp hpm hpr
    have hRamR : TailBlock.ramanujanR (p * r) m = -TailBlock.ramanujanR r m := by
      dsimp [TailBlock.ramanujanR]
      simpa using congrArg (fun z : ℤ => (z : ℝ)) hRamZ
    have hphi_sq :
        ((Nat.totient (p * r) : ℝ) ^ 2)
          = (((p - 1 : ℕ) : ℝ) ^ 2) * ((Nat.totient r : ℝ) ^ 2) := by
      rw [hphi, hphi_p]
      norm_num [pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hp1 : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
    have hr0 : r ≠ 0 := hsq_r.ne_zero
    have hphi_r0 : ((Nat.totient r : ℝ) ^ 2) ≠ 0 := by
      have hphi_r_pos : 0 < Nat.totient r := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr0)
      positivity
    calc
      SigmaTailReindex.sigmaTerm (p * r) m
          = (1 : ℝ)
              * (1 / ((((p - 1 : ℕ) : ℝ) ^ 2) * ((Nat.totient r : ℝ) ^ 2)))
              * (-TailBlock.ramanujanR r m) := by
                simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hsq_pr, hRamR, hphi_sq]
      _ = -((1 : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2))
            * ((1 / ((Nat.totient r : ℝ) ^ 2)) * TailBlock.ramanujanR r m) := by
              field_simp [hp1, hphi_r0]
      _ = -((1 : ℝ) / (((p - 1 : ℕ) : ℝ) ^ 2)) * SigmaTailReindex.sigmaTerm r m := by
            simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hsq_r, mul_assoc, mul_left_comm,
              mul_comm]
  · have hsq_pr : ¬ Squarefree (p * r) := by
      intro hsq_pr
      exact hsq_r (hsq_pr.squarefree_of_dvd (by simpa [Nat.mul_comm] using (dvd_mul_left r p)))
    simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hsq_r, hsq_pr]

private lemma sigmaTerm_mul_prime_input_eq_inv_scale
    {r m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) (hpr : ¬ p ∣ r) :
    SigmaTailReindex.sigmaTerm (p * r) (p * m)
      = ((1 : ℝ) / ((p - 1 : ℕ) : ℝ)) * SigmaTailReindex.sigmaTerm r m := by
  by_cases hsq_r : Squarefree r
  · have hpCr : Nat.Coprime p r := (hp.coprime_iff_not_dvd).2 hpr
    have hsq_pr : Squarefree (p * r) := by
      exact (Nat.squarefree_mul hpCr).2 ⟨by simpa using hp.squarefree, hsq_r⟩
    have hphi : Nat.totient (p * r) = Nat.totient p * Nat.totient r := Nat.totient_mul hpCr
    have hphi_p : Nat.totient p = p - 1 := Nat.totient_prime hp
    have hRamZ :
        TailBlock.ramanujanZ (p * r) (p * m) = (p - 1 : ℕ) * TailBlock.ramanujanZ r m :=
      ramanujanZ_mul_prime_input_eq_scale hp hpm hpr
    have hRamR :
        TailBlock.ramanujanR (p * r) (p * m) = ((p - 1 : ℕ) : ℝ) * TailBlock.ramanujanR r m := by
      dsimp [TailBlock.ramanujanR]
      simpa [Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hRamZ
    have hphi_sq :
        ((Nat.totient (p * r) : ℝ) ^ 2)
          = (((p - 1 : ℕ) : ℝ) ^ 2) * ((Nat.totient r : ℝ) ^ 2) := by
      rw [hphi, hphi_p]
      norm_num [pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hp1 : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
    have hr0 : r ≠ 0 := hsq_r.ne_zero
    have hphi_r0 : ((Nat.totient r : ℝ) ^ 2) ≠ 0 := by
      have hphi_r_pos : 0 < Nat.totient r := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr0)
      positivity
    calc
      SigmaTailReindex.sigmaTerm (p * r) (p * m)
          = (1 : ℝ)
              * (1 / ((((p - 1 : ℕ) : ℝ) ^ 2) * ((Nat.totient r : ℝ) ^ 2)))
              * (((p - 1 : ℕ) : ℝ) * TailBlock.ramanujanR r m) := by
                simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hsq_pr, hRamR, hphi_sq]
      _ = ((1 : ℝ) / ((p - 1 : ℕ) : ℝ))
            * ((1 / ((Nat.totient r : ℝ) ^ 2)) * TailBlock.ramanujanR r m) := by
              field_simp [hp1, hphi_r0]
      _ = ((1 : ℝ) / ((p - 1 : ℕ) : ℝ)) * SigmaTailReindex.sigmaTerm r m := by
            simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hsq_r, mul_assoc, mul_left_comm,
              mul_comm]
  · have hsq_pr : ¬ Squarefree (p * r) := by
      intro hsq_pr
      exact hsq_r (hsq_pr.squarefree_of_dvd (by simpa [Nat.mul_comm] using (dvd_mul_left r p)))
    simp [SigmaTailReindex.sigmaTerm, AO_OffDiag.muSq, hsq_r, hsq_pr]

/--
Pairwise fresh-prime toggle identity for Ramanujan-series summands.

This is the arithmetic core needed for the remaining even-input toggle law of the full Ramanujan
series.
-/
theorem sigmaTerm_pair_toggle
    {r m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) (hpr : ¬ p ∣ r) :
    SigmaTailReindexFun.sigmaTerm r (p * m) + SigmaTailReindexFun.sigmaTerm (p * r) (p * m)
      =
    Goldbach.Singular.oddFactor p
      * (SigmaTailReindexFun.sigmaTerm r m + SigmaTailReindexFun.sigmaTerm (p * r) m) := by
  rw [sigmaTermFun_eq_sigmaTerm, sigmaTermFun_eq_sigmaTerm, sigmaTermFun_eq_sigmaTerm, sigmaTermFun_eq_sigmaTerm]
  rw [sigmaTerm_mul_prime_input_eq hp hpr, sigmaTerm_mul_prime_input_eq_inv_scale hp hp2 hpm hpr,
    sigmaTerm_mul_prime_eq_neg_scale hp hp2 hpm hpr]
  have hpden : (((p - 2 : ℕ) : ℝ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt (lt_of_le_of_ne hp.two_le (by symm; exact hp2))
  have hp1 : (((p - 1 : ℕ) : ℝ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hp.one_lt
  have hp_cast_sub_one : (((p - 1 : ℕ) : ℝ) : ℝ) = (p : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub hp.one_le
  have hp_cast_sub_two : (((p - 2 : ℕ) : ℝ) : ℝ) = (p : ℝ) - 2 := by
    exact_mod_cast Nat.cast_sub hp.two_le
  have hp1R : (p : ℝ) - 1 ≠ 0 := by
    have hp1pos : (0 : ℝ) < (((p - 1 : ℕ) : ℝ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
    simpa [hp_cast_sub_one] using ne_of_gt hp1pos
  have hpdenR : (p : ℝ) - 2 ≠ 0 := by
    have hpdenpos : (0 : ℝ) < (((p - 2 : ℕ) : ℝ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt (lt_of_le_of_ne hp.two_le (by symm; exact hp2))
    simpa [hp_cast_sub_two] using ne_of_gt hpdenpos
  have hscalar :
      (1 : ℝ) + (1 / ((p - 1 : ℕ) : ℝ))
        = Goldbach.Singular.oddFactor p
            * ((1 : ℝ) - (1 / (((p - 1 : ℕ) : ℝ) ^ 2))) := by
    have hleft :
        (1 : ℝ) + (1 / ((p - 1 : ℕ) : ℝ)) = (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
      have hunit :
          (((p - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) = (1 : ℝ) := by
        field_simp [hp1]
      calc
        (1 : ℝ) + (1 / ((p - 1 : ℕ) : ℝ))
            = (((p - 1 : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ)) + (1 / ((p - 1 : ℕ) : ℝ)) := by
                rw [hunit]
        _ = ((((p - 1 : ℕ) : ℝ) + 1) / ((p - 1 : ℕ) : ℝ)) := by ring
        _ = (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
              congr 1
              norm_num [Nat.cast_sub hp.one_le]
    have hright :
        Goldbach.Singular.oddFactor p
          * ((1 : ℝ) - (1 / (((p - 1 : ℕ) : ℝ) ^ 2)))
            = (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
      rw [Goldbach.Singular.oddFactor, hp_cast_sub_one]
      field_simp [hp1R, hpdenR]
      ring
    rw [hleft, hright]
  calc
    SigmaTailReindex.sigmaTerm r m
        + (1 / ((p - 1 : ℕ) : ℝ)) * SigmaTailReindex.sigmaTerm r m
        = ((1 : ℝ) + (1 / ((p - 1 : ℕ) : ℝ))) * SigmaTailReindex.sigmaTerm r m := by ring
    _ = (Goldbach.Singular.oddFactor p
            * ((1 : ℝ) - (1 / (((p - 1 : ℕ) : ℝ) ^ 2))))
          * SigmaTailReindex.sigmaTerm r m := by rw [hscalar]
    _ = Goldbach.Singular.oddFactor p
          * (((1 : ℝ) - (1 / (((p - 1 : ℕ) : ℝ) ^ 2))) * SigmaTailReindex.sigmaTerm r m) := by
            ring
    _ = Goldbach.Singular.oddFactor p
          * (SigmaTailReindex.sigmaTerm r m
              + (-(1 / (((p - 1 : ℕ) : ℝ) ^ 2))) * SigmaTailReindex.sigmaTerm r m) := by
            ring

end

end Goldbach.BankPieces.Cert.RamanujanEvenTogglePair
