import Goldbach.BankPieces.Cert.RamanujanOddZero

namespace Goldbach.BankPieces.Cert.RamanujanEvenSaturation

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.SigmaTailReindexFun
open Goldbach.AO_OffDiag.SigmaTailReindex

noncomputable section

private lemma gcd_mul_prime_eq_of_dvd
    {q m p : ℕ} (hqSq : Squarefree q) (hp : p.Prime) (hpm : p ∣ m) :
    Nat.gcd q (p * m) = Nat.gcd q m := by
  have hsq1 : Squarefree (Nat.gcd q (p * m)) :=
    hqSq.squarefree_of_dvd (Nat.gcd_dvd_left q (p * m))
  have hsq2 : Squarefree (Nat.gcd q m) :=
    hqSq.squarefree_of_dvd (Nat.gcd_dvd_left q m)
  refine (Nat.Squarefree.ext_iff hsq1 hsq2).2 ?_
  intro r hr
  constructor
  · intro hr_d1
    have hrq : r ∣ q := dvd_trans hr_d1 (Nat.gcd_dvd_left q (p * m))
    have hrpm : r ∣ p * m := dvd_trans hr_d1 (Nat.gcd_dvd_right q (p * m))
    have hrm : r ∣ m := by
      rcases hr.dvd_mul.mp hrpm with hrp | hrm
      · rw [(Nat.prime_dvd_prime_iff_eq hr hp).1 hrp]
        exact hpm
      · exact hrm
    exact Nat.dvd_gcd hrq hrm
  · intro hr_d2
    exact Nat.dvd_gcd
      (dvd_trans hr_d2 (Nat.gcd_dvd_left q m))
      (dvd_mul_of_dvd_right (dvd_trans hr_d2 (Nat.gcd_dvd_right q m)) p)

private lemma sigmaTerm_mul_prime_eq_of_dvd
    {q m p : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    SigmaTailReindexFun.sigmaTerm q (p * m) = SigmaTailReindexFun.sigmaTerm q m := by
  by_cases hqSq : Squarefree q
  · have hgcd : Nat.gcd q (p * m) = Nat.gcd q m :=
      gcd_mul_prime_eq_of_dvd hqSq hp hpm
    have hramZ :
        TailBlockFun.ramanujanZ q (p * m) = TailBlockFun.ramanujanZ q m := by
      simp [TailBlockFun.ramanujanZ, hgcd]
    have hramR :
        TailBlockFun.ramanujanR q (p * m) = TailBlockFun.ramanujanR q m := by
      simpa [TailBlockFun.ramanujanR] using congrArg (fun z : ℤ => (z : ℝ)) hramZ
    simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq, hqSq, hramR]
  · simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq, hqSq]

/--
Saturation law for the full Ramanujan series on positive even inputs:
adding another copy of an odd prime already dividing `m` leaves the series unchanged.
-/
theorem sigmaSeriesRamanujan_mul_prime_of_dvd
    {m p : ℕ} (hm0 : m ≠ 0) (hEven : Even m) (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ m) :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan (p * m)
      = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan m := by
  have hpm0 : p * m ≠ 0 := Nat.mul_ne_zero hp.ne_zero hm0
  rw [Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_eq_tsum_sigmaTerm hpm0]
  rw [Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_eq_tsum_sigmaTerm hm0]
  refine tsum_congr ?_
  intro q
  exact sigmaTerm_mul_prime_eq_of_dvd hp hpm

end

end Goldbach.BankPieces.Cert.RamanujanEvenSaturation
