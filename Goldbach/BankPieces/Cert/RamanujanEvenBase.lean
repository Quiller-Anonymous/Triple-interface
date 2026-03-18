import Goldbach.BankPieces.Cert.RamanujanOddZero

namespace Goldbach.BankPieces.Cert.RamanujanEvenBase

open Goldbach
open Goldbach.AO_OffDiag
open Goldbach.AO_OffDiag.SigmaTailReindex
open Goldbach.AO_OffDiag.SigmaTailReindexFun

noncomputable section

/-- `N` has no odd prime divisors. -/
def NoOddPrimeFactor (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ N

private lemma gcd_eq_gcd_two_of_noOddPrimeFactor
    {q N : ℕ} (hqSq : Squarefree q) (hN2 : 2 ∣ N) (hNo : NoOddPrimeFactor N) :
    Nat.gcd q N = Nat.gcd q 2 := by
  have hsq1 : Squarefree (Nat.gcd q N) :=
    hqSq.squarefree_of_dvd (Nat.gcd_dvd_left q N)
  have hsq2 : Squarefree (Nat.gcd q 2) :=
    Nat.squarefree_two.squarefree_of_dvd (Nat.gcd_dvd_right q 2)
  refine (Nat.Squarefree.ext_iff hsq1 hsq2).2 ?_
  intro r hr
  constructor
  · intro hr_d1
    have hrq : r ∣ q := dvd_trans hr_d1 (Nat.gcd_dvd_left q N)
    have hrN : r ∣ N := dvd_trans hr_d1 (Nat.gcd_dvd_right q N)
    by_cases hr2 : r = 2
    · subst hr2
      exact Nat.dvd_gcd hrq (by simp)
    · have h2lt : 2 < r := lt_of_le_of_ne hr.two_le (Ne.symm hr2)
      have hr_ne : ¬ r ∣ N := hNo r hr hr2
      exact (hr_ne hrN).elim
  · intro hr_d2
    have hr2 : r = 2 := by
      have hr_dvd_2 : r ∣ 2 := dvd_trans hr_d2 (Nat.gcd_dvd_right q 2)
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hr_dvd_2
    subst hr2
    have h2q : 2 ∣ q := dvd_trans hr_d2 (Nat.gcd_dvd_left q 2)
    exact Nat.dvd_gcd h2q hN2

private lemma sigmaTerm_eq_at2_of_noOddPrimeFactor
    {q N : ℕ} (hN2 : 2 ∣ N) (hNo : NoOddPrimeFactor N) :
    SigmaTailReindexFun.sigmaTerm q N = SigmaTailReindexFun.sigmaTerm q 2 := by
  by_cases hqSq : Squarefree q
  · have hgcd : Nat.gcd q N = Nat.gcd q 2 :=
      gcd_eq_gcd_two_of_noOddPrimeFactor hqSq hN2 hNo
    have hramZ :
        TailBlockFun.ramanujanZ q N = TailBlockFun.ramanujanZ q 2 := by
      simp [TailBlockFun.ramanujanZ, hgcd]
    have hramR :
        TailBlockFun.ramanujanR q N = TailBlockFun.ramanujanR q 2 := by
      simpa [TailBlockFun.ramanujanR] using congrArg (fun z : ℤ => (z : ℝ)) hramZ
    simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq, hqSq, hramR]
  · simp [SigmaTailReindexFun.sigmaTerm, AO_OffDiag.muSq, hqSq]

/-- The full Ramanujan series is constant on positive even inputs with no odd prime divisors. -/
  theorem sigmaSeriesRamanujan_eq_at2_of_noOddPrimeFactor
    {N : ℕ} (hN0 : N ≠ 0) (hEven : Even N) (hNo : NoOddPrimeFactor N) :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N
      = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan 2 := by
  have hN2 : 2 ∣ N := by simpa using (even_iff_two_dvd.mp hEven)
  rw [Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_eq_tsum_sigmaTerm hN0]
  rw [Goldbach.BankPieces.Cert.RamanujanOddZero.sigmaSeriesRamanujan_eq_tsum_sigmaTerm
    (by decide : (2 : ℕ) ≠ 0)]
  refine tsum_congr ?_
  intro q
  exact sigmaTerm_eq_at2_of_noOddPrimeFactor hN2 hNo

/-- Empty odd-prime support forces the canonical Ramanujan series to take its base value. -/
theorem sigmaSeriesRamanujan_eq_at2_of_support_empty
    {N : ℕ} (hN0 : N ≠ 0) (hEven : Even N) (hSupp : Goldbach.Singular.oddPrimeSupport N = ∅) :
    Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan N
      = Goldbach.BankPieces.Cert.SingularSeriesRamanujanBridge.sigmaSeriesRamanujan 2 := by
  apply sigmaSeriesRamanujan_eq_at2_of_noOddPrimeFactor hN0 hEven
  intro p hp hp2 hpN
  have hp_mem : p ∈ Goldbach.Singular.oddPrimeSupport N := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Nat.mem_divisors.mpr ⟨hpN, hN0⟩, hp, hp2⟩
  simpa [hSupp] using hp_mem

end
end Goldbach.BankPieces.Cert.RamanujanEvenBase
