import Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false

namespace Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage

open scoped BigOperators

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows

/-!
Reusable dyadic transport facts for the periodic-main compression route.

The nonzero complement after removing the q=5 row is dominated by dyadic
records `(q, 2q)` and `(2q, q)`.  This module promotes the one-variable
transport lemmas that were previously private inside generated tail
certificates, so later pair-level dyadic certificates can rewrite rather than
reprove this infrastructure record-by-record.
-/

theorem isEven_of_mem_EvenIn_window
    {X N : ℕ} (hN : N ∈ EvenIn X H) :
    Goldbach.Windows.IsEven N := by
  unfold EvenIn IccShift at hN
  exact (Finset.mem_filter.mp hN).2

theorem gcd_odd_two_mul_eq
    {n k : ℕ} (hnOdd : Odd n) :
    Nat.gcd n (2 * k) = Nat.gcd n k := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  have h := Nat.Coprime.gcd_mul_left_cancel (k := 2) (m := k) (n := n) hcop
  simpa [Nat.gcd_comm, Nat.mul_comm] using h

theorem totient_two_mul_eq_of_odd
    {n : ℕ} (hnOdd : Odd n) :
    Nat.totient (2 * n) = Nat.totient n := by
  have hcop : Nat.Coprime 2 n := by
    simpa [Nat.coprime_comm] using hnOdd.coprime_two_right
  rw [Nat.totient_mul hcop]
  norm_num

theorem ramanujanR_two_mul_eq_of_isEven_of_odd
    {n N : ℕ} (hnOdd : Odd n) (hNEven : Goldbach.Windows.IsEven N) :
    Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
      = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N := by
  have hnpos : 0 < n := hnOdd.pos
  rcases (even_iff_two_dvd).1 (Goldbach.Windows.even_of_isEven hNEven) with ⟨k, hk⟩
  subst hk
  set d : ℕ := Nat.gcd n k
  have hgcdn : Nat.gcd n (2 * k) = d := by
    simpa [d] using gcd_odd_two_mul_eq (n := n) (k := k) hnOdd
  have hgcd2n : Nat.gcd (2 * n) (2 * k) = 2 * d := by
    simpa [d, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Nat.gcd_mul_left 2 n k)
  have hdvd : d ∣ n := by
    simpa [d] using Nat.gcd_dvd_left n k
  have hdpos : 0 < d := by
    simpa [d] using Nat.gcd_pos_of_pos_left k hnpos
  have hdOdd : Odd d := by
    have hnotEven : ¬ Even d := by
      intro hdEven
      rcases hdvd with ⟨m, hm⟩
      rcases hdEven with ⟨c, hc⟩
      have hnEven : Even n := by
        refine ⟨c * m, ?_⟩
        rw [hm, hc]
        ring
      exact (Nat.not_even_iff_odd.mpr hnOdd) hnEven
    exact Nat.not_even_iff_odd.mp hnotEven
  have hquot : (2 * n) / (2 * d) = n / d := by
    apply Nat.div_eq_of_eq_mul_left (by positivity : 0 < 2 * d)
    calc
      2 * n = 2 * ((n / d) * d) := by rw [Nat.div_mul_cancel hdvd]
      _ = (n / d) * (2 * d) := by ring
  have hphi : Nat.totient (2 * d) = Nat.totient d := totient_two_mul_eq_of_odd hdOdd
  rw [ramanujanR_eq_moebius_mul_totient_gcd, ramanujanR_eq_moebius_mul_totient_gcd]
  rw [hgcd2n, hgcdn, hquot, hphi]

theorem ramanujanWindowAverage_two_mul_eq_of_odd
    {X n : ℕ} (hnOdd : Odd n) :
    ramanujanWindowAverage X (2 * n) = ramanujanWindowAverage X n := by
  unfold ramanujanWindowAverage
  refine congrArg ((((EvenIn X H).card : ℝ)⁻¹) * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro N hN
  exact ramanujanR_two_mul_eq_of_isEven_of_odd hnOdd (isEven_of_mem_EvenIn_window hN)

theorem centeredRamanujanObservable_two_mul_eq_of_odd
    {X n N : ℕ} (hnOdd : Odd n) (hN : N ∈ EvenIn X H) :
    centeredRamanujanObservable X (2 * n) N
      = centeredRamanujanObservable X n N := by
  calc
    centeredRamanujanObservable X (2 * n) N
      = Goldbach.AO_OffDiag.TailBlock.ramanujanR (2 * n) N
          - ramanujanWindowAverage X n := by
            simp [centeredRamanujanObservable, ramanujanWindowAverage_two_mul_eq_of_odd hnOdd]
    _ = Goldbach.AO_OffDiag.TailBlock.ramanujanR n N
          - ramanujanWindowAverage X n := by
            rw [ramanujanR_two_mul_eq_of_isEven_of_odd hnOdd (isEven_of_mem_EvenIn_window hN)]
    _ = centeredRamanujanObservable X n N := by
            rfl

theorem centeredRamanujanWindowEnergyRat_two_mul_eq_of_odd
    {X n : ℕ} (hnOdd : Odd n) :
    centeredRamanujanWindowEnergyRat X (2 * n)
      = centeredRamanujanWindowEnergyRat X n := by
  have hnle : 1 ≤ n := Nat.succ_le_of_lt hnOdd.pos
  have h2nle : 1 ≤ 2 * n := by omega
  have hreal :
      centeredRamanujanWindowEnergy X (2 * n)
        = centeredRamanujanWindowEnergy X n := by
    unfold centeredRamanujanWindowEnergy
    refine Finset.sum_congr rfl ?_
    intro N hN
    rw [centeredRamanujanObservable_two_mul_eq_of_odd hnOdd hN]
  have hcast :
      (centeredRamanujanWindowEnergyRat X (2 * n) : ℝ)
        = ((centeredRamanujanWindowEnergyRat X n : ℚ) : ℝ) := by
    rw [← centeredRamanujanWindowEnergy_eq_ratCast (X := X) (q := 2 * n) h2nle]
    rw [hreal]
    rw [centeredRamanujanWindowEnergy_eq_ratCast (X := X) (q := n) hnle]
  exact Rat.cast_inj.mp hcast

theorem surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat_two_mul_eq_of_odd
    {X n : ℕ} (hnOdd : Odd n) (hsq2n : Squarefree (2 * n)) :
    surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X (2 * n)
      = surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat X n := by
  have hsqn : Squarefree n := by
    exact hsq2n.squarefree_of_dvd ⟨2, by ring⟩
  unfold surrogateCenteredNormalizedSigmaTruncSummandWindowEnergyRat
  rw [centeredRamanujanWindowEnergyRat_two_mul_eq_of_odd hnOdd]
  unfold surrogateNormalizedSigmaTruncSummandCoeffRat
  simp [hsq2n, hsqn, totient_two_mul_eq_of_odd hnOdd]

end Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverage
