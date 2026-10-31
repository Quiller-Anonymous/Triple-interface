import Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion
import Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds

/-! Exact grouping of odd and twice-odd moduli on even arguments. -/

namespace Goldbach.Cert.MajorArcModules.Q0SigmaTruncEvenDivisor

open scoped BigOperators ArithmeticFunction.Moebius
open Goldbach.AO_OffDiag.TailBlock
open Goldbach.Cert.MajorArcModules.Q0RamanujanDivisorExpansion
open Goldbach.Cert.MajorArcModules.Q0SigmaTruncScalarBounds

noncomputable section

theorem sum_Icc_odd_even (Q : ℕ) (f : ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, f q) =
      (∑ r ∈ Finset.Icc 1 Q, if Odd r then f r else 0) +
      ∑ r ∈ Finset.Icc 1 Q, if 2 * r ≤ Q then f (2 * r) else 0 := by
  classical
  have heven :
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => ¬ Odd q), f q) =
        ∑ r ∈ (Finset.Icc 1 Q).filter (fun r => 2 * r ≤ Q), f (2 * r) := by
    symm
    apply Finset.sum_bij (fun r hr => 2 * r)
    · intro r hr
      obtain ⟨hr, hrQ⟩ := Finset.mem_filter.mp hr
      obtain ⟨hrpos, hrle⟩ := Finset.mem_Icc.mp hr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, hrQ⟩, ?_⟩
      exact Nat.not_odd_iff_even.mpr (by exact ⟨r, by omega⟩)
    · intro r hr s hs hrs
      omega
    · intro q hq
      obtain ⟨hq, hodd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqpos, hqle⟩ := Finset.mem_Icc.mp hq
      obtain ⟨r, hr⟩ := Nat.not_odd_iff_even.mp hodd
      refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
        by omega⟩, by omega⟩
    · intro r hr
      rfl
  calc
    _ = (∑ r ∈ (Finset.Icc 1 Q).filter Odd, f r) +
        ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => ¬ Odd q), f q :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ = _ := by rw [heven, Finset.sum_filter, Finset.sum_filter]

theorem sigma_trunc_Q0_even_eq_oddWeightRat (n : ℕ) :
    sigma_trunc_Q0 (2 * n) =
      ∑ r ∈ Finset.Icc 1 cutoff, (oddWeightRat r : ℝ) * ramanujanR r n := by
  let f : ℕ → ℝ := fun q =>
    muSq q * (1 / (Nat.totient q : ℝ) ^ 2) * ramanujanR q (2 * n)
  change (∑ q ∈ Finset.Icc 1 cutoff, f q) = _
  rw [sum_Icc_odd_even, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [oddWeightRat_cast]
  by_cases hodd : Odd r
  · have hphi : Nat.totient (2 * r) = Nat.totient r := by
      rw [Nat.totient_mul hodd.coprime_two_left]
      norm_num
    have hsq : Squarefree (2 * r) ↔ Squarefree r := by
      rw [Nat.squarefree_mul hodd.coprime_two_left]
      simp [Nat.prime_two.squarefree]
    by_cases hsf : Squarefree r <;> by_cases hcut : 2 * r ≤ cutoff <;>
      simp [f, hodd, hsf, hcut, muSq, hsq, hphi,
        ramanujanR_two_mul_argument r n hodd,
        ramanujanR_two_mul_modulus_two_mul_argument r n hodd] <;> ring
  · have hsf2 : ¬ Squarefree (2 * r) := by
      intro h
      exact hodd (Nat.coprime_of_squarefree_mul h).odd_of_left
    simp [f, hodd, muSq, hsf2]

/-- The exact rational divisor coefficients used by the scalar certificate describe the
existing singular-series truncation at every even argument. -/
theorem sigma_trunc_Q0_even_eq_divisorCoefficientRat (n : ℕ) :
    sigma_trunc_Q0 (2 * n) =
      ∑ d ∈ Finset.Icc 1 cutoff, if d ∣ n then (divisorCoefficientRat d : ℝ) else 0 := by
  rw [sigma_trunc_Q0_even_eq_oddWeightRat,
    sum_ramanujanR_eq_sum_divisorCoefficient cutoff n (fun r => (oddWeightRat r : ℝ))]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [divisorCoefficientRat_cast]
    rfl
  · intro r hr hsf
    simp [oddWeightRat, hsf]

end
end Goldbach.Cert.MajorArcModules.Q0SigmaTruncEvenDivisor
