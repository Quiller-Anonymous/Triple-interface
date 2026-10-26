import Goldbach.BG_Bank
import Goldbach.CoreTypes

/-!
# Exact broad-convolution endpoint for Route A

The fixed-width arithmetic bank cannot support a universal positive-mean theorem.  This module
states the corrected endpoint directly on the complete finite set of possible first primes in a
representation of `N`.

The main theorem is deliberately elementary: positivity of the broad von Mangoldt convolution is
equivalent to an actual Goldbach representation.  This removes both problematic inferences from
the old route:

* no fixed arithmetic support is assumed to contain a prime;
* positivity somewhere in a window is not used to infer positivity at its center.

The final certificate structure isolates the remaining analytic obligation.  To close Route A one
must decompose this exact pointwise convolution into a positive main term and a strictly smaller
error for every sufficiently large even `N`.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution

open scoped BigOperators

noncomputable section

/-- Every possible first component of a nontrivial prime pair summing to `N`. -/
def primeCandidateSupport (N : ℕ) : Finset ℕ :=
  Finset.Icc 2 (N - 2)

/--
The complete pointwise von Mangoldt convolution at `N`.

Unlike `BG_Bank.wX`, this sum does not discard any candidate representation of `N`.
-/
noncomputable def broadPrimePairConvolution (N : ℕ) : ℝ :=
  Finset.sum (primeCandidateSupport N) fun p =>
    Goldbach.BG_Bank.Λ p * Goldbach.BG_Bank.Λ (N - p)

/-- The broad convolution on the usual prime-counting scale. -/
noncomputable def normalizedBroadPrimePairConvolution (N : ℕ) : ℝ :=
  broadPrimePairConvolution N / (Real.log (N : ℝ)) ^ 2

lemma lambda_nonneg (n : ℕ) : 0 ≤ Goldbach.BG_Bank.Λ n := by
  unfold Goldbach.BG_Bank.Λ
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · exact le_rfl

lemma lambda_pos_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 < Goldbach.BG_Bank.Λ p := by
  have hpcast : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  simpa [Goldbach.BG_Bank.Λ, hp] using Real.log_pos hpcast

theorem broadPrimePairConvolution_nonneg (N : ℕ) :
    0 ≤ broadPrimePairConvolution N := by
  unfold broadPrimePairConvolution
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (lambda_nonneg p) (lambda_nonneg (N - p))

/--
Positivity of the complete pointwise convolution is exactly the existence of a Goldbach pair.

This is the endpoint bridge that a corrected analytic Route A must feed.  It is not itself an
analytic estimate: all remaining difficulty is in proving the convolution positive uniformly.
-/
theorem broadPrimePairConvolution_pos_iff_goldbachRep {N : ℕ} :
    0 < broadPrimePairConvolution N ↔ Goldbach.GoldbachRep N := by
  constructor
  · intro hpos
    have hpoint :
        ∀ p ∈ primeCandidateSupport N,
          0 ≤ Goldbach.BG_Bank.Λ p * Goldbach.BG_Bank.Λ (N - p) := by
      intro p hp
      exact mul_nonneg (lambda_nonneg p) (lambda_nonneg (N - p))
    have hwitness :
        ∃ p ∈ primeCandidateSupport N,
          0 < Goldbach.BG_Bank.Λ p * Goldbach.BG_Bank.Λ (N - p) := by
      exact (Finset.sum_pos_iff_of_nonneg hpoint).mp hpos
    rcases hwitness with ⟨p, hpSupport, hpProduct⟩
    have hpLambda : 0 < Goldbach.BG_Bank.Λ p := by
      by_contra hnot
      have hzero : Goldbach.BG_Bank.Λ p = 0 :=
        le_antisymm (le_of_not_gt hnot) (lambda_nonneg p)
      rw [hzero, zero_mul] at hpProduct
      exact (lt_irrefl 0) hpProduct
    have hqLambda : 0 < Goldbach.BG_Bank.Λ (N - p) := by
      by_contra hnot
      have hzero : Goldbach.BG_Bank.Λ (N - p) = 0 :=
        le_antisymm (le_of_not_gt hnot) (lambda_nonneg (N - p))
      rw [hzero, mul_zero] at hpProduct
      exact (lt_irrefl 0) hpProduct
    have hpPrime : Nat.Prime p := by
      by_contra hnot
      simp [Goldbach.BG_Bank.Λ, hnot] at hpLambda
    have hqPrime : Nat.Prime (N - p) := by
      by_contra hnot
      simp [Goldbach.BG_Bank.Λ, hnot] at hqLambda
    have hpN : p ≤ N := by
      have hpUpper := (Finset.mem_Icc.mp hpSupport).2
      exact le_trans hpUpper (Nat.sub_le N 2)
    exact ⟨p, N - p, hpPrime, hqPrime, Nat.add_sub_of_le hpN⟩
  · rintro ⟨p, q, hpPrime, hqPrime, hpq⟩
    have hpSupport : p ∈ primeCandidateSupport N := by
      rw [primeCandidateSupport, Finset.mem_Icc]
      constructor
      · exact hpPrime.two_le
      · have hqTwo := hqPrime.two_le
        omega
    have hqEq : N - p = q := by omega
    unfold broadPrimePairConvolution
    exact Finset.sum_pos'
      (fun n hn => mul_nonneg (lambda_nonneg n) (lambda_nonneg (N - n)))
      ⟨p, hpSupport, by
        rw [hqEq]
        exact mul_pos (lambda_pos_of_prime hpPrime) (lambda_pos_of_prime hqPrime)⟩

/-- Positivity of the raw convolution is also equivalent to positivity of the raw pair count. -/
theorem broadPrimePairConvolution_pos_iff_repCount_pos {N : ℕ} :
    0 < broadPrimePairConvolution N ↔ 0 < Goldbach.Rep.R N := by
  calc
    0 < broadPrimePairConvolution N ↔ Goldbach.GoldbachRep N :=
      broadPrimePairConvolution_pos_iff_goldbachRep
    _ ↔ 0 < Goldbach.Rep.R N := by
      simpa [Goldbach.GoldbachRep, Goldbach.Base.GoldbachRep] using
        (Goldbach.Rep.R_pos_iff_exists_pair (N := N)).symm

theorem normalizedBroadPrimePairConvolution_pos_iff_goldbachRep
    {N : ℕ} (hN : 2 ≤ N) :
    0 < normalizedBroadPrimePairConvolution N ↔ Goldbach.GoldbachRep N := by
  have hcast : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hcast
  have hden : 0 < (Real.log (N : ℝ)) ^ 2 := sq_pos_of_pos hlog
  have hscale : 0 < ((Real.log (N : ℝ)) ^ 2)⁻¹ := inv_pos.mpr hden
  rw [normalizedBroadPrimePairConvolution, div_eq_mul_inv]
  constructor
  · intro hpos
    have hraw : 0 < broadPrimePairConvolution N :=
      pos_of_mul_pos_left hpos (le_of_lt hscale)
    exact broadPrimePairConvolution_pos_iff_goldbachRep.mp hraw
  · intro hrep
    exact mul_pos
      (broadPrimePairConvolution_pos_iff_goldbachRep.mpr hrep)
      hscale

/--
The exact analytic interface needed to close the large-number part of Route A.

The functions `main` and `error` may use any valid major/minor-arc decomposition.  The structure
requires equality with the full normalized pointwise convolution, not merely with a banked or
averaged proxy.
-/
structure BroadPrimeConvolutionCertificate
    (Xmin : ℕ) (main error : ℕ → ℝ) : Prop where
  decomposition :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      normalizedBroadPrimePairConvolution N = main N + error N
  main_pos :
    ∀ {N : ℕ}, Xmin ≤ N → Even N → 0 < main N
  error_abs_lt_main :
    ∀ {N : ℕ}, Xmin ≤ N → Even N → |error N| < main N

theorem normalizedBroadPrimePairConvolution_pos_of_certificate
    {Xmin : ℕ} {main error : ℕ → ℝ}
    (hcert : BroadPrimeConvolutionCertificate Xmin main error)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    0 < normalizedBroadPrimePairConvolution N := by
  rw [hcert.decomposition hN hEven]
  have hlower : -main N < error N := (abs_lt.mp (hcert.error_abs_lt_main hN hEven)).1
  linarith [hcert.main_pos hN hEven]

theorem goldbachRep_of_broadPrimeConvolutionCertificate
    {Xmin : ℕ} {main error : ℕ → ℝ}
    (hcert : BroadPrimeConvolutionCertificate Xmin main error)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) (hTwo : 2 ≤ N) :
    Goldbach.GoldbachRep N :=
  (normalizedBroadPrimePairConvolution_pos_iff_goldbachRep hTwo).mp
    (normalizedBroadPrimePairConvolution_pos_of_certificate hcert hN hEven)

/--
The corrected Route A interface plugs directly into the existing finite-base endgame.
-/
theorem goldbach_of_finiteBase_and_broadPrimeConvolutionCertificate
    {Xmin : ℕ} {main error : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BroadPrimeConvolutionCertificate Xmin main error) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_broadPrimeConvolutionCertificate hcert (by omega) hEven (by omega)

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
