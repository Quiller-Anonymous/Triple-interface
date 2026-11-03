import Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
import Goldbach.Cert.SiegelWalfiszAxioms

/-!
# Exact von Mangoldt transfer for the broad prime convolution

The existing major-arc machinery is naturally stated for the complete von Mangoldt weight.  The
old prime-only bridge bounded `ΛVM - BG_Bank.Λ` at every integer and therefore paid an error of
order `N log N`.  That loses the decisive fact that the difference is supported only on higher
prime powers.

This module keeps that support visible.  It decomposes the complete von Mangoldt convolution into
the exact prime convolution plus three nonnegative contamination terms:

* prime against higher prime power;
* higher prime power against prime;
* higher prime power against higher prime power.

The final certificate interface consequently asks for one analytic approximation to the von
Mangoldt convolution and one sparse contamination bound.  No fixed arithmetic bank occurs here.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt

open scoped BigOperators

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcStep7FourierOrthogonality

noncomputable section

/-- Complete von Mangoldt weight, named locally for the corrected Route A. -/
noncomputable abbrev broadVonMangoldtWeight (n : ℕ) : ℝ :=
  Goldbach.Cert.SiegelWalfisz.ΛVM n

/-- The part of von Mangoldt supported on non-prime prime powers. -/
noncomputable def higherPrimePowerWeight (n : ℕ) : ℝ :=
  broadVonMangoldtWeight n - Goldbach.BG_Bank.Λ n

lemma broadVonMangoldtWeight_nonneg (n : ℕ) :
    0 ≤ broadVonMangoldtWeight n := by
  simpa [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM] using
    (ArithmeticFunction.vonMangoldt_nonneg (n := n))

lemma broadVonMangoldtWeight_eq_primeWeight_of_prime
    {p : ℕ} (hp : Nat.Prime p) :
    broadVonMangoldtWeight p = Goldbach.BG_Bank.Λ p := by
  simp [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Goldbach.BG_Bank.Λ, hp]

lemma primeWeight_le_broadVonMangoldtWeight (n : ℕ) :
    Goldbach.BG_Bank.Λ n ≤ broadVonMangoldtWeight n := by
  by_cases hn : Nat.Prime n
  · exact (broadVonMangoldtWeight_eq_primeWeight_of_prime hn).ge
  · simpa [Goldbach.BG_Bank.Λ, hn] using broadVonMangoldtWeight_nonneg n

lemma higherPrimePowerWeight_nonneg (n : ℕ) :
    0 ≤ higherPrimePowerWeight n := by
  exact sub_nonneg.mpr (primeWeight_le_broadVonMangoldtWeight n)

@[simp] lemma higherPrimePowerWeight_eq_zero_of_prime
    {p : ℕ} (hp : Nat.Prime p) :
    higherPrimePowerWeight p = 0 := by
  simp [higherPrimePowerWeight, broadVonMangoldtWeight_eq_primeWeight_of_prime hp]

@[simp] lemma higherPrimePowerWeight_eq_zero_of_not_isPrimePow
    {n : ℕ} (hn : ¬IsPrimePow n) :
    higherPrimePowerWeight n = 0 := by
  have hnotPrime : ¬Nat.Prime n := fun hp => hn hp.isPrimePow
  simp [higherPrimePowerWeight, broadVonMangoldtWeight,
    Goldbach.Cert.SiegelWalfisz.ΛVM, ArithmeticFunction.vonMangoldt_apply, hn,
    Goldbach.BG_Bank.Λ, hnotPrime]

theorem higherPrimePowerWeight_pos_iff {n : ℕ} :
    0 < higherPrimePowerWeight n ↔ IsPrimePow n ∧ ¬Nat.Prime n := by
  by_cases hp : Nat.Prime n
  · simp [hp]
  · have hPrimeWeight : Goldbach.BG_Bank.Λ n = 0 := by
      simp [Goldbach.BG_Bank.Λ, hp]
    rw [higherPrimePowerWeight, hPrimeWeight, sub_zero]
    constructor
    · intro hpos
      exact ⟨by
        exact (ArithmeticFunction.vonMangoldt_pos_iff (n := n)).mp
          (by simpa [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM] using hpos), hp⟩
    · rintro ⟨hpow, _⟩
      simpa [broadVonMangoldtWeight, Goldbach.Cert.SiegelWalfisz.ΛVM] using
        (ArithmeticFunction.vonMangoldt_pos_iff (n := n)).mpr hpow

lemma broadVonMangoldtWeight_eq_prime_add_higher (n : ℕ) :
    broadVonMangoldtWeight n = Goldbach.BG_Bank.Λ n + higherPrimePowerWeight n := by
  simp [higherPrimePowerWeight]

/-- Complete von Mangoldt convolution on the exact Goldbach support. -/
noncomputable def broadVonMangoldtPairConvolution (N : ℕ) : ℝ :=
  Finset.sum (primeCandidateSupport N) fun n =>
    broadVonMangoldtWeight n * broadVonMangoldtWeight (N - n)

/-- Complete von Mangoldt exponential sum on the exact candidate support. -/
noncomputable def broadVonMangoldtExponentialSum (N : ℕ) (alpha : UC) : ℂ :=
  finiteWeightExponentialSum broadVonMangoldtWeight N alpha

/-- Circle integrand extracting the broad von Mangoldt convolution. -/
noncomputable def broadVonMangoldtCircleIntegrand (N : ℕ) (alpha : UC) : ℂ :=
  finiteWeightCircleIntegrand broadVonMangoldtWeight N alpha

/-- Exact circle integral for the complete von Mangoldt convolution. -/
noncomputable def broadVonMangoldtCircleIntegral (N : ℕ) : ℂ :=
  finiteWeightCircleIntegral broadVonMangoldtWeight N

theorem broadVonMangoldtCircleIntegral_eq_convolution (N : ℕ) :
    broadVonMangoldtCircleIntegral N = (broadVonMangoldtPairConvolution N : ℂ) := by
  simpa [broadVonMangoldtCircleIntegral, broadVonMangoldtPairConvolution,
    finiteWeightPairConvolution] using
    (finiteWeightCircleIntegral_eq_convolution broadVonMangoldtWeight N)

/--
The exact contribution introduced by replacing the prime-only weight with von Mangoldt.

Writing this as three terms, rather than as an opaque difference of two large convolutions, keeps
the sparse higher-prime-power support available to the eventual bound.
-/
noncomputable def broadPrimePowerContamination (N : ℕ) : ℝ :=
  Finset.sum (primeCandidateSupport N) fun n =>
    Goldbach.BG_Bank.Λ n * higherPrimePowerWeight (N - n)
      + higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n)
      + higherPrimePowerWeight n * higherPrimePowerWeight (N - n)

theorem broadVonMangoldtPairConvolution_nonneg (N : ℕ) :
    0 ≤ broadVonMangoldtPairConvolution N := by
  unfold broadVonMangoldtPairConvolution
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (broadVonMangoldtWeight_nonneg n)
      (broadVonMangoldtWeight_nonneg (N - n))

theorem broadPrimePowerContamination_nonneg (N : ℕ) :
    0 ≤ broadPrimePowerContamination N := by
  unfold broadPrimePowerContamination
  exact Finset.sum_nonneg fun n _ => by
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (lambda_nonneg n) (higherPrimePowerWeight_nonneg (N - n)))
        (mul_nonneg (higherPrimePowerWeight_nonneg n) (lambda_nonneg (N - n))))
      (mul_nonneg (higherPrimePowerWeight_nonneg n)
        (higherPrimePowerWeight_nonneg (N - n)))

/-- Exact algebraic transfer from the von Mangoldt convolution to the prime convolution. -/
theorem broadVonMangoldtPairConvolution_eq_prime_add_contamination (N : ℕ) :
    broadVonMangoldtPairConvolution N
      = broadPrimePairConvolution N + broadPrimePowerContamination N := by
  classical
  unfold broadVonMangoldtPairConvolution broadPrimePairConvolution
    broadPrimePowerContamination
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [broadVonMangoldtWeight_eq_prime_add_higher,
    broadVonMangoldtWeight_eq_prime_add_higher]
  ring

theorem broadPrimePairConvolution_eq_vonMangoldt_sub_contamination (N : ℕ) :
    broadPrimePairConvolution N
      = broadVonMangoldtPairConvolution N - broadPrimePowerContamination N := by
  linarith [broadVonMangoldtPairConvolution_eq_prime_add_contamination N]

/-!
The corrected analytic interface.  A successful circle-method proof may work entirely with the
standard von Mangoldt sum.  It then has to bound only the sparse higher-prime-power contamination
before using the exact prime endpoint.
-/

structure BroadVonMangoldtTransferCertificate
    (Xmin : ℕ) (main analyticError primePowerError : ℕ → ℝ) : Prop where
  analyticError_nonneg : ∀ N, 0 ≤ analyticError N
  primePowerError_nonneg : ∀ N, 0 ≤ primePowerError N
  vonMangoldt_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |broadVonMangoldtPairConvolution N - main N| ≤ analyticError N
  primePower_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      broadPrimePowerContamination N ≤ primePowerError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      analyticError N + primePowerError N < main N

theorem broadPrimePairConvolution_pos_of_vonMangoldtTransferCertificate
    {Xmin : ℕ} {main analyticError primePowerError : ℕ → ℝ}
    (hcert :
      BroadVonMangoldtTransferCertificate Xmin main analyticError primePowerError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    0 < broadPrimePairConvolution N := by
  have hVMAbs := hcert.vonMangoldt_approx hN hEven
  have hVMLower :
      main N - analyticError N ≤ broadVonMangoldtPairConvolution N := by
    have := (abs_le.mp hVMAbs).1
    linarith
  have hPower := hcert.primePower_bound hN hEven
  have hBudget := hcert.strict_budget hN hEven
  rw [broadPrimePairConvolution_eq_vonMangoldt_sub_contamination]
  linarith

theorem goldbachRep_of_vonMangoldtTransferCertificate
    {Xmin : ℕ} {main analyticError primePowerError : ℕ → ℝ}
    (hcert :
      BroadVonMangoldtTransferCertificate Xmin main analyticError primePowerError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N :=
  broadPrimePairConvolution_pos_iff_goldbachRep.mp
    (broadPrimePairConvolution_pos_of_vonMangoldtTransferCertificate hcert hN hEven)

theorem goldbach_of_finiteBase_and_vonMangoldtTransferCertificate
    {Xmin : ℕ} {main analyticError primePowerError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert :
      BroadVonMangoldtTransferCertificate Xmin main analyticError primePowerError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_vonMangoldtTransferCertificate hcert (by omega) hEven

end

end Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
