import Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerCount
import Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit

/-!
# Balanced BMOR-compatible Route A prototype

The complete support `[2, N - 2]` has the correct Goldbach endpoint, but its low endpoint is below
the range of the strong explicit BMOR progression estimate. This module records a conservative
alternative: restrict both summands to the symmetric interval `[L, N - L]`, where `L - 1` may be
chosen at the BMOR cutoff.

This is not a fixed-width prime bank. The interval grows with `N`, and the output remains the exact
convolution at `N`. Positivity therefore still produces a genuine Goldbach representation. The
module proves the exact circle split and shows that its higher-prime-power contamination is no
larger than the already checked broad allowance.

No major- or minor-arc estimate is asserted here. The purpose is to expose a support on which the
published explicit progression estimate can apply without a million-term low-prefix remainder.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype

open Complex MeasureTheory AddCircle

open Goldbach.Cert.MajorArcModules.RouteABroadPrimeConvolution
open Goldbach.Cert.MajorArcModules.RouteABroadPrimePowerCount
open Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircle
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightCircleSplit

noncomputable section

/-- Symmetric growing support for the two summands. -/
def balancedCandidateSupport (L N : ℕ) : Finset ℕ :=
  Finset.Icc L (N - L)

/-- Restrict an arbitrary real weight to the balanced support. -/
noncomputable def balancedRestrictedWeight
    (weight : ℕ → ℝ) (L N n : ℕ) : ℝ :=
  if n ∈ balancedCandidateSupport L N then weight n else 0

lemma balancedCandidateSupport_sub_mem
    {L N n : ℕ} (hn : n ∈ balancedCandidateSupport L N) :
    N - n ∈ balancedCandidateSupport L N := by
  have hnBounds := Finset.mem_Icc.mp hn
  have hLN : L ≤ N := le_trans hnBounds.1 (le_trans hnBounds.2 (Nat.sub_le N L))
  have hnN : n ≤ N := le_trans hnBounds.2 (Nat.sub_le N L)
  rw [balancedCandidateSupport, Finset.mem_Icc]
  constructor <;> omega

lemma balancedRestrictedWeight_nonneg
    {weight : ℕ → ℝ} (hweight : ∀ n, 0 ≤ weight n)
    (L N n : ℕ) :
    0 ≤ balancedRestrictedWeight weight L N n := by
  simp only [balancedRestrictedWeight]
  split_ifs
  · exact hweight n
  · exact le_rfl

lemma balancedRestrictedWeight_le
    {weight : ℕ → ℝ} (hweight : ∀ n, 0 ≤ weight n)
    (L N n : ℕ) :
    balancedRestrictedWeight weight L N n ≤ weight n := by
  simp only [balancedRestrictedWeight]
  split_ifs
  · exact le_rfl
  · exact hweight n

/-- Prime-only weight restricted to the balanced support. -/
noncomputable def balancedPrimeWeight (L N n : ℕ) : ℝ :=
  balancedRestrictedWeight Goldbach.BG_Bank.Λ L N n

/-- Complete von Mangoldt weight restricted to the same support. -/
noncomputable def balancedVonMangoldtWeight (L N n : ℕ) : ℝ :=
  balancedRestrictedWeight broadVonMangoldtWeight L N n

/-- Higher-prime-power weight restricted to the same support. -/
noncomputable def balancedHigherPrimePowerWeight (L N n : ℕ) : ℝ :=
  balancedRestrictedWeight higherPrimePowerWeight L N n

lemma balancedPrimeWeight_nonneg (L N n : ℕ) :
    0 ≤ balancedPrimeWeight L N n :=
  balancedRestrictedWeight_nonneg lambda_nonneg L N n

lemma balancedVonMangoldtWeight_nonneg (L N n : ℕ) :
    0 ≤ balancedVonMangoldtWeight L N n :=
  balancedRestrictedWeight_nonneg broadVonMangoldtWeight_nonneg L N n

lemma balancedHigherPrimePowerWeight_nonneg (L N n : ℕ) :
    0 ≤ balancedHigherPrimePowerWeight L N n :=
  balancedRestrictedWeight_nonneg higherPrimePowerWeight_nonneg L N n

lemma balancedVonMangoldtWeight_eq_prime_add_higher (L N n : ℕ) :
    balancedVonMangoldtWeight L N n
      = balancedPrimeWeight L N n + balancedHigherPrimePowerWeight L N n := by
  by_cases hn : n ∈ balancedCandidateSupport L N
  · simp [balancedVonMangoldtWeight, balancedPrimeWeight,
      balancedHigherPrimePowerWeight, balancedRestrictedWeight, hn,
      broadVonMangoldtWeight_eq_prime_add_higher]
  · simp [balancedVonMangoldtWeight, balancedPrimeWeight,
      balancedHigherPrimePowerWeight, balancedRestrictedWeight, hn]

lemma balancedPrimeWeight_pos_iff {L N n : ℕ} :
    0 < balancedPrimeWeight L N n
      ↔ n ∈ balancedCandidateSupport L N ∧ Nat.Prime n := by
  by_cases hn : n ∈ balancedCandidateSupport L N
  · rw [and_iff_right hn]
    constructor
    · intro hpos
      by_contra hp
      simp [balancedPrimeWeight, balancedRestrictedWeight, hn,
        Goldbach.BG_Bank.Λ, hp] at hpos
    · intro hp
      simpa [balancedPrimeWeight, balancedRestrictedWeight, hn] using
        (lambda_pos_of_prime hp)
  · simp [balancedPrimeWeight, balancedRestrictedWeight, hn]

/-- Exact prime convolution on the balanced support, represented through the generic circle API. -/
noncomputable def balancedPrimePairConvolution (L N : ℕ) : ℝ :=
  finiteWeightPairConvolution (balancedPrimeWeight L N) N

/-- Exact von Mangoldt convolution on the balanced support. -/
noncomputable def balancedVonMangoldtPairConvolution (L N : ℕ) : ℝ :=
  finiteWeightPairConvolution (balancedVonMangoldtWeight L N) N

/-- Sparse correction introduced by the balanced von Mangoldt weight. -/
noncomputable def balancedPrimePowerContamination (L N : ℕ) : ℝ :=
  Finset.sum (primeCandidateSupport N) fun n =>
    balancedPrimeWeight L N n * balancedHigherPrimePowerWeight L N (N - n)
      + balancedHigherPrimePowerWeight L N n * balancedPrimeWeight L N (N - n)
      + balancedHigherPrimePowerWeight L N n
          * balancedHigherPrimePowerWeight L N (N - n)

theorem balancedPrimePairConvolution_nonneg (L N : ℕ) :
    0 ≤ balancedPrimePairConvolution L N := by
  unfold balancedPrimePairConvolution finiteWeightPairConvolution
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (balancedPrimeWeight_nonneg L N n)
      (balancedPrimeWeight_nonneg L N (N - n))

/-- Positivity of the restricted exact-center convolution still gives a genuine Goldbach pair. -/
theorem goldbachRep_of_balancedPrimePairConvolution_pos
    {L N : ℕ} (hpos : 0 < balancedPrimePairConvolution L N) :
    Goldbach.GoldbachRep N := by
  have hpoint :
      ∀ n ∈ primeCandidateSupport N,
        0 ≤ balancedPrimeWeight L N n * balancedPrimeWeight L N (N - n) := by
    intro n hn
    exact mul_nonneg (balancedPrimeWeight_nonneg L N n)
      (balancedPrimeWeight_nonneg L N (N - n))
  have hwitness :
      ∃ n ∈ primeCandidateSupport N,
        0 < balancedPrimeWeight L N n * balancedPrimeWeight L N (N - n) := by
    exact (Finset.sum_pos_iff_of_nonneg hpoint).mp hpos
  rcases hwitness with ⟨n, hnSupport, hnProduct⟩
  have hnPos : 0 < balancedPrimeWeight L N n := by
    by_contra hnot
    have hzero : balancedPrimeWeight L N n = 0 :=
      le_antisymm (le_of_not_gt hnot) (balancedPrimeWeight_nonneg L N n)
    rw [hzero, zero_mul] at hnProduct
    exact (lt_irrefl 0) hnProduct
  have hsubPos : 0 < balancedPrimeWeight L N (N - n) := by
    by_contra hnot
    have hzero : balancedPrimeWeight L N (N - n) = 0 :=
      le_antisymm (le_of_not_gt hnot) (balancedPrimeWeight_nonneg L N (N - n))
    rw [hzero, mul_zero] at hnProduct
    exact (lt_irrefl 0) hnProduct
  have hnPrime := (balancedPrimeWeight_pos_iff.mp hnPos).2
  have hsubPrime := (balancedPrimeWeight_pos_iff.mp hsubPos).2
  have hnN : n ≤ N :=
    le_trans (Finset.mem_Icc.mp hnSupport).2 (Nat.sub_le N 2)
  exact ⟨n, N - n, hnPrime, hsubPrime, Nat.add_sub_of_le hnN⟩

theorem balancedVonMangoldtPairConvolution_eq_prime_add_contamination
    (L N : ℕ) :
    balancedVonMangoldtPairConvolution L N
      = balancedPrimePairConvolution L N
        + balancedPrimePowerContamination L N := by
  classical
  unfold balancedVonMangoldtPairConvolution balancedPrimePairConvolution
    finiteWeightPairConvolution balancedPrimePowerContamination
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [balancedVonMangoldtWeight_eq_prime_add_higher,
    balancedVonMangoldtWeight_eq_prime_add_higher]
  ring

theorem balancedPrimePowerContamination_nonneg (L N : ℕ) :
    0 ≤ balancedPrimePowerContamination L N := by
  unfold balancedPrimePowerContamination
  exact Finset.sum_nonneg fun n _ => by
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (balancedPrimeWeight_nonneg L N n)
          (balancedHigherPrimePowerWeight_nonneg L N (N - n)))
        (mul_nonneg (balancedHigherPrimePowerWeight_nonneg L N n)
          (balancedPrimeWeight_nonneg L N (N - n))))
      (mul_nonneg (balancedHigherPrimePowerWeight_nonneg L N n)
        (balancedHigherPrimePowerWeight_nonneg L N (N - n)))

/-- Restricting the support cannot increase the sparse prime-power correction. -/
theorem balancedPrimePowerContamination_le_broad (L N : ℕ) :
    balancedPrimePowerContamination L N ≤ broadPrimePowerContamination N := by
  unfold balancedPrimePowerContamination broadPrimePowerContamination
  refine Finset.sum_le_sum ?_
  intro n hn
  have hpN := balancedRestrictedWeight_le lambda_nonneg L N n
  have hpSub := balancedRestrictedWeight_le lambda_nonneg L N (N - n)
  have hhN := balancedRestrictedWeight_le higherPrimePowerWeight_nonneg L N n
  have hhSub := balancedRestrictedWeight_le higherPrimePowerWeight_nonneg L N (N - n)
  have hcrossRight :
      balancedPrimeWeight L N n * balancedHigherPrimePowerWeight L N (N - n)
        ≤ Goldbach.BG_Bank.Λ n * higherPrimePowerWeight (N - n) := by
    exact mul_le_mul hpN hhSub
      (balancedHigherPrimePowerWeight_nonneg L N (N - n)) (lambda_nonneg n)
  have hcrossLeft :
      balancedHigherPrimePowerWeight L N n * balancedPrimeWeight L N (N - n)
        ≤ higherPrimePowerWeight n * Goldbach.BG_Bank.Λ (N - n) := by
    exact mul_le_mul hhN hpSub
      (balancedPrimeWeight_nonneg L N (N - n)) (higherPrimePowerWeight_nonneg n)
  have hsquare :
      balancedHigherPrimePowerWeight L N n
          * balancedHigherPrimePowerWeight L N (N - n)
        ≤ higherPrimePowerWeight n * higherPrimePowerWeight (N - n) := by
    exact mul_le_mul hhN hhSub
      (balancedHigherPrimePowerWeight_nonneg L N (N - n))
      (higherPrimePowerWeight_nonneg n)
  linarith

theorem balancedPrimePowerContamination_le_five_halves_sqrt_log_sq
    {L N : ℕ} (hTwo : 2 ≤ N) :
    balancedPrimePowerContamination L N
      ≤ (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2 :=
  (balancedPrimePowerContamination_le_broad L N).trans
    (broadPrimePowerContamination_le_five_halves_sqrt_log_sq hTwo)

/-- Major-arc part of the exact balanced von Mangoldt convolution. -/
noncomputable def balancedVonMangoldtMajorArcIntegral
    (L N B : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightMajorArcIntegral (balancedVonMangoldtWeight L N) N B Delta

/-- Minor-arc part of the exact balanced von Mangoldt convolution. -/
noncomputable def balancedVonMangoldtMinorArcIntegral
    (L N B : ℕ) (Delta : ℝ) : ℂ :=
  finiteWeightMinorArcIntegral (balancedVonMangoldtWeight L N) N B Delta

/-- Exact major/minor split on the BMOR-compatible balanced support. -/
theorem balancedVonMangoldtPairConvolution_eq_major_re_add_minor_re
    (L N B : ℕ) (Delta : ℝ) :
    balancedVonMangoldtPairConvolution L N
      = (balancedVonMangoldtMajorArcIntegral L N B Delta).re
        + (balancedVonMangoldtMinorArcIntegral L N B Delta).re := by
  simpa [balancedVonMangoldtPairConvolution, balancedVonMangoldtMajorArcIntegral,
    balancedVonMangoldtMinorArcIntegral] using
    (finiteWeightPairConvolution_eq_major_re_add_minor_re
      (balancedVonMangoldtWeight L N) N B Delta)

/-- Honest analytic interface for the balanced prototype. -/
structure BalancedVonMangoldtAnalyticCertificate
    (L Xmin B : ℕ) (Delta : ℝ)
    (main majorError minorError : ℕ → ℝ) : Prop where
  two_le_threshold : 2 ≤ Xmin
  major_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(balancedVonMangoldtMajorArcIntegral L N B Delta).re - main N|
        ≤ majorError N
  minor_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      ‖balancedVonMangoldtMinorArcIntegral L N B Delta‖ ≤ minorError N
  strict_budget :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      majorError N + minorError N
          + (5 / 2 : ℝ) * (Nat.sqrt N + 1) * (Real.log (N : ℝ)) ^ 2
        < main N

theorem goldbachRep_of_balancedAnalyticCertificate
    {L Xmin B : ℕ} {Delta : ℝ}
    {main majorError minorError : ℕ → ℝ}
    (hcert : BalancedVonMangoldtAnalyticCertificate L Xmin B Delta
      main majorError minorError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    Goldbach.GoldbachRep N := by
  have hmajorAbs := hcert.major_approx hN hEven
  have hmajorLower :
      main N - majorError N
        ≤ (balancedVonMangoldtMajorArcIntegral L N B Delta).re := by
    have h := (abs_le.mp hmajorAbs).1
    linarith
  have hminorAbs :
      |(balancedVonMangoldtMinorArcIntegral L N B Delta).re| ≤ minorError N :=
    (Complex.abs_re_le_norm _).trans (hcert.minor_bound hN hEven)
  have hminorLower :
      -minorError N ≤ (balancedVonMangoldtMinorArcIntegral L N B Delta).re :=
    (abs_le.mp hminorAbs).1
  have hPower := balancedPrimePowerContamination_le_five_halves_sqrt_log_sq
    (L := L) (hcert.two_le_threshold.trans hN)
  have hBudget := hcert.strict_budget hN hEven
  have hDecomp := balancedVonMangoldtPairConvolution_eq_prime_add_contamination L N
  have hCircle := balancedVonMangoldtPairConvolution_eq_major_re_add_minor_re L N B Delta
  apply goldbachRep_of_balancedPrimePairConvolution_pos
  rw [hDecomp] at hCircle
  linarith

/-- A balanced analytic certificate plus a finite base closes the full Goldbach statement. -/
theorem goldbach_of_finiteBase_and_balancedAnalyticCertificate
    {L Xmin B : ℕ} {Delta : ℝ}
    {main majorError minorError : ℕ → ℝ}
    (hBase : Goldbach.FiniteBaseUpTo Xmin)
    (hcert : BalancedVonMangoldtAnalyticCertificate L Xmin B Delta
      main majorError minorError) :
    ∀ {N : ℕ}, Even N → 4 ≤ N → Goldbach.GoldbachRep N := by
  intro N hEven hFour
  by_cases hSmall : N ≤ Xmin
  · exact hBase hEven hFour hSmall
  · exact goldbachRep_of_balancedAnalyticCertificate hcert (by omega) hEven

end

end Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
