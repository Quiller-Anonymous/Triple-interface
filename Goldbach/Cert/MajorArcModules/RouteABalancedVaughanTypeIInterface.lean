import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
import Goldbach.Cert.SiegelWalfiszWeighted

/-!
# Honest fixed-center Type-I interface

Bombieri--Vinogradov is expected to control the short Type-I--prime correlation after partial
summation, but the required effective theorem is not presently formalized in this repository.
This file therefore does not add an axiom.  It states the exact theorem-facing data such an
application must provide and proves how those data combine with the exact mask identity.

The final theorem leaves one explicit one-sided hard-residual hypothesis.  This is the genuine
remaining analytic problem; it is not replaced by a two-sided norm bound or by an all-array SSU
contract.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface

open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteAFiniteWeightBilinearCircle
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter

noncomputable section

/-- The logarithmic weight occurring in the fixed-center Type-I progression. -/
noncomputable def balancedVaughanTypeILogWeight
    (N d n : ℕ) : ℝ :=
  Real.log ((N - n) / d)

/--
Exact interval summation-by-parts formula for one coprime-modulus error.  This connects the checked
fixed-center residue formula to the repository's existing `psi` deviation object; no progression
estimate is used here.
-/
theorem balancedVaughanTypeICoprimeModulusError_eq_partialSummation
    {L N d : ℕ} (hLU : L ≤ N - L) (hL : 0 < L) :
    balancedVaughanTypeICoprimeModulusError L N d
      = Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (N - L) *
          balancedVaughanTypeILogWeight N d (N - L)
        - Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (L - 1) *
          balancedVaughanTypeILogWeight N d (L - 1)
        - ∑ n ∈ Finset.Ico (L - 1) (N - L),
            Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) n *
              (balancedVaughanTypeILogWeight N d (n + 1)
                - balancedVaughanTypeILogWeight N d n) := by
  have h :=
    Goldbach.Cert.SiegelWalfiszWeighted.weightedSum_Ico_eq_mainTerm_add_error_of_pos
      (q := d) (a := N) (g := balancedVaughanTypeILogWeight N d)
      (L := L) (U := N - L) hLU hL
  simp [balancedVaughanTypeICoprimeModulusError,
    balancedVaughanTypeIPrimeResidueSupport, balancedCandidateSupport,
    balancedVaughanTypeILogWeight, Goldbach.Cert.SiegelWalfiszWeighted.aTerm,
    Goldbach.Cert.MajorArcModules.RouteABroadPrimeVonMangoldt.broadVonMangoldtWeight,
    Goldbach.Cert.SiegelWalfisz.ΛVM, Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_filter] at h ⊢
  linarith

/-- Triangle-inequality form of the exact per-modulus partial-summation identity. -/
theorem abs_balancedVaughanTypeICoprimeModulusError_le
    {L N d : ℕ} (hLU : L ≤ N - L) (hL : 0 < L) :
    |balancedVaughanTypeICoprimeModulusError L N d|
      ≤ |Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (N - L)| *
          |balancedVaughanTypeILogWeight N d (N - L)|
        + |Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) (L - 1)| *
          |balancedVaughanTypeILogWeight N d (L - 1)|
        + ∑ n ∈ Finset.Ico (L - 1) (N - L),
            |Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) n| *
              |balancedVaughanTypeILogWeight N d (n + 1)
                - balancedVaughanTypeILogWeight N d n| := by
  rw [balancedVaughanTypeICoprimeModulusError_eq_partialSummation hLU hL]
  let E : ℕ → ℝ := fun n =>
    Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) n
  let g : ℕ → ℝ := balancedVaughanTypeILogWeight N d
  have hsum :
      |∑ n ∈ Finset.Ico (L - 1) (N - L), E n * (g (n + 1) - g n)|
        ≤ ∑ n ∈ Finset.Ico (L - 1) (N - L), |E n| * |g (n + 1) - g n| := by
    simpa [abs_mul] using
      (Finset.abs_sum_le_sum_abs
        (s := Finset.Ico (L - 1) (N - L))
        (f := fun n => E n * (g (n + 1) - g n)))
  calc
    |E (N - L) * g (N - L) - E (L - 1) * g (L - 1)
        - ∑ n ∈ Finset.Ico (L - 1) (N - L), E n * (g (n + 1) - g n)|
      ≤ |E (N - L) * g (N - L) - E (L - 1) * g (L - 1)|
          + |∑ n ∈ Finset.Ico (L - 1) (N - L), E n * (g (n + 1) - g n)| :=
        abs_sub _ _
    _ ≤ (|E (N - L) * g (N - L)| + |E (L - 1) * g (L - 1)|)
          + |∑ n ∈ Finset.Ico (L - 1) (N - L), E n * (g (n + 1) - g n)| :=
        add_le_add_right (abs_sub _ _) _
    _ ≤ (|E (N - L) * g (N - L)| + |E (L - 1) * g (L - 1)|)
          + ∑ n ∈ Finset.Ico (L - 1) (N - L), |E n| * |g (n + 1) - g n| :=
        add_le_add_left hsum _
    _ = _ := by
      simp [E, g, abs_mul]

/--
Effective maximal Bombieri--Vinogradov input in selector form.  Universality over `residue` and
`endpoint` is the finite equivalent of summing the maximum over reduced residue classes and
partial-sum endpoints.  `bound` must be explicit and computable for the finite-base architecture.
-/
structure EffectiveMaximalBombieriVinogradovInput
    (Xmin : ℕ) (level : ℕ → ℕ) (bound : ℕ → ℝ) : Prop where
  selector_bound :
    ∀ {x : ℕ}, Xmin ≤ x →
      ∀ (residue endpoint : ℕ → ℕ),
        (∀ q ∈ Finset.Icc 1 (level x), Nat.Coprime (residue q) q) →
        (∀ q ∈ Finset.Icc 1 (level x), 2 ≤ endpoint q ∧ endpoint q ≤ x) →
        (∑ q ∈ Finset.Icc 1 (level x),
          |Goldbach.Cert.SiegelWalfisz.psi (endpoint q) q (residue q)
            - (endpoint q : ℝ) / (Nat.totient q : ℝ)|)
          ≤ bound x

/--
The precise analytic input needed for the full-circle Type-I term, stated on the checked
prime-in-progressions formula rather than on the convolution that it is meant to estimate.
-/
structure BalancedVaughanTypeIProgressionEstimate
    (L Xmin : ℕ) (u : ℕ → ℕ) (main fullError : ℕ → ℝ) : Prop where
  support_lower : 2 ≤ L
  residue_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |balancedVaughanTypeIPrimeResidueSum L N (u N) - main N|
        ≤ fullError N

/-- Concrete error target after subtracting the canonical discrete coprime main. -/
structure BalancedVaughanTypeIDiscreteProgressionErrorBound
    (L Xmin : ℕ) (u : ℕ → ℕ) (fullError : ℕ → ℝ) : Prop where
  support_lower : 2 ≤ L
  error_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |balancedVaughanTypeIProgressionError L N (u N)| ≤ fullError N

/-- Maximal-progressions obligation restricted to reduced residue classes. -/
structure BalancedVaughanTypeICoprimeProgressionErrorBound
    (L Xmin : ℕ) (u : ℕ → ℕ) (coprimeError : ℕ → ℝ) : Prop where
  support_lower : 2 ≤ L
  error_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |balancedVaughanTypeICoprimeProgressionError L N (u N)| ≤ coprimeError N

/-- Separate prime-power obligation for the nonreduced residue classes. -/
structure BalancedVaughanTypeINoncoprimeProgressionBound
    (L Xmin : ℕ) (u : ℕ → ℕ) (noncoprimeError : ℕ → ℝ) : Prop where
  contribution_bound :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |balancedVaughanTypeINoncoprimeProgressionContribution L N (u N)|
        ≤ noncoprimeError N

/-- Independent coprime and noncoprime estimates give the required aggregate error bound. -/
theorem discreteProgressionErrorBound_of_coprime_and_noncoprime
    {L Xmin : ℕ} {u : ℕ → ℕ} {coprimeError noncoprimeError : ℕ → ℝ}
    (hCoprime : BalancedVaughanTypeICoprimeProgressionErrorBound
      L Xmin u coprimeError)
    (hNoncoprime : BalancedVaughanTypeINoncoprimeProgressionBound
      L Xmin u noncoprimeError) :
    BalancedVaughanTypeIDiscreteProgressionErrorBound
      L Xmin u (fun N => coprimeError N + noncoprimeError N) := by
  refine ⟨hCoprime.support_lower, ?_⟩
  intro N hN hEven
  rw [balancedVaughanTypeIProgressionError_eq_coprime_add_noncoprime]
  calc
    |balancedVaughanTypeICoprimeProgressionError L N (u N)
        + balancedVaughanTypeINoncoprimeProgressionContribution L N (u N)|
      ≤ |balancedVaughanTypeICoprimeProgressionError L N (u N)|
          + |balancedVaughanTypeINoncoprimeProgressionContribution L N (u N)| :=
        abs_add_le _ _
    _ ≤ coprimeError N + noncoprimeError N :=
      add_le_add (hCoprime.error_bound hN hEven)
        (hNoncoprime.contribution_bound hN hEven)

/-- A bound on the named discrete error supplies the generic progression estimate. -/
theorem typeIProgressionEstimate_of_discreteErrorBound
    {L Xmin : ℕ} {u : ℕ → ℕ} {fullError : ℕ → ℝ}
    (hError : BalancedVaughanTypeIDiscreteProgressionErrorBound
      L Xmin u fullError) :
    BalancedVaughanTypeIProgressionEstimate L Xmin u
      (fun N => balancedVaughanTypeIDiscreteCoprimeMain L N (u N)) fullError := by
  refine ⟨hError.support_lower, ?_⟩
  intro N hN hEven
  simpa [balancedVaughanTypeIProgressionError] using hError.error_bound hN hEven

/-- The exact reindexing transfers a progression estimate to the full Type-I correlation. -/
theorem typeIFullCorrelation_approx_of_progressionEstimate
    {L Xmin : ℕ} {u : ℕ → ℕ} {main fullError : ℕ → ℝ}
    (hProgression : BalancedVaughanTypeIProgressionEstimate
      L Xmin u main fullError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    |finiteWeightBilinearConvolution
        (balancedVaughanTypeIWeight L N (u N)) (balancedVonMangoldtWeight L N) N
        - main N|
      ≤ fullError N := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_residueSum hProgression.support_lower]
  exact hProgression.residue_approx hN hEven

/--
Concrete outputs required from a fixed-center Type-I argument.  `main` is the progression main
expression and `retainedMain` is its retained-arc geometric counterpart.
-/
structure BalancedVaughanTypeIFixedCenterEstimate
    (L Xmin : ℕ) (u : ℕ → ℕ) (retained : ℕ → Set ℝ)
    (main retainedMain fullError retainedError : ℕ → ℝ) : Prop where
  measurable : ∀ N, MeasurableSet (retained N)
  full_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N (u N)) (balancedVonMangoldtWeight L N) N
          - main N|
        ≤ fullError N
  retained_approx :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      |(finiteWeightBilinearSetIntegral
          (balancedVaughanTypeIWeight L N (u N)) (balancedVonMangoldtWeight L N) N
          (retained N)).re - retainedMain N|
        ≤ retainedError N

/-- The exact mask identity turns separate full and retained-arc estimates into a masked one. -/
theorem typeIMaskedCorrelation_approx
    {L Xmin : ℕ} {u : ℕ → ℕ} {retained : ℕ → Set ℝ}
    {main retainedMain fullError retainedError : ℕ → ℝ}
    (hTypeI : BalancedVaughanTypeIFixedCenterEstimate
      L Xmin u retained main retainedMain fullError retainedError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    |(finiteWeightBilinearSetComplementIntegral
        (balancedVaughanTypeIWeight L N (u N)) (balancedVonMangoldtWeight L N) N
        (retained N)).re
        - (main N - retainedMain N)|
      ≤ fullError N + retainedError N := by
  have hMask := congrArg Complex.re
    (balancedVaughanTypeIMaskedCorrelation_eq_full_sub_retained
      L N (u N) (retained N) (hTypeI.measurable N))
  simp only [Complex.sub_re, Complex.ofReal_re] at hMask
  have hFull := hTypeI.full_approx hN hEven
  have hRetained := hTypeI.retained_approx hN hEven
  calc
    |(finiteWeightBilinearSetComplementIntegral
        (balancedVaughanTypeIWeight L N (u N)) (balancedVonMangoldtWeight L N) N
        (retained N)).re - (main N - retainedMain N)|
      = |(finiteWeightBilinearConvolution
            (balancedVaughanTypeIWeight L N (u N))
            (balancedVonMangoldtWeight L N) N - main N)
          - ((finiteWeightBilinearSetIntegral
              (balancedVaughanTypeIWeight L N (u N))
              (balancedVonMangoldtWeight L N) N (retained N)).re
            - retainedMain N)| := by
          congr 1
          rw [hMask]
          ring
    _ ≤ |finiteWeightBilinearConvolution
            (balancedVaughanTypeIWeight L N (u N))
            (balancedVonMangoldtWeight L N) N - main N|
          + |(finiteWeightBilinearSetIntegral
              (balancedVaughanTypeIWeight L N (u N))
              (balancedVonMangoldtWeight L N) N (retained N)).re
            - retainedMain N| := abs_sub _ _
    _ ≤ fullError N + retainedError N := add_le_add hFull hRetained

/-- One-sided input required for the hard fixed-center residual. -/
structure BalancedVaughanHardResidualLowerBound
    (L Xmin : ℕ) (u v : ℕ → ℕ) (retained : ℕ → Set ℝ)
    (allowance : ℕ → ℝ) : Prop where
  lower :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      -allowance N
        ≤ (finiteWeightBilinearSetComplementIntegral
            (balancedVaughanHardWeight L N (u N) (v N))
            (balancedVonMangoldtWeight L N) N (retained N)).re

/--
One-sided estimate for the retained part of the same hard residual.  This is the cancellation-safe
surface for comparing the retained von Mangoldt pair with the retained Type-I model:

`J(S,S) - J(A,S) = J(S-A,S) = J(hard,S)`.

Bounding this difference directly avoids paying for two large retained integrals separately.
-/
structure BalancedVaughanRetainedHardResidualLowerBound
    (L Xmin : ℕ) (u v : ℕ → ℕ) (retained : ℕ → Set ℝ)
    (allowance : ℕ → ℝ) : Prop where
  lower :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      -allowance N
        ≤ (finiteWeightBilinearSetIntegral
            (balancedVaughanHardWeight L N (u N) (v N))
            (balancedVonMangoldtWeight L N) N (retained N)).re

/--
Correct one-sided recombination.  It identifies the exact quantitative margin needed after the
tractable Type-I correlation has been evaluated.
-/
theorem balancedMaskedCorrelation_lower_bound
    {L Xmin : ℕ} {u v : ℕ → ℕ} {retained : ℕ → Set ℝ}
    {main retainedMain fullError retainedError hardAllowance : ℕ → ℝ}
    (hTypeI : BalancedVaughanTypeIFixedCenterEstimate
      L Xmin u retained main retainedMain fullError retainedError)
    (hHard : BalancedVaughanHardResidualLowerBound
      L Xmin u v retained hardAllowance)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    main N - retainedMain N - fullError N - retainedError N - hardAllowance N
      ≤ (finiteWeightBilinearSetComplementIntegral
          (balancedVonMangoldtWeight L N) (balancedVonMangoldtWeight L N) N
          (retained N)).re := by
  have hTypeIAbs := typeIMaskedCorrelation_approx hTypeI hN hEven
  have hTypeILower := (abs_le.mp hTypeIAbs).1
  have hHardLower := hHard.lower hN hEven
  have hSplit := congrArg Complex.re
    (balancedVonMangoldtMaskedCorrelation_eq_typeI_add_hard
      L N (u N) (v N) (retained N) (hTypeI.measurable N))
  rw [Complex.add_re] at hSplit
  linarith

/--
One-sided estimate for the retained part of the original von Mangoldt pair correlation.  Keeping
this input separate is essential: the Type-I complementary correlation may have a negative main
term because the positive `q = 1,2` contribution has deliberately been removed.
-/
structure BalancedRetainedPairLowerEstimate
    (L Xmin : ℕ) (retained : ℕ → Set ℝ)
    (main error : ℕ → ℝ) : Prop where
  lower :
    ∀ {N : ℕ}, Xmin ≤ N → Even N →
      main N - error N
        ≤ (finiteWeightBilinearSetIntegral
            (balancedVonMangoldtWeight L N) (balancedVonMangoldtWeight L N) N
            (retained N)).re

/--
Full-circle lower bound after restoring the retained von Mangoldt pair contribution.  The usable
main margin is

`typeIMain + (retainedPairMain - retainedTypeIMain)`,

not `typeIMain - retainedTypeIMain` by itself.  In particular, this theorem records the exact
cancellation that the retained-arc feasibility audit must establish before any Type-II estimate is
commissioned.
-/
theorem balancedFullCorrelation_lower_bound
    {L Xmin : ℕ} {u v : ℕ → ℕ} {retained : ℕ → Set ℝ}
    {typeIMain retainedTypeIMain typeIFullError retainedTypeIError : ℕ → ℝ}
    {retainedPairMain retainedPairError hardAllowance : ℕ → ℝ}
    (hTypeI : BalancedVaughanTypeIFixedCenterEstimate
      L Xmin u retained typeIMain retainedTypeIMain typeIFullError retainedTypeIError)
    (hHard : BalancedVaughanHardResidualLowerBound
      L Xmin u v retained hardAllowance)
    (hRetained : BalancedRetainedPairLowerEstimate
      L Xmin retained retainedPairMain retainedPairError)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    typeIMain N + (retainedPairMain N - retainedTypeIMain N)
        - typeIFullError N - retainedTypeIError N - retainedPairError N - hardAllowance N
      ≤ finiteWeightBilinearConvolution
          (balancedVonMangoldtWeight L N) (balancedVonMangoldtWeight L N) N := by
  have hMasked := balancedMaskedCorrelation_lower_bound hTypeI hHard hN hEven
  have hRetainedLower := hRetained.lower hN hEven
  have hCircle := congrArg Complex.re
    (finiteWeightBilinearConvolution_cast_eq_set_add_compl
      (balancedVonMangoldtWeight L N) (balancedVonMangoldtWeight L N) N
      (retained N) (hTypeI.measurable N))
  simp only [Complex.ofReal_re, Complex.add_re] at hCircle
  linarith

/--
Cancellation-safe full-circle recombination.  A full Type-I progression estimate is combined with
direct one-sided bounds for the retained and complementary pieces of the hard residual.  No
separate approximation to either large retained main is required.
-/
theorem balancedFullCorrelation_lower_bound_of_retainedHard
    {L Xmin : ℕ} {u v : ℕ → ℕ} {retained : ℕ → Set ℝ}
    {typeIMain typeIFullError retainedHardAllowance hardAllowance : ℕ → ℝ}
    (hTypeI : BalancedVaughanTypeIProgressionEstimate
      L Xmin u typeIMain typeIFullError)
    (hMeasurable : ∀ N, MeasurableSet (retained N))
    (hHard : BalancedVaughanHardResidualLowerBound
      L Xmin u v retained hardAllowance)
    (hRetainedHard : BalancedVaughanRetainedHardResidualLowerBound
      L Xmin u v retained retainedHardAllowance)
    {N : ℕ} (hN : Xmin ≤ N) (hEven : Even N) :
    typeIMain N - typeIFullError N
        - retainedHardAllowance N - hardAllowance N
      ≤ finiteWeightBilinearConvolution
          (balancedVonMangoldtWeight L N) (balancedVonMangoldtWeight L N) N := by
  have hTypeIAbs := typeIFullCorrelation_approx_of_progressionEstimate hTypeI hN hEven
  have hTypeILower := (abs_le.mp hTypeIAbs).1
  have hHardLower := hHard.lower hN hEven
  have hRetainedHardLower := hRetainedHard.lower hN hEven
  have hHardCircle := congrArg Complex.re
    (finiteWeightBilinearConvolution_cast_eq_set_add_compl
      (balancedVaughanHardWeight L N (u N) (v N))
      (balancedVonMangoldtWeight L N) N (retained N) (hMeasurable N))
  simp only [Complex.ofReal_re, Complex.add_re] at hHardCircle
  have hSplit := balancedVonMangoldtBilinearConvolution_eq_typeI_add_hard
    L N (u N) (v N)
  linarith

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface
