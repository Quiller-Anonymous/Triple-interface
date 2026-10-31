import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
import Goldbach.Cert.MajorArcStep4FullExpSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Explicit induced-character correction bounds

Replacing a character by its canonical primitive character changes only the von Mangoldt terms
whose index is not coprime to the original level.  Those indices are prime powers supported on
primes dividing the level.  This module converts that observation into a checked, explicit bound
using the prime-power estimate already proved in `MajorArcStep4FullExpSum`.
-/

namespace Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrection

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor

noncomputable section

/-- Taking a remainder modulo `q` does not change coprimality with `q`. -/
theorem coprime_mod_left_iff (n q : ℕ) :
    Nat.Coprime (n % q) q ↔ Nat.Coprime n q := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one]
  rw [← Nat.gcd_rec q n, Nat.gcd_comm q n]

/-- The scalar von Mangoldt mass on which the induced-character correction is supported. -/
noncomputable def inducedCharacterCorrectionMass (x q : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1),
    if ¬Nat.Coprime n q then |ΛVM n| else 0

/-- The norm of the exact correction is at most its supporting von Mangoldt mass. -/
theorem norm_inducedCharacterCorrection_le_mass
    (x q : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖inducedCharacterCorrection x q χ‖ ≤ inducedCharacterCorrectionMass x q := by
  classical
  unfold inducedCharacterCorrection inducedCharacterCorrectionMass
  calc
    ‖∑ n ∈ Finset.range (x + 1),
        if Nat.Coprime n q then 0
        else (ΛVM n : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
        ∑ n ∈ Finset.range (x + 1),
          ‖if Nat.Coprime n q then 0
            else (ΛVM n : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (x + 1),
        if ¬Nat.Coprime n q then |ΛVM n| else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hcop : Nat.Coprime n q
      · simp [hcop]
      · simp only [hcop, not_false_eq_true, if_false, if_true, norm_mul]
        rw [show ‖(ΛVM n : ℂ)‖ = |ΛVM n| by
          exact Complex.norm_real (ΛVM n)]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (DirichletCharacter.norm_le_one χ.primitiveCharacter _)

/-- The existing bad-residue theorem supplies a fully explicit correction-mass estimate. -/
theorem inducedCharacterCorrectionMass_le
    {x q : ℕ} (hq : 1 ≤ q) :
    inducedCharacterCorrectionMass x q ≤
      (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log (q : ℝ) := by
  simpa [inducedCharacterCorrectionMass, Nat.Ico_zero_eq_range,
    coprime_mod_left_iff] using
    (Goldbach.Cert.MajorArcStep4FullExpSum.sum_Ico_bad_vonMangoldt_le
      (q := q) hq (L := 0) (U := x) (Nat.zero_le x))

/-- A uniform explicit norm bound for every induced-character correction at level `q`. -/
theorem norm_inducedCharacterCorrection_le
    {x q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q) :
    ‖inducedCharacterCorrection x q χ‖ ≤
      (((q + 1) * (Nat.log 2 x + 1) : ℕ) : ℝ) * Real.log (q : ℝ) :=
  (norm_inducedCharacterCorrection_le_mass x q χ).trans
    (inducedCharacterCorrectionMass_le hq)

/-- One occurrence's induced-character correction, including its signed Type-I coefficient. -/
noncomputable def primitiveCharacterOccurrenceInducedCorrectionTerm
    (N t : ℕ) (w : ℕ → ℝ) (p : CharacterOccurrence) : ℂ :=
  (((((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) * w p.1 /
      (Nat.totient p.1 : ℝ)) : ℂ) * p.2 ((N : ZMod p.1)⁻¹)) *
    inducedCharacterCorrection t p.1 p.2

/-- One fiber correction is exactly the sum of its occurrence-level corrections. -/
theorem primitiveCharacterFiberInducedCorrection_eq_occurrenceSum
    {N u t : ℕ} (w : ℕ → ℝ) (key : PrimitiveCharacterKey) :
    primitiveCharacterFiberInducedCorrection N u t w key =
      ∑ p ∈ characterOccurrencesForKey N u key,
        primitiveCharacterOccurrenceInducedCorrectionTerm N t w p := by
  classical
  unfold primitiveCharacterFiberInducedCorrection
    primitiveCharacterOccurrenceInducedCorrectionTerm
  apply Finset.sum_congr rfl
  intro p hp
  rw [occurrence_inv_eq_key_inv hp]

/-- The complete induced-character correction in one generic weighted endpoint sum. -/
noncomputable def primitiveCharacterTotalInducedCorrection
    (N u t : ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ key ∈ representedPrimitiveCharacterKeys N u,
    primitiveCharacterFiberInducedCorrection N u t w key

/-- The complete fiber correction is the corresponding sum over all level-character occurrences. -/
theorem primitiveCharacterTotalInducedCorrection_eq_occurrenceSum
    (N u t : ℕ) (w : ℕ → ℝ) :
    primitiveCharacterTotalInducedCorrection N u t w =
      ∑ p ∈ characterOccurrences N u,
        primitiveCharacterOccurrenceInducedCorrectionTerm N t w p := by
  classical
  unfold primitiveCharacterTotalInducedCorrection
  calc
    (∑ key ∈ representedPrimitiveCharacterKeys N u,
        primitiveCharacterFiberInducedCorrection N u t w key) =
        ∑ key ∈ representedPrimitiveCharacterKeys N u,
          ∑ p ∈ characterOccurrencesForKey N u key,
            primitiveCharacterOccurrenceInducedCorrectionTerm N t w p := by
      apply Finset.sum_congr rfl
      intro key hkey
      exact primitiveCharacterFiberInducedCorrection_eq_occurrenceSum w key
    _ = ∑ p ∈ characterOccurrences N u,
        primitiveCharacterOccurrenceInducedCorrectionTerm N t w p :=
      (sum_characterOccurrences_eq_sum_primitiveCharacterFibers
        N u (primitiveCharacterOccurrenceInducedCorrectionTerm N t w)).symm

/-- Explicit levelwise majorant used for the aggregate induced-character correction. -/
noncomputable def inducedCharacterCorrectionLevelBound (t q : ℕ) : ℝ :=
  (((q + 1) * (Nat.log 2 t + 1) : ℕ) : ℝ) * Real.log (q : ℝ)

/-- One occurrence is bounded after retaining the exact `1 / φ(q)` normalization. -/
theorem norm_primitiveCharacterOccurrenceInducedCorrectionTerm_le
    {N u t : ℕ} (w : ℕ → ℝ) {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrences N u) :
    ‖primitiveCharacterOccurrenceInducedCorrectionTerm N t w p‖ ≤
      |w p.1| / (Nat.totient p.1 : ℝ) *
        inducedCharacterCorrectionLevelBound t p.1 := by
  have hpSigma := Finset.mem_sigma.mp hp
  have hpIcc := (Finset.mem_filter.mp hpSigma.1).1
  have hpPos : 0 < p.1 :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpIcc).1
  have htotient : (0 : ℝ) < Nat.totient p.1 := by
    exact_mod_cast Nat.totient_pos.mpr hpPos
  have hMoebius :
      |(((ArithmeticFunction.moebius p.1 : ℤ) : ℝ))| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := p.1))
  have hcoefficient :
      |(((ArithmeticFunction.moebius p.1 : ℤ) : ℝ))| * |w p.1| /
          (Nat.totient p.1 : ℝ) ≤
        |w p.1| / (Nat.totient p.1 : ℝ) := by
    exact div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_right hMoebius (abs_nonneg (w p.1)))
      htotient.le
  have hcoefficientComplex :
      ‖((((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) : ℂ) * (w p.1 : ℂ) /
          ((Nat.totient p.1 : ℝ) : ℂ))‖ ≤
        |w p.1| / (Nat.totient p.1 : ℝ) := by
    simpa [norm_div, norm_mul, abs_of_pos htotient] using hcoefficient
  have hfirst :
      ‖((((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) : ℂ) * (w p.1 : ℂ) /
          ((Nat.totient p.1 : ℝ) : ℂ))‖ * ‖p.2 ((N : ZMod p.1)⁻¹)‖ ≤
        |w p.1| / (Nat.totient p.1 : ℝ) := by
    calc
      ‖((((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) : ℂ) * (w p.1 : ℂ) /
          ((Nat.totient p.1 : ℝ) : ℂ))‖ * ‖p.2 ((N : ZMod p.1)⁻¹)‖ ≤
          (|w p.1| / (Nat.totient p.1 : ℝ)) * 1 := by
        exact mul_le_mul hcoefficientComplex (DirichletCharacter.norm_le_one p.2 _)
          (norm_nonneg _) (by positivity)
      _ = |w p.1| / (Nat.totient p.1 : ℝ) := mul_one _
  unfold primitiveCharacterOccurrenceInducedCorrectionTerm
  rw [norm_mul, norm_mul]
  exact mul_le_mul hfirst
    (by simpa [inducedCharacterCorrectionLevelBound] using
      norm_inducedCharacterCorrection_le hpPos p.2)
    (norm_nonneg _) (by positivity)

/--
After summing all characters at each level, their cardinality cancels the exact totient
normalization.  This bounds the complete induced correction without any conductor-lift theorem.
-/
theorem norm_primitiveCharacterTotalInducedCorrection_le
    (N u t : ℕ) (w : ℕ → ℝ) :
    ‖primitiveCharacterTotalInducedCorrection N u t w‖ ≤
      ∑ d ∈ coprimeTypeIModuli N u,
        |w d| * inducedCharacterCorrectionLevelBound t d := by
  classical
  rw [primitiveCharacterTotalInducedCorrection_eq_occurrenceSum]
  calc
    ‖∑ p ∈ characterOccurrences N u,
        primitiveCharacterOccurrenceInducedCorrectionTerm N t w p‖ ≤
        ∑ p ∈ characterOccurrences N u,
          ‖primitiveCharacterOccurrenceInducedCorrectionTerm N t w p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ characterOccurrences N u,
        (|w p.1| / (Nat.totient p.1 : ℝ)) *
          inducedCharacterCorrectionLevelBound t p.1 := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_primitiveCharacterOccurrenceInducedCorrectionTerm_le w hp
    _ = ∑ d ∈ coprimeTypeIModuli N u,
        |w d| * inducedCharacterCorrectionLevelBound t d := by
      unfold characterOccurrences
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro d hd
      have hdIcc := (Finset.mem_filter.mp hd).1
      have hdPos : 0 < d :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdIcc).1
      letI : NeZero d := ⟨hdPos.ne'⟩
      have hcard : Nat.card (DirichletCharacter ℂ d) = Nat.totient d :=
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
      have htotient : (Nat.totient d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hdPos).ne'
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, hcard]
      field_simp

/-- The primitive-character part of one weighted endpoint sum, before correction terms. -/
noncomputable def primitiveCharacterTotalMain
    (N u t : ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ key ∈ representedPrimitiveCharacterKeys N u,
    key.2 ((N : ZMod key.1)⁻¹) * dirichletPsi t key.1 key.2 *
      (primitiveCharacterFiberWeight N u w key : ℂ)

/-- Exact three-way decomposition of one regrouped weighted endpoint sum. -/
theorem primitiveCharacterRegroupedWeightedSum_eq_main_sub_corrections
    (N u t : ℕ) (w : ℕ → ℝ) :
    primitiveCharacterRegroupedWeightedSum N u t w =
      primitiveCharacterTotalMain N u t w
        - primitiveCharacterTotalInducedCorrection N u t w
        - signedCoprimeLinearMain N u t w := by
  classical
  unfold primitiveCharacterRegroupedWeightedSum primitiveCharacterTotalMain
    primitiveCharacterTotalInducedCorrection
  rw [← Finset.sum_sub_distrib]
  apply congrArg (fun z : ℂ => z - signedCoprimeLinearMain N u t w)
  apply Finset.sum_congr rfl
  intro key hkey
  exact primitiveCharacterFiberContribution_eq_main_sub_inducedCorrection N u t w key

/-- Primitive-character main part of the exact Type-I partial-summation expression. -/
noncomputable def primitiveCharacterMainPartialSummation
    (L N u : ℕ) : ℂ :=
  primitiveCharacterTotalMain N u (N - L) (upperEndpointWeight L N)
    - primitiveCharacterTotalMain N u (L - 1) (lowerEndpointWeight L N)
    - ∑ n ∈ Finset.Ico (L - 1) (N - L),
        primitiveCharacterTotalMain N u n (interiorDifferenceWeight N n)

/-- Induced-character correction in the exact Type-I partial-summation expression. -/
noncomputable def primitiveCharacterInducedCorrectionPartialSummation
    (L N u : ℕ) : ℂ :=
  primitiveCharacterTotalInducedCorrection N u (N - L) (upperEndpointWeight L N)
    - primitiveCharacterTotalInducedCorrection N u (L - 1) (lowerEndpointWeight L N)
    - ∑ n ∈ Finset.Ico (L - 1) (N - L),
        primitiveCharacterTotalInducedCorrection N u n (interiorDifferenceWeight N n)

/-- Linear-main correction in the exact Type-I partial-summation expression. -/
noncomputable def signedCoprimeLinearMainPartialSummation
    (L N u : ℕ) : ℂ :=
  signedCoprimeLinearMain N u (N - L) (upperEndpointWeight L N)
    - signedCoprimeLinearMain N u (L - 1) (lowerEndpointWeight L N)
    - ∑ n ∈ Finset.Ico (L - 1) (N - L),
        signedCoprimeLinearMain N u n (interiorDifferenceWeight N n)

/-- The checked Type-I error is primitive main minus the two explicit correction terms. -/
theorem balancedVaughanTypeISignedCoprimePartialSummationError_cast_eq_main_sub_corrections
    (L N u : ℕ) :
    (balancedVaughanTypeISignedCoprimePartialSummationError L N u : ℂ) =
      primitiveCharacterMainPartialSummation L N u
        - primitiveCharacterInducedCorrectionPartialSummation L N u
        - signedCoprimeLinearMainPartialSummation L N u := by
  rw [balancedVaughanTypeISignedCoprimePartialSummationError_cast_eq_primitiveCharacterRegrouped]
  unfold primitiveCharacterRegroupedPartialSummation
    primitiveCharacterMainPartialSummation
    primitiveCharacterInducedCorrectionPartialSummation
    signedCoprimeLinearMainPartialSummation
  rw [primitiveCharacterRegroupedWeightedSum_eq_main_sub_corrections]
  rw [primitiveCharacterRegroupedWeightedSum_eq_main_sub_corrections]
  simp_rw [primitiveCharacterRegroupedWeightedSum_eq_main_sub_corrections]
  simp_rw [Finset.sum_sub_distrib]
  ring

/-- Endpoint majorant for the complete induced-character correction. -/
noncomputable def primitiveCharacterInducedCorrectionWeightedBound
    (N u t : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ coprimeTypeIModuli N u,
    |w d| * inducedCharacterCorrectionLevelBound t d

/-- Explicit finite majorant for the induced correction after partial summation. -/
noncomputable def primitiveCharacterInducedCorrectionPartialSummationBound
    (L N u : ℕ) : ℝ :=
  primitiveCharacterInducedCorrectionWeightedBound
      N u (N - L) (upperEndpointWeight L N)
    + primitiveCharacterInducedCorrectionWeightedBound
      N u (L - 1) (lowerEndpointWeight L N)
    + ∑ n ∈ Finset.Ico (L - 1) (N - L),
        primitiveCharacterInducedCorrectionWeightedBound
          N u n (interiorDifferenceWeight N n)

/-- The exact induced correction satisfies its explicit finite partial-summation majorant. -/
theorem norm_primitiveCharacterInducedCorrectionPartialSummation_le
    (L N u : ℕ) :
    ‖primitiveCharacterInducedCorrectionPartialSummation L N u‖ ≤
      primitiveCharacterInducedCorrectionPartialSummationBound L N u := by
  let upper := primitiveCharacterTotalInducedCorrection
    N u (N - L) (upperEndpointWeight L N)
  let lower := primitiveCharacterTotalInducedCorrection
    N u (L - 1) (lowerEndpointWeight L N)
  let interior : ℕ → ℂ := fun n =>
    primitiveCharacterTotalInducedCorrection
      N u n (interiorDifferenceWeight N n)
  let upperBound := primitiveCharacterInducedCorrectionWeightedBound
    N u (N - L) (upperEndpointWeight L N)
  let lowerBound := primitiveCharacterInducedCorrectionWeightedBound
    N u (L - 1) (lowerEndpointWeight L N)
  let interiorBound : ℕ → ℝ := fun n =>
    primitiveCharacterInducedCorrectionWeightedBound
      N u n (interiorDifferenceWeight N n)
  have hUpper : ‖upper‖ ≤ upperBound := by
    simpa [upper, upperBound, primitiveCharacterInducedCorrectionWeightedBound] using
      norm_primitiveCharacterTotalInducedCorrection_le
        N u (N - L) (upperEndpointWeight L N)
  have hLower : ‖lower‖ ≤ lowerBound := by
    simpa [lower, lowerBound, primitiveCharacterInducedCorrectionWeightedBound] using
      norm_primitiveCharacterTotalInducedCorrection_le
        N u (L - 1) (lowerEndpointWeight L N)
  have hInterior : ∀ n, ‖interior n‖ ≤ interiorBound n := by
    intro n
    simpa [interior, interiorBound,
      primitiveCharacterInducedCorrectionWeightedBound] using
      norm_primitiveCharacterTotalInducedCorrection_le
        N u n (interiorDifferenceWeight N n)
  unfold primitiveCharacterInducedCorrectionPartialSummation
    primitiveCharacterInducedCorrectionPartialSummationBound
  change ‖upper - lower - ∑ n ∈ Finset.Ico (L - 1) (N - L), interior n‖ ≤
    upperBound + lowerBound +
      ∑ n ∈ Finset.Ico (L - 1) (N - L), interiorBound n
  calc
    ‖upper - lower - ∑ n ∈ Finset.Ico (L - 1) (N - L), interior n‖ ≤
        ‖upper - lower‖ +
          ‖∑ n ∈ Finset.Ico (L - 1) (N - L), interior n‖ :=
      norm_sub_le _ _
    _ ≤ (‖upper‖ + ‖lower‖) +
        ∑ n ∈ Finset.Ico (L - 1) (N - L), ‖interior n‖ :=
      add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ ≤ (upperBound + lowerBound) +
        ∑ n ∈ Finset.Ico (L - 1) (N - L), interiorBound n := by
      apply add_le_add (add_le_add hUpper hLower)
      apply Finset.sum_le_sum
      intro n hn
      exact hInterior n

end

end Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrection
