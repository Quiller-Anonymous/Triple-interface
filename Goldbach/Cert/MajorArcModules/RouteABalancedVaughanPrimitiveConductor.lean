import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
import Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Primitive-conductor fibers for the balanced Vaughan Type-I term

The character expansion is naturally indexed by pairs `(d, χ)` with `χ` a character modulo `d`.
This module constructs that finite dependent index set and partitions it by the canonical pair
`(χ.conductor, χ.primitiveCharacter)`. The result is exact finite bookkeeping; analytic character
estimates remain separate inputs.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanTypeIInterface
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion

noncomputable section

/-- A character together with the modulus at which it occurs. -/
abbrev CharacterOccurrence :=
  Σ q : ℕ, DirichletCharacter ℂ q

/-- A conductor together with the character at that conductor. -/
abbrev PrimitiveCharacterKey :=
  Σ r : ℕ, DirichletCharacter ℂ r

/-- The canonical primitive-character key of a level-character occurrence. -/
noncomputable def primitiveCharacterKey
    (p : CharacterOccurrence) : PrimitiveCharacterKey :=
  ⟨p.2.conductor, p.2.primitiveCharacter⟩

/-- The coprime Type-I moduli retained in the signed aggregate. -/
def coprimeTypeIModuli (N u : ℕ) : Finset ℕ :=
  (Finset.Icc 1 u).filter (Nat.Coprime N)

/-- All character occurrences above the retained Type-I moduli. -/
noncomputable def characterOccurrences (N u : ℕ) : Finset CharacterOccurrence :=
  (coprimeTypeIModuli N u).sigma fun d =>
    (Finset.univ : Finset (DirichletCharacter ℂ d))

/-- The finite set of primitive-character keys represented among the occurrences. -/
noncomputable def representedPrimitiveCharacterKeys
    (N u : ℕ) : Finset PrimitiveCharacterKey := by
  classical
  exact (characterOccurrences N u).image primitiveCharacterKey

/-- The occurrences inducing one fixed primitive-character key. -/
noncomputable def characterOccurrencesForKey
    (N u : ℕ) (key : PrimitiveCharacterKey) : Finset CharacterOccurrence := by
  classical
  exact (characterOccurrences N u).filter fun p => primitiveCharacterKey p = key

/-- Every occurrence sum is exactly the sum over its primitive-character fibers. -/
theorem sum_characterOccurrences_eq_sum_primitiveCharacterFibers
    (N u : ℕ) (F : CharacterOccurrence → ℂ) :
    ∑ p ∈ characterOccurrences N u, F p =
      ∑ key ∈ representedPrimitiveCharacterKeys N u,
        ∑ p ∈ characterOccurrencesForKey N u key, F p := by
  classical
  unfold representedPrimitiveCharacterKeys characterOccurrencesForKey
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := characterOccurrences N u)
    (t := (characterOccurrences N u).image primitiveCharacterKey)
    (g := primitiveCharacterKey)
    (fun p hp => Finset.mem_image_of_mem primitiveCharacterKey hp)
    F

/-- A generic real weighted sum of the coprime progression deviations at one endpoint. -/
noncomputable def signedCoprimeEWeightedSum
    (N u t : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ coprimeTypeIModuli N u,
    ((moebius d : ℤ) : ℝ) * w d *
      Goldbach.Cert.SiegelWalfiszWeighted.E (q := d) (a := N) t

/-- The primitive-character contribution of one `(modulus, character)` occurrence. -/
noncomputable def primitiveCharacterOccurrenceTerm
    (N t : ℕ) (w : ℕ → ℝ) (p : CharacterOccurrence) : ℂ :=
  ((((moebius p.1 : ℤ) : ℝ) : ℂ) * (w p.1 : ℂ)) *
    ((1 / (Nat.totient p.1 : ℂ)) *
      (p.2 ((N : ZMod p.1)⁻¹) *
        (dirichletPsi t p.2.conductor p.2.primitiveCharacter
          - inducedCharacterCorrection t p.1 p.2)))

/-- The linear main term removed in the definition of `E`, with the same outer weight. -/
noncomputable def signedCoprimeLinearMain
    (N u t : ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ d ∈ coprimeTypeIModuli N u,
    ((((moebius d : ℤ) : ℝ) : ℂ) * (w d : ℂ)) *
      ((t : ℂ) / (Nat.totient d : ℂ))

/-- One primitive-character fiber of the generic weighted deviation sum. -/
noncomputable def primitiveCharacterFiberContribution
    (N u t : ℕ) (w : ℕ → ℝ) (key : PrimitiveCharacterKey) : ℂ :=
  ∑ p ∈ characterOccurrencesForKey N u key,
    primitiveCharacterOccurrenceTerm N t w p

/-- Membership in a key fiber supplies both occurrence membership and the key equation. -/
theorem mem_characterOccurrencesForKey_data
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    p ∈ characterOccurrences N u ∧ primitiveCharacterKey p = key := by
  classical
  exact Finset.mem_filter.mp hp

/-- Every occurrence in a retained fiber has modulus coprime to the fixed center. -/
theorem occurrence_modulus_coprime
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    Nat.Coprime N p.1 := by
  have hpOccurrence := (mem_characterOccurrencesForKey_data hp).1
  have hpSigma := Finset.mem_sigma.mp hpOccurrence
  exact (Finset.mem_filter.mp hpSigma.1).2

/-- Every retained occurrence has a positive modulus. -/
theorem occurrence_modulus_pos
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    0 < p.1 := by
  have hpOccurrence := (mem_characterOccurrencesForKey_data hp).1
  have hpSigma := Finset.mem_sigma.mp hpOccurrence
  have hpIcc := (Finset.mem_filter.mp hpSigma.1).1
  exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hpIcc).1

/-- The primitive conductor attached to a fiber occurrence divides its level. -/
theorem occurrence_key_conductor_dvd_modulus
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    key.1 ∣ p.1 := by
  have hkey := (mem_characterOccurrencesForKey_data hp).2
  rw [← hkey]
  exact DirichletCharacter.conductor_dvd_level p.2

/-- A represented fiber key has positive conductor. -/
theorem occurrence_key_conductor_pos
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    0 < key.1 := by
  have hkey := (mem_characterOccurrencesForKey_data hp).2
  rw [← hkey]
  exact Nat.pos_of_ne_zero
    (DirichletCharacter.conductor_ne_zero p.2
      (Nat.ne_of_gt (occurrence_modulus_pos hp)))

/-- The conductor of every retained fiber is coprime to the fixed center. -/
theorem occurrence_key_conductor_coprime
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    Nat.Coprime N key.1 :=
  (occurrence_modulus_coprime hp).coprime_dvd_right
    (occurrence_key_conductor_dvd_modulus hp)

/-- The character stored in every represented key is primitive at its stated conductor. -/
theorem occurrence_key_isPrimitive
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    key.2.IsPrimitive := by
  have hkey := (mem_characterOccurrencesForKey_data hp).2
  rw [← hkey]
  exact DirichletCharacter.primitiveCharacter_isPrimitive p.2

/-- At a fixed level, the canonical primitive-character key determines the character. -/
theorem character_eq_of_primitiveCharacterKey_eq
    {q : ℕ} {χ ψ : DirichletCharacter ℂ q}
    (hkey : primitiveCharacterKey ⟨q, χ⟩ = primitiveCharacterKey ⟨q, ψ⟩) :
    χ = ψ := by
  have hχ := (DirichletCharacter.factorsThrough_conductor χ).eq_changeLevel
  have hψ := (DirichletCharacter.factorsThrough_conductor ψ).eq_changeLevel
  have hpackaged :
      (⟨primitiveCharacterKey ⟨q, χ⟩,
          DirichletCharacter.conductor_dvd_level χ⟩ :
          {key : PrimitiveCharacterKey // key.1 ∣ q}) =
        ⟨primitiveCharacterKey ⟨q, ψ⟩,
          DirichletCharacter.conductor_dvd_level ψ⟩ :=
    Subtype.ext hkey
  have hlift := congrArg
    (fun z : {key : PrimitiveCharacterKey // key.1 ∣ q} =>
      DirichletCharacter.changeLevel z.2 z.1.2)
    hpackaged
  have hlift' :
      DirichletCharacter.changeLevel
          (DirichletCharacter.conductor_dvd_level χ) χ.primitiveCharacter =
        DirichletCharacter.changeLevel
          (DirichletCharacter.conductor_dvd_level ψ) ψ.primitiveCharacter := by
    simpa [primitiveCharacterKey] using hlift
  exact hχ.trans (hlift'.trans hψ.symm)

/-- A fixed primitive fiber contains at most one character occurrence at each modulus. -/
theorem occurrence_eq_of_same_modulus
    {N u : ℕ} {key : PrimitiveCharacterKey} {p₁ p₂ : CharacterOccurrence}
    (hp₁ : p₁ ∈ characterOccurrencesForKey N u key)
    (hp₂ : p₂ ∈ characterOccurrencesForKey N u key)
    (hmod : p₁.1 = p₂.1) :
    p₁ = p₂ := by
  have hkey : primitiveCharacterKey p₁ = primitiveCharacterKey p₂ :=
    (mem_characterOccurrencesForKey_data hp₁).2.trans
      (mem_characterOccurrencesForKey_data hp₂).2.symm
  rcases p₁ with ⟨q, χ⟩
  rcases p₂ with ⟨q', ψ⟩
  dsimp only at hmod
  subst q'
  refine Sigma.ext (x := ⟨q, χ⟩) (y := ⟨q, ψ⟩) rfl ?_
  exact heq_of_eq (character_eq_of_primitiveCharacterKey_eq hkey)

/-- The inverse character coefficient is constant on each primitive-character fiber. -/
theorem occurrence_inv_eq_key_inv
    {N u : ℕ} {key : PrimitiveCharacterKey} {p : CharacterOccurrence}
    (hp : p ∈ characterOccurrencesForKey N u key) :
    p.2 ((N : ZMod p.1)⁻¹) = key.2 ((N : ZMod key.1)⁻¹) := by
  have hkey := (mem_characterOccurrencesForKey_data hp).2
  rw [← hkey]
  exact apply_inv_eq_primitiveCharacter_inv_of_coprime p.2
    (occurrence_modulus_coprime hp)

/-- The real signed lift weight carried by one primitive-character fiber. -/
noncomputable def primitiveCharacterFiberWeight
    (N u : ℕ) (w : ℕ → ℝ) (key : PrimitiveCharacterKey) : ℝ :=
  ∑ p ∈ characterOccurrencesForKey N u key,
    ((moebius p.1 : ℤ) : ℝ) * w p.1 / (Nat.totient p.1 : ℝ)

/-- The induced-character correction retained inside one primitive-character fiber. -/
noncomputable def primitiveCharacterFiberInducedCorrection
    (N u t : ℕ) (w : ℕ → ℝ) (key : PrimitiveCharacterKey) : ℂ :=
  ∑ p ∈ characterOccurrencesForKey N u key,
    (((((moebius p.1 : ℤ) : ℝ) * w p.1 /
        (Nat.totient p.1 : ℝ)) : ℂ) *
      key.2 ((N : ZMod key.1)⁻¹)) * inducedCharacterCorrection t p.1 p.2

/--
Each fiber is one primitive `psi` value times its signed lift weight, minus the exact correction
from replacing the induced level characters by that primitive character.
-/
theorem primitiveCharacterFiberContribution_eq_main_sub_inducedCorrection
    (N u t : ℕ) (w : ℕ → ℝ) (key : PrimitiveCharacterKey) :
    primitiveCharacterFiberContribution N u t w key =
      key.2 ((N : ZMod key.1)⁻¹) * dirichletPsi t key.1 key.2 *
          (primitiveCharacterFiberWeight N u w key : ℂ)
        - primitiveCharacterFiberInducedCorrection N u t w key := by
  classical
  unfold primitiveCharacterFiberContribution primitiveCharacterOccurrenceTerm
    primitiveCharacterFiberWeight primitiveCharacterFiberInducedCorrection
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hkey := (mem_characterOccurrencesForKey_data hp).2
  have hinv := occurrence_inv_eq_key_inv hp
  rw [hinv]
  cases hkey
  simp only [primitiveCharacterKey]
  ring

/--
Exact expansion of a weighted signed progression-error sum over all character occurrences. This is
the common algebraic surface for the endpoint and finite-difference terms in partial summation.
-/
theorem signedCoprimeEWeightedSum_eq_characterOccurrences
    {N u t : ℕ} (w : ℕ → ℝ) :
    (signedCoprimeEWeightedSum N u t w : ℂ) =
      ∑ p ∈ characterOccurrences N u,
          primitiveCharacterOccurrenceTerm N t w p
        - signedCoprimeLinearMain N u t w := by
  classical
  unfold signedCoprimeEWeightedSum signedCoprimeLinearMain
    characterOccurrences primitiveCharacterOccurrenceTerm
  push_cast
  rw [Finset.sum_sigma]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdParts := Finset.mem_filter.mp hd
  have hdPos : 0 < d := by
    exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdParts.1).1
  have hNd : Nat.Coprime N d := hdParts.2
  rw [E_eq_primitiveCharacterAverage_sub_corrections hdPos hNd]
  rw [mul_sub]
  simp only [Finset.mul_sum]

/-- Exact regrouping of the generic weighted deviation sum by canonical primitive character. -/
theorem signedCoprimeEWeightedSum_eq_primitiveCharacterFibers
    {N u t : ℕ} (w : ℕ → ℝ) :
    (signedCoprimeEWeightedSum N u t w : ℂ) =
      ∑ key ∈ representedPrimitiveCharacterKeys N u,
          primitiveCharacterFiberContribution N u t w key
        - signedCoprimeLinearMain N u t w := by
  rw [signedCoprimeEWeightedSum_eq_characterOccurrences w]
  congr 1
  rw [sum_characterOccurrences_eq_sum_primitiveCharacterFibers]
  apply Finset.sum_congr rfl
  intro key hkey
  rfl

/-- The upper-endpoint weight in the exact Type-I partial-summation formula. -/
noncomputable def upperEndpointWeight (L N d : ℕ) : ℝ :=
  balancedVaughanTypeILogWeight N d (N - L)

/-- The lower-endpoint weight in the exact Type-I partial-summation formula. -/
noncomputable def lowerEndpointWeight (L N d : ℕ) : ℝ :=
  balancedVaughanTypeILogWeight N d (L - 1)

/-- The finite-difference weight at one interior partial-summation index. -/
noncomputable def interiorDifferenceWeight (N n d : ℕ) : ℝ :=
  balancedVaughanTypeILogWeight N d (n + 1)
    - balancedVaughanTypeILogWeight N d n

/--
The exact signed partial-summation expression, written as generic weighted deviation sums. This is
the bridge from the checked Type-I formula to the primitive-character fiber theorem above.
-/
noncomputable def signedCoprimePartialSummationWeightedForm
    (L N u : ℕ) : ℝ :=
  signedCoprimeEWeightedSum N u (N - L) (upperEndpointWeight L N)
    - signedCoprimeEWeightedSum N u (L - 1) (lowerEndpointWeight L N)
    - ∑ n ∈ Finset.Ico (L - 1) (N - L),
        signedCoprimeEWeightedSum N u n (interiorDifferenceWeight N n)

/-- The weighted-sum form is exactly the original signed partial-summation error. -/
theorem balancedVaughanTypeISignedCoprimePartialSummationError_eq_weightedForm
    (L N u : ℕ) :
    balancedVaughanTypeISignedCoprimePartialSummationError L N u =
      signedCoprimePartialSummationWeightedForm L N u := by
  classical
  unfold balancedVaughanTypeISignedCoprimePartialSummationError
    signedCoprimePartialSummationWeightedForm signedCoprimeEWeightedSum
    coprimeTypeIModuli upperEndpointWeight lowerEndpointWeight
    interiorDifferenceWeight
  simp_rw [mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- A generic weighted deviation sum after exact primitive-character regrouping. -/
noncomputable def primitiveCharacterRegroupedWeightedSum
    (N u t : ℕ) (w : ℕ → ℝ) : ℂ :=
  ∑ key ∈ representedPrimitiveCharacterKeys N u,
      primitiveCharacterFiberContribution N u t w key
    - signedCoprimeLinearMain N u t w

/-- The three-part primitive-character expansion of the actual signed Type-I error. -/
noncomputable def primitiveCharacterRegroupedPartialSummation
    (L N u : ℕ) : ℂ :=
  primitiveCharacterRegroupedWeightedSum N u (N - L) (upperEndpointWeight L N)
    - primitiveCharacterRegroupedWeightedSum N u (L - 1) (lowerEndpointWeight L N)
    - ∑ n ∈ Finset.Ico (L - 1) (N - L),
        primitiveCharacterRegroupedWeightedSum N u n (interiorDifferenceWeight N n)

/--
Exact primitive-conductor regrouping of the checked signed Type-I partial-summation error. No
character estimate or correction bound is used.
-/
theorem balancedVaughanTypeISignedCoprimePartialSummationError_cast_eq_primitiveCharacterRegrouped
    (L N u : ℕ) :
    (balancedVaughanTypeISignedCoprimePartialSummationError L N u : ℂ) =
      primitiveCharacterRegroupedPartialSummation L N u := by
  rw [balancedVaughanTypeISignedCoprimePartialSummationError_eq_weightedForm]
  unfold signedCoprimePartialSummationWeightedForm
    primitiveCharacterRegroupedPartialSummation
    primitiveCharacterRegroupedWeightedSum
  push_cast
  rw [signedCoprimeEWeightedSum_eq_primitiveCharacterFibers]
  rw [signedCoprimeEWeightedSum_eq_primitiveCharacterFibers]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [signedCoprimeEWeightedSum_eq_primitiveCharacterFibers]

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
