import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight

/-!
# Character expansion on the active balanced Vaughan Type-I surface

The logarithmic conductor weight is supported on `d ≤ N - p`.  This module expands the corrected
active progression error, rather than the older uniform-endpoint comparison error, into its exact
finite Dirichlet-character sum.  It then partitions the character occurrences by canonical
primitive-character key.  No conductor-lift completeness or analytic character estimate is used.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorWeight
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion

noncomputable section

/-- Character occurrences over the active Type-I moduli at one fixed prime index. -/
noncomputable def activeCharacterOccurrencesAt
    (N u p : ℕ) : Finset CharacterOccurrence :=
  (activeCoprimeTypeIModuliAt N u p).sigma fun d =>
    (Finset.univ : Finset (DirichletCharacter ℂ d))

/-- Primitive-character keys represented at one fixed prime index. -/
noncomputable def activeRepresentedPrimitiveCharacterKeysAt
    (N u p : ℕ) : Finset PrimitiveCharacterKey := by
  classical
  exact (activeCharacterOccurrencesAt N u p).image primitiveCharacterKey

/-- Active occurrences inducing one fixed primitive-character key. -/
noncomputable def activeCharacterOccurrencesForKeyAt
    (N u p : ℕ) (key : PrimitiveCharacterKey) : Finset CharacterOccurrence := by
  classical
  exact (activeCharacterOccurrencesAt N u p).filter fun occurrence =>
    primitiveCharacterKey occurrence = key

/-- Every active occurrence sum partitions exactly into canonical primitive-character fibers. -/
theorem sum_activeCharacterOccurrences_eq_sum_primitiveCharacterFibers
    (N u p : ℕ) (F : CharacterOccurrence → ℂ) :
    ∑ occurrence ∈ activeCharacterOccurrencesAt N u p, F occurrence =
      ∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
        ∑ occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key,
          F occurrence := by
  classical
  unfold activeRepresentedPrimitiveCharacterKeysAt activeCharacterOccurrencesForKeyAt
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := activeCharacterOccurrencesAt N u p)
    (t := (activeCharacterOccurrencesAt N u p).image primitiveCharacterKey)
    (g := primitiveCharacterKey)
    (fun occurrence hOccurrence =>
      Finset.mem_image_of_mem primitiveCharacterKey hOccurrence)
    F

/-- The signed logarithmic coefficient attached to one active character occurrence. -/
noncomputable def activeCharacterOccurrenceCoefficient
    (N p : ℕ) (occurrence : CharacterOccurrence) : ℝ :=
  ((moebius occurrence.1 : ℤ) : ℝ) / (Nat.totient occurrence.1 : ℝ) *
    Real.log ((N - p) / occurrence.1)

/-- One level-character term in the active pointwise progression error. -/
noncomputable def activeCharacterOccurrenceTerm
    (N p : ℕ) (occurrence : CharacterOccurrence) : ℂ :=
  (activeCharacterOccurrenceCoefficient N p occurrence : ℂ) *
    occurrence.2 ((N : ZMod occurrence.1)⁻¹) *
      ((ΛVM p : ℂ) * occurrence.2 (p : ZMod occurrence.1))

/-- The linear term subtracted from the active character average at one fixed prime index. -/
noncomputable def activeCharacterLinearMainAt
    (N u p : ℕ) : ℝ :=
  ∑ d ∈ activeCoprimeTypeIModuliAt N u p,
    ((moebius d : ℤ) : ℝ) / (Nat.totient d : ℝ) *
      Real.log ((N - p) / d)

/-- The active pointwise error after exact expansion over all level characters. -/
noncomputable def activeCharacterExpandedErrorAt
    (N u p : ℕ) : ℂ :=
  (∑ occurrence ∈ activeCharacterOccurrencesAt N u p,
      activeCharacterOccurrenceTerm N p occurrence)
    - (activeCharacterLinearMainAt N u p : ℂ)

/-- Character orthogonality expands one residue-class von Mangoldt summand exactly. -/
theorem aTerm_cast_eq_characterAverage
    {N d p : ℕ} (hd : 0 < d) (hNd : Nat.Coprime N d) :
    (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := d) (a := N) p : ℂ) =
      (1 / (Nat.totient d : ℂ)) *
        ∑ χ : DirichletCharacter ℂ d,
          χ ((N : ZMod d)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod d)) := by
  have hIndicator :=
    reducedResidueIndicator_eq_characterAverage (q := d) (a := N) (n := p) hd hNd
  calc
    (Goldbach.Cert.SiegelWalfiszWeighted.aTerm (q := d) (a := N) p : ℂ) =
        (ΛVM p : ℂ) * (if Nat.ModEq d p N then (1 : ℂ) else 0) := by
      by_cases hmod : Nat.ModEq d p N <;>
        simp [Goldbach.Cert.SiegelWalfiszWeighted.aTerm, hmod]
    _ = (ΛVM p : ℂ) *
        ((1 / (Nat.totient d : ℂ)) *
          ∑ χ : DirichletCharacter ℂ d,
            χ ((N : ZMod d)⁻¹) * χ (p : ZMod d)) := by
      rw [hIndicator]
    _ = (1 / (Nat.totient d : ℂ)) *
        ∑ χ : DirichletCharacter ℂ d,
          χ ((N : ZMod d)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod d)) := by
      calc
        (ΛVM p : ℂ) *
            ((1 / (Nat.totient d : ℂ)) *
              ∑ χ : DirichletCharacter ℂ d,
                χ ((N : ZMod d)⁻¹) * χ (p : ZMod d)) =
            (1 / (Nat.totient d : ℂ)) *
              ((ΛVM p : ℂ) *
                ∑ χ : DirichletCharacter ℂ d,
                  χ ((N : ZMod d)⁻¹) * χ (p : ZMod d)) := by ring
        _ = (1 / (Nat.totient d : ℂ)) *
              ∑ χ : DirichletCharacter ℂ d,
                (ΛVM p : ℂ) *
                  (χ ((N : ZMod d)⁻¹) * χ (p : ZMod d)) := by
            rw [Finset.mul_sum]
        _ = (1 / (Nat.totient d : ℂ)) *
              ∑ χ : DirichletCharacter ℂ d,
                χ ((N : ZMod d)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod d)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro χ hχ
            ring

/-- Exact character expansion of one active progression-deviation increment. -/
theorem activeProgressionDeviationIncrement_cast_eq_characterAverage_sub_main
    {N d p : ℕ} (hd : 0 < d) (hNd : Nat.Coprime N d) :
    (activeProgressionDeviationIncrement N d p : ℂ) =
      (1 / (Nat.totient d : ℂ)) *
          ∑ χ : DirichletCharacter ℂ d,
            χ ((N : ZMod d)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod d))
        - 1 / (Nat.totient d : ℂ) := by
  unfold activeProgressionDeviationIncrement
  push_cast
  rw [aTerm_cast_eq_characterAverage hd hNd]

/-- The active pointwise modulus sum is exactly its character expansion minus the linear term. -/
theorem activePointwiseModulusSum_cast_eq_characterExpandedErrorAt
    (N u p : ℕ) :
    ((∑ d ∈ activeCoprimeTypeIModuliAt N u p,
        ((moebius d : ℤ) : ℝ) * activeProgressionDeviationIncrement N d p *
          Real.log ((N - p) / d) : ℝ) : ℂ) =
      activeCharacterExpandedErrorAt N u p := by
  classical
  unfold activeCharacterExpandedErrorAt activeCharacterOccurrencesAt
    activeCharacterOccurrenceTerm activeCharacterOccurrenceCoefficient
    activeCharacterLinearMainAt
  rw [Finset.sum_sigma]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  have hdPos : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdInner.1).1
  have hNd : Nat.Coprime N d := hdInner.2
  rw [activeProgressionDeviationIncrement_cast_eq_characterAverage_sub_main hdPos hNd]
  rw [Finset.mul_sum]
  have hCharacterPart :
      ((moebius d : ℤ) : ℂ) *
          (∑ χ : DirichletCharacter ℂ d,
            (1 / (Nat.totient d : ℂ)) *
              (χ ((N : ZMod d)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod d)))) *
          (Real.log ((N - p) / d) : ℂ) =
        ∑ χ : DirichletCharacter ℂ d,
          ((moebius d : ℤ) : ℂ) / (Nat.totient d : ℂ) *
            (Real.log ((N - p) / d) : ℂ) *
              χ ((N : ZMod d)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod d)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  rw [mul_sub, sub_mul, hCharacterPart]
  ring

/-- Exact active Type-I character expansion before primitive-conductor regrouping. -/
theorem activeCoprimeProgressionError_cast_eq_characterExpanded
    {L N u : ℕ} (hL : 0 < L) :
    (balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ) =
      ∑ p ∈ balancedCandidateSupport L N,
        activeCharacterExpandedErrorAt N u p := by
  rw [activeCoprimeProgressionError_eq_pointwiseModulusSum hL]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  simpa using activePointwiseModulusSum_cast_eq_characterExpandedErrorAt N u p

/-- One active primitive-character fiber at a fixed prime index. -/
noncomputable def activePrimitiveCharacterFiberContributionAt
    (N u p : ℕ) (key : PrimitiveCharacterKey) : ℂ :=
  ∑ occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key,
    activeCharacterOccurrenceTerm N p occurrence

/-- Membership in an active key fiber supplies both occurrence membership and its key equation. -/
theorem mem_activeCharacterOccurrencesForKeyAt_data
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    occurrence ∈ activeCharacterOccurrencesAt N u p ∧
      primitiveCharacterKey occurrence = key := by
  classical
  exact Finset.mem_filter.mp hOccurrence

/-- The modulus of an active occurrence belongs to the pointwise active modulus set. -/
theorem activeOccurrence_modulus_mem
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    occurrence.1 ∈ activeCoprimeTypeIModuliAt N u p := by
  have hActive := (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).1
  exact (Finset.mem_sigma.mp hActive).1

/-- Every active character occurrence has positive modulus. -/
theorem activeOccurrence_modulus_pos
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    0 < occurrence.1 := by
  have hdOuter := Finset.mem_filter.mp (activeOccurrence_modulus_mem hOccurrence)
  have hdInner := Finset.mem_filter.mp hdOuter.1
  exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdInner.1).1

/-- Every active character occurrence has modulus coprime to the fixed center. -/
theorem activeOccurrence_modulus_coprime
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    Nat.Coprime N occurrence.1 := by
  have hdOuter := Finset.mem_filter.mp (activeOccurrence_modulus_mem hOccurrence)
  exact (Finset.mem_filter.mp hdOuter.1).2

/-- Every active occurrence satisfies the pointwise cutoff `d ≤ N - p`. -/
theorem activeOccurrence_modulus_le_center_sub
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    occurrence.1 ≤ N - p :=
  (Finset.mem_filter.mp (activeOccurrence_modulus_mem hOccurrence)).2

/-- The primitive conductor attached to an active fiber divides every occurrence modulus. -/
theorem activeOccurrence_key_conductor_dvd_modulus
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    key.1 ∣ occurrence.1 := by
  have hKey := (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).2
  rw [← hKey]
  exact DirichletCharacter.conductor_dvd_level occurrence.2

/-- Every represented active fiber has positive conductor. -/
theorem activeOccurrence_key_conductor_pos
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    0 < key.1 := by
  have hKey := (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).2
  rw [← hKey]
  exact Nat.pos_of_ne_zero
    (DirichletCharacter.conductor_ne_zero occurrence.2
      (Nat.ne_of_gt (activeOccurrence_modulus_pos hOccurrence)))

/-- Every represented active conductor is coprime to the fixed center. -/
theorem activeOccurrence_key_conductor_coprime
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    Nat.Coprime N key.1 :=
  (activeOccurrence_modulus_coprime hOccurrence).coprime_dvd_right
    (activeOccurrence_key_conductor_dvd_modulus hOccurrence)

/-- The character stored in every represented active key is primitive at its stated conductor. -/
theorem activeOccurrence_key_isPrimitive
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    key.2.IsPrimitive := by
  have hKey := (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).2
  rw [← hKey]
  exact DirichletCharacter.primitiveCharacter_isPrimitive occurrence.2

/-- A fixed active primitive fiber contains at most one occurrence at each modulus. -/
theorem activeOccurrence_eq_of_same_modulus
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    {occurrence₁ occurrence₂ : CharacterOccurrence}
    (hOccurrence₁ : occurrence₁ ∈ activeCharacterOccurrencesForKeyAt N u p key)
    (hOccurrence₂ : occurrence₂ ∈ activeCharacterOccurrencesForKeyAt N u p key)
    (hModulus : occurrence₁.1 = occurrence₂.1) :
    occurrence₁ = occurrence₂ := by
  have hKey : primitiveCharacterKey occurrence₁ = primitiveCharacterKey occurrence₂ :=
    (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence₁).2.trans
      (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence₂).2.symm
  rcases occurrence₁ with ⟨q, χ⟩
  rcases occurrence₂ with ⟨q', ψ⟩
  dsimp only at hModulus
  subst q'
  refine Sigma.ext (x := ⟨q, χ⟩) (y := ⟨q, ψ⟩) rfl ?_
  exact heq_of_eq (character_eq_of_primitiveCharacterKey_eq hKey)

/-- The inverse center evaluation is constant on an active primitive-character fiber. -/
theorem activeOccurrence_inv_eq_key_inv
    {N u p : ℕ} {key : PrimitiveCharacterKey} {occurrence : CharacterOccurrence}
    (hOccurrence : occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key) :
    occurrence.2 ((N : ZMod occurrence.1)⁻¹) =
      key.2 ((N : ZMod key.1)⁻¹) := by
  have hKey := (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).2
  rw [← hKey]
  exact apply_inv_eq_primitiveCharacter_inv_of_coprime occurrence.2
    (activeOccurrence_modulus_coprime hOccurrence)

/-- The pointwise correction incurred when a level character is replaced by its primitive one. -/
noncomputable def activeInducedCharacterPointCorrection
    (p : ℕ) (occurrence : CharacterOccurrence) : ℂ :=
  if Nat.Coprime p occurrence.1 then 0
  else (ΛVM p : ℂ) *
    occurrence.2.primitiveCharacter (p : ZMod occurrence.2.conductor)

/-- Exact pointwise replacement of a level character by its primitive character. -/
theorem levelCharacterPoint_eq_primitive_sub_activeCorrection
    (p : ℕ) (occurrence : CharacterOccurrence) :
    (ΛVM p : ℂ) * occurrence.2 (p : ZMod occurrence.1) =
      (ΛVM p : ℂ) *
          occurrence.2.primitiveCharacter (p : ZMod occurrence.2.conductor)
        - activeInducedCharacterPointCorrection p occurrence := by
  by_cases hp : Nat.Coprime p occurrence.1
  · rw [apply_eq_primitiveCharacter_of_coprime occurrence.2 hp]
    rw [activeInducedCharacterPointCorrection, if_pos hp, sub_zero]
  · rw [apply_eq_zero_of_not_coprime occurrence.2 hp]
    rw [activeInducedCharacterPointCorrection, if_neg hp, sub_self, mul_zero]

/-- The signed active lift weight represented by one primitive-character fiber. -/
noncomputable def activePrimitiveCharacterFiberWeightAt
    (N u p : ℕ) (key : PrimitiveCharacterKey) : ℝ :=
  ∑ occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key,
    activeCharacterOccurrenceCoefficient N p occurrence

/-- Active moduli divisible by a prospective primitive conductor. -/
def activeConductorLiftModuliAt
    (N u p r : ℕ) : Finset ℕ :=
  (activeCoprimeTypeIModuliAt N u p).filter fun d => r ∣ d

/--
The exact missing algebraic fact: every active conductor multiple carries an occurrence inducing
the chosen primitive key. Uniqueness at each level is already proved separately.
-/
def ActiveConductorLiftCompleteAt
    (N u p : ℕ) (key : PrimitiveCharacterKey) : Prop :=
  ∀ d ∈ activeCoprimeTypeIModuliAt N u p, key.1 ∣ d →
    ∃ χ : DirichletCharacter ℂ d,
      (⟨d, χ⟩ : CharacterOccurrence) ∈
        activeCharacterOccurrencesForKeyAt N u p key

/--
The general Dirichlet-character statement needed to generate all lifts of a primitive key.
Mathlib currently supplies `changeLevel` and its injectivity, but not this conductor-preservation
theorem.
-/
def PrimitiveCharacterChangeLevelStable : Prop :=
  ∀ {r d : ℕ} (χ : DirichletCharacter ℂ r) (hrd : r ∣ d), d ≠ 0 → χ.IsPrimitive →
    primitiveCharacterKey
        (⟨d, DirichletCharacter.changeLevel hrd χ⟩ : CharacterOccurrence) =
      (⟨r, χ⟩ : PrimitiveCharacterKey)

/-- Conductor stability under `changeLevel` supplies the exact active lift-completeness fact. -/
theorem activeConductorLiftCompleteAt_of_changeLevelStable
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hStable : PrimitiveCharacterChangeLevelStable)
    (hKey : key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p) :
    ActiveConductorLiftCompleteAt N u p key := by
  classical
  obtain ⟨occurrence, hOccurrenceActive, hOccurrenceKey⟩ :=
    Finset.mem_image.mp hKey
  have hOccurrence :
      occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key :=
    Finset.mem_filter.mpr ⟨hOccurrenceActive, hOccurrenceKey⟩
  have hPrimitive := activeOccurrence_key_isPrimitive hOccurrence
  intro d hd hKeyDvd
  have hdPos : 0 < d := by
    have hdOuter := Finset.mem_filter.mp hd
    have hdInner := Finset.mem_filter.mp hdOuter.1
    exact (Finset.mem_Icc.mp hdInner.1).1
  refine ⟨DirichletCharacter.changeLevel hKeyDvd key.2, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_sigma.mpr ⟨hd, Finset.mem_univ _⟩
  · simpa using hStable key.2 hKeyDvd hdPos.ne' hPrimitive

/-- The canonical primitive key of the principal character. -/
noncomputable def principalPrimitiveCharacterKey : PrimitiveCharacterKey :=
  ⟨1, (1 : DirichletCharacter ℂ 1)⟩

/-- Principal characters supply every active conductor-one lift without a general stability input. -/
theorem activeConductorLiftCompleteAt_principal
    (N u p : ℕ) :
    ActiveConductorLiftCompleteAt N u p principalPrimitiveCharacterKey := by
  classical
  intro d hd _hOneDvd
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  have hdPos : 0 < d :=
    lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hdInner.1).1
  refine ⟨(1 : DirichletCharacter ℂ d), ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_sigma.mpr ⟨hd, Finset.mem_univ _⟩
  · unfold primitiveCharacterKey principalPrimitiveCharacterKey
    have hConductor :
        DirichletCharacter.conductor (1 : DirichletCharacter ℂ d) = 1 :=
      DirichletCharacter.conductor_one hdPos.ne'
    have hPrimitive :
        (1 : DirichletCharacter ℂ d).primitiveCharacter = 1 :=
      DirichletCharacter.primitiveCharacter_one hdPos.ne'
    let hType :
        DirichletCharacter ℂ (DirichletCharacter.conductor (1 : DirichletCharacter ℂ d)) =
          DirichletCharacter ℂ 1 :=
      congrArg (DirichletCharacter ℂ) hConductor
    have hCastOne :
        cast hType
            (1 : DirichletCharacter ℂ
              (DirichletCharacter.conductor (1 : DirichletCharacter ℂ d))) =
          (1 : DirichletCharacter ℂ 1) :=
      Subsingleton.elim _ _
    have hOne :
        (1 : DirichletCharacter ℂ
            (DirichletCharacter.conductor (1 : DirichletCharacter ℂ d))) ≍
          (1 : DirichletCharacter ℂ 1) :=
      (cast_heq hType _).symm.trans (heq_of_eq hCastOne)
    exact Sigma.ext hConductor ((heq_of_eq hPrimitive).trans hOne)

/-- The active linear subtraction is exactly the conductor-one logarithmic lift weight. -/
theorem activeCharacterLinearMainAt_eq_conductorWeight_one
    (N u p : ℕ) :
    activeCharacterLinearMainAt N u p =
      balancedVaughanTypeIConductorWeight N u 1 p := by
  classical
  unfold activeCharacterLinearMainAt balancedVaughanTypeIConductorWeight
    activeCoprimeTypeIModuliAt
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter, one_dvd, true_and]
  · intro d hd
    rfl

/-- The active linear term inherits the proved conductor-weight bound. -/
theorem abs_activeCharacterLinearMainAt_le
    {N u p : ℕ} (hN : 0 < N) :
    |activeCharacterLinearMainAt N u p| ≤
      6 * (N : ℝ) / (Nat.totient N : ℝ) *
        max 0 (Real.log ((N - p : ℕ) : ℝ)) := by
  rw [activeCharacterLinearMainAt_eq_conductorWeight_one]
  simpa using
    (abs_balancedVaughanTypeIConductorWeight_le
      (N := N) (u := u) (r := 1) (t := p) hN Nat.zero_lt_one (Nat.coprime_one_right N))

/-- The two equivalent descriptions of the active conductor-lift modulus set agree. -/
theorem activeConductorLiftModuliAt_eq
    (N u p r : ℕ) :
    activeConductorLiftModuliAt N u p r =
      ((Finset.Icc 1 u).filter (Nat.Coprime N)).filter
        (fun d => r ∣ d ∧ d ≤ N - p) := by
  ext d
  simp only [activeConductorLiftModuliAt, activeCoprimeTypeIModuliAt,
    Finset.mem_filter]
  aesop

/-- Under the explicit lift-completeness statement, the actual fiber weight is the full weight. -/
theorem activePrimitiveCharacterFiberWeightAt_eq_conductorWeight
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hComplete : ActiveConductorLiftCompleteAt N u p key) :
    activePrimitiveCharacterFiberWeightAt N u p key =
      balancedVaughanTypeIConductorWeight N u key.1 p := by
  classical
  unfold activePrimitiveCharacterFiberWeightAt activeCharacterOccurrenceCoefficient
    balancedVaughanTypeIConductorWeight
  rw [← activeConductorLiftModuliAt_eq]
  exact Finset.sum_bij
    (fun occurrence _hOccurrence => occurrence.1)
    (fun occurrence hOccurrence =>
      Finset.mem_filter.mpr
        ⟨activeOccurrence_modulus_mem hOccurrence,
          activeOccurrence_key_conductor_dvd_modulus hOccurrence⟩)
    (fun occurrence₁ hOccurrence₁ occurrence₂ hOccurrence₂ hModulus =>
      activeOccurrence_eq_of_same_modulus hOccurrence₁ hOccurrence₂ hModulus)
    (fun d hd => by
      have hdData := Finset.mem_filter.mp hd
      obtain ⟨χ, hχ⟩ := hComplete d hdData.1 hdData.2
      exact ⟨⟨d, χ⟩, hχ, rfl⟩)
    (fun occurrence hOccurrence => rfl)

/-- Membership in the represented-key set supplies an actual active occurrence in that fiber. -/
theorem exists_activeOccurrenceForKeyAt_of_mem_represented
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p) :
    ∃ occurrence,
      occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key := by
  classical
  obtain ⟨occurrence, hOccurrence, hOccurrenceKey⟩ :=
    Finset.mem_image.mp hKey
  exact ⟨occurrence, Finset.mem_filter.mpr ⟨hOccurrence, hOccurrenceKey⟩⟩

/-- The proved conductor-weight majorant applies to every complete represented active fiber. -/
theorem abs_activePrimitiveCharacterFiberWeightAt_le
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hN : 0 < N)
    (hKey : key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p)
    (hComplete : ActiveConductorLiftCompleteAt N u p key) :
    |activePrimitiveCharacterFiberWeightAt N u p key| ≤
      6 * ((key.1 * N : ℕ) : ℝ) / (Nat.totient (key.1 * N) : ℝ) /
        (Nat.totient key.1 : ℝ) *
          max 0 (Real.log (((N - p : ℕ) : ℝ) / (key.1 : ℝ))) := by
  obtain ⟨occurrence, hOccurrence⟩ :=
    exists_activeOccurrenceForKeyAt_of_mem_represented hKey
  rw [activePrimitiveCharacterFiberWeightAt_eq_conductorWeight hComplete]
  exact abs_balancedVaughanTypeIConductorWeight_le hN
    (activeOccurrence_key_conductor_pos hOccurrence)
    (activeOccurrence_key_conductor_coprime hOccurrence)

/-- The exact induced-character correction retained inside one active primitive fiber. -/
noncomputable def activePrimitiveCharacterFiberInducedCorrectionAt
    (N u p : ℕ) (key : PrimitiveCharacterKey) : ℂ :=
  ∑ occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key,
    (activeCharacterOccurrenceCoefficient N p occurrence : ℂ) *
      key.2 ((N : ZMod key.1)⁻¹) *
        activeInducedCharacterPointCorrection p occurrence

/--
Each active fiber is a primitive-character point value times its signed lift weight, minus the
exact pointwise correction for induced characters.
-/
theorem activePrimitiveCharacterFiberContributionAt_eq_main_sub_inducedCorrection
    (N u p : ℕ) (key : PrimitiveCharacterKey) :
    activePrimitiveCharacterFiberContributionAt N u p key =
      key.2 ((N : ZMod key.1)⁻¹) *
          ((ΛVM p : ℂ) * key.2 (p : ZMod key.1)) *
            (activePrimitiveCharacterFiberWeightAt N u p key : ℂ)
        - activePrimitiveCharacterFiberInducedCorrectionAt N u p key := by
  classical
  unfold activePrimitiveCharacterFiberContributionAt activeCharacterOccurrenceTerm
    activePrimitiveCharacterFiberWeightAt activePrimitiveCharacterFiberInducedCorrectionAt
  push_cast
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro occurrence hOccurrence
  have hKey := (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).2
  have hInv := activeOccurrence_inv_eq_key_inv hOccurrence
  rw [hInv, levelCharacterPoint_eq_primitive_sub_activeCorrection]
  cases hKey
  simp only [primitiveCharacterKey]
  ring

/-- The active pointwise character expansion partitions exactly by primitive-character key. -/
theorem activeCharacterExpandedErrorAt_eq_primitiveCharacterFibers
    (N u p : ℕ) :
    activeCharacterExpandedErrorAt N u p =
      (∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
        activePrimitiveCharacterFiberContributionAt N u p key)
        - (activeCharacterLinearMainAt N u p : ℂ) := by
  unfold activeCharacterExpandedErrorAt activePrimitiveCharacterFiberContributionAt
  rw [sum_activeCharacterOccurrences_eq_sum_primitiveCharacterFibers]

/-- Primitive-main-minus-correction form of the active pointwise character expansion. -/
theorem activeCharacterExpandedErrorAt_eq_primitiveMain_sub_corrections
    (N u p : ℕ) :
    activeCharacterExpandedErrorAt N u p =
      (∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
        (key.2 ((N : ZMod key.1)⁻¹) *
            ((ΛVM p : ℂ) * key.2 (p : ZMod key.1)) *
              (activePrimitiveCharacterFiberWeightAt N u p key : ℂ)
          - activePrimitiveCharacterFiberInducedCorrectionAt N u p key))
        - (activeCharacterLinearMainAt N u p : ℂ) := by
  rw [activeCharacterExpandedErrorAt_eq_primitiveCharacterFibers]
  congr 1
  apply Finset.sum_congr rfl
  intro key hKey
  exact activePrimitiveCharacterFiberContributionAt_eq_main_sub_inducedCorrection N u p key

/-- Exact primitive-character partition of the corrected active Type-I progression error. -/
theorem activeCoprimeProgressionError_cast_eq_primitiveCharacterFibers
    {L N u : ℕ} (hL : 0 < L) :
    (balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ) =
      ∑ p ∈ balancedCandidateSupport L N,
        ((∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
            activePrimitiveCharacterFiberContributionAt N u p key)
          - (activeCharacterLinearMainAt N u p : ℂ)) := by
  rw [activeCoprimeProgressionError_cast_eq_characterExpanded hL]
  apply Finset.sum_congr rfl
  intro p hp
  exact activeCharacterExpandedErrorAt_eq_primitiveCharacterFibers N u p

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
