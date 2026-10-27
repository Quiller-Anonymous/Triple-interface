import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberDirect

/-!
# Analytic closure over the actually represented primitive-character fibers

The sharper signed-conductor route replaces every represented fiber by the complete set of
conductor lifts.  That replacement currently depends on a conductor-preservation theorem for
`DirichletCharacter.changeLevel` that is not exposed by Mathlib.

This file avoids that dependency.  It extends each moving active-key sum to the fixed finite set of
keys actually represented below the Type-I cutoff, retains the actual represented fiber weight, and
applies finite summation by parts directly.  The price is a factor `3` endpoint-and-variation cost
instead of the factor `2` available for a complete fiber.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberClosure

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanNoncoprime
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveReindexing
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberDirect
open Goldbach.Cert.MajorArcModules.RouteAReciprocalTotientPrefix

noncomputable section

/-- Every active character occurrence is one of the fixed occurrences below the Type-I cutoff. -/
theorem activeCharacterOccurrencesAt_subset_characterOccurrences
    (N u p : ℕ) :
    activeCharacterOccurrencesAt N u p ⊆ characterOccurrences N u := by
  intro occurrence hOccurrence
  have hData := Finset.mem_sigma.mp hOccurrence
  apply Finset.mem_sigma.mpr
  refine ⟨?_, hData.2⟩
  have hd := Finset.mem_filter.mp hData.1
  exact hd.1

/-- Every moving active key belongs to the fixed represented-key set. -/
theorem activeRepresentedPrimitiveCharacterKeysAt_subset_represented
    (N u p : ℕ) :
    activeRepresentedPrimitiveCharacterKeysAt N u p ⊆
      representedPrimitiveCharacterKeys N u := by
  classical
  intro key hKey
  obtain ⟨occurrence, hOccurrence, rfl⟩ := Finset.mem_image.mp hKey
  exact Finset.mem_image.mpr
    ⟨occurrence,
      activeCharacterOccurrencesAt_subset_characterOccurrences N u p hOccurrence,
      rfl⟩

/-- A key absent from the moving active set has zero actual fiber weight. -/
theorem activePrimitiveCharacterFiberWeightAt_eq_zero_of_not_mem
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∉ activeRepresentedPrimitiveCharacterKeysAt N u p) :
    activePrimitiveCharacterFiberWeightAt N u p key = 0 := by
  classical
  unfold activePrimitiveCharacterFiberWeightAt
  apply Finset.sum_eq_zero
  intro occurrence hOccurrence
  exfalso
  apply hKey
  exact Finset.mem_image.mpr
    ⟨occurrence, (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).1,
      (mem_activeCharacterOccurrencesForKeyAt_data hOccurrence).2⟩

/-- The moving key sum can be extended to the fixed represented-key set without adding a term. -/
theorem representedPrimitiveCharacterMainAt_eq_fixedRepresented
    (N u p : ℕ) :
    representedPrimitiveCharacterMainAt N u p =
      ∑ key ∈ representedPrimitiveCharacterKeys N u,
        key.2 ((N : ZMod key.1)⁻¹) *
          ((ΛVM p : ℂ) * key.2 (p : ZMod key.1)) *
            (activePrimitiveCharacterFiberWeightAt N u p key : ℂ) := by
  classical
  unfold representedPrimitiveCharacterMainAt
  apply Finset.sum_subset
  · exact activeRepresentedPrimitiveCharacterKeysAt_subset_represented N u p
  · intro key hStatic hNotActive
    rw [activePrimitiveCharacterFiberWeightAt_eq_zero_of_not_mem hNotActive]
    simp

/-- One represented primitive key summed over a fixed prime interval. -/
noncomputable def representedPrimitiveCharacterConductorSum
    (N u : ℕ) (key : PrimitiveCharacterKey) (a b : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ico a (b + 1),
    key.2 ((N : ZMod key.1)⁻¹) *
      ((ΛVM p : ℂ) * key.2 (p : ZMod key.1)) *
        (activePrimitiveCharacterFiberWeightAt N u p key : ℂ)

/-- Finite Fubini identity for the exact active main over represented fibers. -/
theorem activePrimitiveCharacterTotalMain_eq_representedConductorSums
    (L N u : ℕ) :
    activePrimitiveCharacterTotalMain L N u =
      ∑ key ∈ representedPrimitiveCharacterKeys N u,
        representedPrimitiveCharacterConductorSum N u key L (N - L) := by
  classical
  rw [activePrimitiveCharacterTotalMain_eq_represented]
  unfold representedPrimitiveCharacterTotalMain
  have hSupport :
      balancedCandidateSupport L N = Finset.Ico L (N - L + 1) := by
    ext p
    simp only [balancedCandidateSupport, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hSupport]
  simp_rw [representedPrimitiveCharacterMainAt_eq_fixedRepresented]
  rw [Finset.sum_comm]
  unfold representedPrimitiveCharacterConductorSum
  rfl

/-- A represented conductor sum is the Stieltjes sum of its primitive `psi` function. -/
theorem representedPrimitiveCharacterConductorSum_eq_discreteStieltjesSum
    {N u a b : ℕ} (key : PrimitiveCharacterKey) (ha : 0 < a) :
    representedPrimitiveCharacterConductorSum N u key a b =
      discreteStieltjesSum (twistedPrimitivePsi N key.1 key.2)
        (fun t => (activePrimitiveCharacterFiberWeightAt N u t key : ℂ)) a b := by
  unfold representedPrimitiveCharacterConductorSum discreteStieltjesSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [twistedPrimitivePsi_sub_pred key.2 (by
    have hpData := Finset.mem_Ico.mp hp
    omega)]

/-- Complex variation of a represented real fiber is its previously bounded real variation. -/
theorem sum_norm_activePrimitiveCharacterFiberWeight_diff_eq_variation
    (N u : ℕ) (key : PrimitiveCharacterKey) (a b : ℕ) :
    (∑ t ∈ Finset.Ico a b,
        ‖(activePrimitiveCharacterFiberWeightAt N u t key : ℂ) -
          (activePrimitiveCharacterFiberWeightAt N u (t + 1) key : ℂ)‖) =
      representedPrimitiveCharacterFiberVariation N u key a b := by
  unfold representedPrimitiveCharacterFiberVariation
  apply Finset.sum_congr rfl
  intro t ht
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/--
A maximal primitive-character `psi` bound controls one actual represented fiber without any
conductor-lift completeness assumption.
-/
theorem norm_representedPrimitiveCharacterConductorSum_le
    {N u a b : ℕ} (key : PrimitiveCharacterKey) (M : ℝ)
    (hN : 0 < N) (hr : 0 < key.1) (hNr : Nat.Coprime N key.1)
    (ha : 0 < a) (hab : a ≤ b) (hbN : b < N)
    (hM : 0 ≤ M)
    (hPsi : ∀ t ∈ Finset.Icc (a - 1) b,
      ‖dirichletPsi t key.1 key.2‖ ≤ M) :
    ‖representedPrimitiveCharacterConductorSum N u key a b‖ ≤
      M * (3 * ((1 / (Nat.totient key.1 : ℝ)) *
        reciprocalTotientPrefix (u / key.1)) * Real.log (N : ℝ)) := by
  have hTwisted : ∀ t ∈ Finset.Icc (a - 1) b,
      ‖twistedPrimitivePsi N key.1 key.2 t‖ ≤ M := by
    intro t ht
    unfold twistedPrimitivePsi
    calc
      ‖key.2 ((N : ZMod key.1)⁻¹) * dirichletPsi t key.1 key.2‖ =
          ‖key.2 ((N : ZMod key.1)⁻¹)‖ * ‖dirichletPsi t key.1 key.2‖ :=
        norm_mul _ _
      _ ≤ 1 * ‖dirichletPsi t key.1 key.2‖ :=
        mul_le_mul_of_nonneg_right
          (DirichletCharacter.norm_le_one key.2 _) (norm_nonneg _)
      _ ≤ M := by simpa using hPsi t ht
  rw [representedPrimitiveCharacterConductorSum_eq_discreteStieltjesSum key ha]
  calc
    ‖discreteStieltjesSum (twistedPrimitivePsi N key.1 key.2)
        (fun t => (activePrimitiveCharacterFiberWeightAt N u t key : ℂ)) a b‖ ≤
        M * (|activePrimitiveCharacterFiberWeightAt N u a key| +
          |activePrimitiveCharacterFiberWeightAt N u b key| +
          representedPrimitiveCharacterFiberVariation N u key a b) := by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        sum_norm_activePrimitiveCharacterFiberWeight_diff_eq_variation] using
        (norm_discreteStieltjesSum_le
          (twistedPrimitivePsi N key.1 key.2)
          (fun t => (activePrimitiveCharacterFiberWeightAt N u t key : ℂ))
          hab M hTwisted)
    _ ≤ M * (3 * ((1 / (Nat.totient key.1 : ℝ)) *
          reciprocalTotientPrefix (u / key.1)) * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (representedFiber_endpoints_add_variation_le_direct_three_mul_log
          hN hr hNr hab hbN) hM

/-- Membership in the fixed represented-key set supplies an occurrence inducing that key. -/
theorem exists_characterOccurrenceForKey_of_mem_represented
    {N u : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedPrimitiveCharacterKeys N u) :
    ∃ occurrence, occurrence ∈ characterOccurrencesForKey N u key := by
  classical
  obtain ⟨occurrence, hOccurrence, hOccurrenceKey⟩ := Finset.mem_image.mp hKey
  exact ⟨occurrence, Finset.mem_filter.mpr ⟨hOccurrence, hOccurrenceKey⟩⟩

/-- Every represented key has positive conductor. -/
theorem representedKey_conductor_pos
    {N u : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedPrimitiveCharacterKeys N u) :
    0 < key.1 := by
  obtain ⟨occurrence, hOccurrence⟩ :=
    exists_characterOccurrenceForKey_of_mem_represented hKey
  exact occurrence_key_conductor_pos hOccurrence

/-- Every represented key has conductor coprime to the fixed center. -/
theorem representedKey_conductor_coprime
    {N u : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedPrimitiveCharacterKeys N u) :
    Nat.Coprime N key.1 := by
  obtain ⟨occurrence, hOccurrence⟩ :=
    exists_characterOccurrenceForKey_of_mem_represented hKey
  exact occurrence_key_conductor_coprime hOccurrence

/-- The character stored in a represented key is primitive at its stated conductor. -/
theorem representedKey_isPrimitive
    {N u : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedPrimitiveCharacterKeys N u) :
    key.2.IsPrimitive := by
  obtain ⟨occurrence, hOccurrence⟩ :=
    exists_characterOccurrenceForKey_of_mem_represented hKey
  exact occurrence_key_isPrimitive hOccurrence

/-- Every represented conductor belongs to the fixed primitive conductor support. -/
theorem representedKey_conductor_mem_primitiveConductorSupport
    {N u : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedPrimitiveCharacterKeys N u) :
    key.1 ∈ primitiveConductorSupport N u := by
  obtain ⟨occurrence, hOccurrence⟩ :=
    exists_characterOccurrenceForKey_of_mem_represented hKey
  have hdData := Finset.mem_sigma.mp (mem_characterOccurrencesForKey_data hOccurrence).1
  have hdSupport := Finset.mem_filter.mp hdData.1
  have hdBounds := Finset.mem_Icc.mp hdSupport.1
  have hrLeD := Nat.le_of_dvd (occurrence_modulus_pos hOccurrence)
    (occurrence_key_conductor_dvd_modulus hOccurrence)
  rw [primitiveConductorSupport, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (representedKey_conductor_pos hKey).ne',
    hrLeD.trans hdBounds.2⟩, representedKey_conductor_coprime hKey⟩

/-- A positive Type-I cutoff represents the conductor-one principal key. -/
theorem principalPrimitiveCharacterKey_mem_represented
    {N u : ℕ} (hu : 0 < u) :
    principalPrimitiveCharacterKey ∈ representedPrimitiveCharacterKeys N u := by
  classical
  unfold representedPrimitiveCharacterKeys
  apply Finset.mem_image.mpr
  refine ⟨(⟨1, (1 : DirichletCharacter ℂ 1)⟩ : CharacterOccurrence), ?_, ?_⟩
  · apply Finset.mem_sigma.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rw [coprimeTypeIModuli, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, Nat.one_le_iff_ne_zero.mpr hu.ne'⟩,
      Nat.coprime_one_right N⟩
  · unfold primitiveCharacterKey principalPrimitiveCharacterKey
    have hConductor :
        DirichletCharacter.conductor (1 : DirichletCharacter ℂ 1) = 1 :=
      DirichletCharacter.conductor_one (by norm_num)
    have hPrimitive :
        (1 : DirichletCharacter ℂ 1).primitiveCharacter = 1 :=
      DirichletCharacter.primitiveCharacter_one (by norm_num)
    let hType :
        DirichletCharacter ℂ
            (DirichletCharacter.conductor (1 : DirichletCharacter ℂ 1)) =
          DirichletCharacter ℂ 1 :=
      congrArg (DirichletCharacter ℂ) hConductor
    have hCastOne :
        cast hType
            (1 : DirichletCharacter ℂ
              (DirichletCharacter.conductor (1 : DirichletCharacter ℂ 1))) =
          (1 : DirichletCharacter ℂ 1) :=
      Subsingleton.elim _ _
    have hOne :
        (1 : DirichletCharacter ℂ
            (DirichletCharacter.conductor (1 : DirichletCharacter ℂ 1))) ≍
          (1 : DirichletCharacter ℂ 1) :=
      (cast_heq hType _).symm.trans (heq_of_eq hCastOne)
    exact Sigma.ext hConductor ((heq_of_eq hPrimitive).trans hOne)

/-- The represented principal sum is the usual complete conductor-one family. -/
theorem representedPrimitiveCharacterConductorSum_principal_eq_family_one
    (N u a b : ℕ) :
    representedPrimitiveCharacterConductorSum N u principalPrimitiveCharacterKey a b =
      primitiveCharacterFamilyConductorSum N u 1 a b := by
  rw [primitiveCharacterFamilyConductorSum_one]
  unfold representedPrimitiveCharacterConductorSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [activePrimitiveCharacterFiberWeightAt_eq_conductorWeight
    (activeConductorLiftCompleteAt_principal N u p)]
  unfold principalPrimitiveCharacterKey
  have hNmod : ((N : ZMod 1)⁻¹) = 1 := Subsingleton.elim _ _
  have hpmod : (p : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [hNmod, hpmod]
  norm_num

/-- The represented keys other than the principal conductor-one key. -/
noncomputable def representedNonprincipalPrimitiveCharacterKeys
    (N u : ℕ) : Finset PrimitiveCharacterKey := by
  classical
  exact (representedPrimitiveCharacterKeys N u).erase principalPrimitiveCharacterKey

@[simp]
theorem mem_representedNonprincipalPrimitiveCharacterKeys_iff
    {N u : ℕ} {key : PrimitiveCharacterKey} :
    key ∈ representedNonprincipalPrimitiveCharacterKeys N u ↔
      key ∈ representedPrimitiveCharacterKeys N u ∧
        key ≠ principalPrimitiveCharacterKey := by
  classical
  rw [representedNonprincipalPrimitiveCharacterKeys, Finset.mem_erase]
  constructor
  · exact fun h => ⟨h.2, h.1⟩
  · exact fun h => ⟨h.2, h.1⟩

/--
The exact represented main, after its linear comparison is removed, is the centered principal
family plus the actual represented nonprincipal fibers.
-/
theorem activePrimitiveCharacterTotalMain_sub_linear_eq_principal_add_represented
    {L N u : ℕ} (hu : 0 < u) :
    activePrimitiveCharacterTotalMain L N u - activeCharacterLinearTotal L N u =
      principalCenteredConductorSum N u L (N - L) +
        ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
          representedPrimitiveCharacterConductorSum N u key L (N - L) := by
  classical
  rw [activePrimitiveCharacterTotalMain_eq_representedConductorSums]
  have hPrincipal := principalPrimitiveCharacterKey_mem_represented (N := N) hu
  calc
    (∑ key ∈ representedPrimitiveCharacterKeys N u,
        representedPrimitiveCharacterConductorSum N u key L (N - L)) -
          activeCharacterLinearTotal L N u =
        (representedPrimitiveCharacterConductorSum N u
            principalPrimitiveCharacterKey L (N - L) -
          activeCharacterLinearTotal L N u) +
          ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
            representedPrimitiveCharacterConductorSum N u key L (N - L) := by
      rw [representedNonprincipalPrimitiveCharacterKeys,
        ← Finset.add_sum_erase (representedPrimitiveCharacterKeys N u)
          (fun key => representedPrimitiveCharacterConductorSum N u key L (N - L))
          hPrincipal]
      ring
    _ = principalCenteredConductorSum N u L (N - L) +
          ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
            representedPrimitiveCharacterConductorSum N u key L (N - L) := by
      rw [representedPrimitiveCharacterConductorSum_principal_eq_family_one,
        conductorOneFamily_sub_linear_eq_centered]

/--
Exact closure surface for the active coprime error over actual represented fibers.  Unlike the
complete-fiber version, this identity needs no conductor-stability hypothesis.
-/
theorem activeCoprimeProgressionError_cast_eq_principal_add_represented_sub_induced
    {L N u : ℕ} (hL : 0 < L) (hu : 0 < u) :
    (balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ) =
      principalCenteredConductorSum N u L (N - L) +
        ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
          representedPrimitiveCharacterConductorSum N u key L (N - L) -
        activePrimitiveCharacterTotalInducedCorrection L N u := by
  rw [activeCoprimeProgressionError_cast_eq_primitiveMain_sub_corrections hL]
  calc
    activePrimitiveCharacterTotalMain L N u -
          activePrimitiveCharacterTotalInducedCorrection L N u -
          activeCharacterLinearTotal L N u =
        (activePrimitiveCharacterTotalMain L N u -
          activeCharacterLinearTotal L N u) -
          activePrimitiveCharacterTotalInducedCorrection L N u := by ring
    _ = principalCenteredConductorSum N u L (N - L) +
          ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
            representedPrimitiveCharacterConductorSum N u key L (N - L) -
          activePrimitiveCharacterTotalInducedCorrection L N u := by
      rw [activePrimitiveCharacterTotalMain_sub_linear_eq_principal_add_represented hu]

/-- A primitive-character key at conductor one is necessarily the canonical principal key. -/
theorem primitiveCharacterKey_eq_principal_of_conductor_eq_one
    {key : PrimitiveCharacterKey} (hOne : key.1 = 1) :
    key = principalPrimitiveCharacterKey := by
  rcases key with ⟨r, χ⟩
  dsimp at hOne
  subst r
  unfold principalPrimitiveCharacterKey
  exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _))

/-- Every represented nonprincipal key has conductor in the nonprincipal support. -/
theorem representedNonprincipalKey_conductor_mem_support
    {N u : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedNonprincipalPrimitiveCharacterKeys N u) :
    key.1 ∈ nonprincipalPrimitiveConductorSupport N u := by
  have hData := mem_representedNonprincipalPrimitiveCharacterKeys_iff.mp hKey
  rw [mem_nonprincipalPrimitiveConductorSupport_iff]
  refine ⟨representedKey_conductor_mem_primitiveConductorSupport hData.1, ?_⟩
  intro hOne
  exact hData.2 (primitiveCharacterKey_eq_principal_of_conductor_eq_one hOne)

/-- Every represented nonprincipal key occurs among the primitive characters at its conductor. -/
theorem representedNonprincipalKey_character_mem_primitiveCharacters
    {N u : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedNonprincipalPrimitiveCharacterKeys N u) :
    key.2 ∈ primitiveCharacters key.1 := by
  rw [mem_primitiveCharacters_iff]
  exact representedKey_isPrimitive
    (mem_representedNonprincipalPrimitiveCharacterKeys_iff.mp hKey).1

/-- Endpoint-and-variation cost for an actual represented primitive-character fiber. -/
noncomputable def representedPrimitiveConductorAnalyticCost
    (N u r : ℕ) : ℝ :=
  3 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) *
    Real.log (N : ℝ)

/-- Exact allowance over the nonprincipal primitive keys actually represented below `u`. -/
noncomputable def representedNonprincipalConductorAnalyticAllowance
    (N u : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
    M key.1 key.2 * representedPrimitiveConductorAnalyticCost N u key.1

/-- All nonprincipal primitive-character keys in the fixed Type-I support. -/
noncomputable def allNonprincipalPrimitiveCharacterKeys
    (N u : ℕ) : Finset PrimitiveCharacterKey := by
  classical
  exact (nonprincipalPrimitiveConductorSupport N u).sigma primitiveCharacters

/-- The represented nonprincipal keys form a subset of the conventional primitive support. -/
theorem representedNonprincipalPrimitiveCharacterKeys_subset_all
    (N u : ℕ) :
    representedNonprincipalPrimitiveCharacterKeys N u ⊆
      allNonprincipalPrimitiveCharacterKeys N u := by
  intro key hKey
  rw [allNonprincipalPrimitiveCharacterKeys, Finset.mem_sigma]
  exact ⟨representedNonprincipalKey_conductor_mem_support hKey,
    representedNonprincipalKey_character_mem_primitiveCharacters hKey⟩

/-- Global factor converting the direct represented-fiber cost to mean-value weight. -/
noncomputable def representedPrimitiveMeanValueGlobalFactor
    (N u : ℕ) : ℝ :=
  18 * (1 + Real.log (u : ℝ)) * Real.log (N : ℝ)

/-- The factor-three represented-fiber cost has standard primitive mean-value shape. -/
theorem representedPrimitiveConductorAnalyticCost_le_meanValueWeight
    {N u r : ℕ} (hN : 0 < N) (hu : 0 < u) (hr : 0 < r) :
    representedPrimitiveConductorAnalyticCost N u r ≤
      representedPrimitiveMeanValueGlobalFactor N u *
        ((r : ℝ) / (Nat.totient r : ℝ)) := by
  have hLogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hLogU : 0 ≤ Real.log (u : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hu)
  have hPrefix :
      reciprocalTotientPrefix (u / r) ≤ 6 * (1 + Real.log (u : ℝ)) :=
    (reciprocalTotientPrefix_mono (Nat.div_le_self u r)).trans
      (reciprocalTotientPrefix_le_six_mul_one_add_log u)
  have hBaseNonneg :
      0 ≤ (1 / (Nat.totient r : ℝ)) * (6 * (1 + Real.log (u : ℝ))) := by
    positivity
  have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast hr
  unfold representedPrimitiveConductorAnalyticCost
    representedPrimitiveMeanValueGlobalFactor
  calc
    3 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) *
          Real.log (N : ℝ) ≤
        3 * ((1 / (Nat.totient r : ℝ)) *
          (6 * (1 + Real.log (u : ℝ)))) * Real.log (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hPrefix (by positivity)) (by norm_num)) hLogN
    _ ≤ 3 * (((1 / (Nat.totient r : ℝ)) *
          (6 * (1 + Real.log (u : ℝ)))) * (r : ℝ)) *
          Real.log (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right hBaseNonneg hrOne) (by norm_num)) hLogN
    _ = (18 * (1 + Real.log (u : ℝ)) * Real.log (N : ℝ)) *
          ((r : ℝ) / (Nat.totient r : ℝ)) := by ring

/-- Primitive mean-value mass on the exact nonprincipal conductor support. -/
noncomputable def supportedPrimitiveCharacterMeanValueMass
    (N u : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
    ((r : ℝ) / (Nat.totient r : ℝ)) *
      ∑ χ ∈ primitiveCharacters r, M r χ

/-- The dependent key sum is the ordinary conductor-by-conductor support mass. -/
theorem allNonprincipalPrimitiveCharacterKeys_meanValueSum
    (N u : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) :
    (∑ key ∈ allNonprincipalPrimitiveCharacterKeys N u,
        ((key.1 : ℝ) / (Nat.totient key.1 : ℝ)) * M key.1 key.2) =
      supportedPrimitiveCharacterMeanValueMass N u M := by
  classical
  unfold allNonprincipalPrimitiveCharacterKeys supportedPrimitiveCharacterMeanValueMass
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]

/-- The represented-fiber allowance is controlled by the exact supported mean-value mass. -/
theorem representedNonprincipalConductorAnalyticAllowance_le_supportedMeanValueMass
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hN : 0 < N) (hu : 0 < u) :
    representedNonprincipalConductorAnalyticAllowance N u input.primitiveMax ≤
      representedPrimitiveMeanValueGlobalFactor N u *
        supportedPrimitiveCharacterMeanValueMass N u input.primitiveMax := by
  classical
  have hSubset := representedNonprincipalPrimitiveCharacterKeys_subset_all N u
  have hFactor : 0 ≤ representedPrimitiveMeanValueGlobalFactor N u := by
    unfold representedPrimitiveMeanValueGlobalFactor
    have hLogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hLogU : 0 ≤ Real.log (u : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hu)
    positivity
  calc
    representedNonprincipalConductorAnalyticAllowance N u input.primitiveMax ≤
        ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
          input.primitiveMax key.1 key.2 *
            (representedPrimitiveMeanValueGlobalFactor N u *
              ((key.1 : ℝ) / (Nat.totient key.1 : ℝ))) := by
      unfold representedNonprincipalConductorAnalyticAllowance
      apply Finset.sum_le_sum
      intro key hKey
      have hSupport := representedNonprincipalKey_conductor_mem_support hKey
      have hPrimitive := representedNonprincipalKey_character_mem_primitiveCharacters hKey
      exact mul_le_mul_of_nonneg_left
        (representedPrimitiveConductorAnalyticCost_le_meanValueWeight hN hu
          (representedKey_conductor_pos
            (mem_representedNonprincipalPrimitiveCharacterKeys_iff.mp hKey).1))
        (input.primitiveMax_nonneg key.1 hSupport key.2 hPrimitive)
    _ ≤ ∑ key ∈ allNonprincipalPrimitiveCharacterKeys N u,
          input.primitiveMax key.1 key.2 *
            (representedPrimitiveMeanValueGlobalFactor N u *
              ((key.1 : ℝ) / (Nat.totient key.1 : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro key hKeyAll hKeyNotRepresented
      have hData := Finset.mem_sigma.mp hKeyAll
      have hM := input.primitiveMax_nonneg key.1 hData.1 key.2 hData.2
      positivity
    _ = representedPrimitiveMeanValueGlobalFactor N u *
          (∑ key ∈ allNonprincipalPrimitiveCharacterKeys N u,
            ((key.1 : ℝ) / (Nat.totient key.1 : ℝ)) *
              input.primitiveMax key.1 key.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key hKey
      ring
    _ = representedPrimitiveMeanValueGlobalFactor N u *
          supportedPrimitiveCharacterMeanValueMass N u input.primitiveMax := by
      rw [allNonprincipalPrimitiveCharacterKeys_meanValueSum]

/-- The exact support mass embeds into the conventional primitive-character mass. -/
theorem supportedPrimitiveCharacterMeanValueMass_le_full
    {N u : ℕ} (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ M r χ) :
    supportedPrimitiveCharacterMeanValueMass N u M ≤
      primitiveCharacterMeanValueMass u M := by
  unfold supportedPrimitiveCharacterMeanValueMass primitiveCharacterMeanValueMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (nonprincipalPrimitiveConductorSupport_subset_Icc N u)
  intro r hrRange hrNotSupport
  have hrData := Finset.mem_Icc.mp hrRange
  have hrPos : 0 < r := by omega
  have hMass : 0 ≤ ∑ χ ∈ primitiveCharacters r, M r χ := by
    apply Finset.sum_nonneg
    intro χ hχ
    exact hM r hrRange χ hχ
  positivity

/-- The represented-fiber allowance is bounded by the conventional mean-value mass. -/
theorem representedNonprincipalConductorAnalyticAllowance_le_meanValueMass
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hN : 0 < N) (hu : 0 < u)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ input.primitiveMax r χ) :
    representedNonprincipalConductorAnalyticAllowance N u input.primitiveMax ≤
      representedPrimitiveMeanValueGlobalFactor N u *
        primitiveCharacterMeanValueMass u input.primitiveMax := by
  exact (representedNonprincipalConductorAnalyticAllowance_le_supportedMeanValueMass
    input hN hu).trans
      (mul_le_mul_of_nonneg_left
        (supportedPrimitiveCharacterMeanValueMass_le_full input.primitiveMax hM)
        (by
          unfold representedPrimitiveMeanValueGlobalFactor
          have hLogN : 0 ≤ Real.log (N : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hN)
          have hLogU : 0 ≤ Real.log (u : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hu)
          positivity))

/-- Exact small-conductor portion of the represented-key allowance. -/
noncomputable def representedNonprincipalConductorAnalyticAllowanceUpTo
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
      (fun key => key.1 ≤ R),
    M key.1 key.2 * representedPrimitiveConductorAnalyticCost N u key.1

/-- Exact large-conductor portion of the represented-key allowance. -/
noncomputable def representedNonprincipalConductorAnalyticAllowanceAbove
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) : ℝ :=
  ∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
      (fun key => R < key.1),
    M key.1 key.2 * representedPrimitiveConductorAnalyticCost N u key.1

/-- The represented-key allowance splits exactly at every conductor cutoff. -/
theorem representedNonprincipalConductorAnalyticAllowance_eq_upTo_add_above
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) :
    representedNonprincipalConductorAnalyticAllowance N u M =
      representedNonprincipalConductorAnalyticAllowanceUpTo N u R M +
        representedNonprincipalConductorAnalyticAllowanceAbove N u R M := by
  classical
  unfold representedNonprincipalConductorAnalyticAllowance
    representedNonprincipalConductorAnalyticAllowanceUpTo
    representedNonprincipalConductorAnalyticAllowanceAbove
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := representedNonprincipalPrimitiveCharacterKeys N u)
      (p := fun key => key.1 ≤ R)
      (f := fun key =>
        M key.1 key.2 * representedPrimitiveConductorAnalyticCost N u key.1)).symm

/-- Conventional nonprincipal primitive-character keys above conductor cutoff `R`. -/
noncomputable def allNonprincipalPrimitiveCharacterKeysAbove
    (N u R : ℕ) : Finset PrimitiveCharacterKey := by
  classical
  exact ((nonprincipalPrimitiveConductorSupport N u).filter (fun r => R < r)).sigma
    primitiveCharacters

/-- The represented keys above `R` embed into the conventional primitive support above `R`. -/
theorem representedNonprincipalPrimitiveCharacterKeysAbove_subset_all
    (N u R : ℕ) :
    (representedNonprincipalPrimitiveCharacterKeys N u).filter (fun key => R < key.1) ⊆
      allNonprincipalPrimitiveCharacterKeysAbove N u R := by
  intro key hKey
  have hData := Finset.mem_filter.mp hKey
  rw [allNonprincipalPrimitiveCharacterKeysAbove, Finset.mem_sigma]
  exact ⟨Finset.mem_filter.mpr
      ⟨representedNonprincipalKey_conductor_mem_support hData.1, hData.2⟩,
    representedNonprincipalKey_character_mem_primitiveCharacters hData.1⟩

/-- Large-conductor global factor for actual represented fibers. -/
noncomputable def representedLargeConductorDirectGlobalFactor
    (N R : ℕ) (B : ℝ) : ℝ :=
  3 * B * Real.log (N : ℝ) / (R : ℝ)

/-- The represented-fiber cost above `R` gains the same `1/R` factor, with constant three. -/
theorem representedPrimitiveConductorAnalyticCost_le_largeConductorWeight
    {N u R r : ℕ} {B : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hRr : R < r)
    (hPrefix : reciprocalTotientPrefix u ≤ B) :
    representedPrimitiveConductorAnalyticCost N u r ≤
      representedLargeConductorDirectGlobalFactor N R B *
        ((r : ℝ) / (Nat.totient r : ℝ)) := by
  have hr : 0 < r := lt_trans hR hRr
  have hPrefixUr : reciprocalTotientPrefix (u / r) ≤ B :=
    (reciprocalTotientPrefix_mono (Nat.div_le_self u r)).trans hPrefix
  have hB : 0 ≤ B := (reciprocalTotientPrefix_nonneg u).trans hPrefix
  have hRatio : (1 : ℝ) ≤ (r : ℝ) / (R : ℝ) := by
    rw [one_le_div₀]
    · exact_mod_cast hRr.le
    · exact_mod_cast hR
  have hCore :
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) ≤
        ((1 / (Nat.totient r : ℝ)) * B) * ((r : ℝ) / (R : ℝ)) := by
    calc
      (1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r) ≤
          (1 / (Nat.totient r : ℝ)) * B :=
        mul_le_mul_of_nonneg_left hPrefixUr (by positivity)
      _ ≤ ((1 / (Nat.totient r : ℝ)) * B) * ((r : ℝ) / (R : ℝ)) :=
        le_mul_of_one_le_right (mul_nonneg (by positivity) hB) hRatio
  have hLog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  unfold representedPrimitiveConductorAnalyticCost
    representedLargeConductorDirectGlobalFactor
  calc
    3 * ((1 / (Nat.totient r : ℝ)) * reciprocalTotientPrefix (u / r)) *
          Real.log (N : ℝ) ≤
        3 * (((1 / (Nat.totient r : ℝ)) * B) * ((r : ℝ) / (R : ℝ))) *
          Real.log (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCore (by norm_num)) hLog
    _ = (3 * B * Real.log (N : ℝ) / (R : ℝ)) *
          ((r : ℝ) / (Nat.totient r : ℝ)) := by ring

/-- The dependent key sum above `R` is the conventional large-conductor mean-value mass. -/
theorem allNonprincipalPrimitiveCharacterKeysAbove_meanValueSum
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) :
    (∑ key ∈ allNonprincipalPrimitiveCharacterKeysAbove N u R,
        ((key.1 : ℝ) / (Nat.totient key.1 : ℝ)) * M key.1 key.2) =
      largeConductorPrimitiveMeanValueMass N u R M := by
  classical
  unfold allNonprincipalPrimitiveCharacterKeysAbove
    largeConductorPrimitiveMeanValueMass
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]

/-- The represented large-conductor allowance has a direct conventional mean-value bound. -/
theorem representedNonprincipalConductorAnalyticAllowanceAbove_le_meanValueMass
    {L N u R : ℕ} {B : ℝ} (input : PrimitivePsiMaxInput L N u)
    (hN : 0 < N) (hR : 0 < R)
    (hPrefix : reciprocalTotientPrefix u ≤ B) :
    representedNonprincipalConductorAnalyticAllowanceAbove
        N u R input.primitiveMax ≤
      representedLargeConductorDirectGlobalFactor N R B *
        largeConductorPrimitiveMeanValueMass N u R input.primitiveMax := by
  classical
  have hSubset := representedNonprincipalPrimitiveCharacterKeysAbove_subset_all N u R
  have hFactor : 0 ≤ representedLargeConductorDirectGlobalFactor N R B := by
    have hB : 0 ≤ B := (reciprocalTotientPrefix_nonneg u).trans hPrefix
    have hLog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    unfold representedLargeConductorDirectGlobalFactor
    positivity
  unfold representedNonprincipalConductorAnalyticAllowanceAbove
  calc
    (∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => R < key.1),
        input.primitiveMax key.1 key.2 *
          representedPrimitiveConductorAnalyticCost N u key.1) ≤
      ∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => R < key.1),
        input.primitiveMax key.1 key.2 *
          (representedLargeConductorDirectGlobalFactor N R B *
            ((key.1 : ℝ) / (Nat.totient key.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro key hKey
      have hData := Finset.mem_filter.mp hKey
      have hSupport := representedNonprincipalKey_conductor_mem_support hData.1
      have hPrimitive := representedNonprincipalKey_character_mem_primitiveCharacters hData.1
      exact mul_le_mul_of_nonneg_left
        (representedPrimitiveConductorAnalyticCost_le_largeConductorWeight
          hN hR hData.2 hPrefix)
        (input.primitiveMax_nonneg key.1 hSupport key.2 hPrimitive)
    _ ≤ ∑ key ∈ allNonprincipalPrimitiveCharacterKeysAbove N u R,
        input.primitiveMax key.1 key.2 *
          (representedLargeConductorDirectGlobalFactor N R B *
            ((key.1 : ℝ) / (Nat.totient key.1 : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro key hKeyAll hKeyNotRepresented
      have hData := Finset.mem_sigma.mp hKeyAll
      have hSupport := (Finset.mem_filter.mp hData.1).1
      have hM := input.primitiveMax_nonneg key.1 hSupport key.2 hData.2
      positivity
    _ = representedLargeConductorDirectGlobalFactor N R B *
          (∑ key ∈ allNonprincipalPrimitiveCharacterKeysAbove N u R,
            ((key.1 : ℝ) / (Nat.totient key.1 : ℝ)) *
              input.primitiveMax key.1 key.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro key hKey
      ring
    _ = representedLargeConductorDirectGlobalFactor N R B *
          largeConductorPrimitiveMeanValueMass N u R input.primitiveMax := by
      rw [allNonprincipalPrimitiveCharacterKeysAbove_meanValueSum]

/-- Full coprime allowance for the represented-fiber route. -/
noncomputable def representedActiveCoprimeAnalyticAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) : ℝ :=
  principalConductorAnalyticAllowance N input.principalMax +
    representedNonprincipalConductorAnalyticAllowance N u input.primitiveMax +
      inducedCharacterAnalyticAllowance N u

/-- Full short Type-I allowance after adding the proved noncoprime branch. -/
noncomputable def representedActiveTypeIAnalyticAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) : ℝ :=
  representedActiveCoprimeAnalyticAllowance input +
    balancedVaughanTypeINoncoprimeExplicitBound N u

/-- Closed coprime allowance after a conventional primitive mean-value bound `B`. -/
noncomputable def representedActiveCoprimeMeanValueAllowance
    (N u : ℕ) (principalMax B : ℝ) : ℝ :=
  principalConductorAnalyticAllowance N principalMax +
    representedPrimitiveMeanValueGlobalFactor N u * B +
      inducedCharacterAnalyticAllowance N u

/-- Closed short Type-I allowance after a conventional primitive mean-value bound `B`. -/
noncomputable def representedActiveTypeIMeanValueAllowance
    (N u : ℕ) (principalMax B : ℝ) : ℝ :=
  representedActiveCoprimeMeanValueAllowance N u principalMax B +
    balancedVaughanTypeINoncoprimeExplicitBound N u

/-- The primitive input controls one actual represented nonprincipal fiber. -/
theorem norm_representedPrimitiveCharacterConductorSum_le_input
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    {key : PrimitiveCharacterKey}
    (hKey : key ∈ representedNonprincipalPrimitiveCharacterKeys N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
      input.primitiveMax key.1 key.2 *
        representedPrimitiveConductorAnalyticCost N u key.1 := by
  have hRepresented :=
    (mem_representedNonprincipalPrimitiveCharacterKeys_iff.mp hKey).1
  have hSupport := representedNonprincipalKey_conductor_mem_support hKey
  have hPrimitive := representedNonprincipalKey_character_mem_primitiveCharacters hKey
  have hN : 0 < N := by omega
  have hInterval : L ≤ N - L := by omega
  have hRight : N - L < N := by omega
  simpa [representedPrimitiveConductorAnalyticCost] using
    (norm_representedPrimitiveCharacterConductorSum_le key
      (input.primitiveMax key.1 key.2) hN
      (representedKey_conductor_pos hRepresented)
      (representedKey_conductor_coprime hRepresented)
      hL hInterval hRight
      (input.primitiveMax_nonneg key.1 hSupport key.2 hPrimitive)
      (input.primitive_bound key.1 hSupport key.2 hPrimitive))

/-- The input controls the sum over all actual represented nonprincipal fibers. -/
theorem norm_representedNonprincipalConductorSums_le_input
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
        representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
      representedNonprincipalConductorAnalyticAllowance
        N u input.primitiveMax := by
  unfold representedNonprincipalConductorAnalyticAllowance
  calc
    ‖∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
        representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
        ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
          ‖representedPrimitiveCharacterConductorSum N u key L (N - L)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
        input.primitiveMax key.1 key.2 *
          representedPrimitiveConductorAnalyticCost N u key.1 := by
      apply Finset.sum_le_sum
      intro key hKey
      exact norm_representedPrimitiveCharacterConductorSum_le_input
        input hKey hL hTwoL

/--
Unconditional quantitative endpoint of the represented-fiber reduction.  It needs no
`PrimitiveCharacterChangeLevelStable` assumption.
-/
theorem norm_activeCoprimeProgressionError_le_representedAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      representedActiveCoprimeAnalyticAllowance input := by
  have hN : 0 < N := by omega
  rw [activeCoprimeProgressionError_cast_eq_principal_add_represented_sub_induced
    hL hu]
  calc
    ‖principalCenteredConductorSum N u L (N - L) +
        (∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
          representedPrimitiveCharacterConductorSum N u key L (N - L)) -
        activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
        ‖principalCenteredConductorSum N u L (N - L) +
          (∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
            representedPrimitiveCharacterConductorSum N u key L (N - L))‖ +
          ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ :=
      norm_sub_le _ _
    _ ≤ (‖principalCenteredConductorSum N u L (N - L)‖ +
          ‖∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
            representedPrimitiveCharacterConductorSum N u key L (N - L)‖) +
          ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ := by
      exact add_le_add_right (norm_add_le _ _) _
    _ ≤ principalConductorAnalyticAllowance N input.principalMax +
          representedNonprincipalConductorAnalyticAllowance N u input.primitiveMax +
          inducedCharacterAnalyticAllowance N u := by
      exact add_le_add
        (add_le_add
          (norm_principalCenteredConductorSum_le_input input hL hTwoL)
          (norm_representedNonprincipalConductorSums_le_input input hL hTwoL))
        (norm_activeInducedCorrection_le_allowance hN hu)
    _ = representedActiveCoprimeAnalyticAllowance input := rfl

/-- Add the proved noncoprime branch to the represented-fiber coprime estimate. -/
theorem abs_primeResidueSum_sub_activeMain_le_representedAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) :
    |balancedVaughanTypeIPrimeResidueSum L N u -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      representedActiveTypeIAnalyticAllowance input := by
  have hLN : L ≤ N := by omega
  have hCoprime :
      |balancedVaughanTypeIActiveCoprimeProgressionError L N u| ≤
        representedActiveCoprimeAnalyticAllowance input := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      (norm_activeCoprimeProgressionError_le_representedAllowance
        input hL hu hTwoL)
  have hNoncoprime :
      |balancedVaughanTypeINoncoprimeProgressionContribution L N u| ≤
        balancedVaughanTypeINoncoprimeExplicitBound N u :=
    abs_balancedVaughanTypeINoncoprimeProgressionContribution_le
      (by omega : 1 ≤ L) hLN
  rw [primeResidueSum_eq_activeMain_add_coprimeError_add_noncoprime]
  calc
    |balancedVaughanTypeIActiveDiscreteCoprimeMain L N u +
          balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u -
          balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| =
        |balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u| := by
      congr 1
      ring
    _ ≤ |balancedVaughanTypeIActiveCoprimeProgressionError L N u| +
          |balancedVaughanTypeINoncoprimeProgressionContribution L N u| :=
      abs_add_le _ _
    _ ≤ representedActiveCoprimeAnalyticAllowance input +
          balancedVaughanTypeINoncoprimeExplicitBound N u :=
      add_le_add hCoprime hNoncoprime
    _ = representedActiveTypeIAnalyticAllowance input := rfl

/--
Complete short Type-I correlation theorem over actual represented fibers.  This removes the
change-level stability premise from the convolution endpoint.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_representedAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      representedActiveTypeIAnalyticAllowance input := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_residueSum hL]
  exact abs_primeResidueSum_sub_activeMain_le_representedAllowance
    input (by omega) hu hTwoL

/-- Insert a conventional primitive-character mean-value bound into the coprime endpoint. -/
theorem norm_activeCoprimeProgressionError_le_representedMeanValueAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) (B : ℝ)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ input.primitiveMax r χ)
    (hMass : primitiveCharacterMeanValueMass u input.primitiveMax ≤ B) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      representedActiveCoprimeMeanValueAllowance
        N u input.principalMax B := by
  have hN : 0 < N := by omega
  have hFactor : 0 ≤ representedPrimitiveMeanValueGlobalFactor N u := by
    unfold representedPrimitiveMeanValueGlobalFactor
    have hLogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hLogU : 0 ≤ Real.log (u : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hu)
    positivity
  have hNonprincipal :
      representedNonprincipalConductorAnalyticAllowance N u input.primitiveMax ≤
        representedPrimitiveMeanValueGlobalFactor N u * B :=
    (representedNonprincipalConductorAnalyticAllowance_le_meanValueMass
      input hN hu hM).trans (mul_le_mul_of_nonneg_left hMass hFactor)
  calc
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
        representedActiveCoprimeAnalyticAllowance input :=
      norm_activeCoprimeProgressionError_le_representedAllowance
        input hL hu hTwoL
    _ ≤ representedActiveCoprimeMeanValueAllowance
          N u input.principalMax B := by
      unfold representedActiveCoprimeAnalyticAllowance
        representedActiveCoprimeMeanValueAllowance
      linarith

/--
Complete short Type-I correlation theorem with the no-stability represented-fiber reduction and a
standard primitive-character mean-value hypothesis.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_representedMeanValueAllowance
    {L N u : ℕ} (input : PrimitivePsiMaxInput L N u) (B : ℝ)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hM : ∀ r ∈ Finset.Icc 2 u,
      ∀ χ ∈ primitiveCharacters r, 0 ≤ input.primitiveMax r χ)
    (hMass : primitiveCharacterMeanValueMass u input.primitiveMax ≤ B) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      representedActiveTypeIMeanValueAllowance
        N u input.principalMax B := by
  have hCoprime :=
    norm_activeCoprimeProgressionError_le_representedMeanValueAllowance
      input B (by omega : 0 < L) hu hTwoL hM hMass
  have hLN : L ≤ N := by omega
  have hNoncoprime :
      |balancedVaughanTypeINoncoprimeProgressionContribution L N u| ≤
        balancedVaughanTypeINoncoprimeExplicitBound N u :=
    abs_balancedVaughanTypeINoncoprimeProgressionContribution_le
      (by omega : 1 ≤ L) hLN
  rw [balancedVaughanTypeIPrimeConvolution_eq_residueSum hL,
    primeResidueSum_eq_activeMain_add_coprimeError_add_noncoprime]
  have hCoprimeReal :
      |balancedVaughanTypeIActiveCoprimeProgressionError L N u| ≤
        representedActiveCoprimeMeanValueAllowance
          N u input.principalMax B := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hCoprime
  calc
    |balancedVaughanTypeIActiveDiscreteCoprimeMain L N u +
          balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u -
          balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| =
        |balancedVaughanTypeIActiveCoprimeProgressionError L N u +
          balancedVaughanTypeINoncoprimeProgressionContribution L N u| := by
      congr 1
      ring
    _ ≤ |balancedVaughanTypeIActiveCoprimeProgressionError L N u| +
          |balancedVaughanTypeINoncoprimeProgressionContribution L N u| :=
      abs_add_le _ _
    _ ≤ representedActiveCoprimeMeanValueAllowance
          N u input.principalMax B +
          balancedVaughanTypeINoncoprimeExplicitBound N u :=
      add_le_add hCoprimeReal hNoncoprime
    _ = representedActiveTypeIMeanValueAllowance
          N u input.principalMax B := rfl

/-- Independent represented small/large estimates dominate the exact represented allowance. -/
theorem representedActiveTypeIAnalyticAllowance_le_split
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (smallBound largeBound : ℝ)
    (hSmall : representedNonprincipalConductorAnalyticAllowanceUpTo
      N u R input.primitiveMax ≤ smallBound)
    (hLarge : representedNonprincipalConductorAnalyticAllowanceAbove
      N u R input.primitiveMax ≤ largeBound) :
    representedActiveTypeIAnalyticAllowance input ≤
      activeTypeISplitAnalyticAllowance
        N u input.principalMax smallBound largeBound := by
  rw [representedActiveTypeIAnalyticAllowance,
    representedActiveCoprimeAnalyticAllowance,
    representedNonprincipalConductorAnalyticAllowance_eq_upTo_add_above]
  unfold activeTypeISplitAnalyticAllowance activeCoprimeSplitAnalyticAllowance
  linarith

/--
No-stability split Type-I endpoint.  The represented fibers preserve the large-conductor `1/R`
saving with explicit factor `18 * (1 + log u) * log N / R`; only the represented small-conductor
allowance and the conventional large-conductor primitive mean-value mass remain to be estimated.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_representedHybridMeanValueAllowance
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hSmall : representedNonprincipalConductorAnalyticAllowanceUpTo
      N u R input.primitiveMax ≤ smallBound)
    (hMass : largeConductorPrimitiveMeanValueMass
      N u R input.primitiveMax ≤ massBound) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
        (representedLargeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound) := by
  have hN : 0 < N := by omega
  have hPrefix :
      reciprocalTotientPrefix u ≤ 6 * (1 + Real.log (u : ℝ)) :=
    reciprocalTotientPrefix_le_six_mul_one_add_log u
  have hFactor :
      0 ≤ representedLargeConductorDirectGlobalFactor N R
        (6 * (1 + Real.log (u : ℝ))) := by
    unfold representedLargeConductorDirectGlobalFactor
    have hLogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN)
    have hLogU : 0 ≤ Real.log (u : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hu)
    positivity
  have hLarge :
      representedNonprincipalConductorAnalyticAllowanceAbove
          N u R input.primitiveMax ≤
        representedLargeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound :=
    (representedNonprincipalConductorAnalyticAllowanceAbove_le_meanValueMass
      input hN hR hPrefix).trans
        (mul_le_mul_of_nonneg_left hMass hFactor)
  exact (abs_typeIPrimeConvolution_sub_activeMain_le_representedAllowance
    input hL hu hTwoL).trans
      (representedActiveTypeIAnalyticAllowance_le_split
        input smallBound
          (representedLargeConductorDirectGlobalFactor N R
            (6 * (1 + Real.log (u : ℝ))) * massBound)
          hSmall hLarge)

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberClosure
