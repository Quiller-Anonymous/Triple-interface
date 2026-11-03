import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberClosure
import Goldbach.Cert.MajorArcModules.RouteADirichletCharacterConductorTransport

/-!
# Localized signed/direct hybrid for balanced Vaughan Type I

The complete-fiber signed estimate is valuable at small primitive conductors, but the existing
reindexing theorem assumes change-level stability for every represented primitive character.
This file localizes that algebraic requirement to the represented keys with conductor at most a
chosen cutoff `R`.  Above `R`, it retains the unconditional direct represented-fiber estimate.

Thus the exact Type-I endpoint no longer needs global change-level stability. The initially
isolated completeness premise only concerns small represented fibers on the prime interval used by
the convolution and at moduli carrying a nonzero Mobius coefficient. The squarefree conductor
transport theorem now discharges that premise.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLocalizedHybrid

open scoped BigOperators
open ArithmeticFunction
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanFixedCenter
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanNoncoprime
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveAnalyticInterface
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLargeConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberDirect
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanRepresentedFiberClosure
open Goldbach.Cert.MajorArcModules.RouteAReciprocalTotientPrefix
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterConductorTransport

noncomputable section

/--
Completeness only for represented nonprincipal fibers below `R`, only on the interval used by the
balanced convolution, and only at moduli carrying a nonzero Mobius coefficient.
-/
def RepresentedConductorLiftCompleteUpTo
    (L N u R : ℕ) : Prop :=
  ∀ p ∈ Finset.Ico L (N - L + 1),
    ∀ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
      key.1 ≤ R →
        ∀ d ∈ activeCoprimeTypeIModuliAt N u p,
          key.1 ∣ d → (moebius d : ℤ) ≠ 0 →
            d ∈ representedPrimitiveCharacterFiberModuli N u key

/-- Conductor preservation is needed only at levels with nonzero Mobius coefficient. -/
def PrimitiveCharacterSupportedChangeLevelStable : Prop :=
  ∀ {r d : ℕ} (χ : DirichletCharacter ℂ r) (hrd : r ∣ d),
    (moebius d : ℤ) ≠ 0 → d ≠ 0 → χ.IsPrimitive →
      primitiveCharacterKey
          (⟨d, DirichletCharacter.changeLevel hrd χ⟩ : CharacterOccurrence) =
        (⟨r, χ⟩ : PrimitiveCharacterKey)

/-- Primitive keys are preserved on the nonzero Mobius support. -/
theorem primitiveCharacterSupportedChangeLevelStable :
    PrimitiveCharacterSupportedChangeLevelStable := by
  intro r d χ hrd hMu hd hPrimitive
  exact primitiveCharacterKey_changeLevel_eq_of_squarefree χ hrd
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hMu) hPrimitive

/-- The older global statement implies the supported conductor-preservation statement. -/
theorem primitiveCharacterSupportedChangeLevelStable_of_changeLevelStable
    (hStable : PrimitiveCharacterChangeLevelStable) :
    PrimitiveCharacterSupportedChangeLevelStable := by
  intro r d χ hrd hMu hd hPrimitive
  exact hStable χ hrd hd hPrimitive

/-- Supported change-level stability implies the localized completeness premise. -/
theorem representedConductorLiftCompleteUpTo_of_supportedChangeLevelStable
    {L N u R : ℕ} (hStable : PrimitiveCharacterSupportedChangeLevelStable) :
    RepresentedConductorLiftCompleteUpTo L N u R := by
  classical
  intro p hp key hKey hKeyR d hd hKeyDvd hMu
  have hRepresented :=
    (mem_representedNonprincipalPrimitiveCharacterKeys_iff.mp hKey).1
  have hPrimitive := representedKey_isPrimitive hRepresented
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  have hdPos : 0 < d := (Finset.mem_Icc.mp hdInner.1).1
  let occurrence : CharacterOccurrence :=
    ⟨d, DirichletCharacter.changeLevel hKeyDvd key.2⟩
  have hOccurrence :
      occurrence ∈ activeCharacterOccurrencesForKeyAt N u p key := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_sigma.mpr ⟨hd, Finset.mem_univ _⟩
    · simpa [occurrence] using hStable key.2 hKeyDvd hMu hdPos.ne' hPrimitive
  rw [activeCharacterOccurrencesForKeyAt_eq_static_filter] at hOccurrence
  exact Finset.mem_image.mpr
    ⟨occurrence, (Finset.mem_filter.mp hOccurrence).1, rfl⟩

/-- The localized lift-completeness premise is proved on its exact Mobius support. -/
theorem representedConductorLiftCompleteUpTo_proved
    (L N u R : ℕ) :
    RepresentedConductorLiftCompleteUpTo L N u R :=
  representedConductorLiftCompleteUpTo_of_supportedChangeLevelStable
    primitiveCharacterSupportedChangeLevelStable

/-- Global change-level stability implies the localized completeness premise. -/
theorem representedConductorLiftCompleteUpTo_of_changeLevelStable
    {L N u R : ℕ} (hStable : PrimitiveCharacterChangeLevelStable) :
    RepresentedConductorLiftCompleteUpTo L N u R :=
  representedConductorLiftCompleteUpTo_of_supportedChangeLevelStable
    (primitiveCharacterSupportedChangeLevelStable_of_changeLevelStable hStable)

/--
Completeness on the nonzero Mobius support is enough: omitted represented levels have coefficient
zero and therefore do not change the conductor weight.
-/
theorem activePrimitiveCharacterFiberWeightAt_eq_conductorWeight_of_supported_complete
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hpN : p ≤ N)
    (hComplete : ∀ d ∈ activeCoprimeTypeIModuliAt N u p,
      key.1 ∣ d → (moebius d : ℤ) ≠ 0 →
        d ∈ representedPrimitiveCharacterFiberModuli N u key) :
    activePrimitiveCharacterFiberWeightAt N u p key =
      balancedVaughanTypeIConductorWeight N u key.1 p := by
  rw [activePrimitiveCharacterFiberWeightAt_eq_representedLogWeight]
  unfold representedPrimitiveCharacterFiberLogWeight
    balancedVaughanTypeIConductorWeight
  rw [← activeConductorLiftModuliAt_eq]
  rw [Nat.cast_sub hpN]
  apply Finset.sum_subset
  · intro d hd
    have hdData := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨representedFiberModulus_mem_coprimeTypeIModuli hdData.1, hdData.2⟩,
        representedFiber_conductor_dvd_modulus hdData.1⟩
  · intro d hdFull hdMissing
    have hdData := Finset.mem_filter.mp hdFull
    have hMu : (moebius d : ℤ) = 0 := by
      by_contra hMu
      have hRepresented := hComplete d hdData.1 hdData.2 hMu
      have hCutoff : d ≤ N - p :=
        (Finset.mem_filter.mp hdData.1).2
      exact hdMissing (Finset.mem_filter.mpr ⟨hRepresented, hCutoff⟩)
    simp [hMu]

/-- A represented fiber with complete lifts is the ordinary complete conductor sum. -/
theorem representedPrimitiveCharacterConductorSum_eq_primitive_of_complete
    {N u a b : ℕ} {key : PrimitiveCharacterKey}
    (hbN : b ≤ N)
    (hComplete : ∀ p ∈ Finset.Ico a (b + 1),
      ∀ d ∈ activeCoprimeTypeIModuliAt N u p,
        key.1 ∣ d → (moebius d : ℤ) ≠ 0 →
          d ∈ representedPrimitiveCharacterFiberModuli N u key) :
    representedPrimitiveCharacterConductorSum N u key a b =
      primitiveCharacterConductorSum N u key.1 a b key.2 := by
  unfold representedPrimitiveCharacterConductorSum primitiveCharacterConductorSum
  apply Finset.sum_congr rfl
  intro p hp
  have hpN : p ≤ N := by
    have hpb : p ≤ b :=
      Nat.lt_succ_iff.mp (by
        simpa [Nat.succ_eq_add_one] using (Finset.mem_Ico.mp hp).2)
    exact hpb.trans hbN
  have hWeight :=
    activePrimitiveCharacterFiberWeightAt_eq_conductorWeight_of_supported_complete
      (N := N) (u := u) (p := p) (key := key) hpN (hComplete p hp)
  rw [hWeight]

/-- The represented nonprincipal sum splits exactly at the conductor cutoff. -/
theorem representedNonprincipalConductorSums_eq_upTo_add_above
    (L N u R : ℕ) :
    (∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
        representedPrimitiveCharacterConductorSum N u key L (N - L)) =
      (∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
          (fun key => key.1 ≤ R),
        representedPrimitiveCharacterConductorSum N u key L (N - L)) +
      (∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
          (fun key => R < key.1),
        representedPrimitiveCharacterConductorSum N u key L (N - L)) := by
  classical
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (s := representedNonprincipalPrimitiveCharacterKeys N u)
      (p := fun key => key.1 ≤ R)
      (f := fun key =>
        representedPrimitiveCharacterConductorSum N u key L (N - L))).symm

/-- Conventional nonprincipal primitive-character keys through conductor cutoff `R`. -/
noncomputable def allNonprincipalPrimitiveCharacterKeysUpTo
    (N u R : ℕ) : Finset PrimitiveCharacterKey := by
  classical
  exact ((nonprincipalPrimitiveConductorSupport N u).filter (fun r => r ≤ R)).sigma
    primitiveCharacters

/-- Represented keys through `R` embed into the conventional primitive support through `R`. -/
theorem representedNonprincipalPrimitiveCharacterKeysUpTo_subset_all
    (N u R : ℕ) :
    (representedNonprincipalPrimitiveCharacterKeys N u).filter (fun key => key.1 ≤ R) ⊆
      allNonprincipalPrimitiveCharacterKeysUpTo N u R := by
  intro key hKey
  have hData := Finset.mem_filter.mp hKey
  rw [allNonprincipalPrimitiveCharacterKeysUpTo, Finset.mem_sigma]
  exact ⟨Finset.mem_filter.mpr
      ⟨representedNonprincipalKey_conductor_mem_support hData.1, hData.2⟩,
    representedNonprincipalKey_character_mem_primitiveCharacters hData.1⟩

/-- The dependent small-key sum is the ordinary small-conductor signed allowance. -/
theorem allNonprincipalPrimitiveCharacterKeysUpTo_allowanceSum
    (N u R : ℕ) (M : (r : ℕ) → DirichletCharacter ℂ r → ℝ) :
    (∑ key ∈ allNonprincipalPrimitiveCharacterKeysUpTo N u R,
        M key.1 key.2 * primitiveConductorAnalyticCost N key.1) =
      nonprincipalConductorAnalyticAllowanceUpTo N u R M := by
  classical
  unfold allNonprincipalPrimitiveCharacterKeysUpTo
    nonprincipalConductorAnalyticAllowanceUpTo
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_mul]

/--
Localized lift completeness recovers the signed factor-two conductor cost on every represented
small-conductor fiber.
-/
theorem norm_representedNonprincipalConductorSumsUpTo_le_signedAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N)
    (hComplete : RepresentedConductorLiftCompleteUpTo L N u R) :
    ‖∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => key.1 ≤ R),
        representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
      nonprincipalConductorAnalyticAllowanceUpTo
        N u R input.primitiveMax := by
  classical
  have hN : 0 < N := by omega
  have hInterval : L ≤ N - L := by omega
  have hRight : N - L < N := by omega
  have hSubset :=
    representedNonprincipalPrimitiveCharacterKeysUpTo_subset_all N u R
  calc
    ‖∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => key.1 ≤ R),
        representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
      ∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => key.1 ≤ R),
        ‖representedPrimitiveCharacterConductorSum N u key L (N - L)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => key.1 ≤ R),
        input.primitiveMax key.1 key.2 *
          primitiveConductorAnalyticCost N key.1 := by
      apply Finset.sum_le_sum
      intro key hKey
      have hData := Finset.mem_filter.mp hKey
      have hRepresented :=
        (mem_representedNonprincipalPrimitiveCharacterKeys_iff.mp hData.1).1
      have hSupport := representedNonprincipalKey_conductor_mem_support hData.1
      have hPrimitive :=
        representedNonprincipalKey_character_mem_primitiveCharacters hData.1
      rw [representedPrimitiveCharacterConductorSum_eq_primitive_of_complete
        (by omega) (fun p hp => hComplete p hp key hData.1 hData.2)]
      simpa [primitiveConductorAnalyticCost] using
        (norm_primitiveCharacterConductorSum_le key.2
          (input.primitiveMax key.1 key.2) hN
          (representedKey_conductor_pos hRepresented)
          (representedKey_conductor_coprime hRepresented)
          hL hInterval hRight
          (input.primitiveMax_nonneg key.1 hSupport key.2 hPrimitive)
          (input.primitive_bound key.1 hSupport key.2 hPrimitive))
    _ ≤ ∑ key ∈ allNonprincipalPrimitiveCharacterKeysUpTo N u R,
        input.primitiveMax key.1 key.2 *
          primitiveConductorAnalyticCost N key.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro key hKeyAll hKeyNotRepresented
      have hData := Finset.mem_sigma.mp hKeyAll
      have hSupport := (Finset.mem_filter.mp hData.1).1
      have hM := input.primitiveMax_nonneg key.1 hSupport key.2 hData.2
      unfold primitiveConductorAnalyticCost
      have hLogN : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hN)
      positivity
    _ = nonprincipalConductorAnalyticAllowanceUpTo
        N u R input.primitiveMax :=
      allNonprincipalPrimitiveCharacterKeysUpTo_allowanceSum
        N u R input.primitiveMax

/-- The represented large-conductor sum retains its unconditional direct factor-three cost. -/
theorem norm_representedNonprincipalConductorSumsAbove_le_directAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N) :
    ‖∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => R < key.1),
        representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
      representedNonprincipalConductorAnalyticAllowanceAbove
        N u R input.primitiveMax := by
  unfold representedNonprincipalConductorAnalyticAllowanceAbove
  calc
    ‖∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => R < key.1),
        representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
      ∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => R < key.1),
        ‖representedPrimitiveCharacterConductorSum N u key L (N - L)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ key ∈ (representedNonprincipalPrimitiveCharacterKeys N u).filter
        (fun key => R < key.1),
        input.primitiveMax key.1 key.2 *
          representedPrimitiveConductorAnalyticCost N u key.1 := by
      apply Finset.sum_le_sum
      intro key hKey
      exact norm_representedPrimitiveCharacterConductorSum_le_input
        input (Finset.mem_filter.mp hKey).1 hL hTwoL

/--
The represented nonprincipal main admits a signed small-conductor bound and an unconditional
direct large-conductor bound.
-/
theorem norm_representedNonprincipalConductorSums_le_localizedHybridAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hTwoL : 2 * L ≤ N)
    (hComplete : RepresentedConductorLiftCompleteUpTo L N u R) :
    ‖∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
        representedPrimitiveCharacterConductorSum N u key L (N - L)‖ ≤
      nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax +
        representedNonprincipalConductorAnalyticAllowanceAbove
          N u R input.primitiveMax := by
  rw [representedNonprincipalConductorSums_eq_upTo_add_above L N u R]
  exact (norm_add_le _ _).trans
    (add_le_add
      (norm_representedNonprincipalConductorSumsUpTo_le_signedAllowance
        input hL hTwoL hComplete)
      (norm_representedNonprincipalConductorSumsAbove_le_directAllowance
        input hL hTwoL))

/-- Exact coprime endpoint for the localized signed/direct hybrid. -/
theorem norm_activeCoprimeProgressionError_le_localizedHybridAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hComplete : RepresentedConductorLiftCompleteUpTo L N u R) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance N u input.principalMax
        (nonprincipalConductorAnalyticAllowanceUpTo
          N u R input.primitiveMax)
        (representedNonprincipalConductorAnalyticAllowanceAbove
          N u R input.primitiveMax) := by
  have hN : 0 < N := by omega
  rw [activeCoprimeProgressionError_cast_eq_principal_add_represented_sub_induced
    hL hu]
  calc
    ‖principalCenteredConductorSum N u L (N - L) +
        (∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
          representedPrimitiveCharacterConductorSum N u key L (N - L)) -
        activePrimitiveCharacterTotalInducedCorrection L N u‖ ≤
      (‖principalCenteredConductorSum N u L (N - L)‖ +
        ‖∑ key ∈ representedNonprincipalPrimitiveCharacterKeys N u,
          representedPrimitiveCharacterConductorSum N u key L (N - L)‖) +
        ‖activePrimitiveCharacterTotalInducedCorrection L N u‖ := by
      exact (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ principalConductorAnalyticAllowance N input.principalMax +
        (nonprincipalConductorAnalyticAllowanceUpTo N u R input.primitiveMax +
          representedNonprincipalConductorAnalyticAllowanceAbove
            N u R input.primitiveMax) +
        inducedCharacterAnalyticAllowance N u := by
      exact add_le_add
        (add_le_add
          (norm_principalCenteredConductorSum_le_input input hL hTwoL)
          (norm_representedNonprincipalConductorSums_le_localizedHybridAllowance
            input hL hTwoL hComplete))
        (norm_activeInducedCorrection_le_allowance hN hu)
    _ = activeCoprimeSplitAnalyticAllowance N u input.principalMax
        (nonprincipalConductorAnalyticAllowanceUpTo
          N u R input.primitiveMax)
        (representedNonprincipalConductorAnalyticAllowanceAbove
          N u R input.primitiveMax) := by
      unfold activeCoprimeSplitAnalyticAllowance
      ring

/-- Insert independent numerical estimates for the two conductor ranges. -/
theorem norm_activeCoprimeProgressionError_le_localizedHybridSplitAllowance
    {L N u R : ℕ} (input : PrimitivePsiMaxInput L N u)
    (smallBound largeBound : ℝ)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N)
    (hComplete : RepresentedConductorLiftCompleteUpTo L N u R)
    (hSmall : nonprincipalConductorAnalyticAllowanceUpTo
      N u R input.primitiveMax ≤ smallBound)
    (hLarge : representedNonprincipalConductorAnalyticAllowanceAbove
      N u R input.primitiveMax ≤ largeBound) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance
        N u input.principalMax smallBound largeBound := by
  calc
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
        activeCoprimeSplitAnalyticAllowance N u input.principalMax
          (nonprincipalConductorAnalyticAllowanceUpTo
            N u R input.primitiveMax)
          (representedNonprincipalConductorAnalyticAllowanceAbove
            N u R input.primitiveMax) :=
      norm_activeCoprimeProgressionError_le_localizedHybridAllowance
        input hL hu hTwoL hComplete
    _ ≤ activeCoprimeSplitAnalyticAllowance
        N u input.principalMax smallBound largeBound := by
      unfold activeCoprimeSplitAnalyticAllowance
      linarith

/--
Mean-value form of the localized coprime endpoint.  The small range uses the signed conductor
cost; the large range has the explicit represented-fiber factor `18 (1 + log u) log N / R`.
-/
theorem norm_activeCoprimeProgressionError_le_localizedHybridMeanValueAllowance
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hComplete : RepresentedConductorLiftCompleteUpTo L N u R)
    (hSmall : nonprincipalConductorAnalyticAllowanceUpTo
      N u R input.primitiveMax ≤ smallBound)
    (hMass : largeConductorPrimitiveMeanValueMass
      N u R input.primitiveMax ≤ massBound) :
    ‖(balancedVaughanTypeIActiveCoprimeProgressionError L N u : ℂ)‖ ≤
      activeCoprimeSplitAnalyticAllowance N u input.principalMax smallBound
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
  exact norm_activeCoprimeProgressionError_le_localizedHybridSplitAllowance
    input smallBound
      (representedLargeConductorDirectGlobalFactor N R
        (6 * (1 + Real.log (u : ℝ))) * massBound)
      hL hu hTwoL hComplete hSmall hLarge

/-- Add the proved noncoprime branch to the localized hybrid coprime estimate. -/
theorem abs_primeResidueSum_sub_activeMain_le_localizedHybridMeanValueAllowance
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 0 < L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hComplete : RepresentedConductorLiftCompleteUpTo L N u R)
    (hSmall : nonprincipalConductorAnalyticAllowanceUpTo
      N u R input.primitiveMax ≤ smallBound)
    (hMass : largeConductorPrimitiveMeanValueMass
      N u R input.primitiveMax ≤ massBound) :
    |balancedVaughanTypeIPrimeResidueSum L N u -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
        (representedLargeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound) := by
  have hLN : L ≤ N := by omega
  have hCoprime :
      |balancedVaughanTypeIActiveCoprimeProgressionError L N u| ≤
        activeCoprimeSplitAnalyticAllowance N u input.principalMax smallBound
          (representedLargeConductorDirectGlobalFactor N R
            (6 * (1 + Real.log (u : ℝ))) * massBound) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      (norm_activeCoprimeProgressionError_le_localizedHybridMeanValueAllowance
        input hL hu hTwoL hR hComplete hSmall hMass)
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
    _ ≤ activeCoprimeSplitAnalyticAllowance N u input.principalMax smallBound
          (representedLargeConductorDirectGlobalFactor N R
            (6 * (1 + Real.log (u : ℝ))) * massBound) +
          balancedVaughanTypeINoncoprimeExplicitBound N u :=
      add_le_add hCoprime hNoncoprime
    _ = activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
          (representedLargeConductorDirectGlobalFactor N R
            (6 * (1 + Real.log (u : ℝ))) * massBound) := rfl

/--
Complete short Type-I convolution endpoint for the localized signed/direct split.  This replaces
global change-level stability by completeness only for represented conductors at most `R`.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_localizedHybridMeanValueAllowance
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hComplete : RepresentedConductorLiftCompleteUpTo L N u R)
    (hSmall : nonprincipalConductorAnalyticAllowanceUpTo
      N u R input.primitiveMax ≤ smallBound)
    (hMass : largeConductorPrimitiveMeanValueMass
      N u R input.primitiveMax ≤ massBound) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
        (representedLargeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound) := by
  rw [balancedVaughanTypeIPrimeConvolution_eq_residueSum hL]
  exact abs_primeResidueSum_sub_activeMain_le_localizedHybridMeanValueAllowance
    input (by omega) hu hTwoL hR hComplete hSmall hMass

/--
Final localized signed/direct Type-I endpoint. The squarefree conductor-transport theorem removes
the last algebraic completeness premise; only the displayed analytic estimates remain.
-/
theorem abs_typeIPrimeConvolution_sub_activeMain_le_localizedHybridMeanValueAllowance_unconditional
    {L N u R : ℕ} {smallBound massBound : ℝ}
    (input : PrimitivePsiMaxInput L N u)
    (hL : 2 ≤ L) (hu : 0 < u) (hTwoL : 2 * L ≤ N) (hR : 0 < R)
    (hSmall : nonprincipalConductorAnalyticAllowanceUpTo
      N u R input.primitiveMax ≤ smallBound)
    (hMass : largeConductorPrimitiveMeanValueMass
      N u R input.primitiveMax ≤ massBound) :
    |RouteAFiniteWeightBilinearCircle.finiteWeightBilinearConvolution
          (balancedVaughanTypeIWeight L N u) (balancedVonMangoldtWeight L N) N -
        balancedVaughanTypeIActiveDiscreteCoprimeMain L N u| ≤
      activeTypeISplitAnalyticAllowance N u input.principalMax smallBound
        (representedLargeConductorDirectGlobalFactor N R
          (6 * (1 + Real.log (u : ℝ))) * massBound) := by
  exact abs_typeIPrimeConvolution_sub_activeMain_le_localizedHybridMeanValueAllowance
    input hL hu hTwoL hR (representedConductorLiftCompleteUpTo_proved L N u R)
      hSmall hMass

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanLocalizedHybrid
