import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
import Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp

/-!
# Reindexing the active primitive-character main by conductor

The exact active character expansion initially uses only primitive keys represented at each prime
index.  Under the explicitly isolated conductor-stability statement for `changeLevel`, those keys
are precisely all primitive characters at the active conductors, and every fiber weight is the
complete signed conductor weight.

This file is finite algebra.  It does not assert conductor stability or any analytic character
estimate.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveReindexing

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveMain
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
open Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor

noncomputable section

/-- All primitive characters at the conductors active at one prime index. -/
noncomputable def activePrimitiveCharactersAt
    (N u p : ℕ) : Finset PrimitiveCharacterKey :=
  (activeCoprimeTypeIModuliAt N u p).sigma fun r => primitiveCharacters r

/-- A represented key's own conductor is itself an active modulus. -/
theorem representedKey_conductor_mem_activeModuli
    {N u p : ℕ} {key : PrimitiveCharacterKey}
    (hKey : key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p) :
    key.1 ∈ activeCoprimeTypeIModuliAt N u p := by
  obtain ⟨occurrence, hOccurrence⟩ :=
    exists_activeOccurrenceForKeyAt_of_mem_represented hKey
  have hd := activeOccurrence_modulus_mem hOccurrence
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  have hdBounds := Finset.mem_Icc.mp hdInner.1
  have hrPos := activeOccurrence_key_conductor_pos hOccurrence
  have hrDvd := activeOccurrence_key_conductor_dvd_modulus hOccurrence
  have hrLeD := Nat.le_of_dvd (activeOccurrence_modulus_pos hOccurrence) hrDvd
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hrPos.ne',
      hrLeD.trans hdBounds.2⟩,
      activeOccurrence_key_conductor_coprime hOccurrence⟩
  · exact hrLeD.trans hdOuter.2

/--
Assuming conductor stability under level change, the moving represented-key set has the simple
description "all primitive characters at all active conductors".
-/
theorem activeRepresentedPrimitiveCharacterKeysAt_eq_activePrimitiveCharactersAt
    {N u p : ℕ} (hStable : PrimitiveCharacterChangeLevelStable) :
    activeRepresentedPrimitiveCharacterKeysAt N u p =
      activePrimitiveCharactersAt N u p := by
  classical
  ext key
  constructor
  · intro hKey
    apply Finset.mem_sigma.mpr
    refine ⟨representedKey_conductor_mem_activeModuli hKey, ?_⟩
    rw [mem_primitiveCharacters_iff]
    obtain ⟨occurrence, hOccurrence⟩ :=
      exists_activeOccurrenceForKeyAt_of_mem_represented hKey
    exact activeOccurrence_key_isPrimitive hOccurrence
  · intro hKey
    rcases key with ⟨r, χ⟩
    have hKeyData := Finset.mem_sigma.mp hKey
    have hrActive : r ∈ activeCoprimeTypeIModuliAt N u p := hKeyData.1
    have hrPos : 0 < r := by
      have hrOuter := Finset.mem_filter.mp hrActive
      have hrInner := Finset.mem_filter.mp hrOuter.1
      exact (Finset.mem_Icc.mp hrInner.1).1
    have hχPrimitive : χ.IsPrimitive :=
      mem_primitiveCharacters_iff.mp hKeyData.2
    apply Finset.mem_image.mpr
    refine ⟨(⟨r, χ⟩ : CharacterOccurrence), ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨hrActive, Finset.mem_univ χ⟩
    · simpa only [DirichletCharacter.changeLevel_self] using
        hStable χ (dvd_refl r) hrPos.ne' hχPrimitive

/-- The active primitive main at one prime index, before conductor reindexing. -/
noncomputable def representedPrimitiveCharacterMainAt
    (N u p : ℕ) : ℂ :=
  ∑ key ∈ activeRepresentedPrimitiveCharacterKeysAt N u p,
    key.2 ((N : ZMod key.1)⁻¹) *
      ((ΛVM p : ℂ) * key.2 (p : ZMod key.1)) *
        (activePrimitiveCharacterFiberWeightAt N u p key : ℂ)

/-- The same pointwise main, indexed directly by primitive characters at active conductors. -/
noncomputable def conductorReindexedPrimitiveCharacterMainAt
    (N u p : ℕ) : ℂ :=
  ∑ key ∈ activePrimitiveCharactersAt N u p,
    key.2 ((N : ZMod key.1)⁻¹) *
      ((ΛVM p : ℂ) * key.2 (p : ZMod key.1)) *
        (balancedVaughanTypeIConductorWeight N u key.1 p : ℂ)

/-- Pointwise replacement of represented fibers by complete signed conductor weights. -/
theorem representedPrimitiveCharacterMainAt_eq_conductorReindexed
    {N u p : ℕ} (hStable : PrimitiveCharacterChangeLevelStable) :
    representedPrimitiveCharacterMainAt N u p =
      conductorReindexedPrimitiveCharacterMainAt N u p := by
  classical
  unfold representedPrimitiveCharacterMainAt
    conductorReindexedPrimitiveCharacterMainAt
  rw [← activeRepresentedPrimitiveCharacterKeysAt_eq_activePrimitiveCharactersAt hStable]
  apply Finset.sum_congr rfl
  intro key hKey
  rw [activePrimitiveCharacterFiberWeightAt_eq_conductorWeight
    (activeConductorLiftCompleteAt_of_changeLevelStable hStable hKey)]

/-- Expanded fixed-conductor form of the pointwise reindexed main. -/
theorem conductorReindexedPrimitiveCharacterMainAt_eq_iterated
    (N u p : ℕ) :
    conductorReindexedPrimitiveCharacterMainAt N u p =
      ∑ r ∈ activeCoprimeTypeIModuliAt N u p,
        ∑ χ ∈ primitiveCharacters r,
          χ ((N : ZMod r)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod r)) *
            (balancedVaughanTypeIConductorWeight N u r p : ℂ) := by
  unfold conductorReindexedPrimitiveCharacterMainAt activePrimitiveCharactersAt
  rw [Finset.sum_sigma]

/-- Once a conductor is larger than the active cutoff, its complete lift weight is exactly zero. -/
theorem conductorWeight_eq_zero_of_center_sub_lt
    {N u r p : ℕ} (hInactive : N - p < r) :
    balancedVaughanTypeIConductorWeight N u r p = 0 := by
  classical
  unfold balancedVaughanTypeIConductorWeight
  apply Finset.sum_eq_zero
  intro d hd
  have hdOuter := Finset.mem_filter.mp hd
  have hdInner := Finset.mem_filter.mp hdOuter.1
  have hdBounds := Finset.mem_Icc.mp hdInner.1
  have hrd : r ∣ d := hdOuter.2.1
  have hdLe : d ≤ N - p := hdOuter.2.2
  have hrLeD : r ≤ d :=
    Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hdBounds.1) hrd
  omega

/-- The fixed conductor range used after the active cutoff has been absorbed into the weight. -/
def primitiveConductorSupport (N u : ℕ) : Finset ℕ :=
  (Finset.Icc 1 u).filter (Nat.Coprime N)

/-- Pointwise reindexed main with a fixed, prime-independent conductor range. -/
noncomputable def fixedConductorPrimitiveCharacterMainAt
    (N u p : ℕ) : ℂ :=
  ∑ r ∈ primitiveConductorSupport N u,
    ∑ χ ∈ primitiveCharacters r,
      χ ((N : ZMod r)⁻¹) * ((ΛVM p : ℂ) * χ (p : ZMod r)) *
        (balancedVaughanTypeIConductorWeight N u r p : ℂ)

/-- Extending the active conductor range to the fixed Type-I range adds only zero terms. -/
theorem conductorReindexedPrimitiveCharacterMainAt_eq_fixed
    (N u p : ℕ) :
    conductorReindexedPrimitiveCharacterMainAt N u p =
      fixedConductorPrimitiveCharacterMainAt N u p := by
  classical
  rw [conductorReindexedPrimitiveCharacterMainAt_eq_iterated]
  unfold fixedConductorPrimitiveCharacterMainAt primitiveConductorSupport
  apply Finset.sum_subset
  · intro r hr
    exact (Finset.mem_filter.mp hr).1
  · intro r hrFixed hrNotActive
    have hrData := Finset.mem_filter.mp hrFixed
    have hInactive : N - p < r := by
      by_contra hnot
      have hrLe : r ≤ N - p := Nat.le_of_not_gt hnot
      exact hrNotActive (Finset.mem_filter.mpr ⟨hrFixed, hrLe⟩)
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [conductorWeight_eq_zero_of_center_sub_lt hInactive]
    simp

/-- Global represented primitive main, factored out as a named intermediate object. -/
noncomputable def representedPrimitiveCharacterTotalMain
    (L N u : ℕ) : ℂ :=
  ∑ p ∈ RouteABalancedBMORPrototype.balancedCandidateSupport L N,
    representedPrimitiveCharacterMainAt N u p

/-- The existing active main is definitionally the sum of the named pointwise represented mains. -/
theorem activePrimitiveCharacterTotalMain_eq_represented
    (L N u : ℕ) :
    activePrimitiveCharacterTotalMain L N u =
      representedPrimitiveCharacterTotalMain L N u := by
  rfl

/-- Conductor stability reindexes the complete active primitive main pointwise. -/
theorem activePrimitiveCharacterTotalMain_eq_fixedConductorPointwise
    {L N u : ℕ} (hStable : PrimitiveCharacterChangeLevelStable) :
    activePrimitiveCharacterTotalMain L N u =
      ∑ p ∈ RouteABalancedBMORPrototype.balancedCandidateSupport L N,
        fixedConductorPrimitiveCharacterMainAt N u p := by
  rw [activePrimitiveCharacterTotalMain_eq_represented]
  unfold representedPrimitiveCharacterTotalMain
  apply Finset.sum_congr rfl
  intro p hp
  rw [representedPrimitiveCharacterMainAt_eq_conductorReindexed hStable,
    conductorReindexedPrimitiveCharacterMainAt_eq_fixed]

/--
Global finite Fubini identity: the exact active primitive main becomes a fixed sum over conductors,
with one complete primitive-character family sum at each conductor.
-/
theorem activePrimitiveCharacterTotalMain_eq_conductorFamilies
    {L N u : ℕ} (hStable : PrimitiveCharacterChangeLevelStable) :
    activePrimitiveCharacterTotalMain L N u =
      ∑ r ∈ primitiveConductorSupport N u,
        primitiveCharacterFamilyConductorSum N u r L (N - L) := by
  rw [activePrimitiveCharacterTotalMain_eq_fixedConductorPointwise hStable]
  unfold fixedConductorPrimitiveCharacterMainAt
    primitiveCharacterFamilyConductorSum primitiveCharacterConductorSum
  have hSupport :
      RouteABalancedBMORPrototype.balancedCandidateSupport L N =
        Finset.Ico L (N - L + 1) := by
    ext p
    simp only [RouteABalancedBMORPrototype.balancedCandidateSupport,
      Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hSupport, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveReindexing
