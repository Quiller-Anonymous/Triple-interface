import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveReindexing

/-!
# Principal cancellation and analytic closure surface for balanced Vaughan Type I

The conductor-one primitive family is not estimated as an ordinary character family: its linear
main term is already subtracted in the exact active character expansion.  This module performs
that cancellation exactly, leaving the centered principal `psi` error and the conductors `r > 1`
as separate analytic objects.
-/

namespace Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz
open Goldbach.Cert.MajorArcModules.RouteABalancedBMORPrototype
open Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanSignedConductor
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanActiveCharacterExpansion
open Goldbach.Cert.MajorArcModules.RouteAInducedCharacterCorrectionSharp
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanConductorVariation
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveMeanValue
open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveReindexing

noncomputable section

/-- At level one, the unique character is primitive. -/
theorem primitiveCharacters_one :
    primitiveCharacters 1 = {(1 : DirichletCharacter ℂ 1)} := by
  classical
  ext χ
  constructor
  · intro hχ
    rw [Finset.mem_singleton]
    exact Subsingleton.elim _ _
  · intro hχ
    rw [Finset.mem_singleton] at hχ
    subst χ
    rw [mem_primitiveCharacters_iff]
    exact DirichletCharacter.isPrimitive_one_level_one

/-- The conductor-one family is the ordinary von Mangoldt sum against the conductor-one weight. -/
theorem primitiveCharacterFamilyConductorSum_one
    (N u a b : ℕ) :
    primitiveCharacterFamilyConductorSum N u 1 a b =
      ∑ p ∈ Finset.Ico a (b + 1),
        (ΛVM p : ℂ) * (balancedVaughanTypeIConductorWeight N u 1 p : ℂ) := by
  classical
  unfold primitiveCharacterFamilyConductorSum
  rw [primitiveCharacters_one]
  simp only [Finset.sum_singleton]
  unfold primitiveCharacterConductorSum
  apply Finset.sum_congr rfl
  intro p hp
  have hNmod : ((N : ZMod 1)⁻¹) = 1 := Subsingleton.elim _ _
  have hpmod : (p : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [hNmod, hpmod]
  norm_num

/-- The global linear subtraction is the conductor-one weight summed over the balanced support. -/
theorem activeCharacterLinearTotal_eq_conductorWeight_one
    (L N u : ℕ) :
    activeCharacterLinearTotal L N u =
      ∑ p ∈ balancedCandidateSupport L N,
        (balancedVaughanTypeIConductorWeight N u 1 p : ℂ) := by
  unfold activeCharacterLinearTotal
  apply Finset.sum_congr rfl
  intro p hp
  rw [activeCharacterLinearMainAt_eq_conductorWeight_one]

/-- Centered principal cumulative sum `psi(t) - t`. -/
noncomputable def principalPsiError (t : ℕ) : ℂ :=
  dirichletPsi t 1 (1 : DirichletCharacter ℂ 1) - (t : ℂ)

/-- Its positive-index increment is exactly `Lambda(p) - 1`. -/
theorem principalPsiError_sub_pred {p : ℕ} (hp : 0 < p) :
    principalPsiError p - principalPsiError (p - 1) =
      (ΛVM p : ℂ) - 1 := by
  have hpmod : (p : ZMod 1) = 1 := Subsingleton.elim _ _
  have hPsiStep :
      dirichletPsi p 1 (1 : DirichletCharacter ℂ 1) -
          dirichletPsi (p - 1) 1 (1 : DirichletCharacter ℂ 1) =
        (ΛVM p : ℂ) := by
    rw [dirichletPsi_sub_pred (1 : DirichletCharacter ℂ 1) hp,
      hpmod, map_one, mul_one]
  have hCastStep :
      (p : ℂ) - ((p - 1 : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  unfold principalPsiError
  calc
    (dirichletPsi p 1 (1 : DirichletCharacter ℂ 1) - (p : ℂ)) -
        (dirichletPsi (p - 1) 1 (1 : DirichletCharacter ℂ 1) -
          ((p - 1 : ℕ) : ℂ)) =
        (dirichletPsi p 1 (1 : DirichletCharacter ℂ 1) -
          dirichletPsi (p - 1) 1 (1 : DirichletCharacter ℂ 1)) -
          ((p : ℂ) - ((p - 1 : ℕ) : ℂ)) := by ring
    _ = (ΛVM p : ℂ) - 1 := by rw [hPsiStep, hCastStep]

/-- The conductor-one family after cancellation of its exact linear comparison. -/
noncomputable def principalCenteredConductorSum
    (N u a b : ℕ) : ℂ :=
  ∑ p ∈ Finset.Ico a (b + 1),
    ((ΛVM p : ℂ) - 1) *
      (balancedVaughanTypeIConductorWeight N u 1 p : ℂ)

/-- The centered principal sum is a finite Stieltjes sum of `psi(t) - t`. -/
theorem principalCenteredConductorSum_eq_discreteStieltjesSum
    {N u a b : ℕ} (ha : 0 < a) :
    principalCenteredConductorSum N u a b =
      discreteStieltjesSum principalPsiError
        (fun t => (balancedVaughanTypeIConductorWeight N u 1 t : ℂ)) a b := by
  unfold principalCenteredConductorSum discreteStieltjesSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [principalPsiError_sub_pred (by
    have hpData := Finset.mem_Ico.mp hp
    omega)]

/-- Exact cancellation of the conductor-one family against the active linear total. -/
theorem conductorOneFamily_sub_linear_eq_centered
    {L N u : ℕ} :
    primitiveCharacterFamilyConductorSum N u 1 L (N - L) -
        activeCharacterLinearTotal L N u =
      principalCenteredConductorSum N u L (N - L) := by
  rw [primitiveCharacterFamilyConductorSum_one,
    activeCharacterLinearTotal_eq_conductorWeight_one]
  unfold principalCenteredConductorSum
  have hSupport :
      balancedCandidateSupport L N = Finset.Ico L (N - L + 1) := by
    ext p
    simp only [balancedCandidateSupport, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hSupport, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- A maximal PNT error bound controls the centered conductor-one weighted sum. -/
theorem norm_principalCenteredConductorSum_le
    {N u a b : ℕ} (M : ℝ)
    (hN : 0 < N) (ha : 0 < a) (hab : a ≤ b) (hbN : b < N)
    (hM : 0 ≤ M)
    (hPsi : ∀ t ∈ Finset.Icc (a - 1) b, ‖principalPsiError t‖ ≤ M) :
    ‖principalCenteredConductorSum N u a b‖ ≤
      M * (2 * (6 * (N : ℝ) / (Nat.totient N : ℝ)) * Real.log (N : ℝ)) := by
  rw [principalCenteredConductorSum_eq_discreteStieltjesSum ha]
  calc
    ‖discreteStieltjesSum principalPsiError
        (fun t => (balancedVaughanTypeIConductorWeight N u 1 t : ℂ)) a b‖ ≤
        M * (|balancedVaughanTypeIConductorWeight N u 1 a| +
          |balancedVaughanTypeIConductorWeight N u 1 b| +
          balancedVaughanTypeIConductorVariation N u 1 a b) := by
      simpa [Complex.norm_real, Real.norm_eq_abs,
        sum_norm_conductorWeight_diff_eq_variation] using
        (norm_discreteStieltjesSum_le principalPsiError
          (fun t => (balancedVaughanTypeIConductorWeight N u 1 t : ℂ))
          hab M hPsi)
    _ ≤ M * (2 * (6 * (N : ℝ) / (Nat.totient N : ℝ)) *
          Real.log (N : ℝ)) := by
      have hVariation :=
        conductorWeight_endpoints_add_variation_le_two_mul_log
          (N := N) (u := u) (r := 1) (a := a) (b := b)
          hN Nat.zero_lt_one (Nat.coprime_one_right N) hab hbN
      simpa using mul_le_mul_of_nonneg_left hVariation hM

/-- Conductors other than the principal conductor in the fixed Type-I support. -/
def nonprincipalPrimitiveConductorSupport (N u : ℕ) : Finset ℕ :=
  (primitiveConductorSupport N u).erase 1

/-- A positive Type-I cutoff always contains the principal conductor. -/
theorem one_mem_primitiveConductorSupport
    {N u : ℕ} (hu : 0 < u) :
    1 ∈ primitiveConductorSupport N u := by
  rw [primitiveConductorSupport, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, by omega⟩, Nat.coprime_one_right N⟩

@[simp]
theorem mem_nonprincipalPrimitiveConductorSupport_iff
    {N u r : ℕ} :
    r ∈ nonprincipalPrimitiveConductorSupport N u ↔
      r ∈ primitiveConductorSupport N u ∧ r ≠ 1 := by
  rw [nonprincipalPrimitiveConductorSupport, Finset.mem_erase]
  constructor
  · exact fun h => ⟨h.2, h.1⟩
  · exact fun h => ⟨h.2, h.1⟩

/--
The exact primitive main, after its linear comparison is removed, is the centered principal
family plus the genuinely nonprincipal conductor families.
-/
theorem activePrimitiveCharacterTotalMain_sub_linear_eq_principal_add_nonprincipal
    {L N u : ℕ} (hu : 0 < u)
    (hStable : PrimitiveCharacterChangeLevelStable) :
    activePrimitiveCharacterTotalMain L N u - activeCharacterLinearTotal L N u =
      principalCenteredConductorSum N u L (N - L) +
        ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
          primitiveCharacterFamilyConductorSum N u r L (N - L) := by
  rw [activePrimitiveCharacterTotalMain_eq_conductorFamilies hStable]
  have hOne : 1 ∈ primitiveConductorSupport N u :=
    one_mem_primitiveConductorSupport hu
  calc
    (∑ r ∈ primitiveConductorSupport N u,
        primitiveCharacterFamilyConductorSum N u r L (N - L)) -
          activeCharacterLinearTotal L N u =
        (primitiveCharacterFamilyConductorSum N u 1 L (N - L) -
          activeCharacterLinearTotal L N u) +
          ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
            primitiveCharacterFamilyConductorSum N u r L (N - L) := by
      rw [nonprincipalPrimitiveConductorSupport,
        ← Finset.add_sum_erase (primitiveConductorSupport N u)
          (fun r => primitiveCharacterFamilyConductorSum N u r L (N - L)) hOne]
      ring
    _ = principalCenteredConductorSum N u L (N - L) +
          ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
            primitiveCharacterFamilyConductorSum N u r L (N - L) := by
      rw [conductorOneFamily_sub_linear_eq_centered]

/--
Exact analytic closure surface for the active coprime Type-I error.  The remaining terms are the
centered principal `psi` error, the nonprincipal primitive-character families, and the explicit
induced-character correction.
-/
theorem activeCoprimeProgressionError_cast_eq_principal_add_nonprincipal_sub_induced
    {L N u : ℕ} (hL : 0 < L) (hu : 0 < u)
    (hStable : PrimitiveCharacterChangeLevelStable) :
    (RouteABalancedVaughanActiveMain.balancedVaughanTypeIActiveCoprimeProgressionError
        L N u : ℂ) =
      principalCenteredConductorSum N u L (N - L) +
        ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
          primitiveCharacterFamilyConductorSum N u r L (N - L) -
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
          ∑ r ∈ nonprincipalPrimitiveConductorSupport N u,
            primitiveCharacterFamilyConductorSum N u r L (N - L) -
          activePrimitiveCharacterTotalInducedCorrection L N u := by
      rw [activePrimitiveCharacterTotalMain_sub_linear_eq_principal_add_nonprincipal
        hu hStable]

end

end Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveClosure
