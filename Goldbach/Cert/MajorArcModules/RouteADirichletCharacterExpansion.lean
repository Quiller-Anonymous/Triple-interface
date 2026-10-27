import Goldbach.Cert.SiegelWalfiszWeighted
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Exact Dirichlet-character expansion for the balanced Route A Type-I error

This module supplies the finite algebraic first half of the signed-conductor regrouping. It expands
the repository's reduced-residue `psi` and deviation `E` through all Dirichlet characters at the
same level. No primitive-character estimate, zero-free region, or asymptotic input is asserted.
-/

namespace Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion

open scoped BigOperators
open Goldbach.Cert.SiegelWalfisz

noncomputable section

/-- The finite von Mangoldt character sum through `x`. -/
noncomputable def dirichletPsi
    (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (x + 1),
    (ΛVM n : ℂ) * χ (n : ZMod q)

/-- Character orthogonality as the exact indicator of one reduced residue class. -/
theorem reducedResidueIndicator_eq_characterAverage
    {q a n : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) :
    (if Nat.ModEq q n a then (1 : ℂ) else 0) =
      (1 / (Nat.totient q : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * χ (n : ZMod q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have haUnit : IsUnit (a : ZMod q) :=
    (ZMod.isUnit_iff_coprime a q).2 ha
  have horth :=
    DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) haUnit (n : ZMod q)
  have htot : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  by_cases hna : Nat.ModEq q n a
  · have heq : (a : ZMod q) = (n : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hna.symm
    rw [horth]
    simp [hna, heq, htot]
  · have hne : (a : ZMod q) ≠ (n : ZMod q) := by
      intro heq
      apply hna
      exact ((ZMod.natCast_eq_natCast_iff a n q).mp heq).symm
    rw [horth]
    simp [hna, hne]

/-- Exact finite character expansion of the repository's reduced-residue `psi`. -/
theorem psi_eq_characterAverage
    {x q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) :
    (psi x q a : ℂ) =
      (1 / (Nat.totient q : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * dirichletPsi x q χ := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    (psi x q a : ℂ) =
        ∑ n ∈ Finset.range (x + 1),
          (ΛVM n : ℂ) * (if Nat.ModEq q n a then (1 : ℂ) else 0) := by
      rw [psi]
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hna : Nat.ModEq q n a <;> simp [hna]
    _ = ∑ n ∈ Finset.range (x + 1),
          (ΛVM n : ℂ) *
            ((1 / (Nat.totient q : ℂ)) *
              ∑ χ : DirichletCharacter ℂ q,
                χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← reducedResidueIndicator_eq_characterAverage hq ha]
    _ = ∑ n ∈ Finset.range (x + 1),
          ∑ χ : DirichletCharacter ℂ q,
            (1 / (Nat.totient q : ℂ)) *
              (χ ((a : ZMod q)⁻¹) * ((ΛVM n : ℂ) * χ (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n hn
      let c : ℂ := 1 / (Nat.totient q : ℂ)
      let w : ℂ := ΛVM n
      let A : DirichletCharacter ℂ q → ℂ :=
        fun χ => χ ((a : ZMod q)⁻¹) * χ (n : ZMod q)
      change w * (c * ∑ χ, A χ) =
        ∑ χ : DirichletCharacter ℂ q,
          c * (χ ((a : ZMod q)⁻¹) * (w * χ (n : ZMod q)))
      calc
        w * (c * ∑ χ, A χ) = c * (w * ∑ χ, A χ) := by ring
        _ = c * ∑ χ, w * A χ := by rw [Finset.mul_sum]
        _ = ∑ χ : DirichletCharacter ℂ q,
            c * (χ ((a : ZMod q)⁻¹) * (w * χ (n : ZMod q))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro χ hχ
          simp only [A]
          ring
    _ = ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.range (x + 1),
            (1 / (Nat.totient q : ℂ)) *
              (χ ((a : ZMod q)⁻¹) * ((ΛVM n : ℂ) * χ (n : ZMod q))) := by
      exact Finset.sum_comm
    _ = (1 / (Nat.totient q : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          χ ((a : ZMod q)⁻¹) * dirichletPsi x q χ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [dirichletPsi, Finset.mul_sum, Finset.mul_sum]

/-- The repository deviation `E` is the character average minus its linear main term. -/
theorem E_eq_characterAverage_sub_main
    {x q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) :
    (Goldbach.Cert.SiegelWalfiszWeighted.E (q := q) (a := a) x : ℂ) =
      (1 / (Nat.totient q : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q,
            χ ((a : ZMod q)⁻¹) * dirichletPsi x q χ
        - (x : ℂ) / (Nat.totient q : ℂ) := by
  rw [Goldbach.Cert.SiegelWalfiszWeighted.E_def]
  push_cast
  rw [psi_eq_characterAverage hq ha]

/-- On integers coprime to the level, a character agrees with its primitive character. -/
theorem apply_eq_primitiveCharacter_of_coprime
    {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hn : Nat.Coprime n q) :
    χ (n : ZMod q) = χ.primitiveCharacter (n : ZMod χ.conductor) := by
  have hnUnit : IsUnit (n : ZMod q) :=
    (ZMod.isUnit_iff_coprime n q).2 hn
  have hdiv : χ.conductor ∣ q := DirichletCharacter.conductor_dvd_level χ
  have hχ :
      χ = DirichletCharacter.changeLevel hdiv χ.primitiveCharacter := by
    exact Classical.choose_spec
      (DirichletCharacter.factorsThrough_conductor χ).choose_spec
  calc
    χ (n : ZMod q) =
        (DirichletCharacter.changeLevel hdiv χ.primitiveCharacter) (n : ZMod q) := by
      exact congrArg (fun ψ : DirichletCharacter ℂ q => ψ (n : ZMod q)) hχ
    _ = (DirichletCharacter.changeLevel hdiv χ.primitiveCharacter) hnUnit.unit := by
      rw [hnUnit.unit_spec]
    _ = χ.primitiveCharacter (ZMod.cast (hnUnit.unit : ZMod q)) :=
      DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter hdiv hnUnit.unit
    _ = χ.primitiveCharacter (n : ZMod χ.conductor) := by
      rw [hnUnit.unit_spec, ZMod.cast_natCast hdiv]

/-- On a reduced residue, the inverse evaluation also descends to the primitive character. -/
theorem apply_inv_eq_primitiveCharacter_inv_of_coprime
    {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hn : Nat.Coprime n q) :
    χ ((n : ZMod q)⁻¹) =
      χ.primitiveCharacter ((n : ZMod χ.conductor)⁻¹) := by
  have hnUnit : IsUnit (n : ZMod q) :=
    (ZMod.isUnit_iff_coprime n q).2 hn
  have hconductor : χ.conductor ∣ q := DirichletCharacter.conductor_dvd_level χ
  have hnPrimitive : Nat.Coprime n χ.conductor :=
    hn.coprime_dvd_right hconductor
  have hnPrimitiveUnit : IsUnit (n : ZMod χ.conductor) :=
    (ZMod.isUnit_iff_coprime n χ.conductor).2 hnPrimitive
  have hvalue := apply_eq_primitiveCharacter_of_coprime χ hn
  have hvalueUnit : IsUnit (χ (n : ZMod q)) := hnUnit.map χ.toMonoidHom
  apply mul_left_cancel₀ hvalueUnit.ne_zero
  calc
    χ (n : ZMod q) * χ ((n : ZMod q)⁻¹) = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ hnUnit, map_one]
    _ = χ.primitiveCharacter (n : ZMod χ.conductor) *
        χ.primitiveCharacter ((n : ZMod χ.conductor)⁻¹) := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ hnPrimitiveUnit, map_one]
    _ = χ (n : ZMod q) *
        χ.primitiveCharacter ((n : ZMod χ.conductor)⁻¹) := by
      rw [hvalue]

/-- A Dirichlet character vanishes on integers not coprime to its level. -/
theorem apply_eq_zero_of_not_coprime
    {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hn : ¬Nat.Coprime n q) :
    χ (n : ZMod q) = 0 := by
  apply MulChar.map_nonunit
  exact (ZMod.isUnit_iff_coprime n q).not.mpr hn

/--
The exact finite correction between an induced character sum and its primitive-character sum.
Only integers noncoprime to the original level occur.
-/
noncomputable def inducedCharacterCorrection
    (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (x + 1),
    if Nat.Coprime n q then 0
    else (ΛVM n : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)

/-- Exact replacement of an imprimitive character sum by its primitive sum and correction. -/
theorem dirichletPsi_eq_primitive_sub_inducedCharacterCorrection
    {x q : ℕ} (χ : DirichletCharacter ℂ q) :
    dirichletPsi x q χ =
      dirichletPsi x χ.conductor χ.primitiveCharacter
        - inducedCharacterCorrection x q χ := by
  unfold dirichletPsi inducedCharacterCorrection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hnMem
  by_cases hn : Nat.Coprime n q
  · rw [apply_eq_primitiveCharacter_of_coprime χ hn, if_pos hn, sub_zero]
  · rw [apply_eq_zero_of_not_coprime χ hn, if_neg hn, sub_self, mul_zero]

/--
Exact per-modulus reduction of `E` to primitive-character sums. The induced-character correction
and the linear main term remain explicit.
-/
theorem E_eq_primitiveCharacterAverage_sub_corrections
    {x q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) :
    (Goldbach.Cert.SiegelWalfiszWeighted.E (q := q) (a := a) x : ℂ) =
      (1 / (Nat.totient q : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q,
            χ ((a : ZMod q)⁻¹) *
              (dirichletPsi x χ.conductor χ.primitiveCharacter
                - inducedCharacterCorrection x q χ)
        - (x : ℂ) / (Nat.totient q : ℂ) := by
  rw [E_eq_characterAverage_sub_main hq ha]
  congr 2
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [dirichletPsi_eq_primitive_sub_inducedCharacterCorrection χ]

/-- The level-`q` characters whose canonical conductor is exactly `r`. -/
noncomputable def charactersOfConductor (q r : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter fun χ => χ.conductor = r

/-- Every finite character sum partitions exactly into its conductor fibers. -/
theorem sum_characters_eq_sum_conductorFibers
    {q : ℕ} (hq : q ≠ 0) (F : DirichletCharacter ℂ q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, F χ) =
      ∑ r ∈ q.divisors, ∑ χ ∈ charactersOfConductor q r, F χ := by
  classical
  unfold charactersOfConductor
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
    (t := q.divisors)
    (g := fun χ : DirichletCharacter ℂ q => χ.conductor)
    (fun χ hχ => Nat.mem_divisors.mpr
      ⟨DirichletCharacter.conductor_dvd_level χ, hq⟩)
    F

/-- One exact conductor fiber in the primitive-character expansion of `E`. -/
noncomputable def primitiveConductorContribution
    (x q a r : ℕ) : ℂ :=
  ∑ χ ∈ charactersOfConductor q r,
    χ ((a : ZMod q)⁻¹) *
      (dirichletPsi x χ.conductor χ.primitiveCharacter
        - inducedCharacterCorrection x q χ)

/-- Exact conductor-fiber regrouping of the repository deviation `E`. -/
theorem E_eq_sum_primitiveConductorContributions_sub_main
    {x q a : ℕ} (hq : 0 < q) (ha : Nat.Coprime a q) :
    (Goldbach.Cert.SiegelWalfiszWeighted.E (q := q) (a := a) x : ℂ) =
      (1 / (Nat.totient q : ℂ)) *
          ∑ r ∈ q.divisors, primitiveConductorContribution x q a r
        - (x : ℂ) / (Nat.totient q : ℂ) := by
  rw [E_eq_primitiveCharacterAverage_sub_corrections hq ha]
  congr 2
  rw [sum_characters_eq_sum_conductorFibers hq.ne']
  apply Finset.sum_congr rfl
  intro r hr
  rfl

end

end Goldbach.Cert.MajorArcModules.RouteADirichletCharacterExpansion
