import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-- Dirichlet characters modulo `q` with complex values. -/
abbrev DirichletCharacter (q : ℕ) := _root_.DirichletCharacter ℂ q

namespace DirichletCharacter

variable {q : ℕ}

/-- Evaluate a Dirichlet character on a natural number by reducing modulo `q`. -/
@[simp] def evalNat (χ : DirichletCharacter q) (n : ℕ) : ℂ := χ (n : ZMod q)

lemma conj_evalNat_eq_inv
    (χ : DirichletCharacter q) (hq : 0 < q) {a : ℕ} (hcop : Nat.Coprime a q) :
    Complex.conj (χ.evalNat a) = χ ((a : ZMod q)⁻¹) := by
  classical
  haveI : NeZero q := ⟨(ne_of_gt hq)⟩
  set aZ : ZMod q := (a : ℕ)
  have ha_unit : IsUnit aZ := (ZMod.isUnit_iff_coprime _ _).2 hcop
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  have hcoeu : (u : ZMod q) = aZ := by
    simpa [aZ] using (ZMod.coe_unitOfCoprime a hcop : ((ZMod.unitOfCoprime a hcop : (ZMod q)ˣ) : ZMod q) = _)
  have hnorm : ‖χ aZ‖ = 1 := by
    simpa [aZ, hcoeu, Complex.norm_eq_abs] using
      (DirichletCharacter.unit_norm_eq_one (χ := χ) u : ‖χ u‖ = 1)
  have hchi_inv : χ (aZ)⁻¹ = (χ aZ)⁻¹ := by
    have hmul := χ.map_mul aZ aZ⁻¹
    have hmul' : χ aZ * χ aZ⁻¹ = 1 := by
      simpa [ZMod.mul_inv_eq_one_of_isUnit ha_unit] using hmul.symm
    simpa using (eq_inv_of_mul_eq_one_right hmul' : χ aZ⁻¹ = (χ aZ)⁻¹)
  have hconj : Complex.conj (χ aZ) = (χ aZ)⁻¹ := by
    simpa using (Complex.inv_eq_conj hnorm).symm
  simpa [evalNat, aZ, hchi_inv] using hconj

end DirichletCharacter

/-- Orthogonality relation for Dirichlet characters: averaging `χ(n)` against the complex
conjugate of `χ(a)` detects the congruence `n ≡ a (mod q)`. -/
theorem orthogonality
    (q : ℕ) (hq : 0 < q) (a n : ℕ) (hcop : Nat.Coprime a q) :
    (1 : ℂ) / (Nat.totient q : ℂ) *
        ∑ χ : DirichletCharacter q,
            Complex.conj (χ.evalNat a) * χ.evalNat n
        = if n % q = a % q then (1 : ℂ) else 0 := by
  classical
  haveI : NeZero q := ⟨(ne_of_gt hq)⟩
  set aZ : ZMod q := (a : ℕ)
  set nZ : ZMod q := (n : ℕ)
  have ha_unit : IsUnit aZ := (ZMod.isUnit_iff_coprime _ _).2 hcop
  have hsum_inv :
      ∑ χ : DirichletCharacter q, χ aZ⁻¹ * χ nZ =
          if aZ = nZ then (Nat.totient q : ℂ) else 0 := by
    simpa [aZ, nZ] using
      DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := q)
        (a := aZ) ha_unit nZ
  have hsum_term :
      ∑ χ : DirichletCharacter q,
          Complex.conj (χ.evalNat a) * χ.evalNat n
        = ∑ χ : DirichletCharacter q, χ aZ⁻¹ * χ nZ := by
    refine Finset.sum_congr rfl ?_
    intro χ _
    simpa [DirichletCharacter.evalNat, aZ, nZ,
      DirichletCharacter.conj_evalNat_eq_inv (χ := χ) hq hcop]
  have hsum_nat :
      ∑ χ : DirichletCharacter q,
          Complex.conj (χ.evalNat a) * χ.evalNat n
        = if n % q = a % q then (Nat.totient q : ℂ) else 0 := by
    refine hsum_term.trans ?_
    by_cases hres : n % q = a % q
    · have hres' :
        aZ = nZ := by
          have :=
            (ZMod.natCast_eq_natCast_iff' n a q).2 hres
          simpa [aZ, nZ, eq_comm] using this.symm
      have hvalue :
          ∑ χ : DirichletCharacter q, χ aZ⁻¹ * χ nZ = (Nat.totient q : ℂ) := by
        simpa [hres'] using hsum_inv
      simpa [hres] using hvalue
    · have hres' :
        aZ ≠ nZ := by
          intro h'
          apply hres
          simpa [aZ, nZ] using (ZMod.natCast_eq_natCast_iff' n a q).1 h'.symm
      have hvalue :
          ∑ χ : DirichletCharacter q, χ aZ⁻¹ * χ nZ = 0 := by
        simpa [hres'] using hsum_inv
      simpa [hres] using hvalue
  have htot_pos : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have htot_ne : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt htot_pos)
  have := congrArg (fun z =>
      (1 : ℂ) / (Nat.totient q : ℂ) * z) hsum_nat
  simpa [mul_ite, htot_ne, hsum_nat, mul_comm, mul_left_comm, mul_assoc] using this

end Twin.SW
