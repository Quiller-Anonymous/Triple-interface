import Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Squarefree

/-!
# Primitive-character transport through squarefree levels

The signed Type-I conductor sum only uses levels `d` with nonzero Mobius coefficient, hence only
squarefree levels.  This file proves the conductor-preservation theorem needed on exactly that
support.

The key group-theoretic fact is that a character at a squarefree level which factors through two
divisors also factors through their gcd.  The proof constructs compatible units by the generalized
Chinese remainder theorem.  It then follows that changing the level of a primitive character to a
squarefree multiple preserves both its conductor and its canonical primitive-character key.
-/

namespace Goldbach.Cert.MajorArcModules.RouteADirichletCharacterConductorTransport

open Goldbach.Cert.MajorArcModules.RouteABalancedVaughanPrimitiveConductor

noncomputable section

/-- Coprimality is invariant under congruence modulo the second argument. -/
lemma coprime_of_modEq_of_coprime
    {x y n : ℕ} (hxy : x ≡ y [MOD n]) (hy : y.Coprime n) :
    x.Coprime n := by
  apply Nat.coprime_of_dvd
  intro p hp hpx hpn
  have hxyP : x ≡ y [MOD p] := hxy.of_dvd hpn
  have hpY : p ∣ y :=
    Nat.modEq_zero_iff_dvd.mp (hxyP.symm.trans hpx.modEq_zero_nat)
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpY, hpn⟩) hy

/--
At a squarefree level, compatible residues modulo two divisors have a representative which is a
unit at the full level.
-/
lemma exists_coprime_crt_of_squarefree
    {n a b x : ℕ} (hn : Squarefree n) (ha : a ∣ n) (hb : b ∣ n)
    (hx : x.Coprime n) (hcompat : x ≡ 1 [MOD a.gcd b]) :
    ∃ y : ℕ, y.Coprime n ∧ y ≡ 1 [MOD a] ∧ y ≡ x [MOD b] := by
  let l := a.lcm b
  have hlN : l ∣ n := Nat.lcm_dvd ha hb
  have hl0 : l ≠ 0 := by
    intro hl
    exact hn.ne_zero (Nat.eq_zero_of_zero_dvd (hl ▸ hlN))
  let y0 := Nat.chineseRemainder' hcompat.symm
  have hy0a : (y0 : ℕ) ≡ 1 [MOD a] := y0.property.1
  have hy0b : (y0 : ℕ) ≡ x [MOD b] := y0.property.2
  have hy0aCoprime : (y0 : ℕ).Coprime a :=
    coprime_of_modEq_of_coprime hy0a (Nat.coprime_one_left a)
  have hy0bCoprime : (y0 : ℕ).Coprime b :=
    coprime_of_modEq_of_coprime hy0b (hx.coprime_dvd_right hb)
  have hy0lCoprime : (y0 : ℕ).Coprime l := by
    apply Nat.coprime_of_dvd
    intro p hp hpY hpL
    rcases (Nat.Prime.dvd_lcm hp).mp hpL with hpA | hpB
    · exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, hpY, hpA⟩) hy0aCoprime
    · exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, hpY, hpB⟩) hy0bCoprime
  have hSquareProduct : Squarefree (l * (n / l)) := by
    rwa [Nat.mul_div_cancel' hlN]
  have hPartsCoprime : l.Coprime (n / l) :=
    Nat.coprime_of_squarefree_mul hSquareProduct
  let y := Nat.chineseRemainder hPartsCoprime (y0 : ℕ) 1
  have hyl : (y : ℕ) ≡ (y0 : ℕ) [MOD l] := y.property.1
  have hyRest : (y : ℕ) ≡ 1 [MOD n / l] := y.property.2
  have hylCoprime : (y : ℕ).Coprime l :=
    coprime_of_modEq_of_coprime hyl hy0lCoprime
  have hyRestCoprime : (y : ℕ).Coprime (n / l) :=
    coprime_of_modEq_of_coprime hyRest (Nat.coprime_one_left (n / l))
  refine ⟨y, ?_, ?_, ?_⟩
  · apply Nat.coprime_of_dvd
    intro p hp hpY hpN
    have hpProduct : p ∣ l * (n / l) := by
      rwa [Nat.mul_div_cancel' hlN]
    rcases hp.dvd_mul.mp hpProduct with hpL | hpRest
    · exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, hpY, hpL⟩) hylCoprime
    · exact (Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p, hp, hpY, hpRest⟩) hyRestCoprime
  · exact (hyl.of_dvd (Nat.dvd_lcm_left a b)).trans hy0a
  · exact (hyl.of_dvd (Nat.dvd_lcm_right a b)).trans hy0b

/-- A congruence to one produces kernel membership for the corresponding unit reduction. -/
lemma unitsMap_unitOfCoprime_eq_one
    {n m y : ℕ} [NeZero n] (hm : m ∣ n) (hy : y.Coprime n)
    (hyOne : y ≡ 1 [MOD m]) :
    ZMod.unitsMap hm (ZMod.unitOfCoprime y hy) = 1 := by
  have hm0 : m ≠ 0 := by
    intro hmZero
    exact NeZero.ne n (Nat.eq_zero_of_zero_dvd (hmZero ▸ hm))
  letI : NeZero m := ⟨hm0⟩
  apply Units.ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  rw [ZMod.cast_natCast hm]
  simpa only [Nat.cast_one] using
    (ZMod.natCast_eq_natCast_iff y 1 m).mpr hyOne

/-- Kernel membership for a unit reduction gives the corresponding congruence to one. -/
lemma val_modEq_one_of_unitsMap_eq_one
    {n m : ℕ} [NeZero n] (hm : m ∣ n) {u : (ZMod n)ˣ}
    (hu : ZMod.unitsMap hm u = 1) :
    (u : ZMod n).val ≡ 1 [MOD m] := by
  have hm0 : m ≠ 0 := by
    intro hmZero
    exact NeZero.ne n (Nat.eq_zero_of_zero_dvd (hmZero ▸ hm))
  letI : NeZero m := ⟨hm0⟩
  have hval := congrArg Units.val hu
  change (↑(ZMod.unitsMap hm u) : ZMod m) = 1 at hval
  rw [ZMod.unitsMap_val] at hval
  rw [← ZMod.natCast_zmod_val (u : ZMod n)] at hval
  rw [ZMod.cast_natCast hm] at hval
  exact (ZMod.natCast_eq_natCast_iff _ 1 m).mp
    (by simpa only [Nat.cast_one] using hval)

/-- A chosen CRT unit has the prescribed reduction of an existing unit. -/
lemma unitsMap_unitOfCoprime_eq
    {n m y : ℕ} [NeZero n] (hm : m ∣ n) (hy : y.Coprime n)
    (u : (ZMod n)ˣ) (hyu : y ≡ (u : ZMod n).val [MOD m]) :
    ZMod.unitsMap hm (ZMod.unitOfCoprime y hy) = ZMod.unitsMap hm u := by
  have hm0 : m ≠ 0 := by
    intro hmZero
    exact NeZero.ne n (Nat.eq_zero_of_zero_dvd (hmZero ▸ hm))
  letI : NeZero m := ⟨hm0⟩
  apply Units.ext
  rw [ZMod.unitsMap_val, ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  rw [ZMod.cast_natCast hm]
  rw [← ZMod.natCast_zmod_val (u : ZMod n), ZMod.cast_natCast hm]
  exact (ZMod.natCast_eq_natCast_iff _ _ m).mpr hyu

/-- Factor-through levels are closed under gcd when the ambient level is squarefree. -/
theorem factorsThrough_gcd_of_squarefree_level
    {R : Type*} [CommMonoidWithZero R]
    {n a b : ℕ} {χ : DirichletCharacter R n}
    (hn : Squarefree n) (ha : a ∣ n) (hb : b ∣ n)
    (hA : χ.FactorsThrough a) (hB : χ.FactorsThrough b) :
    χ.FactorsThrough (a.gcd b) := by
  letI : NeZero n := ⟨hn.ne_zero⟩
  have hG : a.gcd b ∣ n := (Nat.gcd_dvd_left a b).trans ha
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hG]
  have hAKer :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap ha).mp hA
  have hBKer :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap hb).mp hB
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  have hCompat : (x : ZMod n).val ≡ 1 [MOD a.gcd b] :=
    val_modEq_one_of_unitsMap_eq_one hG hx
  obtain ⟨y, hyCoprime, hyA, hyB⟩ :=
    exists_coprime_crt_of_squarefree hn ha hb
      (ZMod.val_coe_unit_coprime x) hCompat
  let uy : (ZMod n)ˣ := ZMod.unitOfCoprime y hyCoprime
  have hMapA : ZMod.unitsMap ha uy = 1 :=
    unitsMap_unitOfCoprime_eq_one ha hyCoprime hyA
  have hMapB : ZMod.unitsMap hb uy = ZMod.unitsMap hb x :=
    unitsMap_unitOfCoprime_eq hb hyCoprime x hyB
  let z : (ZMod n)ˣ := x * uy⁻¹
  have hMapBZ : ZMod.unitsMap hb z = 1 := by
    simp [z, hMapB]
  have hChiY : χ.toUnitHom uy = 1 := hAKer hMapA
  have hChiZ : χ.toUnitHom z = 1 := hBKer hMapBZ
  have hDecomp : uy * z = x := by
    simp [z, mul_left_comm]
  calc
    χ.toUnitHom x = χ.toUnitHom (uy * z) := congrArg χ.toUnitHom hDecomp.symm
    _ = χ.toUnitHom uy * χ.toUnitHom z := map_mul _ _ _
    _ = 1 := by rw [hChiY, hChiZ, mul_one]

/-- A primitive character keeps its conductor after lifting to a squarefree multiple. -/
theorem conductor_changeLevel_eq_of_squarefree
    {R : Type*} [CommMonoidWithZero R]
    {r d : ℕ} (χ : DirichletCharacter R r) (hrd : r ∣ d)
    (hdSquarefree : Squarefree d) (hPrimitive : χ.IsPrimitive) :
    DirichletCharacter.conductor (DirichletCharacter.changeLevel hrd χ) = r := by
  letI : NeZero d := ⟨hdSquarefree.ne_zero⟩
  let ψ : DirichletCharacter R d := DirichletCharacter.changeLevel hrd χ
  let c := DirichletCharacter.conductor ψ
  have hcDvd : c ∣ d := DirichletCharacter.conductor_dvd_level ψ
  have hThroughC : ψ.FactorsThrough c :=
    DirichletCharacter.factorsThrough_conductor ψ
  have hThroughR : ψ.FactorsThrough r :=
    DirichletCharacter.changeLevel_factorsThrough χ hrd
  have hThroughGcd : ψ.FactorsThrough (c.gcd r) :=
    factorsThrough_gcd_of_squarefree_level hdSquarefree hcDvd hrd
      hThroughC hThroughR
  rcases hThroughGcd with ⟨hgD, θ, hψθ⟩
  have hgR : c.gcd r ∣ r := Nat.gcd_dvd_right c r
  have hAtD :
      DirichletCharacter.changeLevel hrd χ =
        DirichletCharacter.changeLevel hrd
          (DirichletCharacter.changeLevel hgR θ) := by
    rw [← DirichletCharacter.changeLevel_trans θ hgR hrd]
    exact hψθ
  have hχθ : χ = DirichletCharacter.changeLevel hgR θ :=
    DirichletCharacter.changeLevel_injective hrd hAtD
  have hχThroughGcd : χ.FactorsThrough (c.gcd r) :=
    ⟨hgR, θ, hχθ⟩
  have hConductorLeGcd : DirichletCharacter.conductor χ ≤ c.gcd r :=
    Nat.sInf_le hχThroughGcd
  have hPrimitiveEq : DirichletCharacter.conductor χ = r := hPrimitive
  have hrLeGcd : r ≤ c.gcd r := by
    simpa only [hPrimitiveEq] using hConductorLeGcd
  have hrPos : 0 < r :=
    Nat.pos_of_ne_zero (fun hrZero =>
      hdSquarefree.ne_zero (Nat.eq_zero_of_zero_dvd (hrZero ▸ hrd)))
  have hGcdEq : c.gcd r = r :=
    Nat.le_antisymm (Nat.le_of_dvd hrPos (Nat.gcd_dvd_right c r)) hrLeGcd
  have hrDvdC : r ∣ c := Nat.gcd_eq_right_iff_dvd.mp hGcdEq
  have hcLeR : c ≤ r := Nat.sInf_le hThroughR
  have hcPos : 0 < c :=
    Nat.pos_of_ne_zero (DirichletCharacter.conductor_ne_zero ψ hdSquarefree.ne_zero)
  exact Nat.le_antisymm hcLeR (Nat.le_of_dvd hcPos hrDvdC)

/-- Transporting the canonical primitive character across its conductor equality. -/
lemma changeLevel_cast_primitiveCharacter_eq
    {d r : ℕ} (ψ : DirichletCharacter ℂ d)
    (hConductor : DirichletCharacter.conductor ψ = r) :
    ∀ hrd : r ∣ d,
      DirichletCharacter.changeLevel hrd
          (cast (congrArg (DirichletCharacter ℂ) hConductor) ψ.primitiveCharacter) = ψ := by
  cases hConductor
  intro hrd
  exact (DirichletCharacter.factorsThrough_conductor ψ).eq_changeLevel.symm

/-- The canonical primitive-character key is preserved by a squarefree level lift. -/
theorem primitiveCharacterKey_changeLevel_eq_of_squarefree
    {r d : ℕ} (χ : DirichletCharacter ℂ r) (hrd : r ∣ d)
    (hdSquarefree : Squarefree d) (hPrimitive : χ.IsPrimitive) :
    primitiveCharacterKey
        (⟨d, DirichletCharacter.changeLevel hrd χ⟩ : CharacterOccurrence) =
      (⟨r, χ⟩ : PrimitiveCharacterKey) := by
  letI : NeZero d := ⟨hdSquarefree.ne_zero⟩
  unfold primitiveCharacterKey
  have hConductor :
      DirichletCharacter.conductor (DirichletCharacter.changeLevel hrd χ) = r :=
    conductor_changeLevel_eq_of_squarefree χ hrd hdSquarefree hPrimitive
  apply Sigma.ext hConductor
  let hType := congrArg (DirichletCharacter ℂ) hConductor
  have hCast :
      cast hType
          (DirichletCharacter.changeLevel hrd χ).primitiveCharacter = χ := by
    apply DirichletCharacter.changeLevel_injective hrd
    rw [changeLevel_cast_primitiveCharacter_eq
      (DirichletCharacter.changeLevel hrd χ) hConductor hrd]
  exact (cast_heq hType _).symm.trans (heq_of_eq hCast)

end

end Goldbach.Cert.MajorArcModules.RouteADirichletCharacterConductorTransport
