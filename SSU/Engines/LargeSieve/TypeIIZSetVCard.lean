import SSU.Engines.LargeSieve.TypeIISumDecomposeV
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval

/-!
Cardinality bounds for the Type–II Step 4 progression parameter `z`.

This is deterministic geometry: for fixed `v` (i.e. fixed `d`), the `z` values occur in the
representation

`u = u₀(v) + z*q`,

and the tube constraint `|u| ≤ U` forces `z` to lie in an interval of length `≍ U/q`.

We keep both:
* an exact floor/ceil interval containment, and
* a simplified `O(U/q + 1)` cardinality bound.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open MeasureTheory

private theorem mem_zSetV_imp_U_bounds (td : TubeData) {v z : ℤ} (hz : z ∈ zSetV td v) :
    |((uResidue td v + z * td.q : ℤ) : ℝ)| ≤ td.U := by
  classical
  -- Unpack `z ∈ zSetV td v`.
  rcases Finset.mem_image.mp hz with ⟨p, hpV, rfl⟩
  have hpT : p ∈ td.T := (Finset.mem_filter.mp hpV).1
  have hv : shearV p = v := (Finset.mem_filter.mp hpV).2
  -- Use the progression identity `u = uResidue + z*q`.
  have hu :
      shearU td.a td.q p = uResidue td v + zCoordV td v p * td.q :=
    shearU_eq_uResidue_add_z_mul_q (td := td) (v := v) (p := p) hv
  -- Pull `|u| ≤ U` from tube membership.
  have hub : |(shearU td.a td.q p : ℝ)| ≤ td.U := (td.mem_T p hpT).2.2
  -- Rewrite `shearU` as the progression value.
  simpa [hu, Int.cast_add, Int.cast_mul, add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm] using hub

/-- Any `z` occurring in the Step 4 decomposition lies in an explicit floor/ceil interval. -/
theorem mem_zSetV_imp_mem_Icc_floor_ceil (td : TubeData) {v z : ℤ} (hz : z ∈ zSetV td v) :
    z ∈
      (Finset.Icc
        (⌊((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌋ : ℤ)
        (⌈((td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌉ : ℤ)) := by
  classical
  have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hq0 : (td.q : ℝ) ≠ 0 := ne_of_gt hq
  set u0R : ℝ := (uResidue td v : ℝ)
  set qR : ℝ := (td.q : ℝ)

  have hub : |(u0R + (z : ℝ) * qR)| ≤ td.U := by
    -- Convert the bound from `mem_zSetV_imp_U_bounds`.
    have := mem_zSetV_imp_U_bounds (td := td) (v := v) (z := z) hz
    simpa [u0R, qR, Int.cast_add, Int.cast_mul, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm] using this
  have hub' : -td.U ≤ u0R + (z : ℝ) * qR ∧ u0R + (z : ℝ) * qR ≤ td.U := by
    simpa [abs_le] using hub

  have hlow : ((-td.U - u0R) / qR) ≤ (z : ℝ) := by
    have : (-td.U - u0R) ≤ (z : ℝ) * qR := by
      linarith [hub'.1]
    have : (-td.U - u0R) / qR ≤ ((z : ℝ) * qR) / qR :=
      div_le_div_of_nonneg_right this (le_of_lt hq)
    simpa [div_eq_mul_inv, qR, hq0, mul_assoc] using this

  have hhigh : (z : ℝ) ≤ ((td.U - u0R) / qR) := by
    have : (z : ℝ) * qR ≤ (td.U - u0R) := by
      linarith [hub'.2]
    have : ((z : ℝ) * qR) / qR ≤ (td.U - u0R) / qR :=
      div_le_div_of_nonneg_right this (le_of_lt hq)
    simpa [div_eq_mul_inv, qR, hq0, mul_assoc] using this

  -- Turn `hlow`/`hhigh` into integer bounds using `floor ≤` and `≤ ceil`.
  have hleft :
      (⌊((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌋ : ℤ) ≤ z := by
    have : (⌊((-td.U - u0R) / qR)⌋ : ℤ) ≤ z := by
      have hfloor : (⌊((-td.U - u0R) / qR)⌋ : ℝ) ≤ ((-td.U - u0R) / qR) :=
        Int.floor_le _
      have : (⌊((-td.U - u0R) / qR)⌋ : ℝ) ≤ (z : ℝ) := le_trans hfloor hlow
      exact_mod_cast this
    simpa [u0R, qR] using this

  have hright :
      z ≤ (⌈((td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌉ : ℤ) := by
    have : z ≤ (⌈((td.U - u0R) / qR)⌉ : ℤ) := by
      have hceil : ((td.U - u0R) / qR) ≤ (⌈((td.U - u0R) / qR)⌉ : ℝ) :=
        Int.le_ceil _
      have : (z : ℝ) ≤ (⌈((td.U - u0R) / qR)⌉ : ℝ) := le_trans hhigh hceil
      exact_mod_cast this
    simpa [u0R, qR] using this

  simpa [Finset.mem_Icc] using And.intro hleft hright

/-- A deterministic cardinality bound for `zSetV td v` in terms of a floor/ceil interval. -/
theorem card_zSetV_le_Icc_floor_ceil (td : TubeData) (v : ℤ) :
    (zSetV td v).card
      ≤
    (Finset.Icc
        (⌊((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌋ : ℤ)
        (⌈((td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌉ : ℤ)).card := by
  classical
  refine Finset.card_le_card ?_
  intro z hz
  exact mem_zSetV_imp_mem_Icc_floor_ceil (td := td) (v := v) (z := z) hz

/-!
### A usable `O(U/q + 1)` bound
-/

theorem card_zSetV_le_two_mul_U_div_q_add_three (td : TubeData) (v : ℤ) (hU : 0 ≤ td.U) :
    ((zSetV td v).card : ℝ) ≤ (2 * td.U) / (td.q : ℝ) + 3 := by
  classical
  have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hq0 : (td.q : ℝ) ≠ 0 := ne_of_gt hq
  let A : ℤ := (⌊((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌋ : ℤ)
  let B : ℤ := (⌈((td.U - (uResidue td v : ℤ)) / (td.q : ℝ))⌉ : ℤ)
  let I : Finset ℤ := Finset.Icc A B

  have hcard_le : ((zSetV td v).card : ℝ) ≤ (I.card : ℝ) := by
    have hnat : (zSetV td v).card ≤ I.card := by
      simpa [I, A, B] using card_zSetV_le_Icc_floor_ceil (td := td) (v := v)
    exact_mod_cast hnat

  -- If `A ≤ B`, then `card(Icc A B) = (B+1-A).toNat`, hence `≤ (B - A) + 1`.
  have hAB : A ≤ B := by
    -- same argument as in the `D/q` case: `A ≤ (-U-u0)/q ≤ (U-u0)/q ≤ B` in `ℝ`.
    set r : ℝ := (-td.U - (uResidue td v : ℤ)) / (td.q : ℝ)
    set s : ℝ := (td.U - (uResidue td v : ℤ)) / (td.q : ℝ)
    have hrs : r ≤ s := by
      have : (-td.U - (uResidue td v : ℤ)) ≤ (td.U - (uResidue td v : ℤ)) := by linarith
      exact div_le_div_of_nonneg_right this (le_of_lt hq)
    have : (A : ℝ) ≤ (B : ℝ) := by
      have hA : (A : ℝ) ≤ r := by simpa [A, r] using (Int.floor_le r)
      have hB : s ≤ (B : ℝ) := by simpa [B, s] using (Int.le_ceil s)
      exact le_trans (le_trans hA hrs) hB
    exact_mod_cast this

  have hcardZ : ((I.card : ℤ)) = B + 1 - A := by
    simpa [I] using (Int.card_Icc_of_le (a := A) (b := B) (by omega : A ≤ B + 1))

  have hcardR : (I.card : ℝ) = (B + 1 - A : ℝ) := by
    exact_mod_cast hcardZ

  have hBA :
      (B - A : ℝ) ≤ (2 * td.U) / (td.q : ℝ) + 2 := by
    set r : ℝ := (-td.U - (uResidue td v : ℤ)) / (td.q : ℝ)
    set s : ℝ := (td.U - (uResidue td v : ℤ)) / (td.q : ℝ)
    have hB : (B : ℝ) ≤ s + 1 := by
      have : (⌈s⌉ : ℝ) < s + 1 := Int.ceil_lt_add_one s
      simpa [B, s] using this.le
    have hA : r - 1 ≤ (A : ℝ) := by
      have : r - 1 < (⌊r⌋ : ℝ) := Int.sub_one_lt_floor r
      simpa [A, r] using this.le
    have : (B - A : ℝ) ≤ (s + 1) - (r - 1) := by
      have hA' : -(A : ℝ) ≤ -(r - 1) := neg_le_neg hA
      have hB' : (B : ℝ) + (-(A : ℝ)) ≤ (s + 1) + (-(r - 1)) := add_le_add hB hA'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hB'
    have hs_r : s - r = (2 * td.U) / (td.q : ℝ) := by
      have hnum :
          (td.U - (uResidue td v : ℤ)) - (-td.U - (uResidue td v : ℤ)) = 2 * td.U := by
        ring
      calc
        s - r
            = ((td.U - (uResidue td v : ℤ)) / (td.q : ℝ)) -
                ((-td.U - (uResidue td v : ℤ)) / (td.q : ℝ)) := by rfl
        _ = (((td.U - (uResidue td v : ℤ)) - (-td.U - (uResidue td v : ℤ))) / (td.q : ℝ)) := by
              simpa using (div_sub_div_same (td.U - (uResidue td v : ℤ)) (-td.U - (uResidue td v : ℤ)) (td.q : ℝ))
        _ = (2 * td.U) / (td.q : ℝ) := by simpa [hnum]
    nlinarith [this, hs_r]

  have hIcard :
      (I.card : ℝ) ≤ (2 * td.U) / (td.q : ℝ) + 3 := by
    -- `card(Icc) = (B+1-A) = (B-A)+1`.
    have : (B + 1 - A : ℝ) = (B - A : ℝ) + 1 := by ring
    calc
      (I.card : ℝ) = (B + 1 - A : ℝ) := hcardR
      _ = (B - A : ℝ) + 1 := this
      _ ≤ ((2 * td.U) / (td.q : ℝ) + 2) + 1 := by gcongr
      _ = (2 * td.U) / (td.q : ℝ) + 3 := by ring

  exact le_trans hcard_le hIcard

end
end LargeSieve
end TypeII
end Engines
end SSU

