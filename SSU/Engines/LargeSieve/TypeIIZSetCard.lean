import SSU.Engines.LargeSieve.TypeIISumDecompose
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval

/-!
Cardinality bounds for the Type–II Step 3 progression parameter `z`.

This is deterministic geometry: for fixed `u`, the `z` values occur in the representation

`v = v₀(u) + z*q`,

and the tube box constraint `D < v ≤ 2D` forces `z` to lie in an interval of length `≍ D/q`.

We keep the bound in a floor/ceil form. Downstream analytic steps can simplify it (e.g. to
`O(1 + D/q)`) under whatever parameter regime the application assumes.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open MeasureTheory

private theorem mem_zSet_imp_D_bounds (td : TubeData) {u z : ℤ} (hz : z ∈ zSet td u) :
    td.D < ((vResidue td u + z * td.q : ℤ) : ℝ) ∧
      (((vResidue td u + z * td.q : ℤ) : ℝ) ≤ 2 * td.D) := by
  classical
  -- Unpack `z ∈ zSet td u`.
  rcases Finset.mem_image.mp hz with ⟨p, hpU, rfl⟩
  have hpT : p ∈ td.T := (Finset.mem_filter.mp hpU).1
  have hu : shearU td.a td.q p = u := (Finset.mem_filter.mp hpU).2
  -- Convert `shearV p` into the progression form `v₀(u) + z*q`.
  have hv :
      (shearV p : ℤ) = vResidue td u + zCoord td u p * td.q :=
    shearV_eq_vResidue_add_z_mul_q (td := td) (u := u) (p := p) hu
  -- Pull the box bounds from `mem_T`.
  have hbox : InIoc td.D (2 * td.D) p.1 := (td.mem_T p hpT).1
  -- Rewrite `p.1` as `vResidue + z*q`.
  have : (p.1 : ℤ) = vResidue td u + zCoord td u p * td.q := by
    simpa [shearV] using hv
  -- Finish.
  constructor
  · simpa [this] using hbox.1
  · simpa [this] using hbox.2

/-- Any `z` occurring in the Step 3 decomposition lies in an explicit floor/ceil interval. -/
theorem mem_zSet_imp_mem_Ioc_floor_ceil (td : TubeData) {u z : ℤ} (hz : z ∈ zSet td u) :
    z ∈
      (Finset.Ioc
        (⌊(td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌋ : ℤ)
        (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℤ)) := by
  classical
  have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hq0 : (td.q : ℝ) ≠ 0 := ne_of_gt hq
  set v0R : ℝ := (vResidue td u : ℝ)
  set qR : ℝ := (td.q : ℝ)
  -- Convert the `D`-bounds on `v₀(u) + z*q` into bounds on `z`.
  have hb := mem_zSet_imp_D_bounds (td := td) (u := u) (z := z) hz
  have hlt :
      (td.D - v0R) / qR < (z : ℝ) := by
    -- From `D < v₀ + z*q`.
    have hzq : td.D - v0R < (z : ℝ) * qR := by
      -- Rewrite `v₀ + z*q` in `ℝ`.
      have hb1 : td.D < v0R + (z : ℝ) * qR := by
        simpa [v0R, qR, Int.cast_add, Int.cast_mul, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using hb.1
      linarith
    have : (td.D - v0R) / qR < ((z : ℝ) * qR) / qR :=
      div_lt_div_of_pos_right hzq hq
    simpa [div_eq_mul_inv, qR, hq0, mul_assoc] using this
  have hle :
      (z : ℝ) ≤ (2 * td.D - v0R) / qR := by
    -- From `v₀ + z*q ≤ 2D`.
    have hzq : (z : ℝ) * qR ≤ 2 * td.D - v0R := by
      have hb2 : v0R + (z : ℝ) * qR ≤ 2 * td.D := by
        simpa [v0R, qR, Int.cast_add, Int.cast_mul, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using hb.2
      linarith
    have : ((z : ℝ) * qR) / qR ≤ (2 * td.D - v0R) / qR :=
      div_le_div_of_nonneg_right hzq (le_of_lt hq)
    simpa [div_eq_mul_inv, qR, hq0, mul_assoc] using this

  -- Convert the real inequalities into membership in `Ioc`.
  have hleft : (⌊(td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌋ : ℤ) < z := by
    -- `floor r < z ↔ r < z`.
    have : (td.D - v0R) / qR < (z : ℝ) := hlt
    -- rewrite into the exact term used in the statement
    have : ((td.D - (vResidue td u : ℤ)) / (td.q : ℝ)) < (z : ℝ) := by
      simpa [v0R, qR] using this
    simpa using (Int.floor_lt (a := (td.D - (vResidue td u : ℤ)) / (td.q : ℝ)) (z := z)).2 this
  have hright : z ≤ (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℤ) := by
    -- Since `r ≤ ceil r` and `z ≤ r`, we get `z ≤ ceil r`.
    have hce :
        (2 * td.D - v0R) / qR ≤ (⌈(2 * td.D - v0R) / qR⌉ : ℝ) :=
      Int.le_ceil (a := (2 * td.D - v0R) / qR)
    have : (z : ℝ) ≤ (⌈(2 * td.D - v0R) / qR⌉ : ℝ) := le_trans hle hce
    -- rewrite the RHS back to the exact term used in the statement
    have : (z : ℝ) ≤ (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℝ) := by
      simpa [v0R, qR] using this
    exact_mod_cast this

  simpa [Finset.mem_Ioc] using And.intro hleft hright

/-- A deterministic cardinality bound for `zSet td u` in terms of a floor/ceil interval. -/
theorem card_zSet_le_Ioc_floor_ceil (td : TubeData) (u : ℤ) :
    (zSet td u).card
      ≤
    (Finset.Ioc
        (⌊(td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌋ : ℤ)
        (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℤ)).card := by
  classical
  refine Finset.card_le_card ?_
  intro z hz
  exact mem_zSet_imp_mem_Ioc_floor_ceil (td := td) (u := u) (z := z) hz

/-!
### A usable `O(1 + D/q)` bound (under a mild lower bound on `D/q`)

The exact interval bound above is already sufficient for many downstream arguments, but the TeX
large-sieve scaffolding wants a simple upper bound of the shape `C * (D/q)`.

Since the interval length is at most `D/q + 2`, we can absorb the additive constant provided
`1 ≤ D/q`.
-/

theorem card_zSet_le_three_mul_D_div_q (td : TubeData) (u : ℤ)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hD : 0 ≤ td.D) :
    ((zSet td u).card : ℝ) ≤ 3 * (td.D / (td.q : ℝ)) := by
  classical
  have hq : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hq0 : (td.q : ℝ) ≠ 0 := ne_of_gt hq

  let A : ℤ := (⌊(td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌋ : ℤ)
  let B : ℤ := (⌈(2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)⌉ : ℤ)
  let I : Finset ℤ := Finset.Ioc A B

  have hcard_le : ((zSet td u).card : ℝ) ≤ (I.card : ℝ) := by
    have hnat : (zSet td u).card ≤ I.card := by
      simpa [I, A, B] using card_zSet_le_Ioc_floor_ceil (td := td) (u := u)
    exact_mod_cast hnat

  -- Bound `card I` by bounding `B - A`.
  have hAB : A ≤ B := by
    -- `A = floor r` and `B = ceil s` with `r ≤ s`.
    set r : ℝ := (td.D - (vResidue td u : ℤ)) / (td.q : ℝ)
    set s : ℝ := (2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)
    have hrs : r ≤ s := by
      -- Numerators differ by exactly `D`.
      have : td.D - (vResidue td u : ℤ) ≤ 2 * td.D - (vResidue td u : ℤ) := by linarith
      exact div_le_div_of_nonneg_right this (le_of_lt hq)
    -- Cast inequalities and finish.
    have : (A : ℝ) ≤ (B : ℝ) := by
      have hA : (A : ℝ) ≤ r := by
        -- `floor r ≤ r`
        simpa [A, r] using (Int.floor_le r)
      have hB : s ≤ (B : ℝ) := by
        -- `s ≤ ceil s`
        simpa [B, s] using (Int.le_ceil s)
      exact le_trans (le_trans hA hrs) hB
    exact_mod_cast this

  have hcardZ : ((I.card : ℤ)) = B - A := by
    -- `card_Ioc_of_le` gives the integer-valued cardinality.
    simpa [I] using (Int.card_Ioc_of_le (a := A) (b := B) hAB)

  have hcardR : (I.card : ℝ) = (B - A : ℝ) := by
    exact_mod_cast hcardZ

  -- Now bound `B - A` using floor/ceil estimates.
  have hBA :
      (B - A : ℝ) ≤ (td.D / (td.q : ℝ)) + 2 := by
    set r : ℝ := (td.D - (vResidue td u : ℤ)) / (td.q : ℝ)
    set s : ℝ := (2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)
    have hB : (B : ℝ) ≤ s + 1 := by
      -- `ceil s < s + 1`.
      have : (⌈s⌉ : ℝ) < s + 1 := Int.ceil_lt_add_one s
      simpa [B, s] using this.le
    have hA : r - 1 ≤ (A : ℝ) := by
      -- `r - 1 < floor r`.
      have : r - 1 < (⌊r⌋ : ℝ) := Int.sub_one_lt_floor r
      simpa [A, r] using this.le
    have : (B - A : ℝ) ≤ (s + 1) - (r - 1) := by
      -- subtract the lower bound for `A` and use the upper bound for `B`.
      have hA' : -(A : ℝ) ≤ -(r - 1) := by exact neg_le_neg hA
      have hB' : (B : ℝ) + (-(A : ℝ)) ≤ (s + 1) + (-(r - 1)) := add_le_add hB hA'
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hB'
    -- Simplify `(s+1) - (r-1) = (s-r) + 2 = D/q + 2`.
    have hs_r : s - r = td.D / (td.q : ℝ) := by
      -- `s - r = ( (2D - v0) / q ) - ( (D - v0) / q ) = D / q`.
      have hnum :
          (2 * td.D - (vResidue td u : ℤ)) - (td.D - (vResidue td u : ℤ)) = td.D := by
        ring
      calc
        s - r
            = ((2 * td.D - (vResidue td u : ℤ)) / (td.q : ℝ)) -
                ((td.D - (vResidue td u : ℤ)) / (td.q : ℝ)) := by rfl
        _ = (((2 * td.D - (vResidue td u : ℤ)) - (td.D - (vResidue td u : ℤ))) / (td.q : ℝ)) := by
              simpa using (div_sub_div_same (2 * td.D - (vResidue td u : ℤ)) (td.D - (vResidue td u : ℤ)) (td.q : ℝ))
        _ = td.D / (td.q : ℝ) := by simpa [hnum]
    -- Finish.
    nlinarith [this, hs_r]

  -- Absorb the `+2` term using `1 ≤ D/q`.
  have hDq0 : 0 ≤ td.D / (td.q : ℝ) := div_nonneg hD (le_of_lt hq)
  have habsorb : (td.D / (td.q : ℝ)) + 2 ≤ 3 * (td.D / (td.q : ℝ)) := by
    nlinarith [hDq, hDq0]

  -- Combine.
  have : (I.card : ℝ) ≤ 3 * (td.D / (td.q : ℝ)) := by
    calc
      (I.card : ℝ) = (B - A : ℝ) := hcardR
      _ ≤ (td.D / (td.q : ℝ)) + 2 := hBA
      _ ≤ 3 * (td.D / (td.q : ℝ)) := habsorb

  exact le_trans hcard_le this

end
end LargeSieve
end TypeII
end Engines
end SSU
