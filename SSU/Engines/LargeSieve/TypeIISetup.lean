import SSU.Engines.TypeII

/-!
Deterministic setup for the TeX Step 3–4 large-sieve bounds (`05b_SSU.tex`, lines 535–561).

The TeX argument works in shear coordinates `(u,v) = (qn - ad, d)` and uses the congruence

`u ≡ -a v (mod q)`  ⇔  `v ≡ -(aInv) u (mod q)`.

This file records the residue-class bookkeeping in a Lean-friendly way. No analytic large sieve
inequality is proved here.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

namespace LargeSieve

/-- Canonical residue class `v₀(u) ∈ [0,q)` from the TeX congruence `v ≡ -(aInv) u (mod q)`. -/
def vResidue (td : TubeData) (u : ℤ) : ℤ :=
  (-(aInv td) * u) % td.q

theorem vResidue_nonneg (td : TubeData) (u : ℤ) : 0 ≤ vResidue td u := by
  have hq : 0 < td.q := td.q_pos
  simpa [vResidue] using Int.emod_nonneg (-(aInv td) * u) (ne_of_gt hq)

theorem vResidue_lt (td : TubeData) (u : ℤ) : vResidue td u < td.q := by
  have hq : 0 < td.q := td.q_pos
  simpa [vResidue] using Int.emod_lt_of_pos (-(aInv td) * u) hq

/-- The residue definition is congruent to the raw expression modulo `q`. -/
theorem modEq_vResidue (td : TubeData) (u : ℤ) :
    (-(aInv td) * u) ≡ vResidue td u [ZMOD td.q] := by
  -- `a ≡ a % q` is definitional for `Int.ModEq` (equality after `emod`).
  simp [Int.ModEq, vResidue, Int.emod_emod]

/-- TeX congruence rewritten in the `v ≡ v₀(u) (mod q)` form for a lattice point `p = (d,n)`. -/
theorem shearV_modEq_vResidue (td : TubeData) (p : TubePoint) :
    shearV p ≡ vResidue td (shearU td.a td.q p) [ZMOD td.q] := by
  -- Start from `u ≡ -a v`.
  have hu :
      shearU td.a td.q p ≡ (-td.a * shearV p) [ZMOD td.q] :=
    shearU_modEq_neg_a_mul_v (a := td.a) (q := td.q) (p := p)
  -- Solve for `v` using the modular inverse witness.
  have hv : shearV p ≡ (-(aInv td) * shearU td.a td.q p) [ZMOD td.q] :=
    modEq_v_of_modEq_u td hu
  -- Replace the RHS by the canonical residue.
  exact hv.trans (modEq_vResidue td (shearU td.a td.q p))

/-- Any `v ≡ v₀(u) (mod q)` can be written as `v = v₀(u) + z*q`. -/
theorem exists_eq_add_mul_q_of_modEq_vResidue (td : TubeData) {u v : ℤ}
    (hv : v ≡ vResidue td u [ZMOD td.q]) :
    ∃ z : ℤ, v = vResidue td u + z * td.q := by
  -- `ModEq` is `q ∣ (vResidue - v)`.
  rw [Int.modEq_iff_dvd] at hv
  rcases hv with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  -- Rearrange `vResidue - v = q*z`.
  have : v = vResidue td u - td.q * z := by
    linarith
  -- Rewrite into `vResidue + (-z)*q`.
  simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using this

/-- Canonical residue class `u₀(v) ∈ [0,q)` from the TeX congruence `u ≡ -a v (mod q)`. -/
def uResidue (td : TubeData) (v : ℤ) : ℤ :=
  (-(td.a) * v) % td.q

theorem uResidue_nonneg (td : TubeData) (v : ℤ) : 0 ≤ uResidue td v := by
  have hq : 0 < td.q := td.q_pos
  simpa [uResidue] using Int.emod_nonneg (-(td.a) * v) (ne_of_gt hq)

theorem uResidue_lt (td : TubeData) (v : ℤ) : uResidue td v < td.q := by
  have hq : 0 < td.q := td.q_pos
  simpa [uResidue] using Int.emod_lt_of_pos (-(td.a) * v) hq

/-- The residue definition is congruent to the raw expression modulo `q`. -/
theorem modEq_uResidue (td : TubeData) (v : ℤ) :
    (-(td.a) * v) ≡ uResidue td v [ZMOD td.q] := by
  simp [Int.ModEq, uResidue, Int.emod_emod]

/-- TeX congruence rewritten in the `u ≡ u₀(v) (mod q)` form for a lattice point `p = (d,n)`. -/
theorem shearU_modEq_uResidue (td : TubeData) (p : TubePoint) :
    shearU td.a td.q p ≡ uResidue td (shearV p) [ZMOD td.q] := by
  have hu :
      shearU td.a td.q p ≡ (-td.a * shearV p) [ZMOD td.q] :=
    shearU_modEq_neg_a_mul_v (a := td.a) (q := td.q) (p := p)
  -- Rewrite `-a*v` as `-(a)*v` (just notation) and then to the canonical residue.
  simpa [uResidue, neg_mul] using hu.trans (modEq_uResidue td (shearV p))

/-- Any `u ≡ u₀(v) (mod q)` can be written as `u = u₀(v) + z*q`. -/
theorem exists_eq_add_mul_q_of_modEq_uResidue (td : TubeData) {u v : ℤ}
    (hu : u ≡ uResidue td v [ZMOD td.q]) :
    ∃ z : ℤ, u = uResidue td v + z * td.q := by
  rw [Int.modEq_iff_dvd] at hu
  rcases hu with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  have : u = uResidue td v - td.q * z := by
    linarith
  simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using this

end LargeSieve

end

end TypeII
end Engines
end SSU
