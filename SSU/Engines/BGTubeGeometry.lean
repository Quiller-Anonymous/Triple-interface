import SSU.SingleTube

/-!
05_BG.tex — tube geometry layer (TeX-faithful).

This file records the *shear-form* Type–II tube sets used in 05_BG.tex, Subsection
“Tube partition and bounded overlap”:

* dyadic box `(D,2D] × (N,2N]`,
* shear coordinate `u := q n - a d`,
* tube constraint `|u - s| ≤ U`,
* tube-parameter range `S_{a/q} := { s ∈ ℤ : |s| ≤ X/(2 q H) }` (integer-truncated in Lean).

The SSU Type–II/Toeplitz engines work with `Finset` tubes; we therefore provide both:

* `tubeSet` (as a `Set`), and
* `tubeFinset` (as a `Finset`, enumerating the dyadic box and filtering by the shear constraint).
-/

namespace SSU
namespace Engines
namespace BGTube

open scoped BigOperators

noncomputable section

abbrev TubePoint : Type := SSU.TubePoint

/-- Parameters for the BG tube geometry. -/
structure Params where
  /-- Global scale parameter (TeX: `X`). -/
  X : ℕ
  /-- Bandwidth parameter (TeX: `H`). -/
  H : ℕ
  /-- Dyadic box `d ∈ (D,2D]`. -/
  D : ℕ
  /-- Dyadic box `n ∈ (N,2N]`. -/
  N : ℕ
  /-- Tube radius (TeX: `U`). -/
  U : ℕ

namespace Params

variable (P : Params)

/-- The `d`-range as a finset of integers: `(D,2D] ∩ ℤ = [D+1,2D]`. -/
def dRange : Finset ℤ :=
  Finset.Icc ((P.D : ℤ) + 1) ((2 * P.D : ℕ) : ℤ)

/-- The `n`-range as a finset of integers: `(N,2N] ∩ ℤ = [N+1,2N]`. -/
def nRange : Finset ℤ :=
  Finset.Icc ((P.N : ℤ) + 1) ((2 * P.N : ℕ) : ℤ)

/-- The dyadic box as a finset of lattice points. -/
def box : Finset TubePoint :=
  (P.dRange.product P.nRange)

end Params

/-!
### Tube definition (shear form)
-/

/-- Shear coordinate centered at slope `a/q` and offset `s` (TeX: `qn - ad - s`). -/
def shear (a : ℤ) (q : ℕ) (s : ℤ) (p : TubePoint) : ℤ :=
  (q : ℤ) * p.2 - a * p.1 - s

/-- The tube set (as a `Set`) in shear form: `p ∈ box ∧ |shear| ≤ U`. -/
def tubeSet (P : Params) (a : ℤ) (q : ℕ) (s : ℤ) : Set TubePoint :=
  {p : TubePoint | p ∈ P.box ∧ Int.natAbs (shear a q s p) ≤ P.U}

/-- The tube as a `Finset`, by filtering the dyadic box. -/
def tubeFinset (P : Params) (a : ℤ) (q : ℕ) (s : ℤ) : Finset TubePoint :=
  (P.box).filter (fun p => Int.natAbs (shear a q s p) ≤ P.U)

theorem mem_tubeFinset_iff (P : Params) (a : ℤ) (q : ℕ) (s : ℤ) (p : TubePoint) :
    p ∈ tubeFinset P a q s ↔ p ∈ P.box ∧ Int.natAbs (shear a q s p) ≤ P.U := by
  simp [tubeFinset, and_left_comm, and_assoc]

theorem mem_tubeSet_iff (P : Params) (a : ℤ) (q : ℕ) (s : ℤ) (p : TubePoint) :
    p ∈ tubeSet P a q s ↔ p ∈ P.box ∧ Int.natAbs (shear a q s p) ≤ P.U := by
  rfl

/-!
### Box-as-tube specialization (TeX 05_BG “Toeplitz block”)

The Toeplitz regrouping identity in `05_BG.tex` is stated on the full dyadic box
`(D,2D] × (N,2N]` (with a smooth cutoff), without imposing a shear constraint.

In Lean, we can represent the dyadic box as a “tube” by choosing the trivial slope/offset
`a = 0, q = 1, s = 0` and taking `U ≥ 2N`, since then `|qn - ad - s| = |n| ≤ 2N` on the box.

This lemma is used to reuse the tube-based infrastructure for the box-only Toeplitz reduction.
-/

theorem tubeFinset_eq_box_of_U_ge_twoN (P : Params) (hU : 2 * P.N ≤ P.U) :
    tubeFinset P (a := 0) (q := 1) (s := 0) = P.box := by
  classical
  ext p
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).1
  · intro hp
    refine Finset.mem_filter.mpr ?_
    refine ⟨hp, ?_⟩
    -- On the box, `shear 0 1 0 (d,n) = n`, so it suffices to show `Int.natAbs n ≤ U`.
    have hs : shear (a := 0) (q := 1) (s := 0) p = p.2 := by
      simp [shear]
    -- Bound `natAbs p.2 ≤ 2N` using the `n`-range membership.
    have hnRange : p.2 ∈ P.nRange := by
      -- `p ∈ box = dRange × nRange`.
      have : p.2 ∈ P.nRange := by
        exact (Finset.mem_product.mp (by simpa [Params.box] using hp)).2
      exact this
    have hnIcc :
        (P.N : ℤ) + 1 ≤ p.2 ∧ p.2 ≤ ((2 * P.N : ℕ) : ℤ) := by
      simpa [Params.nRange] using (Finset.mem_Icc.mp hnRange)
    have hn0 : 0 ≤ p.2 :=
      le_trans (by
        have hN0 : 0 ≤ (P.N : ℤ) := by exact Int.natCast_nonneg P.N
        exact add_nonneg hN0 (by norm_num)) hnIcc.1
    have htwoN0 : 0 ≤ ((2 * P.N : ℕ) : ℤ) := by
      exact Int.natCast_nonneg (2 * P.N)
    have hsq :
        p.2 * p.2 ≤ ((2 * P.N : ℕ) : ℤ) * ((2 * P.N : ℕ) : ℤ) := by
      have h1 : p.2 * p.2 ≤ ((2 * P.N : ℕ) : ℤ) * p.2 :=
        mul_le_mul_of_nonneg_right hnIcc.2 hn0
      have h2 : ((2 * P.N : ℕ) : ℤ) * p.2 ≤ ((2 * P.N : ℕ) : ℤ) * ((2 * P.N : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hnIcc.2 htwoN0
      exact le_trans h1 h2
    have hnatAbs_le_twoN :
        Int.natAbs p.2 ≤ Int.natAbs ((2 * P.N : ℕ) : ℤ) := by
      -- Use the square characterization of `natAbs ≤`.
      exact (Int.natAbs_le_iff_mul_self_le).2 hsq
    have hnatAbs_twoN :
        Int.natAbs (2 * (P.N : ℤ)) = 2 * P.N := by
      have hcast : (2 * (P.N : ℤ)) = ((2 * P.N : ℕ) : ℤ) := by
        -- `((m*n:ℕ):ℤ) = (m:ℤ) * (n:ℤ)`.
        simpa using (Int.natCast_mul 2 P.N).symm
      rw [hcast]
      simpa using (Int.natAbs_natCast (2 * P.N))
    have hnatAbs_le : Int.natAbs p.2 ≤ P.U := by
      -- Convert the bound `≤ 2N` to `≤ U` via `hU`.
      have : Int.natAbs p.2 ≤ 2 * P.N := by
        simpa [hnatAbs_twoN] using hnatAbs_le_twoN
      exact le_trans this hU
    simpa [hs] using hnatAbs_le

/-!
### Tube offset range `S_{a/q}`

TeX: `S_{a/q} := { s ∈ ℤ : |s| ≤ X/(2 q H) }`.

In Lean we use integer truncation via `Nat` division:
`bound := X / (2*q*H)` and `|s| ≤ bound`.
-/

/-- Integer-truncated TeX bound `⌊X/(2 q H)⌋` (as `Nat`). -/
def sBound (P : Params) (q : ℕ) : ℕ :=
  P.X / (2 * q * P.H)

/-- Offset range `S_{a/q}` as a set of integers (`Int.natAbs s ≤ sBound`). -/
def sSet (P : Params) (q : ℕ) : Set ℤ :=
  Set.Icc (-(sBound P q : ℤ)) (sBound P q : ℤ)

/-- Offset range `S_{a/q}` as a finset of integers: `[-bound, bound]`. -/
def sFinset (P : Params) (q : ℕ) : Finset ℤ :=
  Finset.Icc (-(sBound P q : ℤ)) (sBound P q : ℤ)

theorem mem_sFinset_iff (P : Params) (q : ℕ) (s : ℤ) :
    s ∈ sFinset P q ↔ s ∈ sSet P q := by
  simp [sFinset, sSet]

theorem mem_sFinset_iff' (P : Params) (q : ℕ) (s : ℤ) :
    s ∈ sFinset P q ↔ (-(sBound P q : ℤ) ≤ s ∧ s ≤ (sBound P q : ℤ)) := by
  simpa [sFinset] using (Finset.mem_Icc : s ∈ Finset.Icc (-(sBound P q : ℤ)) (sBound P q : ℤ) ↔ _)

end
end BGTube
end Engines
end SSU
