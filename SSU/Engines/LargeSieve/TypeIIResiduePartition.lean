import SSU.Engines.LargeSieve.TypeIISetup
import SSU.Engines.LargeSieve.TypeIISumDecompose
import SSU.Engines.LargeSieve.TypeIISumDecomposeV
import SSU.Engines.LargeSieve.TypeIIIndexBounds

/-!
Deterministic residue-class partitions used in TeX Step 3/4.

TeX Step 3 groups by the congruence class `v ≡ v₀(u) (mod q)` where `v₀(u) ∈ [0,q)`. In Lean we
encode `v₀(u)` as `vResidue td u`. This file records the purely algebraic partition of `uSet td`
by the map `u ↦ vResidue td u`.

Analogously, TeX Step 4 groups by `u ≡ u₀(v) (mod q)` using `uResidue td v`.

These lemmas do **not** prove any large sieve bounds; they are bookkeeping tools for later proofs.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

/-!
## Step 3 bookkeeping: partition `uSet td` by `vResidue td`
-/

namespace ResiduePartition

variable (td : TubeData)

/-!
## Bounds on the progression index set `uIndexSet`

These are used to build an MV `FiniteLargeSieve` instance on the progression parameter.
-/

/-! The residue set `r ∈ [0,q)` (as integers) used to partition `uSet td` by `vResidue td`. -/
def residuesU : Finset ℤ :=
  Finset.Icc 0 (td.q - 1)

theorem mem_residuesU (u : ℤ) : vResidue td u ∈ residuesU td := by
  have hq : 0 < td.q := td.q_pos
  have h0 : 0 ≤ vResidue td u := vResidue_nonneg td u
  have hlt : vResidue td u ≤ td.q - 1 := by
    have : vResidue td u < td.q := vResidue_lt td u
    -- Convert `< q` to `≤ q-1`.
    have : vResidue td u ≤ td.q - 1 := Int.le_sub_one_of_lt this
    simpa using this
  exact Finset.mem_Icc.mpr ⟨h0, hlt⟩

/-- The residue class subset of `uSet td` at a given `r ∈ [0,q)`. -/
def uClass (r : ℤ) : Finset ℤ :=
  (uSet td).filter fun u => vResidue td u = r

/-!
### Congruence reformulation (`uClass` is an arithmetic progression mod `q`)

In TeX Step 3, fixing `r = v₀(u) ∈ [0,q)` is equivalent to fixing the congruence class of `u`
modulo `q`.  Concretely, since

`vResidue td u = (-(aInv td) * u) % q`,

the equation `vResidue td u = r` implies

`u ≡ uResidue td r [ZMOD q]`,

and hence `u = uResidue td r + z*q` for some `z : ℤ`.
-/

theorem modEq_uResidue_of_eq_vResidue {u r : ℤ} (h : vResidue td u = r) :
    u ≡ uResidue td r [ZMOD td.q] := by
  -- Start from the defining congruence for `vResidue td u`.
  have hv : (-(aInv td) * u) ≡ r [ZMOD td.q] := by
    simpa [h] using (modEq_vResidue td u)
  -- Multiply by `-a` to solve for `u`.
  have hv' : (-td.a) * (-(aInv td) * u) ≡ (-td.a) * r [ZMOD td.q] :=
    Int.ModEq.mul_left (-td.a) hv
  have hv'' : (td.a * (aInv td)) * u ≡ (-td.a) * r [ZMOD td.q] := by
    -- `(-a)*(-(aInv*u)) = (a*aInv)*u`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using hv'
  -- Use `a*aInv ≡ 1` to reduce the LHS to `u`.
  have hunit : (td.a * (aInv td)) ≡ 1 [ZMOD td.q] := a_mul_aInv_modEq_one td
  have hunitMul : (td.a * (aInv td)) * u ≡ (1 : ℤ) * u [ZMOD td.q] :=
    Int.ModEq.mul_right u hunit
  have hu : u ≡ (-td.a) * r [ZMOD td.q] := by
    -- Replace the LHS using `hunitMul`.
    have : (1 : ℤ) * u ≡ (-td.a) * r [ZMOD td.q] := by
      exact (hunitMul.symm.trans hv'')
    simpa [one_mul] using this
  -- Finally, replace `(-a)*r` by its canonical representative `uResidue td r`.
  exact hu.trans (modEq_uResidue td r)

theorem exists_eq_add_mul_q_of_mem_uClass {u r : ℤ} (hu : u ∈ uClass td r) :
    ∃ z : ℤ, u = uResidue td r + z * td.q := by
  -- `hu` is exactly the equation `vResidue td u = r`.
  have hEq : vResidue td u = r := by
    simpa [uClass] using (Finset.mem_filter.mp hu).2
  exact exists_eq_add_mul_q_of_modEq_uResidue (td := td) (u := u) (v := r)
    (modEq_uResidue_of_eq_vResidue (td := td) (u := u) (r := r) hEq)

/-- The arithmetic-progression index `z` for `u = u₀(r) + z*q` on a fixed residue class. -/
def uIndex (r u : ℤ) : ℤ :=
  (u - uResidue td r) / td.q

theorem eq_uResidue_add_uIndex_mul_q_of_mem_uClass {u r : ℤ} (hu : u ∈ uClass td r) :
    u = uResidue td r + uIndex td r u * td.q := by
  -- Convert `hu` to the congruence `u ≡ uResidue r (mod q)`.
  have hEq : vResidue td u = r := by
    simpa [uClass] using (Finset.mem_filter.mp hu).2
  have hmod : u ≡ uResidue td r [ZMOD td.q] :=
    modEq_uResidue_of_eq_vResidue (td := td) (u := u) (r := r) hEq
  -- Turn `ModEq` into a divisibility statement for `u - u₀(r)`.
  have hdvd0 : td.q ∣ (uResidue td r - u) := (Int.modEq_iff_dvd).1 hmod
  have hdvd : td.q ∣ (u - uResidue td r) := by
    -- `u - u₀ = -(u₀ - u)`.
    have : td.q ∣ -(uResidue td r - u) := (Int.dvd_neg).2 hdvd0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  -- Use exact division since `q ∣ u - u₀`.
  calc
    u
        = uResidue td r + (u - uResidue td r) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = uResidue td r + ((u - uResidue td r) / td.q) * td.q := by
            -- `a = (a/q)*q` when `q ∣ a`.
            have : (u - uResidue td r) / td.q * td.q = (u - uResidue td r) :=
              (Int.ediv_mul_cancel hdvd)
            simp [this, mul_assoc, mul_left_comm, mul_comm]
    _ = uResidue td r + uIndex td r u * td.q := by
            rfl

/-- TeX Step 3 phase split on a fixed residue class: write `u = u₀(r) + z*q` and split the
oscillatory factor accordingly. -/
theorem e_mul_u_mul_z_div_X_eq_mul (ξ : ℝ) {u r z : ℤ} (hu : u ∈ uClass td r) :
    e (ξ * (u : ℝ) * (z : ℝ) / td.X)
      =
    e (ξ * (uResidue td r : ℝ) * (z : ℝ) / td.X) *
      e (ξ * ((uIndex td r u : ℝ) * (td.q : ℝ)) * (z : ℝ) / td.X) := by
  have e_add (x y : ℝ) : e (x + y) = e x * e y := by
    simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  -- Rewrite `u` as `u₀(r) + uIndex*u*q` and expand.
  have huZ : u = uResidue td r + uIndex td r u * td.q :=
    eq_uResidue_add_uIndex_mul_q_of_mem_uClass (td := td) (u := u) (r := r) hu
  have huR : (u : ℝ) = (uResidue td r : ℝ) + (uIndex td r u : ℝ) * (td.q : ℝ) := by
    have h := congrArg (fun t : ℤ => (t : ℝ)) huZ
    simpa [Int.cast_add, Int.cast_mul] using h
  have hsplit :
      ξ * (u : ℝ) * (z : ℝ) / td.X
        =
      (ξ * (uResidue td r : ℝ) * (z : ℝ) / td.X) +
      (ξ * ((uIndex td r u : ℝ) * (td.q : ℝ)) * (z : ℝ) / td.X) := by
    -- purely algebraic (in `ℝ`)
    simp [huR, div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]
  calc
    e (ξ * (u : ℝ) * (z : ℝ) / td.X)
        = e ((ξ * (uResidue td r : ℝ) * (z : ℝ) / td.X) +
              (ξ * ((uIndex td r u : ℝ) * (td.q : ℝ)) * (z : ℝ) / td.X)) := by
              simpa [hsplit]
    _ = e (ξ * (uResidue td r : ℝ) * (z : ℝ) / td.X) *
          e (ξ * ((uIndex td r u : ℝ) * (td.q : ℝ)) * (z : ℝ) / td.X) := by
          simpa using
            (e_add (ξ * (uResidue td r : ℝ) * (z : ℝ) / td.X)
              (ξ * ((uIndex td r u : ℝ) * (td.q : ℝ)) * (z : ℝ) / td.X))

theorem injOn_uIndex_uClass (r : ℤ) :
    Set.InjOn (uIndex td r) (uClass td r : Set ℤ) := by
  intro u1 hu1 u2 hu2 hEq
  -- Expand both `u1` and `u2` in the `u₀(r) + z*q` form.
  have hu1' : u1 = uResidue td r + uIndex td r u1 * td.q :=
    eq_uResidue_add_uIndex_mul_q_of_mem_uClass (td := td) (u := u1) (r := r) hu1
  have hu2' : u2 = uResidue td r + uIndex td r u2 * td.q :=
    eq_uResidue_add_uIndex_mul_q_of_mem_uClass (td := td) (u := u2) (r := r) hu2
  -- Substitute `uIndex u1 = uIndex u2`.
  calc
    u1 = uResidue td r + uIndex td r u1 * td.q := hu1'
    _ = uResidue td r + uIndex td r u2 * td.q := by simpa [hEq]
    _ = u2 := hu2'.symm

def uIndexSet (r : ℤ) : Finset ℤ :=
  (uClass td r).image (uIndex td r)

theorem uClass_subset_uSet (r : ℤ) : uClass td r ⊆ uSet td := by
  intro u hu
  exact (Finset.mem_filter.mp hu).1

theorem uIndexSet_subset_Icc_ceilU_add_q
    (hU0 : 0 ≤ td.U) (r : ℤ) :
    uIndexSet (td := td) r ⊆ Finset.Icc (-(Int.ceil td.U + td.q)) (Int.ceil td.U + td.q) := by
  classical
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨u, huClass, rfl⟩
  -- `u ∈ uSet`, hence `|u| ≤ ceil U`.
  have huSet : u ∈ uSet td := (uClass_subset_uSet (td := td) (r := r)) huClass
  have huIcc : u ∈ Finset.Icc (-(Int.ceil td.U)) (Int.ceil td.U) :=
    IndexBounds.mem_uSet_mem_Icc_ceilU (td := td) huSet
  have habs_u : |u| ≤ Int.ceil td.U := by
    have : -(Int.ceil td.U) ≤ u ∧ u ≤ Int.ceil td.U := by simpa [Finset.mem_Icc] using huIcc
    exact abs_le.mpr this

  -- `uResidue td r ∈ [0,q)`, hence `|uResidue td r| ≤ q`.
  have hq0 : 0 ≤ td.q := le_of_lt td.q_pos
  have huR0 : 0 ≤ uResidue td r := uResidue_nonneg td r
  have huRle : uResidue td r ≤ td.q := le_of_lt (uResidue_lt td r)
  have habs_uR : |uResidue td r| ≤ td.q := by
    simpa [abs_of_nonneg huR0] using huRle

  -- Bound the index: `| (u-u₀)/q | ≤ |u-u₀| ≤ |u|+|u₀|`.
  have h1 : |uIndex td r u| ≤ |u - uResidue td r| := by
    -- `abs_ediv_le_abs`.
    simpa [uIndex] using (Int.abs_ediv_le_abs (u - uResidue td r) td.q)
  have h2 : |u - uResidue td r| ≤ |u| + |uResidue td r| := by
    simpa [sub_eq_add_neg] using (abs_add_le u (-uResidue td r))
  have h3 : |uIndex td r u| ≤ Int.ceil td.U + td.q := by
    calc
      |uIndex td r u| ≤ |u - uResidue td r| := h1
      _ ≤ |u| + |uResidue td r| := h2
      _ ≤ Int.ceil td.U + td.q := by gcongr

  -- Convert to Icc membership.
  have hM0 : 0 ≤ Int.ceil td.U + td.q := by
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg (α := ℝ) hU0
    exact add_nonneg hceil0 hq0
  have : (-(Int.ceil td.U + td.q) ≤ uIndex td r u ∧ uIndex td r u ≤ Int.ceil td.U + td.q) := by
    simpa using (abs_le.mp (le_trans h3 (le_rfl)))
  simpa [Finset.mem_Icc] using this

theorem distZ_le_two_mul_toNat_ceilU_add_q_on_uIndexSet
    (hU0 : 0 ≤ td.U) (r : ℤ) :
    ∀ i ∈ uIndexSet (td := td) r, ∀ j ∈ uIndexSet (td := td) r,
      SSU.Hilbert.distZ i j ≤ 2 * Int.toNat (Int.ceil td.U + td.q) := by
  classical
  intro i hi j hj
  have hiIcc :=
    uIndexSet_subset_Icc_ceilU_add_q (td := td) (hU0 := hU0) (r := r) hi
  have hjIcc :=
    uIndexSet_subset_Icc_ceilU_add_q (td := td) (hU0 := hU0) (r := r) hj
  have hM0 : 0 ≤ (Int.ceil td.U + td.q) := by
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg (α := ℝ) hU0
    have hq0 : 0 ≤ td.q := le_of_lt td.q_pos
    exact add_nonneg hceil0 hq0
  -- From membership in `Icc`, get `|i| ≤ M` and `|j| ≤ M`.
  have habsi : |i| ≤ Int.ceil td.U + td.q := by
    have : -(Int.ceil td.U + td.q) ≤ i ∧ i ≤ Int.ceil td.U + td.q := by
      simpa [Finset.mem_Icc] using hiIcc
    exact abs_le.mpr this
  have habsj : |j| ≤ Int.ceil td.U + td.q := by
    have : -(Int.ceil td.U + td.q) ≤ j ∧ j ≤ Int.ceil td.U + td.q := by
      simpa [Finset.mem_Icc] using hjIcc
    exact abs_le.mpr this

  -- Convert to `natAbs` bounds (copy the pattern from `TypeIIIndexBounds`).
  have hnat_i : i.natAbs ≤ Int.toNat (Int.ceil td.U + td.q) := by
    have hmulAbs : |i| * |i| ≤ (Int.ceil td.U + td.q) * (Int.ceil td.U + td.q) :=
      mul_le_mul habsi habsi (by positivity) (by positivity)
    have hmul : i * i ≤ (Int.ceil td.U + td.q) * (Int.ceil td.U + td.q) := by
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : i.natAbs ≤ (Int.ceil td.U + td.q).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    have hM : (Int.ceil td.U + td.q).natAbs = Int.toNat (Int.ceil td.U + td.q) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : (((Int.ceil td.U + td.q).natAbs : ℤ)) = (Int.ceil td.U + td.q) :=
        Int.natAbs_of_nonneg hM0
      have h2 : (((Int.ceil td.U + td.q).toNat : ℤ)) = (Int.ceil td.U + td.q) :=
        Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs
  have hnat_j : j.natAbs ≤ Int.toNat (Int.ceil td.U + td.q) := by
    have hmulAbs : |j| * |j| ≤ (Int.ceil td.U + td.q) * (Int.ceil td.U + td.q) :=
      mul_le_mul habsj habsj (by positivity) (by positivity)
    have hmul : j * j ≤ (Int.ceil td.U + td.q) * (Int.ceil td.U + td.q) := by
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : j.natAbs ≤ (Int.ceil td.U + td.q).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    have hM : (Int.ceil td.U + td.q).natAbs = Int.toNat (Int.ceil td.U + td.q) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : (((Int.ceil td.U + td.q).natAbs : ℤ)) = (Int.ceil td.U + td.q) :=
        Int.natAbs_of_nonneg hM0
      have h2 : (((Int.ceil td.U + td.q).toNat : ℤ)) = (Int.ceil td.U + td.q) :=
        Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs

  have htri : (i - j).natAbs ≤ i.natAbs + j.natAbs := by
    simpa [sub_eq_add_neg] using (Int.natAbs_add_le i (-j))
  dsimp [SSU.Hilbert.distZ]
  calc
    (i - j).natAbs ≤ i.natAbs + j.natAbs := htri
    _ ≤ Int.toNat (Int.ceil td.U + td.q) + Int.toNat (Int.ceil td.U + td.q) := by gcongr
    _ = 2 * Int.toNat (Int.ceil td.U + td.q) := by ring

/-!
## Reindexing a residue class by the progression parameter

On a fixed residue class, `u = u₀(r) + uIndex(r,u)*q`. For TeX Step 3/4 we want to sum over
`uIndex` instead of `u`.
The following lemmas are purely deterministic bookkeeping.
-/

/-- Canonical representative of an index `m` in the residue class `r`: `u₀(r) + m*q`. -/
def uFromIndex (r m : ℤ) : ℤ :=
  uResidue td r + m * td.q

theorem uFromIndex_uIndex_of_mem_uClass {u r : ℤ} (hu : u ∈ uClass td r) :
    uFromIndex (td := td) r (uIndex td r u) = u := by
  -- `u = u₀(r) + uIndex(r,u)*q`.
  simpa [uFromIndex, mul_assoc, mul_left_comm, mul_comm] using
    (eq_uResidue_add_uIndex_mul_q_of_mem_uClass (td := td) (u := u) (r := r) hu).symm

theorem uIndex_uFromIndex_of_mem_uIndexSet {r m : ℤ} (hm : m ∈ uIndexSet (td := td) r) :
    uIndex td r (uFromIndex (td := td) r m) = m := by
  classical
  rcases Finset.mem_image.mp hm with ⟨u, hu, rfl⟩
  -- `uFromIndex (uIndex u) = u`, then cancel by `rfl`.
  simpa [uFromIndex_uIndex_of_mem_uClass (td := td) (u := u) (r := r) hu]

theorem uFromIndex_mem_uClass_of_mem_uIndexSet {r m : ℤ} (hm : m ∈ uIndexSet (td := td) r) :
    uFromIndex (td := td) r m ∈ uClass td r := by
  classical
  rcases Finset.mem_image.mp hm with ⟨u, hu, hmEq⟩
  -- `m = uIndex u`, so `uFromIndex r m = u`.
  have : uFromIndex (td := td) r m = u := by
    -- Rewrite `m` and apply `uFromIndex_uIndex_of_mem_uClass`.
    simpa [hmEq] using (uFromIndex_uIndex_of_mem_uClass (td := td) (u := u) (r := r) hu)
  simpa [this] using hu

/-- `uFromIndex` lands in `uSet` whenever `m ∈ uIndexSet`. -/
theorem uFromIndex_mem_uSet_of_mem_uIndexSet {r m : ℤ} (hm : m ∈ uIndexSet (td := td) r) :
    uFromIndex (td := td) r m ∈ uSet td := by
  exact
    (uClass_subset_uSet (td := td) (r := r))
      (uFromIndex_mem_uClass_of_mem_uIndexSet (td := td) (r := r) hm)

/-- On `uIndexSet`, `uFromIndex` has residue `r` for the Step 3 partition map `u ↦ vResidue`. -/
theorem vResidue_uFromIndex_eq_of_mem_uIndexSet {r m : ℤ}
    (hm : m ∈ uIndexSet (td := td) r) :
    vResidue td (uFromIndex (td := td) r m) = r := by
  have huClass : uFromIndex (td := td) r m ∈ uClass td r :=
    uFromIndex_mem_uClass_of_mem_uIndexSet (td := td) (r := r) hm
  exact (Finset.mem_filter.mp huClass).2

theorem sum_uClass_eq_sum_uIndexSet {β : Type*} [AddCommMonoid β]
    (r : ℤ) (f : ℤ → β) :
    (uClass td r).sum (fun u => f u) =
      (uIndexSet (td := td) r).sum (fun m => f (uFromIndex (td := td) r m)) := by
  classical
  -- Reorder the sum using `uIndex` as a surjective injection onto `uIndexSet`.
  refine Finset.sum_nbij (s := uClass td r) (t := uIndexSet (td := td) r) (i := uIndex td r)
    (f := fun u => f u) (g := fun m => f (uFromIndex (td := td) r m)) ?_ ?_ ?_ ?_
  · intro u hu
    exact Finset.mem_image_of_mem (uIndex td r) hu
  · intro u1 hu1 u2 hu2 hEq
    have hInj := injOn_uIndex_uClass (td := td) (r := r)
    have hu1' : u1 ∈ (uClass td r : Set ℤ) := by simpa using hu1
    have hu2' : u2 ∈ (uClass td r : Set ℤ) := by simpa using hu2
    exact hInj hu1' hu2' hEq
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · intro u hu
    -- `uFromIndex (uIndex u) = u` on the residue class.
    simpa [uFromIndex_uIndex_of_mem_uClass (td := td) (u := u) (r := r) hu]

theorem sum_uSet_eq_sum_residueClasses
    {α : Type*} [AddCommMonoid α] (f : ℤ → α) :
    (∑ u ∈ uSet td, f u)
      =
    ∑ r ∈ residuesU td, ∑ u ∈ uClass td r, f u := by
  classical
  -- Use `sum_fiberwise_of_maps_to` for `g := vResidue td`.
  have hMapsTo : ∀ u ∈ uSet td, vResidue td u ∈ residuesU td := by
    intro u hu
    exact mem_residuesU (td := td) u
  -- Partition the sum over `uSet td` by `r := vResidue td u`.
  have hpart :=
    (Finset.sum_fiberwise_of_maps_to (s := uSet td) (t := residuesU td)
      (g := vResidue td) (f := fun u : ℤ => f u) hMapsTo)
  -- Unfold the fiber filter as `uClass`.
  -- `sum_fiberwise_of_maps_to` returns `∑_r ∑_{u: g u = r} f u = ∑_u f u`.
  -- So we use `.symm` and then rewrite.
  refine hpart.symm.trans ?_
  refine Finset.sum_congr rfl ?_
  intro r hr
  -- The fiber is exactly `uClass td r`.
  simp [uClass]  -- simplifies the `with`-filter into our definition

end ResiduePartition

/-!
## Step 4 bookkeeping: partition `vSet td` by `uResidue td`
-/

namespace ResiduePartitionV

variable (td : TubeData)

/-! The residue set `r ∈ [0,q)` (as integers) used to partition `vSet td` by `uResidue td`. -/
def residuesV : Finset ℤ :=
  Finset.Icc 0 (td.q - 1)

theorem mem_residuesV (v : ℤ) : uResidue td v ∈ residuesV td := by
  have h0 : 0 ≤ uResidue td v := uResidue_nonneg td v
  have hlt : uResidue td v ≤ td.q - 1 := by
    have : uResidue td v < td.q := uResidue_lt td v
    exact Int.le_sub_one_of_lt this
  exact Finset.mem_Icc.mpr ⟨h0, hlt⟩

/-- The residue class subset of `vSet td` at a given `r ∈ [0,q)`. -/
def vClass (r : ℤ) : Finset ℤ :=
  (vSet td).filter fun v => uResidue td v = r

theorem modEq_vResidue_of_eq_uResidue {v r : ℤ} (h : uResidue td v = r) :
    v ≡ vResidue td r [ZMOD td.q] := by
  -- Start from the defining congruence for `uResidue td v`.
  have hu : (-td.a * v) ≡ r [ZMOD td.q] := by
    simpa [h] using (modEq_uResidue td v)
  -- Multiply by `-aInv` to solve for `v`.
  have hu' : (-(aInv td)) * (-td.a * v) ≡ (-(aInv td)) * r [ZMOD td.q] :=
    Int.ModEq.mul_left (-(aInv td)) hu
  have hu'' : ((aInv td) * td.a) * v ≡ (-(aInv td)) * r [ZMOD td.q] := by
    -- `(-aInv)*(-a*v) = (aInv*a)*v`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using hu'
  -- Use `aInv*a ≡ 1` to reduce to `v`.
  have hunit : (aInv td) * td.a ≡ 1 [ZMOD td.q] := by
    simpa [mul_comm] using (a_mul_aInv_modEq_one td)
  have hunitMul : ((aInv td) * td.a) * v ≡ (1 : ℤ) * v [ZMOD td.q] :=
    Int.ModEq.mul_right v hunit
  have hv : v ≡ (-(aInv td)) * r [ZMOD td.q] := by
    have : (1 : ℤ) * v ≡ (-(aInv td)) * r [ZMOD td.q] := by
      exact (hunitMul.symm.trans hu'')
    simpa [one_mul] using this
  -- Replace by the canonical residue representative `vResidue td r`.
  exact hv.trans (modEq_vResidue td r)

theorem exists_eq_add_mul_q_of_mem_vClass {v r : ℤ} (hv : v ∈ vClass td r) :
    ∃ z : ℤ, v = vResidue td r + z * td.q := by
  have hEq : uResidue td v = r := by
    simpa [vClass] using (Finset.mem_filter.mp hv).2
  exact exists_eq_add_mul_q_of_modEq_vResidue (td := td) (u := r) (v := v)
    (modEq_vResidue_of_eq_uResidue (td := td) (v := v) (r := r) hEq)

/-- The arithmetic-progression index `z` for `v = v₀(r) + z*q` on a fixed residue class. -/
def vIndex (r v : ℤ) : ℤ :=
  (v - vResidue td r) / td.q

theorem eq_vResidue_add_vIndex_mul_q_of_mem_vClass {v r : ℤ} (hv : v ∈ vClass td r) :
    v = vResidue td r + vIndex td r v * td.q := by
  have hEq : uResidue td v = r := by
    simpa [vClass] using (Finset.mem_filter.mp hv).2
  have hmod : v ≡ vResidue td r [ZMOD td.q] :=
    modEq_vResidue_of_eq_uResidue (td := td) (v := v) (r := r) hEq
  have hdvd0 : td.q ∣ (vResidue td r - v) := (Int.modEq_iff_dvd).1 hmod
  have hdvd : td.q ∣ (v - vResidue td r) := by
    have : td.q ∣ -(vResidue td r - v) := (Int.dvd_neg).2 hdvd0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  calc
    v
        = vResidue td r + (v - vResidue td r) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = vResidue td r + ((v - vResidue td r) / td.q) * td.q := by
            have : (v - vResidue td r) / td.q * td.q = (v - vResidue td r) :=
              (Int.ediv_mul_cancel hdvd)
            simp [this, mul_assoc, mul_left_comm, mul_comm]
    _ = vResidue td r + vIndex td r v * td.q := by
            rfl

/-- TeX Step 4 phase split on a fixed residue class: write `v = v₀(r) + z*q` and split the
oscillatory factor accordingly. -/
theorem e_mul_z_mul_v_div_X_eq_mul (ξ : ℝ) {v r z : ℤ} (hv : v ∈ vClass td r) :
    e (ξ * (z : ℝ) * (v : ℝ) / td.X)
      =
    e (ξ * (z : ℝ) * (vResidue td r : ℝ) / td.X) *
      e (ξ * (z : ℝ) * ((vIndex td r v : ℝ) * (td.q : ℝ)) / td.X) := by
  have e_add (x y : ℝ) : e (x + y) = e x * e y := by
    simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  have hvZ : v = vResidue td r + vIndex td r v * td.q :=
    eq_vResidue_add_vIndex_mul_q_of_mem_vClass (td := td) (v := v) (r := r) hv
  have hvR : (v : ℝ) = (vResidue td r : ℝ) + (vIndex td r v : ℝ) * (td.q : ℝ) := by
    have h := congrArg (fun t : ℤ => (t : ℝ)) hvZ
    simpa [Int.cast_add, Int.cast_mul] using h
  have hsplit :
      ξ * (z : ℝ) * (v : ℝ) / td.X
        =
      (ξ * (z : ℝ) * (vResidue td r : ℝ) / td.X) +
      (ξ * (z : ℝ) * ((vIndex td r v : ℝ) * (td.q : ℝ)) / td.X) := by
    -- purely algebraic (in `ℝ`)
    simp [hvR, div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  -- Now apply the additive property of `e`.
  calc
    e (ξ * (z : ℝ) * (v : ℝ) / td.X)
        = e ((ξ * (z : ℝ) * (vResidue td r : ℝ) / td.X) +
              (ξ * (z : ℝ) * ((vIndex td r v : ℝ) * (td.q : ℝ)) / td.X)) := by
              simpa [hsplit]
    _ = e (ξ * (z : ℝ) * (vResidue td r : ℝ) / td.X) *
          e (ξ * (z : ℝ) * ((vIndex td r v : ℝ) * (td.q : ℝ)) / td.X) := by
          simpa using
            (e_add (ξ * (z : ℝ) * (vResidue td r : ℝ) / td.X)
              (ξ * (z : ℝ) * ((vIndex td r v : ℝ) * (td.q : ℝ)) / td.X))

theorem injOn_vIndex_vClass (r : ℤ) :
    Set.InjOn (vIndex td r) (vClass td r : Set ℤ) := by
  intro v1 hv1 v2 hv2 hEq
  have hv1' : v1 = vResidue td r + vIndex td r v1 * td.q :=
    eq_vResidue_add_vIndex_mul_q_of_mem_vClass (td := td) (v := v1) (r := r) hv1
  have hv2' : v2 = vResidue td r + vIndex td r v2 * td.q :=
    eq_vResidue_add_vIndex_mul_q_of_mem_vClass (td := td) (v := v2) (r := r) hv2
  calc
    v1 = vResidue td r + vIndex td r v1 * td.q := hv1'
    _ = vResidue td r + vIndex td r v2 * td.q := by simpa [hEq]
    _ = v2 := hv2'.symm

def vIndexSet (r : ℤ) : Finset ℤ :=
  (vClass td r).image (vIndex td r)

theorem vClass_subset_vSet (r : ℤ) : vClass td r ⊆ vSet td := by
  intro v hv
  exact (Finset.mem_filter.mp hv).1

theorem vIndexSet_subset_Icc_ceilTwoD_add_q
    (hD0 : 0 ≤ td.D) (r : ℤ) :
    vIndexSet (td := td) r ⊆
      Finset.Icc (-(Int.ceil (2 * td.D) + td.q)) (Int.ceil (2 * td.D) + td.q) := by
  classical
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨v, hvClass, rfl⟩
  have hvSet : v ∈ vSet td := (vClass_subset_vSet (td := td) (r := r)) hvClass
  have hvIcc : v ∈ Finset.Icc (-(Int.ceil (2 * td.D))) (Int.ceil (2 * td.D)) :=
    IndexBounds.mem_vSet_mem_Icc_ceilTwoD (td := td) (hD0 := hD0) hvSet
  have habs_v : |v| ≤ Int.ceil (2 * td.D) := by
    have : -(Int.ceil (2 * td.D)) ≤ v ∧ v ≤ Int.ceil (2 * td.D) := by
      simpa [Finset.mem_Icc] using hvIcc
    exact abs_le.mpr this

  have hvR0 : 0 ≤ vResidue td r := vResidue_nonneg td r
  have hvRle : vResidue td r ≤ td.q := le_of_lt (vResidue_lt td r)
  have habs_vR : |vResidue td r| ≤ td.q := by
    simpa [abs_of_nonneg hvR0] using hvRle

  have h1 : |vIndex td r v| ≤ |v - vResidue td r| := by
    simpa [vIndex] using (Int.abs_ediv_le_abs (v - vResidue td r) td.q)
  have h2 : |v - vResidue td r| ≤ |v| + |vResidue td r| := by
    simpa [sub_eq_add_neg] using (abs_add_le v (-vResidue td r))
  have h3 : |vIndex td r v| ≤ Int.ceil (2 * td.D) + td.q := by
    calc
      |vIndex td r v| ≤ |v - vResidue td r| := h1
      _ ≤ |v| + |vResidue td r| := h2
      _ ≤ Int.ceil (2 * td.D) + td.q := by gcongr

  have hM0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (α := ℝ) (by nlinarith [hD0])
    have hq0 : 0 ≤ td.q := le_of_lt td.q_pos
    exact add_nonneg hceil0 hq0
  have : (-(Int.ceil (2 * td.D) + td.q) ≤ vIndex td r v ∧ vIndex td r v ≤ Int.ceil (2 * td.D) + td.q) := by
    simpa using (abs_le.mp (le_trans h3 (le_rfl)))
  simpa [Finset.mem_Icc] using this

theorem distZ_le_two_mul_toNat_ceilTwoD_add_q_on_vIndexSet
    (hD0 : 0 ≤ td.D) (r : ℤ) :
    ∀ i ∈ vIndexSet (td := td) r, ∀ j ∈ vIndexSet (td := td) r,
      SSU.Hilbert.distZ i j ≤ 2 * Int.toNat (Int.ceil (2 * td.D) + td.q) := by
  classical
  intro i hi j hj
  have hiIcc :=
    vIndexSet_subset_Icc_ceilTwoD_add_q (td := td) (hD0 := hD0) (r := r) hi
  have hjIcc :=
    vIndexSet_subset_Icc_ceilTwoD_add_q (td := td) (hD0 := hD0) (r := r) hj
  have hM0 : 0 ≤ (Int.ceil (2 * td.D) + td.q) := by
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (α := ℝ) (by nlinarith [hD0])
    have hq0 : 0 ≤ td.q := le_of_lt td.q_pos
    exact add_nonneg hceil0 hq0
  have habsi : |i| ≤ Int.ceil (2 * td.D) + td.q := by
    have : -(Int.ceil (2 * td.D) + td.q) ≤ i ∧ i ≤ Int.ceil (2 * td.D) + td.q := by
      simpa [Finset.mem_Icc] using hiIcc
    exact abs_le.mpr this
  have habsj : |j| ≤ Int.ceil (2 * td.D) + td.q := by
    have : -(Int.ceil (2 * td.D) + td.q) ≤ j ∧ j ≤ Int.ceil (2 * td.D) + td.q := by
      simpa [Finset.mem_Icc] using hjIcc
    exact abs_le.mpr this

  have hnat_i : i.natAbs ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
    have hmulAbs : |i| * |i| ≤ (Int.ceil (2 * td.D) + td.q) * (Int.ceil (2 * td.D) + td.q) :=
      mul_le_mul habsi habsi (by positivity) (by positivity)
    have hmul : i * i ≤ (Int.ceil (2 * td.D) + td.q) * (Int.ceil (2 * td.D) + td.q) := by
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : i.natAbs ≤ (Int.ceil (2 * td.D) + td.q).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    have hM : (Int.ceil (2 * td.D) + td.q).natAbs = Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : (((Int.ceil (2 * td.D) + td.q).natAbs : ℤ)) = (Int.ceil (2 * td.D) + td.q) :=
        Int.natAbs_of_nonneg hM0
      have h2 : (((Int.ceil (2 * td.D) + td.q).toNat : ℤ)) = (Int.ceil (2 * td.D) + td.q) :=
        Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs
  have hnat_j : j.natAbs ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
    have hmulAbs : |j| * |j| ≤ (Int.ceil (2 * td.D) + td.q) * (Int.ceil (2 * td.D) + td.q) :=
      mul_le_mul habsj habsj (by positivity) (by positivity)
    have hmul : j * j ≤ (Int.ceil (2 * td.D) + td.q) * (Int.ceil (2 * td.D) + td.q) := by
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : j.natAbs ≤ (Int.ceil (2 * td.D) + td.q).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    have hM : (Int.ceil (2 * td.D) + td.q).natAbs = Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : (((Int.ceil (2 * td.D) + td.q).natAbs : ℤ)) = (Int.ceil (2 * td.D) + td.q) :=
        Int.natAbs_of_nonneg hM0
      have h2 : (((Int.ceil (2 * td.D) + td.q).toNat : ℤ)) = (Int.ceil (2 * td.D) + td.q) :=
        Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs

  have htri : (i - j).natAbs ≤ i.natAbs + j.natAbs := by
    simpa [sub_eq_add_neg] using (Int.natAbs_add_le i (-j))
  dsimp [SSU.Hilbert.distZ]
  calc
    (i - j).natAbs ≤ i.natAbs + j.natAbs := htri
    _ ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) + Int.toNat (Int.ceil (2 * td.D) + td.q) := by gcongr
    _ = 2 * Int.toNat (Int.ceil (2 * td.D) + td.q) := by ring

/-!
The `v`-analogue of the `u` reindexing lemmas above (TeX Step 4).
-/

/-- Canonical representative of an index `m` in the `v`-residue class `r`: `v₀(r) + m*q`. -/
def vFromIndex (r m : ℤ) : ℤ :=
  vResidue td r + m * td.q

theorem vFromIndex_vIndex_of_mem_vClass {v r : ℤ} (hv : v ∈ vClass td r) :
    vFromIndex (td := td) r (vIndex td r v) = v := by
  simpa [vFromIndex, mul_assoc, mul_left_comm, mul_comm] using
    (eq_vResidue_add_vIndex_mul_q_of_mem_vClass (td := td) (v := v) (r := r) hv).symm

theorem vIndex_vFromIndex_of_mem_vIndexSet {r m : ℤ} (hm : m ∈ vIndexSet (td := td) r) :
    vIndex td r (vFromIndex (td := td) r m) = m := by
  classical
  rcases Finset.mem_image.mp hm with ⟨v, hv, rfl⟩
  simpa [vFromIndex_vIndex_of_mem_vClass (td := td) (v := v) (r := r) hv]

theorem vFromIndex_mem_vClass_of_mem_vIndexSet {r m : ℤ} (hm : m ∈ vIndexSet (td := td) r) :
    vFromIndex (td := td) r m ∈ vClass td r := by
  classical
  rcases Finset.mem_image.mp hm with ⟨v, hv, hmEq⟩
  have : vFromIndex (td := td) r m = v := by
    simpa [hmEq] using (vFromIndex_vIndex_of_mem_vClass (td := td) (v := v) (r := r) hv)
  simpa [this] using hv

/-- `vFromIndex` lands in `vSet` whenever `m ∈ vIndexSet`. -/
theorem vFromIndex_mem_vSet_of_mem_vIndexSet {r m : ℤ} (hm : m ∈ vIndexSet (td := td) r) :
    vFromIndex (td := td) r m ∈ vSet td := by
  exact
    (vClass_subset_vSet (td := td) (r := r))
      (vFromIndex_mem_vClass_of_mem_vIndexSet (td := td) (r := r) hm)

/-- On `vIndexSet`, `vFromIndex` has residue `r` for the Step 4 partition map `v ↦ uResidue`. -/
theorem uResidue_vFromIndex_eq_of_mem_vIndexSet {r m : ℤ}
    (hm : m ∈ vIndexSet (td := td) r) :
    uResidue td (vFromIndex (td := td) r m) = r := by
  have hvClass : vFromIndex (td := td) r m ∈ vClass td r :=
    vFromIndex_mem_vClass_of_mem_vIndexSet (td := td) (r := r) hm
  exact (Finset.mem_filter.mp hvClass).2

theorem sum_vClass_eq_sum_vIndexSet {β : Type*} [AddCommMonoid β]
    (r : ℤ) (f : ℤ → β) :
    (vClass td r).sum (fun v => f v) =
      (vIndexSet (td := td) r).sum (fun m => f (vFromIndex (td := td) r m)) := by
  classical
  refine Finset.sum_nbij (s := vClass td r) (t := vIndexSet (td := td) r) (i := vIndex td r)
    (f := fun v => f v) (g := fun m => f (vFromIndex (td := td) r m)) ?_ ?_ ?_ ?_
  · intro v hv
    exact Finset.mem_image_of_mem (vIndex td r) hv
  · intro v1 hv1 v2 hv2 hEq
    have hInj := injOn_vIndex_vClass (td := td) (r := r)
    have hv1' : v1 ∈ (vClass td r : Set ℤ) := by simpa using hv1
    have hv2' : v2 ∈ (vClass td r : Set ℤ) := by simpa using hv2
    exact hInj hv1' hv2' hEq
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · intro v hv
    simpa [vFromIndex_vIndex_of_mem_vClass (td := td) (v := v) (r := r) hv]

theorem sum_vSet_eq_sum_residueClasses
    {α : Type*} [AddCommMonoid α] (f : ℤ → α) :
    (∑ v ∈ vSet td, f v)
      =
    ∑ r ∈ residuesV td, ∑ v ∈ vClass td r, f v := by
  classical
  have hMapsTo : ∀ v ∈ vSet td, uResidue td v ∈ residuesV td := by
    intro v hv
    exact mem_residuesV (td := td) v
  have hpart :=
    (Finset.sum_fiberwise_of_maps_to (s := vSet td) (t := residuesV td)
      (g := uResidue td) (f := fun v : ℤ => f v) hMapsTo)
  refine hpart.symm.trans ?_
  refine Finset.sum_congr rfl ?_
  intro r hr
  simp [vClass]

end ResiduePartitionV

end

end LargeSieve
end TypeII
end Engines
end SSU
