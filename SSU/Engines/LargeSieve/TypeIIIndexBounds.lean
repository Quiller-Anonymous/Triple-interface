import SSU.Engines.LargeSieve.TypeIISumDecompose
import SSU.Engines.LargeSieve.TypeIISumDecomposeV
import SSU.Hilbert.DistZ
import Mathlib.Algebra.Order.Floor.Defs

/-!
Deterministic bounds on the index sets (`uSet`, `vSet`) coming from the tube box constraints.

These lemmas are used to build a finite distance bound `distZ i j ≤ R` on the relevant finite
index sets, so the proved finite ℤ-indexed MV large sieve can be applied later.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace IndexBounds

theorem abs_u_le_U_of_mem_uSet (td : TubeData) {u : ℤ} (hu : u ∈ uSet td) :
    |(u : ℝ)| ≤ td.U := by
  classical
  rcases Finset.mem_image.mp hu with ⟨p, hpT, rfl⟩
  have hU : |(shearU td.a td.q p : ℝ)| ≤ td.U := (td.mem_T p hpT).2.2
  simpa using hU

theorem abs_v_le_twoD_of_mem_vSet (td : TubeData) (hD0 : 0 ≤ td.D) {v : ℤ} (hv : v ∈ vSet td) :
    |(v : ℝ)| ≤ 2 * td.D := by
  classical
  rcases Finset.mem_image.mp hv with ⟨p, hpT, rfl⟩
  have hbox : InIoc td.D (2 * td.D) p.1 := (td.mem_T p hpT).1
  -- Since `D < v` and `0 ≤ D`, we have `0 ≤ v`, hence `|v| = v`.
  have hv0 : 0 ≤ ((p.1 : ℤ) : ℝ) := le_trans hD0 (le_of_lt hbox.1)
  have hvle : ((p.1 : ℤ) : ℝ) ≤ 2 * td.D := hbox.2
  simpa [shearV, abs_of_nonneg hv0] using hvle

theorem mem_uSet_mem_Icc_ceilU (td : TubeData) {u : ℤ} (hu : u ∈ uSet td) :
    u ∈ Finset.Icc (-(Int.ceil td.U)) (Int.ceil td.U) := by
  classical
  have h1 : |(u : ℝ)| ≤ td.U := abs_u_le_U_of_mem_uSet (td := td) hu
  have h2 : td.U ≤ (Int.ceil td.U : ℝ) := Int.le_ceil td.U
  have h3 : |(u : ℝ)| ≤ (Int.ceil td.U : ℝ) := le_trans h1 h2
  -- Convert the real inequality into an integer `abs` inequality.
  have habsInt : |u| ≤ Int.ceil td.U := by
    -- `|u|` casts to `|u:ℝ|`.
    have : ((|u| : ℤ) : ℝ) ≤ (Int.ceil td.U : ℝ) := by
      simpa using h3
    exact_mod_cast this
  -- Turn `|u| ≤ M` into `-M ≤ u ≤ M`.
  have hIcc : (-(Int.ceil td.U) ≤ u ∧ u ≤ Int.ceil td.U) := by
    simpa using (abs_le.mp habsInt)
  simpa [Finset.mem_Icc] using hIcc

theorem distZ_le_two_mul_toNat_ceilU_of_mem_uSet
    (td : TubeData) (hU0 : 0 ≤ td.U)
    {i : ℤ} (hi : i ∈ uSet td) {j : ℤ} (hj : j ∈ uSet td) :
    SSU.Hilbert.distZ i j ≤ 2 * Int.toNat (Int.ceil td.U) := by
  classical
  -- Bound `|i|,|j|` by `ceil U` using the previous lemma.
  have hiIcc := mem_uSet_mem_Icc_ceilU (td := td) hi
  have hjIcc := mem_uSet_mem_Icc_ceilU (td := td) hj
  have hM0 : (0 : ℤ) ≤ Int.ceil td.U := Int.ceil_nonneg (α := ℝ) hU0
  -- From membership in `Icc`, get `|i| ≤ M` and `|j| ≤ M`.
  have habsi : |i| ≤ Int.ceil td.U := by
    have : -(Int.ceil td.U) ≤ i ∧ i ≤ Int.ceil td.U := by simpa [Finset.mem_Icc] using hiIcc
    exact (abs_le.mpr this)
  have habsj : |j| ≤ Int.ceil td.U := by
    have : -(Int.ceil td.U) ≤ j ∧ j ≤ Int.ceil td.U := by simpa [Finset.mem_Icc] using hjIcc
    exact (abs_le.mpr this)
  -- Convert to `natAbs` bounds.
  have hnat_i : i.natAbs ≤ Int.toNat (Int.ceil td.U) := by
    -- `i*i ≤ M*M` from `|i| ≤ M`.
    have hmulAbs : |i| * |i| ≤ (Int.ceil td.U) * (Int.ceil td.U) :=
      mul_le_mul habsi habsi (by positivity) (by positivity)
    have hmul : i * i ≤ (Int.ceil td.U) * (Int.ceil td.U) := by
      -- `|i|*|i| = i*i`.
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : i.natAbs ≤ (Int.ceil td.U).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    -- For `M ≥ 0`, `M.natAbs = M.toNat`.
    have hM : (Int.ceil td.U).natAbs = Int.toNat (Int.ceil td.U) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : ((Int.ceil td.U).natAbs : ℤ) = Int.ceil td.U := Int.natAbs_of_nonneg hM0
      have h2 : ((Int.ceil td.U).toNat : ℤ) = Int.ceil td.U := Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs
  have hnat_j : j.natAbs ≤ Int.toNat (Int.ceil td.U) := by
    have hmulAbs : |j| * |j| ≤ (Int.ceil td.U) * (Int.ceil td.U) :=
      mul_le_mul habsj habsj (by positivity) (by positivity)
    have hmul : j * j ≤ (Int.ceil td.U) * (Int.ceil td.U) := by
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : j.natAbs ≤ (Int.ceil td.U).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    have hM : (Int.ceil td.U).natAbs = Int.toNat (Int.ceil td.U) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : ((Int.ceil td.U).natAbs : ℤ) = Int.ceil td.U := Int.natAbs_of_nonneg hM0
      have h2 : ((Int.ceil td.U).toNat : ℤ) = Int.ceil td.U := Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs
  -- Triangle inequality for `natAbs`: `natAbs(i-j) ≤ natAbs i + natAbs j`.
  have htri : (i - j).natAbs ≤ i.natAbs + j.natAbs := by
    simpa [sub_eq_add_neg] using (Int.natAbs_add_le i (-j))
  -- Finish.
  dsimp [SSU.Hilbert.distZ]
  calc
    (i - j).natAbs ≤ i.natAbs + j.natAbs := htri
    _ ≤ Int.toNat (Int.ceil td.U) + Int.toNat (Int.ceil td.U) := by gcongr
    _ = 2 * Int.toNat (Int.ceil td.U) := by ring

theorem distZ_le_two_mul_toNat_ceilU_on_uSet (td : TubeData) (hU0 : 0 ≤ td.U) :
    ∀ i ∈ uSet td, ∀ j ∈ uSet td, SSU.Hilbert.distZ i j ≤ 2 * Int.toNat (Int.ceil td.U) := by
  intro i hi j hj
  exact distZ_le_two_mul_toNat_ceilU_of_mem_uSet (td := td) (hU0 := hU0) (hi := hi) (hj := hj)

theorem mem_vSet_mem_Icc_ceilTwoD (td : TubeData) (hD0 : 0 ≤ td.D) {v : ℤ} (hv : v ∈ vSet td) :
    v ∈ Finset.Icc (-(Int.ceil (2 * td.D))) (Int.ceil (2 * td.D)) := by
  classical
  have h1 : |(v : ℝ)| ≤ 2 * td.D := abs_v_le_twoD_of_mem_vSet (td := td) (hD0 := hD0) hv
  have h2 : 2 * td.D ≤ (Int.ceil (2 * td.D) : ℝ) := Int.le_ceil (2 * td.D)
  have h3 : |(v : ℝ)| ≤ (Int.ceil (2 * td.D) : ℝ) := le_trans h1 h2
  have habsInt : |v| ≤ Int.ceil (2 * td.D) := by
    have : ((|v| : ℤ) : ℝ) ≤ (Int.ceil (2 * td.D) : ℝ) := by
      simpa using h3
    exact_mod_cast this
  have hIcc : (-(Int.ceil (2 * td.D)) ≤ v ∧ v ≤ Int.ceil (2 * td.D)) := by
    simpa using (abs_le.mp habsInt)
  simpa [Finset.mem_Icc] using hIcc

theorem distZ_le_two_mul_toNat_ceilTwoD_of_mem_vSet
    (td : TubeData) (hD0 : 0 ≤ td.D)
    {i : ℤ} (hi : i ∈ vSet td) {j : ℤ} (hj : j ∈ vSet td) :
    SSU.Hilbert.distZ i j ≤ 2 * Int.toNat (Int.ceil (2 * td.D)) := by
  classical
  have hiIcc := mem_vSet_mem_Icc_ceilTwoD (td := td) (hD0 := hD0) hi
  have hjIcc := mem_vSet_mem_Icc_ceilTwoD (td := td) (hD0 := hD0) hj
  have hM0 : (0 : ℤ) ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (α := ℝ) (by nlinarith [hD0])
  have habsi : |i| ≤ Int.ceil (2 * td.D) := by
    have : -(Int.ceil (2 * td.D)) ≤ i ∧ i ≤ Int.ceil (2 * td.D) := by
      simpa [Finset.mem_Icc] using hiIcc
    exact (abs_le.mpr this)
  have habsj : |j| ≤ Int.ceil (2 * td.D) := by
    have : -(Int.ceil (2 * td.D)) ≤ j ∧ j ≤ Int.ceil (2 * td.D) := by
      simpa [Finset.mem_Icc] using hjIcc
    exact (abs_le.mpr this)
  have hnat_i : i.natAbs ≤ Int.toNat (Int.ceil (2 * td.D)) := by
    have hmulAbs : |i| * |i| ≤ (Int.ceil (2 * td.D)) * (Int.ceil (2 * td.D)) :=
      mul_le_mul habsi habsi (by positivity) (by positivity)
    have hmul : i * i ≤ (Int.ceil (2 * td.D)) * (Int.ceil (2 * td.D)) := by
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : i.natAbs ≤ (Int.ceil (2 * td.D)).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    have hM : (Int.ceil (2 * td.D)).natAbs = Int.toNat (Int.ceil (2 * td.D)) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : ((Int.ceil (2 * td.D)).natAbs : ℤ) = Int.ceil (2 * td.D) := Int.natAbs_of_nonneg hM0
      have h2 : ((Int.ceil (2 * td.D)).toNat : ℤ) = Int.ceil (2 * td.D) := Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs
  have hnat_j : j.natAbs ≤ Int.toNat (Int.ceil (2 * td.D)) := by
    have hmulAbs : |j| * |j| ≤ (Int.ceil (2 * td.D)) * (Int.ceil (2 * td.D)) :=
      mul_le_mul habsj habsj (by positivity) (by positivity)
    have hmul : j * j ≤ (Int.ceil (2 * td.D)) * (Int.ceil (2 * td.D)) := by
      simpa [abs_mul_abs_self] using hmulAbs
    have hnatAbs : j.natAbs ≤ (Int.ceil (2 * td.D)).natAbs :=
      (Int.natAbs_le_iff_mul_self_le).2 hmul
    have hM : (Int.ceil (2 * td.D)).natAbs = Int.toNat (Int.ceil (2 * td.D)) := by
      apply Nat.cast_injective (R := ℤ)
      have h1 : ((Int.ceil (2 * td.D)).natAbs : ℤ) = Int.ceil (2 * td.D) := Int.natAbs_of_nonneg hM0
      have h2 : ((Int.ceil (2 * td.D)).toNat : ℤ) = Int.ceil (2 * td.D) := Int.toNat_of_nonneg hM0
      simpa [h1, h2]
    simpa [hM] using hnatAbs
  have htri : (i - j).natAbs ≤ i.natAbs + j.natAbs := by
    simpa [sub_eq_add_neg] using (Int.natAbs_add_le i (-j))
  dsimp [SSU.Hilbert.distZ]
  calc
    (i - j).natAbs ≤ i.natAbs + j.natAbs := htri
    _ ≤ Int.toNat (Int.ceil (2 * td.D)) + Int.toNat (Int.ceil (2 * td.D)) := by gcongr
    _ = 2 * Int.toNat (Int.ceil (2 * td.D)) := by ring

theorem distZ_le_two_mul_toNat_ceilTwoD_on_vSet (td : TubeData) (hD0 : 0 ≤ td.D) :
    ∀ i ∈ vSet td, ∀ j ∈ vSet td, SSU.Hilbert.distZ i j ≤ 2 * Int.toNat (Int.ceil (2 * td.D)) := by
  intro i hi j hj
  exact distZ_le_two_mul_toNat_ceilTwoD_of_mem_vSet (td := td) (hD0 := hD0) (hi := hi) (hj := hj)

end IndexBounds

end

end LargeSieve
end TypeII
end Engines
end SSU
