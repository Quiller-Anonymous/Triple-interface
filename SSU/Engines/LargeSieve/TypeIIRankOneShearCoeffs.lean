import SSU.Engines.LargeSieve.TypeIIStep3Reduce
import SSU.Engines.LargeSieve.TypeIIStep4Reduce
import SSU.Engines.LargeSieve.TypeIIFiberEnergy

/-!
Rank-one (separated) coefficient algebra in shear coordinates.

This file is *deterministic*: it rewrites the Step 3/4 inner sums `innerSumUZ` / `innerSumVZ`
when the coefficient array factors through shear coordinates:

`F p = α (shearV p) * β (shearU p)`.

It is the first algebraic bridge needed before proving the TeX Step 3/4 large sieve bounds:
it expresses the inner sum as a `z`-exponential sum with coefficients given by sampling `α` along
the progression `v = v₀(u) + z*q` (and dually for Step 4).

TeX reference: `05b_SSU.tex`, lines 535–561.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

namespace RankOneShear

/-- Rank-one (separated) coefficient array in shear coordinates. -/
def coeff (td : TubeData) (α β : ℤ → ℂ) (p : TubePoint) : ℂ :=
  α (shearV p) * β (shearU td.a td.q p)

theorem exists_mem_fiberUZ_of_mem_zSet (td : TubeData) {u z : ℤ} (hz : z ∈ zSet td u) :
    ∃ p, p ∈ fiberUZ td u z := by
  classical
  -- `z ∈ image` gives a witness in the `u`-fiber with `zCoord = z`.
  rcases Finset.mem_image.1 hz with ⟨p, hpU, rfl⟩
  refine ⟨p, ?_⟩
  exact Finset.mem_filter.2 ⟨hpU, rfl⟩

theorem exists_mem_fiberVZ_of_mem_zSetV (td : TubeData) {v z : ℤ} (hz : z ∈ zSetV td v) :
    ∃ p, p ∈ fiberVZ td v z := by
  classical
  rcases Finset.mem_image.1 hz with ⟨p, hpV, rfl⟩
  refine ⟨p, ?_⟩
  exact Finset.mem_filter.2 ⟨hpV, rfl⟩

/-!
### Fiber coefficient sums

These are the basic “collapse the fiber sum to a single representative” lemmas.
They are convenient to reuse outside `innerSumUZ_eq_rankOne` / `innerSumVZ_eq_rankOne`.
-/

/-- On the `u,z`-fiber, the coefficient sum collapses to a single term for rank-one shear
coefficients. -/
theorem sum_fiberUZ_coeff_eq
    (td : TubeData) (α β : ℤ → ℂ) (u z : ℤ) (hz : z ∈ zSet td u) :
    (∑ p ∈ fiberUZ td u z, coeff td α β p) = β u * α (vResidue td u + z * td.q) := by
  classical
  rcases exists_mem_fiberUZ_of_mem_zSet (td := td) (u := u) (z := z) hz with ⟨p, hp⟩
  have hcard : (fiberUZ td u z).card ≤ 1 :=
    card_fiberUZ_le_one (td := td) (u := u) (z := z)
  have hpos : 0 < (fiberUZ td u z).card := Finset.card_pos.mpr ⟨p, hp⟩
  have hcardEq : (fiberUZ td u z).card = 1 :=
    Nat.le_antisymm hcard (Nat.succ_le_iff.2 hpos)
  rcases Finset.card_eq_one.1 hcardEq with ⟨a, ha⟩
  have hap : a = p := by
    have : p ∈ ({a} : Finset TubePoint) := by simpa [ha] using hp
    simpa using (Finset.mem_singleton.1 this).symm
  have hsum : (∑ q ∈ fiberUZ td u z, coeff td α β q) = coeff td α β p := by
    simpa [ha, hap]
  have hup : shearU td.a td.q p = u :=
    (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
  have hpz : zCoord td u p = z := (Finset.mem_filter.1 hp).2
  have hvp : shearV p = vResidue td u + z * td.q := by
    simpa [hpz] using (shearV_eq_vResidue_add_z_mul_q (td := td) (u := u) (p := p) hup)
  calc
    (∑ p ∈ fiberUZ td u z, coeff td α β p) = coeff td α β p := hsum
    _ = α (shearV p) * β (shearU td.a td.q p) := rfl
    _ = α (vResidue td u + z * td.q) * β u := by simp [hup, hvp, coeff]
    _ = β u * α (vResidue td u + z * td.q) := by ring

/-- Step 4 analogue of `sum_fiberUZ_coeff_eq`. -/
theorem sum_fiberVZ_coeff_eq
    (td : TubeData) (α β : ℤ → ℂ) (v z : ℤ) (hz : z ∈ zSetV td v) :
    (∑ p ∈ fiberVZ td v z, coeff td α β p) = α v * β (uResidue td v + z * td.q) := by
  classical
  rcases exists_mem_fiberVZ_of_mem_zSetV (td := td) (v := v) (z := z) hz with ⟨p, hp⟩
  have hcard : (fiberVZ td v z).card ≤ 1 :=
    card_fiberVZ_le_one (td := td) (v := v) (z := z)
  have hpos : 0 < (fiberVZ td v z).card := Finset.card_pos.mpr ⟨p, hp⟩
  have hcardEq : (fiberVZ td v z).card = 1 :=
    Nat.le_antisymm hcard (Nat.succ_le_iff.2 hpos)
  rcases Finset.card_eq_one.1 hcardEq with ⟨a, ha⟩
  have hap : a = p := by
    have : p ∈ ({a} : Finset TubePoint) := by simpa [ha] using hp
    simpa using (Finset.mem_singleton.1 this).symm
  have hsum : (∑ q ∈ fiberVZ td v z, coeff td α β q) = coeff td α β p := by
    simpa [ha, hap]
  have hvp : shearV p = v :=
    (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2
  have hpz : zCoordV td v p = z := (Finset.mem_filter.1 hp).2
  have hup : shearU td.a td.q p = uResidue td v + z * td.q := by
    simpa [hpz] using (shearU_eq_uResidue_add_z_mul_q (td := td) (v := v) (p := p) hvp)
  calc
    (∑ p ∈ fiberVZ td v z, coeff td α β p) = coeff td α β p := hsum
    _ = α (shearV p) * β (shearU td.a td.q p) := rfl
    _ = α v * β (uResidue td v + z * td.q) := by simp [hvp, hup, coeff]

/-- Step 3 inner sum for rank-one shear coefficients: sample `α` along `v = v₀(u) + z*q`. -/
theorem innerSumUZ_eq_rankOne
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) (u : ℤ) :
    innerSumUZ td ξ (coeff td α β) u
      =
    β u *
      ∑ z ∈ zSet td u,
        α (vResidue td u + z * td.q) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
  classical
  unfold innerSumUZ
  have hcoef :
      ∀ z, z ∈ zSet td u →
        (∑ p ∈ fiberUZ td u z, coeff td α β p) = β u * α (vResidue td u + z * td.q) := by
    intro z hz
    simpa using (sum_fiberUZ_coeff_eq (td := td) (α := α) (β := β) (u := u) (z := z) hz)
  calc
    (∑ z ∈ zSet td u,
        (∑ p ∈ fiberUZ td u z, coeff td α β p) * e (ξ * (u : ℝ) * (z : ℝ) / td.X))
        =
      ∑ z ∈ zSet td u,
        (β u * α (vResidue td u + z * td.q)) *
          e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      simp [hcoef z hz]
    _ = β u *
        ∑ z ∈ zSet td u,
          α (vResidue td u + z * td.q) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Step 4 inner sum for rank-one shear coefficients: sample `β` along `u = u₀(v) + z*q`. -/
theorem innerSumVZ_eq_rankOne
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) (v : ℤ) :
    innerSumVZ td ξ (coeff td α β) v
      =
    α v *
      ∑ z ∈ zSetV td v,
        β (uResidue td v + z * td.q) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
  classical
  unfold innerSumVZ
  have hcoef :
      ∀ z, z ∈ zSetV td v →
        (∑ p ∈ fiberVZ td v z, coeff td α β p) = α v * β (uResidue td v + z * td.q) := by
    intro z hz
    simpa using (sum_fiberVZ_coeff_eq (td := td) (α := α) (β := β) (v := v) (z := z) hz)
  calc
    (∑ z ∈ zSetV td v,
        (∑ p ∈ fiberVZ td v z, coeff td α β p) * e (ξ * (z : ℝ) * (v : ℝ) / td.X))
        =
      ∑ z ∈ zSetV td v,
        (α v * β (uResidue td v + z * td.q)) *
          e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
      refine Finset.sum_congr rfl ?_
      intro z hz
      simp [hcoef z hz]
    _ = α v *
        ∑ z ∈ zSetV td v,
          β (uResidue td v + z * td.q) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
      simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-!
### Specializations on residue classes (TeX Step 3/4 bookkeeping)

On a fixed residue class, the “residue representative” becomes constant. These are small
rewrites that help mirror `05b_SSU.tex` Step 3/4 more literally.
-/

theorem innerSumUZ_eq_rankOne_on_uClass
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) (r u : ℤ)
    (hu : u ∈ ResiduePartition.uClass td r) :
    innerSumUZ td ξ (coeff td α β) u
      =
    β u *
      ∑ z ∈ zSet td u,
        α (r + z * td.q) * e (ξ * (u : ℝ) * (z : ℝ) / td.X) := by
  have hr : vResidue td u = r := by
    simpa [ResiduePartition.uClass] using (Finset.mem_filter.1 hu).2
  simpa [hr] using
    (innerSumUZ_eq_rankOne (td := td) (ξ := ξ) (α := α) (β := β) (u := u))

theorem innerSumVZ_eq_rankOne_on_vClass
    (td : TubeData) (ξ : ℝ) (α β : ℤ → ℂ) (r v : ℤ)
    (hv : v ∈ ResiduePartitionV.vClass td r) :
    innerSumVZ td ξ (coeff td α β) v
      =
    α v *
      ∑ z ∈ zSetV td v,
        β (r + z * td.q) * e (ξ * (z : ℝ) * (v : ℝ) / td.X) := by
  have hr : uResidue td v = r := by
    simpa [ResiduePartitionV.vClass] using (Finset.mem_filter.1 hv).2
  simpa [hr] using
    (innerSumVZ_eq_rankOne (td := td) (ξ := ξ) (α := α) (β := β) (v := v))

end RankOneShear

end

end LargeSieve
end TypeII
end Engines
end SSU
