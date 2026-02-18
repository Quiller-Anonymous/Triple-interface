import SSU.Engines.LargeSieve.BGTubeZSetGeometry
import SSU.Engines.LargeSieve.TypeIIFiberLargeSieveFromFiniteLargeSieve
import SSU.Engines.LargeSieve.TypeIIRankOneShearCoeffs
import SSU.Engines.LargeSieve.TypeIIConstCoeffMV

/-!
BG-specialized wrappers for residue-index MV application.

These lemmas discharge the `hZeq` hypotheses in the new
`..._on_zSet...` / `..._on_zSetV...` wrappers using pure BG geometry
(`zSet`/`zSetV` constancy on residue classes under regime assumptions).
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace BGTubeBridge

open SSU.Engines.BGTube
open ResidueIndexLargeSieve
open FiberFromFiniteLargeSieve
open RankOneShear
open ZBoxRewrite
open ZBoxToFin

/-- Step 3 extraction helper: on a fixed residue progression, rank-one shear fiber sums are
uniform in the progression index once `β` is constant on that progression. -/
theorem sum_fiberUZ_uFromIndex_eq_ref_on_zSet_of_rankOneShear_of_regime
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
      ∀ z : ℤ, z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m0) →
        (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z,
            RankOneShear.coeff td α β p)
          =
        (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z,
            RankOneShear.coeff td α β p) := by
  classical
  intro td m hm z hz0
  have hZeq :
      zSet td (ResiduePartition.uFromIndex (td := td) r m)
        = zSet td (ResiduePartition.uFromIndex (td := td) r m0) :=
    zSet_eq_uFromIndex_of_mem_uIndexSet_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (m₁ := m) (m₂ := m0)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper) hm hm0
  have hz : z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m) := by
    simpa [hZeq] using hz0
  have hsum_m :
      (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z,
          RankOneShear.coeff td α β p)
        =
      β (ResiduePartition.uFromIndex (td := td) r m) *
        α (vResidue td (ResiduePartition.uFromIndex (td := td) r m) + z * td.q) := by
    simpa using
      (RankOneShear.sum_fiberUZ_coeff_eq (td := td) (α := α) (β := β)
        (u := ResiduePartition.uFromIndex (td := td) r m) (z := z) hz)
  have hsum_0 :
      (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z,
          RankOneShear.coeff td α β p)
        =
      β (ResiduePartition.uFromIndex (td := td) r m0) *
        α (vResidue td (ResiduePartition.uFromIndex (td := td) r m0) + z * td.q) := by
    simpa using
      (RankOneShear.sum_fiberUZ_coeff_eq (td := td) (α := α) (β := β)
        (u := ResiduePartition.uFromIndex (td := td) r m0) (z := z) hz0)
  have hv_m :
      vResidue td (ResiduePartition.uFromIndex (td := td) r m) = r :=
    ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet (td := td) (r := r) (m := m) hm
  have hv_0 :
      vResidue td (ResiduePartition.uFromIndex (td := td) r m0) = r :=
    ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet (td := td) (r := r) (m := m0) hm0
  have hβ : β (ResiduePartition.uFromIndex (td := td) r m)
      = β (ResiduePartition.uFromIndex (td := td) r m0) := by
    simpa [td] using (hβconst m hm)
  calc
    (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z,
        RankOneShear.coeff td α β p)
      = β (ResiduePartition.uFromIndex (td := td) r m) *
          α (vResidue td (ResiduePartition.uFromIndex (td := td) r m) + z * td.q) := hsum_m
    _ = β (ResiduePartition.uFromIndex (td := td) r m0) * α (r + z * td.q) := by
          rw [hβ, hv_m]
    _ = β (ResiduePartition.uFromIndex (td := td) r m0) *
          α (vResidue td (ResiduePartition.uFromIndex (td := td) r m0) + z * td.q) := by
          simp [hv_0]
    _ = (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z,
          RankOneShear.coeff td α β p) := hsum_0.symm

/-- Step 4 extraction helper: on a fixed residue progression, rank-one shear fiber sums are
uniform in the progression index once `α` is constant on that progression. -/
theorem sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_of_rankOneShear_of_regime
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
      ∀ z : ℤ, z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) →
        (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z,
            RankOneShear.coeff td α β p)
          =
        (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z,
            RankOneShear.coeff td α β p) := by
  classical
  intro td m hm z hz0
  have hZeq :
      zSetV td (ResiduePartitionV.vFromIndex (td := td) r m)
        = zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) :=
    zSetV_eq_vFromIndex_of_mem_vIndexSet_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (m₁ := m) (m₂ := m0)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper) hm hm0
  have hz : z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m) := by
    simpa [hZeq] using hz0
  have hsum_m :
      (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z,
          RankOneShear.coeff td α β p)
        =
      α (ResiduePartitionV.vFromIndex (td := td) r m) *
        β (uResidue td (ResiduePartitionV.vFromIndex (td := td) r m) + z * td.q) := by
    simpa using
      (RankOneShear.sum_fiberVZ_coeff_eq (td := td) (α := α) (β := β)
        (v := ResiduePartitionV.vFromIndex (td := td) r m) (z := z) hz)
  have hsum_0 :
      (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z,
          RankOneShear.coeff td α β p)
        =
      α (ResiduePartitionV.vFromIndex (td := td) r m0) *
        β (uResidue td (ResiduePartitionV.vFromIndex (td := td) r m0) + z * td.q) := by
    simpa using
      (RankOneShear.sum_fiberVZ_coeff_eq (td := td) (α := α) (β := β)
        (v := ResiduePartitionV.vFromIndex (td := td) r m0) (z := z) hz0)
  have hu_m :
      uResidue td (ResiduePartitionV.vFromIndex (td := td) r m) = r :=
    ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet (td := td) (r := r) (m := m) hm
  have hu_0 :
      uResidue td (ResiduePartitionV.vFromIndex (td := td) r m0) = r :=
    ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet (td := td) (r := r) (m := m0) hm0
  have hα : α (ResiduePartitionV.vFromIndex (td := td) r m)
      = α (ResiduePartitionV.vFromIndex (td := td) r m0) := by
    simpa [td] using (hαconst m hm)
  calc
    (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z,
        RankOneShear.coeff td α β p)
      = α (ResiduePartitionV.vFromIndex (td := td) r m) *
          β (uResidue td (ResiduePartitionV.vFromIndex (td := td) r m) + z * td.q) := hsum_m
    _ = α (ResiduePartitionV.vFromIndex (td := td) r m0) * β (r + z * td.q) := by
          rw [hα, hu_m]
    _ = α (ResiduePartitionV.vFromIndex (td := td) r m0) *
          β (uResidue td (ResiduePartitionV.vFromIndex (td := td) r m0) + z * td.q) := by
          simp [hu_0]
    _ = (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z,
          RankOneShear.coeff td α β p) := hsum_0.symm

/-- Step 3 MV wrapper specialized to rank-one shear coefficients; the `hEqOn` premise is
discharged by geometry + residue-class constancy of `β`. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  intro td
  have hZeq :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        zSet td (ResiduePartition.uFromIndex (td := td) r m)
          = zSet td (ResiduePartition.uFromIndex (td := td) r m0) := by
    intro m hm
    exact zSet_eq_uFromIndex_of_mem_uIndexSet_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (m₁ := m) (m₂ := m0)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper) hm hm0
  have hEqOn :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        ∀ z : ℤ, z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m0) →
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z,
              RankOneShear.coeff td α β p)
            =
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z,
              RankOneShear.coeff td α β p) :=
    sum_fiberUZ_uFromIndex_eq_ref_on_zSet_of_rankOneShear_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (α := α) (β := β) (m0 := m0) hm0 hβconst
  exact
    step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet_finiteLargeSieve
      (td := td) (hU0 := hU0) (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := RankOneShear.coeff td α β) (m0 := m0) (hm0 := hm0)
      (hZeq := hZeq) (hEqOn := hEqOn)

/-- Step 4 MV wrapper specialized to rank-one shear coefficients; the `hEqOn` premise is
discharged by geometry + residue-class constancy of `α`. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td (RankOneShear.coeff td α β)
              (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  intro td
  have hZeq :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        zSetV td (ResiduePartitionV.vFromIndex (td := td) r m)
          = zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) := by
    intro m hm
    exact zSetV_eq_vFromIndex_of_mem_vIndexSet_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (m₁ := m) (m₂ := m0)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper) hm hm0
  have hEqOn :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        ∀ z : ℤ, z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) →
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z,
              RankOneShear.coeff td α β p)
            =
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z,
              RankOneShear.coeff td α β p) :=
    sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_of_rankOneShear_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (α := α) (β := β) (m0 := m0) hm0 hαconst
  exact
    step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_finiteLargeSieve
      (td := td) (hD0 := hD0) (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := RankOneShear.coeff td α β) (m0 := m0) (hm0 := hm0)
      (hZeq := hZeq) (hEqOn := hEqOn)

/-- Step 3 wrapper: under BG regime assumptions, `hZeq` is geometric and only `hEqOn` remains. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet_finiteLargeSieve_of_regime
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (F : TubePoint → ℂ)
    (m0 : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    m0 ∈ ResiduePartition.uIndexSet (td := td) r →
    (∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
      ∀ z : ℤ, z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m0) →
        (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z, F p)
          =
        (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z, F p)) →
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  intro td hm0 hEqOn
  have hZeq :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        zSet td (ResiduePartition.uFromIndex (td := td) r m)
          = zSet td (ResiduePartition.uFromIndex (td := td) r m0) := by
    intro m hm
    exact zSet_eq_uFromIndex_of_mem_uIndexSet_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (m₁ := m) (m₂ := m0)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper) hm hm0
  exact step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet_finiteLargeSieve
      (td := td) (hU0 := hU0) (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := F) (m0 := m0) (hm0 := hm0) (hZeq := hZeq) (hEqOn := hEqOn)

/-- Step 4 wrapper: under BG regime assumptions, `hZeq` is geometric and only `hEqOn` remains. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_finiteLargeSieve_of_regime
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (F : TubePoint → ℂ)
    (m0 : ℤ) :
    let td := tubeDataOfBGTube P a q hq hcop
    m0 ∈ ResiduePartitionV.vIndexSet (td := td) r →
    (∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
      ∀ z : ℤ, z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) →
        (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
          =
        (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z, F p)) →
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  intro td hm0 hEqOn
  have hZeq :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        zSetV td (ResiduePartitionV.vFromIndex (td := td) r m)
          = zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) := by
    intro m hm
    exact zSetV_eq_vFromIndex_of_mem_vIndexSet_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (m₁ := m) (m₂ := m0)
      (ha0 := ha0) (hlower := hlower) (hupper := hupper) hm hm0
  exact step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_finiteLargeSieve
      (td := td) (hD0 := hD0) (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := F) (m0 := m0) (hm0 := hm0) (hZeq := hZeq) (hEqOn := hEqOn)

/-- On a fixed Step 3 residue progression, any coefficient function invariant under
`[ZMOD q]` is constant on `uFromIndex`. -/
theorem beta_const_on_uFromIndex_of_modEq
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (r : ℤ)
    (β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
      β (ResiduePartition.uFromIndex (td := td) r m)
        = β (ResiduePartition.uFromIndex (td := td) r m0) := by
  intro td m hm
  have hrm :
      vResidue td (ResiduePartition.uFromIndex (td := td) r m) = r :=
    ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet (td := td) (r := r) hm
  have hr0 :
      vResidue td (ResiduePartition.uFromIndex (td := td) r m0) = r :=
    ResiduePartition.vResidue_uFromIndex_eq_of_mem_uIndexSet (td := td) (r := r) hm0
  have hmodm :
      ResiduePartition.uFromIndex (td := td) r m
        ≡ uResidue td r [ZMOD td.q] :=
    ResiduePartition.modEq_uResidue_of_eq_vResidue (td := td) (u := ResiduePartition.uFromIndex (td := td) r m)
      (r := r) hrm
  have hmod0 :
      ResiduePartition.uFromIndex (td := td) r m0
        ≡ uResidue td r [ZMOD td.q] :=
    ResiduePartition.modEq_uResidue_of_eq_vResidue
      (td := td) (u := ResiduePartition.uFromIndex (td := td) r m0) (r := r) hr0
  have hmod :
      ResiduePartition.uFromIndex (td := td) r m
        ≡ ResiduePartition.uFromIndex (td := td) r m0 [ZMOD td.q] :=
    hmodm.trans hmod0.symm
  have hβmod' :
      ∀ u₁ u₂ : ℤ, u₁ ≡ u₂ [ZMOD td.q] → β u₁ = β u₂ := by
    simpa [td] using hβmod
  exact hβmod' _ _ hmod

/-- On a fixed Step 4 residue progression, any coefficient function invariant under
`[ZMOD q]` is constant on `vFromIndex`. -/
theorem alpha_const_on_vFromIndex_of_modEq
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (r : ℤ)
    (α : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
      α (ResiduePartitionV.vFromIndex (td := td) r m)
        = α (ResiduePartitionV.vFromIndex (td := td) r m0) := by
  intro td m hm
  have hrm :
      uResidue td (ResiduePartitionV.vFromIndex (td := td) r m) = r :=
    ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet (td := td) (r := r) hm
  have hr0 :
      uResidue td (ResiduePartitionV.vFromIndex (td := td) r m0) = r :=
    ResiduePartitionV.uResidue_vFromIndex_eq_of_mem_vIndexSet (td := td) (r := r) hm0
  have hmodm :
      ResiduePartitionV.vFromIndex (td := td) r m
        ≡ vResidue td r [ZMOD td.q] :=
    ResiduePartitionV.modEq_vResidue_of_eq_uResidue
      (td := td) (v := ResiduePartitionV.vFromIndex (td := td) r m) (r := r) hrm
  have hmod0 :
      ResiduePartitionV.vFromIndex (td := td) r m0
        ≡ vResidue td r [ZMOD td.q] :=
    ResiduePartitionV.modEq_vResidue_of_eq_uResidue
      (td := td) (v := ResiduePartitionV.vFromIndex (td := td) r m0) (r := r) hr0
  have hmod :
      ResiduePartitionV.vFromIndex (td := td) r m
        ≡ ResiduePartitionV.vFromIndex (td := td) r m0 [ZMOD td.q] :=
    hmodm.trans hmod0.symm
  have hαmod' :
      ∀ v₁ v₂ : ℤ, v₁ ≡ v₂ [ZMOD td.q] → α v₁ = α v₂ := by
    simpa [td] using hαmod
  exact hαmod' _ _ hmod

/-- Step 3 rank-one wrapper with regime geometry and modulo-invariant `β`; this removes the
explicit progression-constancy hypothesis. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
  intro td
  refine step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime
    (P := P) (a := a) (q := q) hq hcop
    (ha0 := ha0) (hlower := hlower) (hupper := hupper)
    (r := r) (ξ := ξ) (hξ0 := hξ0)
    (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
    (α := α) (β := β) (m0 := m0) hm0 ?_
  exact beta_const_on_uFromIndex_of_modEq
    (P := P) (a := a) (q := q) hq hcop
    (r := r) (β := β) (m0 := m0) hm0 hβmod

/-- Step 4 rank-one wrapper with regime geometry and modulo-invariant `α`; this removes the
explicit progression-constancy hypothesis. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td (RankOneShear.coeff td α β)
              (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
  intro td
  refine step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime
    (P := P) (a := a) (q := q) hq hcop
    (ha0 := ha0) (hlower := hlower) (hupper := hupper)
    (r := r) (ξ := ξ) (hξ0 := hξ0)
    (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
    (α := α) (β := β) (m0 := m0) hm0 ?_
  exact alpha_const_on_vFromIndex_of_modEq
    (P := P) (a := a) (q := q) hq hcop
    (r := r) (α := α) (m0 := m0) hm0 hαmod

/-- Step 3 rank-one/modEq wrapper with a residue-class witness `u0 ∈ uClass r` (so no explicit
`m0 ∈ uIndexSet r` needs to be supplied). -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2) := by
  intro td
  have hu0' : u0 ∈ ResiduePartition.uClass (td := td) r := by
    simpa [td] using hu0
  let m0 : ℤ := ResiduePartition.uIndex td r u0
  have hm0 : m0 ∈ ResiduePartition.uIndexSet (td := td) r := by
    refine Finset.mem_image.mpr ?_
    exact ⟨u0, hu0', by simp [m0]⟩
  have huFrom :
      ResiduePartition.uFromIndex (td := td) r m0 = u0 := by
    simpa [m0] using
      (ResiduePartition.uFromIndex_uIndex_of_mem_uClass
        (td := td) (u := u0) (r := r) hu0')
  have hmain :
      (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
        ≤
      (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
          (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            ‖coeffUZFin td (RankOneShear.coeff td α β)
                (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
    simpa [td] using
      (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (m0 := m0) hm0 (hβmod := hβmod))
  simpa [huFrom] using hmain

/-- Interval-geometry wrapper for
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by
          have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
            exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
          simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (u0 := u0) hu0 (hβmod := hβmod))

/-- Step 4 rank-one/modEq wrapper with a residue-class witness `v0 ∈ vClass r` (so no explicit
`m0 ∈ vIndexSet r` needs to be supplied). -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2) := by
  intro td
  have hv0' : v0 ∈ ResiduePartitionV.vClass (td := td) r := by
    simpa [td] using hv0
  let m0 : ℤ := ResiduePartitionV.vIndex td r v0
  have hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := td) r := by
    refine Finset.mem_image.mpr ?_
    exact ⟨v0, hv0', by simp [m0]⟩
  have hvFrom :
      ResiduePartitionV.vFromIndex (td := td) r m0 = v0 := by
    simpa [m0] using
      (ResiduePartitionV.vFromIndex_vIndex_of_mem_vClass
        (td := td) (v := v0) (r := r) hv0')
  have hmain :
      (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
        ≤
      (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β)
                (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
    simpa [td] using
      (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (m0 := m0) hm0 (hαmod := hαmod))
  simpa [hvFrom] using hmain

/-- Interval-geometry wrapper for
`step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by
          have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
            exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
          simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (v0 := v0) hv0 (hαmod := hαmod))

/-- Step 3 rank-one/modEq bound in residue-class (`uClass`) form, using a witness `u0 ∈ uClass r`
for the reference coefficient side. -/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2) := by
  intro td
  have hclass :
      (∑ u ∈ ResiduePartition.uClass td r,
          ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
        =
      (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2) := by
    simpa using
      (sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet
        (td := td) (ξ := ξ) (F := RankOneShear.coeff td α β) (r := r))
  calc
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      =
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2) := hclass
    _ ≤
      (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
          (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2) :=
      step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (u0 := u0) hu0 (hβmod := hβmod)

/-- Step 4 rank-one/modEq bound in residue-class (`vClass`) form, using a witness `v0 ∈ vClass r`
for the reference coefficient side. -/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2) := by
  intro td
  have hclass :
      (∑ v ∈ ResiduePartitionV.vClass td r,
          ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
        =
      (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2) := by
    simpa using
      (sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet
        (td := td) (ξ := ξ) (F := RankOneShear.coeff td α β) (r := r))
  calc
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      =
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2) := hclass
    _ ≤
      (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2) :=
      step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (v0 := v0) hv0 (hαmod := hαmod)

/-- Interval-geometry wrapper for
`step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by
          have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
            exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
          simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (u0 := u0) hu0 (hβmod := hβmod))

/-- Interval-geometry wrapper for
`step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by
          have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
            exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
          simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (v0 := v0) hv0 (hαmod := hαmod))

/-- Step 3 rank-one/regime wrapper with an explicit one-add-log bound for the MV constant. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_one_add_log
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2)) := by
  intro td
  have hmain :=
    step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) hm0 (hβconst := hβconst)
  have hC :=
    (uIndexSet_finiteLargeSieve_C_le_one_add_log
      (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
      (hξH := by simpa using hξH) (hXH := hXH))
  have hC' :
      (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C
        ≤
      (zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))) := by
    simpa [abs_neg] using hC
  have hmul :
      (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            ‖coeffUZFin td (RankOneShear.coeff td α β)
                (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2)
        ≤
      ((zBoxN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            ‖coeffUZFin td (RankOneShear.coeff td α β)
                (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_right hC' ?_
    positivity
  exact hmain.trans hmul

/-- Interval-geometry wrapper for
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_one_add_log`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_one_add_log_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = β (ResiduePartition.uFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_one_add_log
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hβconst := hβconst))

/-- Step 3 rank-one/modEq wrapper with an explicit one-add-log bound for the MV constant. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2)) := by
  intro td
  have hβconst :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        β (ResiduePartition.uFromIndex (td := td) r m)
          = β (ResiduePartition.uFromIndex (td := td) r m0) :=
    beta_const_on_uFromIndex_of_modEq
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (β := β) (m0 := m0) (hm0 := hm0) (hβmod := hβmod)
  exact
    step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_one_add_log
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hβconst := hβconst)

/-- Interval-geometry wrapper for
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hβmod := hβmod))

/-- Step 4 rank-one/regime wrapper with an explicit one-add-log bound for the MV constant. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_one_add_log
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β)
                (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2)) := by
  intro td
  have hmain :=
    step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) hm0 (hαconst := hαconst)
  have hC :=
    (vIndexSet_finiteLargeSieve_C_le_one_add_log
      (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
      (hξH := by simpa using hξH) (hXH := hXH))
  have hC' :
      (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C
        ≤
      (zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))) := by
    simpa [abs_neg] using hC
  have hmul :
      (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β)
                (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2)
        ≤
      (((zBoxVN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β)
                (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2)) := by
    refine mul_le_mul_of_nonneg_right hC' ?_
    positivity
  exact hmain.trans hmul

/-- Interval-geometry wrapper for
`step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_one_add_log`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_one_add_log_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r →
        α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m)
          = α (ResiduePartitionV.vFromIndex (td := tubeDataOfBGTube P a q hq hcop) r m0)) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β)
                (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_one_add_log
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hαconst := hαconst))

/-- Step 4 rank-one/modEq wrapper with an explicit one-add-log bound for the MV constant. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β)
                (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2)) := by
  intro td
  have hαconst :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        α (ResiduePartitionV.vFromIndex (td := td) r m)
          = α (ResiduePartitionV.vFromIndex (td := td) r m0) :=
    alpha_const_on_vFromIndex_of_modEq
      (P := P) (a := a) (q := q) hq hcop
      (r := r) (α := α) (m0 := m0) (hm0 := hm0) (hαmod := hαmod)
  exact
    step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_one_add_log
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hαconst := hαconst)

/-- Interval-geometry wrapper for
`step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (m0 : ℤ)
    (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β)
                (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hαmod := hαmod))

/-- Step 3 one-add-log wrapper with a residue-class witness `u0 ∈ uClass r` (so no explicit
`m0 ∈ uIndexSet r` needs to be supplied). -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2)) := by
  intro td
  have hu0' : u0 ∈ ResiduePartition.uClass (td := td) r := by
    simpa [td] using hu0
  let m0 : ℤ := ResiduePartition.uIndex td r u0
  have hm0 : m0 ∈ ResiduePartition.uIndexSet (td := td) r := by
    refine Finset.mem_image.mpr ?_
    exact ⟨u0, hu0', by simp [m0]⟩
  have huFrom :
      ResiduePartition.uFromIndex (td := td) r m0 = u0 := by
    simpa [m0] using
      (ResiduePartition.uFromIndex_uIndex_of_mem_uClass
        (td := td) (u := u0) (r := r) hu0')
  have hmain :
      (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
        ≤
      (((zBoxN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            ‖coeffUZFin td (RankOneShear.coeff td α β)
                (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2)) := by
    simpa [td] using
      (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (m0 := m0) hm0 (hβmod := hβmod))
  simpa [huFrom] using hmain

/-- Interval-geometry wrapper for
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (u0 := u0) (hu0 := hu0) (hβmod := hβmod))

/-- Step 4 one-add-log wrapper with a residue-class witness `v0 ∈ vClass r` (so no explicit
`m0 ∈ vIndexSet r` needs to be supplied). -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2)) := by
  intro td
  have hv0' : v0 ∈ ResiduePartitionV.vClass (td := td) r := by
    simpa [td] using hv0
  let m0 : ℤ := ResiduePartitionV.vIndex td r v0
  have hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := td) r := by
    refine Finset.mem_image.mpr ?_
    exact ⟨v0, hv0', by simp [m0]⟩
  have hvFrom :
      ResiduePartitionV.vFromIndex (td := td) r m0 = v0 := by
    simpa [m0] using
      (ResiduePartitionV.vFromIndex_vIndex_of_mem_vClass
        (td := td) (v := v0) (r := r) hv0')
  have hmain :
      (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
        ≤
      (((zBoxVN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
            (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
              ‖coeffVZFin td (RankOneShear.coeff td α β)
                  (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2)) := by
    simpa [td] using
      (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (m0 := m0) hm0 (hαmod := hαmod))
  simpa [hvFrom] using hmain

/-- Interval-geometry wrapper for
`step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (v0 := v0) (hv0 := hv0) (hαmod := hαmod))

/-- Step 3 one-add-log bound in residue-class (`uClass`) form, using a witness `u0 ∈ uClass r`
for the reference coefficient side. -/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2)) := by
  intro td
  have hclass :
      (∑ u ∈ ResiduePartition.uClass td r,
          ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
        =
      (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2) := by
    simpa using
      (sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet
        (td := td) (ξ := ξ) (F := RankOneShear.coeff td α β) (r := r))
  calc
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      =
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2) := hclass
    _ ≤
      (((zBoxN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2)) :=
      step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (u0 := u0) hu0 (hβmod := hβmod)

/-- Interval-geometry wrapper for
`step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (u0 := u0) (hu0 := hu0) (hβmod := hβmod))

/-- Step 3 one-add-log bound in residue-class form, with RHS expressed by the class fiber energy
(`∑_{u∈uClass} ∑_{z∈zSet(u)} ‖⋯‖²`) instead of a reference `coeffUZFin` witness. -/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_uClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
      (∑ u ∈ ResiduePartition.uClass td r,
          ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  intro td
  have hu0' : u0 ∈ ResiduePartition.uClass (td := td) r := by
    simpa [td] using hu0
  have hmain :
      (∑ u ∈ ResiduePartition.uClass td r,
          ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
        ≤
      (((zBoxN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2)) := by
    simpa [td] using
      step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (u0 := u0) hu0 (hβmod := hβmod)
  have hcoeffEq :
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2)
        =
      (∑ z ∈ zSet td u0, ‖∑ p ∈ fiberUZ td u0 z, RankOneShear.coeff td α β p‖ ^ 2) := by
    simpa using
      ConstCoeffMV.sum_univ_norm_coeffUZFin_sq_eq_sum_zSet_norm_fiberUZ_sum_sq
        (td := td) (F := RankOneShear.coeff td α β) (u := u0)
  have hzLe :
      (∑ z ∈ zSet td u0, ‖∑ p ∈ fiberUZ td u0 z, RankOneShear.coeff td α β p‖ ^ 2)
        ≤
      (∑ u ∈ ResiduePartition.uClass td r,
        ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, RankOneShear.coeff td α β p‖ ^ 2) := by
    have hnonneg :
        ∀ u : ℤ, u ∈ ResiduePartition.uClass td r →
          0 ≤ (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, RankOneShear.coeff td α β p‖ ^ 2 : ℝ) := by
      intro u hu
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    exact Finset.single_le_sum hnonneg hu0'
  have hCnonneg :
      0 ≤
      ((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) := by
    have hq0 : 0 ≤ td.q := le_of_lt td.q_pos
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      exact Real.log_nonneg harg1
    have hmult_nonneg :
        0 ≤ (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))) := by
      have habs_pos : 0 < |ξ| := abs_pos.mpr hξ0
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := mul_pos habs_pos (by exact_mod_cast td.q_pos)
      have hx_over : 0 ≤ td.X / (|ξ| * (td.q : ℝ)) := div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
      have hlog1 : 0 ≤ 1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) := by linarith
      exact mul_nonneg hx_over hlog1
    exact add_nonneg (by positivity) hmult_nonneg
  have hmul :
      (((zBoxN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td (RankOneShear.coeff td α β) u0 k‖ ^ 2))
      ≤
      (((zBoxN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
        (∑ u ∈ ResiduePartition.uClass td r,
          ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, RankOneShear.coeff td α β p‖ ^ 2)) := by
    rw [hcoeffEq]
    exact mul_le_mul_of_nonneg_left hzLe hCnonneg
  exact hmain.trans hmul

/-- Interval-geometry wrapper for
`step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_uClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_uClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (u0 : ℤ)
    (hu0 : u0 ∈ ResiduePartition.uClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
      (∑ u ∈ ResiduePartition.uClass td r,
          ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_uClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (u0 := u0) (hu0 := hu0) (hβmod := hβmod))

/-- Step 4 one-add-log bound in residue-class (`vClass`) form, using a witness `v0 ∈ vClass r`
for the reference coefficient side. -/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2)) := by
  intro td
  have hclass :
      (∑ v ∈ ResiduePartitionV.vClass td r,
          ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
        =
      (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
              (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2) := by
    simpa using
      (sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet
        (td := td) (ξ := ξ) (F := RankOneShear.coeff td α β) (r := r))
  calc
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      =
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β)
            (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2) := hclass
    _ ≤
      (((zBoxVN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
            (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
              ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2)) :=
      step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (v0 := v0) hv0 (hαmod := hαmod)

/-- Interval-geometry wrapper for
`step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (v0 := v0) (hv0 := hv0) (hαmod := hαmod))

/-- Step 4 one-add-log bound in residue-class form, with RHS expressed by the class fiber energy
(`∑_{v∈vClass} ∑_{z∈zSetV(v)} ‖⋯‖²`) instead of a reference `coeffVZFin` witness. -/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_vClass
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
      (∑ v ∈ ResiduePartitionV.vClass td r,
          ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  intro td
  have hv0' : v0 ∈ ResiduePartitionV.vClass (td := td) r := by
    simpa [td] using hv0
  have hmain :
      (∑ v ∈ ResiduePartitionV.vClass td r,
          ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
        ≤
      (((zBoxVN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2)) := by
    simpa [td] using
      step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (v0 := v0) hv0 (hαmod := hαmod)
  have hcoeffEq :
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2)
        =
      (∑ z ∈ zSetV td v0, ‖∑ p ∈ fiberVZ td v0 z, RankOneShear.coeff td α β p‖ ^ 2) := by
    simpa using
      ConstCoeffMV.sum_univ_norm_coeffVZFin_sq_eq_sum_zSetV_norm_fiberVZ_sum_sq
        (td := td) (F := RankOneShear.coeff td α β) (v := v0)
  have hzLe :
      (∑ z ∈ zSetV td v0, ‖∑ p ∈ fiberVZ td v0 z, RankOneShear.coeff td α β p‖ ^ 2)
        ≤
      (∑ v ∈ ResiduePartitionV.vClass td r,
        ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, RankOneShear.coeff td α β p‖ ^ 2) := by
    have hnonneg :
        ∀ v : ℤ, v ∈ ResiduePartitionV.vClass td r →
          0 ≤ (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, RankOneShear.coeff td α β p‖ ^ 2 : ℝ) := by
      intro v hv
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    exact Finset.single_le_sum hnonneg hv0'
  have hCnonneg :
      0 ≤
      ((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) := by
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by positivity)
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      exact Real.log_nonneg harg1
    have hmult_nonneg :
        0 ≤ (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))) := by
      have habs_pos : 0 < |ξ| := abs_pos.mpr hξ0
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := mul_pos habs_pos (by exact_mod_cast td.q_pos)
      have hx_over : 0 ≤ td.X / (|ξ| * (td.q : ℝ)) := div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
      have hlog1 : 0 ≤ 1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) := by linarith
      exact mul_nonneg hx_over hlog1
    exact add_nonneg (by positivity) hmult_nonneg
  have hmul :
      (((zBoxVN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            ‖coeffVZFin td (RankOneShear.coeff td α β) v0 k‖ ^ 2))
      ≤
      (((zBoxVN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) *
            (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ v ∈ ResiduePartitionV.vClass td r,
            ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, RankOneShear.coeff td α β p‖ ^ 2)) := by
    rw [hcoeffEq]
    exact mul_le_mul_of_nonneg_left hzLe hCnonneg
  exact hmain.trans hmul

/-- Interval-geometry wrapper for
`step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_vClass`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_vClass_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (v0 : ℤ)
    (hv0 : v0 ∈ ResiduePartitionV.vClass (td := tubeDataOfBGTube P a q hq hcop) r)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
      (∑ v ∈ ResiduePartitionV.vClass td r,
          ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_vClass
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (v0 := v0) (hv0 := hv0) (hαmod := hαmod))

/-- Step 3 one-add-log class-energy bound without choosing a class witness explicitly.

If `uClass td r` is nonempty, this is exactly
`step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_uClass`;
if empty, both sides are `0`.
-/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
      (∑ u ∈ ResiduePartition.uClass td r,
          ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  intro td
  by_cases huClass : (ResiduePartition.uClass td r).Nonempty
  · rcases huClass with ⟨u0, hu0⟩
    exact
      step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_uClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (u0 := u0) (hu0 := hu0) (hβmod := hβmod)
  · have huClass' : ResiduePartition.uClass td r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp huClass
    simp [huClass']

/-- Interval-geometry wrapper for
`step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hU0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (tubeDataOfBGTube P a q hq hcop).U
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ u ∈ ResiduePartition.uClass td r,
        ‖innerSumUZ td ξ (RankOneShear.coeff td α β) u‖ ^ 2)
      ≤
    (((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
      (∑ u ∈ ResiduePartition.uClass td r,
          ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hU0 := hU0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (hβmod := hβmod))

/-- Step 4 one-add-log class-energy bound without choosing a class witness explicitly.

If `vClass td r` is nonempty, this is exactly
`step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_vClass`;
if empty, both sides are `0`.
-/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
      (∑ v ∈ ResiduePartitionV.vClass td r,
          ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  intro td
  by_cases hvClass : (ResiduePartitionV.vClass td r).Nonempty
  · rcases hvClass with ⟨v0, hv0⟩
    exact
      step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_of_mem_vClass
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (r := r) (ξ := ξ) (hξ0 := hξ0)
        (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        (α := α) (β := β) (v0 := v0) (hv0 := hv0) (hαmod := hαmod)
  · have hvClass' : ResiduePartitionV.vClass td r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hvClass
    simp [hvClass']

/-- Interval-geometry wrapper for
`step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy`.

It derives the ξ-band hypothesis from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_outerGeom
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hD0 : 0 ≤ (tubeDataOfBGTube P a q hq hcop).D)
    (hX : 0 < (tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (tubeDataOfBGTube P a q hq hcop).H)
    (hξI : ξ ∈ Set.Icc (-(1 / (tubeDataOfBGTube P a q hq hcop).H))
        (1 / (tubeDataOfBGTube P a q hq hcop).H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (tubeDataOfBGTube P a q hq hcop).D)
            + (tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (tubeDataOfBGTube P a q hq hcop).X * (tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := tubeDataOfBGTube P a q hq hcop
    (∑ v ∈ ResiduePartitionV.vClass td r,
        ‖innerSumVZ td ξ (RankOneShear.coeff td α β) v‖ ^ 2)
      ≤
    (((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) *
          (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
      (∑ v ∈ ResiduePartitionV.vClass td r,
          ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, RankOneShear.coeff td α β p‖ ^ 2)) := by
  have hξH : |ξ| ≤ 1 / (tubeDataOfBGTube P a q hq hcop).H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (r := r) (ξ := ξ) (hξ0 := hξ0)
      (hD0 := hD0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (α := α) (β := β) (hαmod := hαmod))

end BGTubeBridge

end
end LargeSieve
end TypeII
end Engines
end SSU
