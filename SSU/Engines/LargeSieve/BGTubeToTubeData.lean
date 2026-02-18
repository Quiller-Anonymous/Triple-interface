import SSU.Engines.BGTubeGeometry
import SSU.Engines.TypeII
import SSU.Engines.LargeSieve.RankOneShearBoxLargeSieveTeX
import SSU.Engines.LargeSieve.TypeIIShearSumTeX
import SSU.Engines.LargeSieve.TypeIISumDecompose
import SSU.Engines.LargeSieve.TypeIISumDecomposeV
import SSU.Engines.LargeSieve.TypeIIIndexBounds

/-!
Bridge from the TeX-faithful BG tube geometry (`05_BG.tex` / `BGTubeGeometry`) to the
Type–II large-sieve `TubeData` record (`SSU.Engines.TypeII.TubeData`).

This is deterministic plumbing:
it packages the explicit `Finset` tube `tubeFinset P a q s` as a `TubeData` instance, by
translating the integer box constraints and the shear bound into the `InTypeIITube` predicate.

Notes:
* The current `TubeData` predicate uses `u = qn - ad` (no offset `s`).
  For the first large-sieve instantiations we therefore expose the centered case `s = 0`.
  Handling general offsets is a later (straightforward) extension by translating `u`.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace BGTubeBridge

open SSU.Engines.BGTube

abbrev TubePoint : Type := SSU.TubePoint
abbrev ShearPoint : Type := SSU.Engines.TypeII.LargeSieve.ShearPoint

private lemma inIoc_of_mem_Icc_dRange
    (P : SSU.Engines.BGTube.Params) {d : ℤ} (hd : d ∈ P.dRange) :
    InIoc (P.D : ℝ) (2 * (P.D : ℝ)) d := by
  have hdIcc :
      ((P.D : ℤ) + 1 ≤ d ∧ d ≤ ((2 * P.D : ℕ) : ℤ)) := by
    simpa [SSU.Engines.BGTube.Params.dRange] using (Finset.mem_Icc.mp hd)
  have hltZ : (P.D : ℤ) < d := lt_of_lt_of_le (lt_add_one (P.D : ℤ)) hdIcc.1
  have hleZ : d ≤ ((2 * P.D : ℕ) : ℤ) := hdIcc.2
  constructor
  · exact_mod_cast hltZ
  · -- `((2*D:ℕ):ℤ) = (2*D:ℤ)`.
    simpa [Int.cast_mul, Int.cast_natCast] using (show (d : ℝ) ≤ (((2 * P.D : ℕ) : ℤ) : ℝ) from
      (by exact_mod_cast hleZ))

private lemma inIoc_of_mem_Icc_nRange
    (P : SSU.Engines.BGTube.Params) {n : ℤ} (hn : n ∈ P.nRange) :
    InIoc (P.N : ℝ) (2 * (P.N : ℝ)) n := by
  have hnIcc :
      ((P.N : ℤ) + 1 ≤ n ∧ n ≤ ((2 * P.N : ℕ) : ℤ)) := by
    simpa [SSU.Engines.BGTube.Params.nRange] using (Finset.mem_Icc.mp hn)
  have hltZ : (P.N : ℤ) < n := lt_of_lt_of_le (lt_add_one (P.N : ℤ)) hnIcc.1
  have hleZ : n ≤ ((2 * P.N : ℕ) : ℤ) := hnIcc.2
  constructor
  · exact_mod_cast hltZ
  · simpa [Int.cast_mul, Int.cast_natCast] using (show (n : ℝ) ≤ (((2 * P.N : ℕ) : ℤ) : ℝ) from
      (by exact_mod_cast hleZ))

private lemma abs_shearU_le_of_natAbs_le
    {z : ℤ} {U : ℕ} (h : Int.natAbs z ≤ U) :
    |(z : ℝ)| ≤ (U : ℝ) := by
  have hZ : (z.natAbs : ℤ) ≤ (U : ℤ) := by
    exact_mod_cast h
  have hAbsZ : |z| ≤ (U : ℤ) := by
    -- Avoid `simp [Int.abs_eq_natAbs]` (can loop on some simp sets).
    have hEq : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
    -- Rewrite the LHS of `hZ` into `|z|`.
    simpa [hEq] using hZ
  have hR : ((|z| : ℤ) : ℝ) ≤ (U : ℝ) := by
    exact_mod_cast hAbsZ
  simpa using hR

/-- Build a `TubeData` object from BG tube parameters, for the centered tube (`s = 0`). -/
def tubeDataOfBGTube
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 0 < q)
    (hcop : Nat.Coprime a.natAbs q) :
    SSU.Engines.TypeII.TubeData where
  X := (P.X : ℝ)
  H := (P.H : ℝ)
  a := a
  q := (q : ℤ)
  q_pos := by
    -- Cast `0 < q` from `ℕ` to `ℤ`.
    exact_mod_cast hq
  coprime := by
    -- `((q : ℤ).natAbs) = q`.
    simpa using hcop
  D := (P.D : ℝ)
  N := (P.N : ℝ)
  U := (P.U : ℝ)
  T := SSU.Engines.BGTube.tubeFinset P a q 0
  mem_T := by
    intro p hp
    -- Unpack membership in the BG tube finset.
    have hp' :
        p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
      simpa [SSU.Engines.BGTube.mem_tubeFinset_iff] using
        (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 hp
    have hpBox : p ∈ P.box := hp'.1
    have hpShear : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := hp'.2
    -- Box bounds.
    have hdRange : p.1 ∈ P.dRange := (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).1
    have hnRange : p.2 ∈ P.nRange := (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).2
    have hD : InIoc (P.D : ℝ) (2 * (P.D : ℝ)) p.1 := inIoc_of_mem_Icc_dRange P hdRange
    have hN : InIoc (P.N : ℝ) (2 * (P.N : ℝ)) p.2 := inIoc_of_mem_Icc_nRange P hnRange
    -- Shear bound: `BGTube.shear a q 0 p = shearU a (q:ℤ) p`.
    have hshearEq : SSU.Engines.BGTube.shear a q 0 p = shearU a (q : ℤ) p := by
      simp [SSU.Engines.BGTube.shear, shearU]
    have hU : |(shearU a (q : ℤ) p : ℝ)| ≤ (P.U : ℝ) := by
      -- Convert `natAbs` bound to a real `abs` bound.
      simpa [hshearEq] using (abs_shearU_le_of_natAbs_le (z := SSU.Engines.BGTube.shear a q 0 p) (U := P.U) hpShear)
    -- Assemble `InTypeIITube`.
    refine ⟨hD, hN, ?_⟩
    -- `TubeData` uses `U : ℝ` already.
    simpa using hU

/-- Deterministic geometry: the shear-image of a centered BG tube lies in the TeX shear box
`u ∈ [-U,U]`, `v ∈ (D,2D]`. -/
theorem image_shearMap_subset_rankOneShearBox
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) :
    let td := tubeDataOfBGTube P a q hq hcop
    td.T.image (shearMap td.a td.q) ⊆
      SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
        (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D := by
  classical
  intro td uv huv
  rcases Finset.mem_image.mp huv with ⟨p, hpT, rfl⟩
  -- Unpack membership in the BG tube.
  have hp' :
      p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
    exact (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 hpT
  have hpBox : p ∈ P.box := hp'.1
  have hpShear : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := hp'.2
  -- `v = d` lives in `[D+1,2D]`.
  have hdRange : p.1 ∈ P.dRange := (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).1
  have hvIcc :
      shearV p ∈ Finset.Icc ((P.D : ℤ) + 1) ((2 * P.D : ℕ) : ℤ) := by
    simpa [shearV, SSU.Engines.BGTube.Params.dRange] using hdRange
  -- `u = qn - ad` lives in `[-U,U]` (since `s = 0`).
  have hshearEq : SSU.Engines.BGTube.shear a q 0 p = shearU a (q : ℤ) p := by
    simp [SSU.Engines.BGTube.shear, shearU]
  have huAbs : |shearU a (q : ℤ) p| ≤ (P.U : ℤ) := by
    have hZ : ((SSU.Engines.BGTube.shear a q 0 p).natAbs : ℤ) ≤ (P.U : ℤ) := by
      exact_mod_cast hpShear
    have hEq : ((SSU.Engines.BGTube.shear a q 0 p).natAbs : ℤ) = |SSU.Engines.BGTube.shear a q 0 p| :=
      Int.natCast_natAbs (SSU.Engines.BGTube.shear a q 0 p)
    -- Rewrite using `hshearEq`.
    have : |SSU.Engines.BGTube.shear a q 0 p| ≤ (P.U : ℤ) := by
      simpa [hEq] using hZ
    simpa [hshearEq] using this
  have huIcc : shearU a (q : ℤ) p ∈ Finset.Icc (-(P.U : ℤ)) (P.U : ℤ) := by
    exact Finset.mem_Icc.mpr (abs_le.mp huAbs)
  -- Now show membership in the product box.
  -- (We coarsen the `v`-endpoint to match `box`'s `Icc (D+1) (2D)` presentation.)
  have hvIcc' :
      shearV p ∈ Finset.Icc ((P.D : ℤ) + 1) (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) := by
    -- `((D+1)+D-1) = 2D`.
    have htop : (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = (2 * (P.D : ℤ)) := by ring
    -- `((2*D:ℕ):ℤ) = 2*D`.
    have htop' : ((2 * P.D : ℕ) : ℤ) = 2 * (P.D : ℤ) := by
      norm_cast
    -- Transport the membership.
    simpa [htop, htop', shearV] using hvIcc
  -- Finish via the `mem_box_iff` characterization.
  refine
    (SSU.Engines.TypeII.LargeSieve.RankOneShearBox.mem_box_iff
        (J := Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) (a := (P.D : ℤ) + 1) (N := P.D)
        (uv := shearMap td.a td.q p)).2 ?_
  constructor
  · simpa [shearMap] using huIcc
  · simpa [shearMap] using hvIcc'

/--
Exact membership description of the centered BG tube shear image.

This is a pure *geometry* lemma: it expands
`uv ∈ (tubeFinset P a q 0).image (shearMap a q)` into the explicit dyadic box constraints on
`(d,n)` and the shear constraint `|q*n - a*d| ≤ U`, together with the identity
`uv = (q*n - a*d, d)`.

It intentionally does **not** attempt to eliminate the `n`-range (that would require additional
parameter-regime assumptions linking `a/q` to `N/D`).
-/
theorem mem_image_shearMap_iff_exists_dn_ofBG
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (uv : ShearPoint) :
    let td := tubeDataOfBGTube P a q hq hcop
    uv ∈ td.T.image (shearMap td.a td.q) ↔
      ∃ d ∈ P.dRange, ∃ n ∈ P.nRange,
        Int.natAbs ((q : ℤ) * n - a * d) ≤ P.U ∧
          uv = ((q : ℤ) * n - a * d, d) := by
  classical
  intro td
  -- Expand membership in the image finset.
  constructor
  · intro huv
    rcases Finset.mem_image.mp huv with ⟨p, hpT, rfl⟩
    -- Unpack tube membership as box + shear bound.
    have hp' :
        p ∈ P.box ∧ Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
      -- `td.T` is the BG tube finset.
      have : p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
        simpa [td, tubeDataOfBGTube] using hpT
      simpa [SSU.Engines.BGTube.mem_tubeFinset_iff] using
        (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 this
    have hpBox : p ∈ P.box := hp'.1
    have hpShear : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := hp'.2
    -- Split `p ∈ box` into `d ∈ dRange` and `n ∈ nRange`.
    have hd : p.1 ∈ P.dRange :=
      (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).1
    have hn : p.2 ∈ P.nRange :=
      (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).2
    -- Rewrite the shear expression.
    have hshear :
        SSU.Engines.BGTube.shear a q 0 p = (q : ℤ) * p.2 - a * p.1 := by
      simp [SSU.Engines.BGTube.shear]
    refine ⟨p.1, hd, p.2, hn, ?_, ?_⟩
    · simpa [hshear] using hpShear
    · -- `shearMap (d,n) = (q*n - a*d, d)`.
      simp [shearMap, td, tubeDataOfBGTube, shearU, shearV]
  · rintro ⟨d, hd, n, hn, hshear, rfl⟩
    -- Build the tube point and show it lies in `td.T`, then map into the image.
    let p : TubePoint := (d, n)
    have hpBox : p ∈ P.box := by
      -- `p ∈ dRange × nRange`.
      exact Finset.mem_product.mpr ⟨hd, hn⟩
    have hpT : p ∈ td.T := by
      -- Rewrite to BG tube finset membership.
      have : p ∈ SSU.Engines.BGTube.tubeFinset P a q 0 := by
        refine (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).2 ?_
        refine ⟨?_, ?_⟩
        · simpa [SSU.Engines.BGTube.Params.box] using hpBox
        · -- `BGTube.shear a q 0 (d,n) = q*n - a*d`.
          have : SSU.Engines.BGTube.shear a q 0 p = (q : ℤ) * n - a * d := by
            simp [SSU.Engines.BGTube.shear, p]
          simpa [this, p] using hshear
      simpa [td, tubeDataOfBGTube] using this
    exact Finset.mem_image_of_mem (shearMap td.a td.q) hpT

/-- Deterministic congruence: on the shear image, we have `u ≡ -a*v (mod q)` (TeX Step 3/4). -/
theorem shearMap_fst_modEq_neg_a_mul_snd_of_mem_image
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) :
    let td := tubeDataOfBGTube P a q hq hcop
    ∀ uv : SSU.Engines.TypeII.LargeSieve.ShearPoint,
      uv ∈ td.T.image (shearMap td.a td.q) →
        uv.1 ≡ (-td.a * uv.2) [ZMOD td.q] := by
  classical
  intro td uv huv
  rcases Finset.mem_image.mp huv with ⟨p, hpT, rfl⟩
  -- This is exactly the general congruence lemma for `shearU`.
  simpa [shearMap] using (shearU_modEq_neg_a_mul_v (a := td.a) (q := td.q) (p := p))

/-!
### Convenience bounds on `uSet` / `vSet` for the centered BG tube

These are small deterministic helpers for later MV applications: they eliminate `ceil`/casts and
give the TeX-shaped index ranges directly.
-/

theorem uSet_subset_Icc_negU_U_ofBG
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) :
    uSet (tubeDataOfBGTube P a q hq hcop) ⊆ Finset.Icc (-(P.U : ℤ)) (P.U : ℤ) := by
  classical
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨p, hpT, rfl⟩
  -- Unpack membership in the BG tube.
  have hpShear : Int.natAbs (SSU.Engines.BGTube.shear a q 0 p) ≤ P.U := by
    have hp' :=
      (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 hpT
    exact hp'.2
  have hshearEq :
      SSU.Engines.BGTube.shear a q 0 p =
        shearU (tubeDataOfBGTube P a q hq hcop).a (tubeDataOfBGTube P a q hq hcop).q p := by
    simp [tubeDataOfBGTube, SSU.Engines.BGTube.shear, shearU]
  have huAbs :
      |shearU (tubeDataOfBGTube P a q hq hcop).a (tubeDataOfBGTube P a q hq hcop).q p|
        ≤ (P.U : ℤ) := by
    have hZ : ((SSU.Engines.BGTube.shear a q 0 p).natAbs : ℤ) ≤ (P.U : ℤ) := by
      exact_mod_cast hpShear
    have hEq : ((SSU.Engines.BGTube.shear a q 0 p).natAbs : ℤ) = |SSU.Engines.BGTube.shear a q 0 p| :=
      Int.natCast_natAbs (SSU.Engines.BGTube.shear a q 0 p)
    have : |SSU.Engines.BGTube.shear a q 0 p| ≤ (P.U : ℤ) := by
      simpa [hEq] using hZ
    simpa [hshearEq] using this
  exact Finset.mem_Icc.mpr (abs_le.mp huAbs)

theorem vSet_subset_Icc_Dp1_twoD_ofBG
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) :
    vSet (tubeDataOfBGTube P a q hq hcop) ⊆ Finset.Icc ((P.D : ℤ) + 1) ((2 * P.D : ℕ) : ℤ) := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨p, hpT, rfl⟩
  have hp' :=
    (SSU.Engines.BGTube.mem_tubeFinset_iff (P := P) (a := a) (q := q) (s := 0) (p := p)).1 hpT
  have hpBox : p ∈ P.box := hp'.1
  have hdRange : p.1 ∈ P.dRange :=
    (Finset.mem_product.mp (by simpa [SSU.Engines.BGTube.Params.box] using hpBox)).1
  -- `shearV p = p.1`.
  simpa [shearV, SSU.Engines.BGTube.Params.dRange] using hdRange

/-!
### Energy comparison: tube energy ≤ box energy

Later, the large-sieve bounds are naturally phrased on a full rank-one shear box.
The centered BG tube shear image is a subset of that box, so any nonnegative `ℓ²` energy
restricted to the tube is bounded by the corresponding energy on the ambient box.
-/

theorem tubeEnergy_le_sum_norm_sq_on_rankOneShearBox_ofBG
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (α β : ℤ → ℂ) :
    let td := tubeDataOfBGTube P a q hq hcop
    tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
      ≤
    (∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
          (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D,
        ‖β uv.1 * α uv.2‖ ^ 2) := by
  classical
  intro td
  -- Rewrite tube energy as a sum over the shear image.
  have hsum :
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
        =
      ∑ uv ∈ td.T.image (shearMap td.a td.q), ‖β uv.1 * α uv.2‖ ^ 2 := by
    simpa using
      (tubeEnergy_eq_sum_image_shearMap_of_comp (td := td)
        (G := fun uv : SSU.Engines.TypeII.LargeSieve.ShearPoint => β uv.1 * α uv.2))
  -- Use the subset inclusion of the shear image into the ambient box.
  have hsub :
      td.T.image (shearMap td.a td.q)
        ⊆
      SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
        (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D := by
    simpa using
      (image_shearMap_subset_rankOneShearBox (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop))
  -- Now sum monotonicity for a nonnegative integrand.
  have hle :
      (∑ uv ∈ td.T.image (shearMap td.a td.q), ‖β uv.1 * α uv.2‖ ^ 2)
        ≤
      (∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D,
          ‖β uv.1 * α uv.2‖ ^ 2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro uv _huv _huv'
    positivity
  simpa [hsum] using hle

theorem tubeEnergy_le_boxEnergy_on_rankOneShearBox_ofBG
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (α β : ℤ → ℂ) :
    let td := tubeDataOfBGTube P a q hq hcop
    tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
      ≤
    SSU.Engines.LargeSieve.RankOneShear.boxEnergy
      (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D α β := by
  classical
  intro td
  have hle :
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
        ≤
      (∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D,
          ‖β uv.1 * α uv.2‖ ^ 2) := by
    simpa using
      (tubeEnergy_le_sum_norm_sq_on_rankOneShearBox_ofBG
        (P := P) (a := a) (q := q) (hq := hq) (hcop := hcop) (α := α) (β := β))
  have hle' :
      tubeEnergy td.T (fun p => β (shearU td.a td.q p) * α (shearV p))
        ≤
      (∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D,
          (‖β uv.1‖ * ‖α uv.2‖) ^ 2) := by
    -- Pointwise rewrite `‖β(u)*α(v)‖^2 = (‖β(u)‖*‖α(v)‖)^2`.
    simpa [norm_mul, mul_pow] using hle
  -- Rewrite the ambient box energy sum into `RankOneShear.boxEnergy`.
  have hE :
      (∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D,
          (‖β uv.1‖ * ‖α uv.2‖) ^ 2)
        =
      SSU.Engines.LargeSieve.RankOneShear.boxEnergy
        (Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) ((P.D : ℤ) + 1) P.D α β := by
    have h0 :=
      (SSU.Engines.TypeII.LargeSieve.RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy
        (J := Finset.Icc (-(P.U : ℤ)) (P.U : ℤ)) (a := (P.D : ℤ) + 1) (N := P.D)
        (α := α) (β := β))
    simpa [norm_mul, mul_pow] using h0
  simpa [hE] using hle'

/-!
### Diameter bounds for MV (centered BG tube)

These are deterministic convenience lemmas: they re-express the general
`TypeIIIndexBounds.distZ_le_*_on_uSet/vSet` bounds in the concrete BG setting, eliminating the
`ceil` wrappers introduced by `TubeData`'s real-valued parameters.
-/

private theorem toNat_ceil_natCast (n : ℕ) :
    Int.toNat (Int.ceil (n : ℝ)) = n := by
  -- First: `⌈(n:ℝ)⌉ = (n:ℤ)` (rewrite from the integer-cast statement).
  have hceil_int : Int.ceil ((n : ℤ) : ℝ) = (n : ℤ) := by
    simpa using (Int.ceil_intCast (R := ℝ) (z := (n : ℤ)))
  have hn_cast : ((n : ℤ) : ℝ) = (n : ℝ) := by norm_cast
  have hceil : Int.ceil (n : ℝ) = (n : ℤ) := by
    -- Avoid `simp` loops by rewriting once.
    simpa [hn_cast] using hceil_int
  -- Second: `toNat (n:ℤ) = n`.
  have htoNat : Int.toNat (n : ℤ) = n := by
    apply Int.ofNat.inj
    -- `((toNat (n:ℤ) : ℤ) = (n:ℤ))` is the core lemma.
    simpa using (Int.toNat_of_nonneg (a := (n : ℤ)) (by exact_mod_cast (Nat.zero_le n)))
  -- Combine.
  simpa [hceil] using htoNat

private theorem toNat_ceil_two_mul_natCast (n : ℕ) :
    Int.toNat (Int.ceil (2 * (n : ℝ))) = 2 * n := by
  -- As above, but for `2*n`.
  have hceil_int : Int.ceil ((2 * n : ℤ) : ℝ) = (2 * n : ℤ) := by
    simpa using (Int.ceil_intCast (R := ℝ) (z := (2 * n : ℤ)))
  have htwo_cast : ((2 * n : ℤ) : ℝ) = (2 * (n : ℝ)) := by norm_cast
  have hceil : Int.ceil (2 * (n : ℝ)) = (2 * n : ℤ) := by
    -- Rewrite once; no `simp`-heavy normalization.
    simpa [htwo_cast] using hceil_int
  have htoNat : Int.toNat (2 * n : ℤ) = 2 * n := by
    apply Int.ofNat.inj
    simpa using
      (Int.toNat_of_nonneg (a := (2 * n : ℤ)) (by exact_mod_cast (Nat.zero_le (2 * n))))
  simpa [hceil] using htoNat

theorem distZ_le_two_mul_U_on_uSet_ofBG
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) :
    let td := tubeDataOfBGTube P a q hq hcop
    ∀ i ∈ uSet td, ∀ j ∈ uSet td, SSU.Hilbert.distZ i j ≤ 2 * P.U := by
  -- Unfold the `let`-binder, keeping `tubeDataOfBGTube` opaque except for projections.
  dsimp
  set td : SSU.Engines.TypeII.TubeData := tubeDataOfBGTube P a q hq hcop
  have hU0 : 0 ≤ td.U := by
    -- `td.U = (P.U : ℝ)` by construction.
    dsimp [td, tubeDataOfBGTube]
    positivity
  intro i hi j hj
  have h :=
    IndexBounds.distZ_le_two_mul_toNat_ceilU_on_uSet (td := td) hU0 i hi j hj
  have htoNat : Int.toNat (Int.ceil td.U) = P.U := by
    dsimp [td, tubeDataOfBGTube]
    exact toNat_ceil_natCast (n := P.U)
  simpa [htoNat] using h

theorem distZ_le_two_mul_twoD_on_vSet_ofBG
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q) :
    let td := tubeDataOfBGTube P a q hq hcop
    ∀ i ∈ vSet td, ∀ j ∈ vSet td, SSU.Hilbert.distZ i j ≤ 4 * P.D := by
  dsimp
  set td : SSU.Engines.TypeII.TubeData := tubeDataOfBGTube P a q hq hcop
  have hD0 : 0 ≤ td.D := by
    dsimp [td, tubeDataOfBGTube]
    positivity
  intro i hi j hj
  have h :=
    IndexBounds.distZ_le_two_mul_toNat_ceilTwoD_on_vSet (td := td) hD0 i hi j hj
  have htoNat : Int.toNat (Int.ceil (2 * td.D)) = 2 * P.D := by
    dsimp [td, tubeDataOfBGTube]
    exact toNat_ceil_two_mul_natCast (n := P.D)
  simpa [htoNat, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

end BGTubeBridge

end
end LargeSieve
end TypeII
end Engines
end SSU
