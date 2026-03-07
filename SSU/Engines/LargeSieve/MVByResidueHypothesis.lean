import SSU.Engines.LargeSieve.MontgomeryVaughanTypeII
import SSU.Engines.TypeIILargeSieveTeXFor

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

/-- Deterministic broad-geometry Step 3 large-sieve input on residue classes. -/
noncomputable def step3MV_byResidue
    (td : TubeData)
    (hDpos : 0 < td.D) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    Step3MontgomeryVaughanByResidue td :=
  Step3MontgomeryVaughanByResidue.of_general_geometry
    (td := td) hDpos hD hU hX

/-- Deterministic box-geometry Step 4 large-sieve input on residue classes. -/
noncomputable def step4MV_byResidue
    (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) :
    Step4MontgomeryVaughanByResidue td :=
  Step4MontgomeryVaughanByResidue.of_box_geometry
    (td := td) (hU := hU) (hX := hX) (hD1 := hD1) (hXH1 := hXH1)

/-- Parameter-only Step 3 constant coming from `step3MV_byResidue`. -/
noncomputable def C3
    (td : TubeData)
    (hDpos : 0 < td.D) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) : ℝ :=
  (step3MV_byResidue td hDpos hD hU hX).C

/-- Parameter-only Step 4 constant coming from `step4MV_byResidue`. -/
noncomputable def C4
    (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) : ℝ :=
  (step4MV_byResidue td hU hX hD1 hXH1).C

theorem C3_nonneg
    (td : TubeData)
    (hDpos : 0 < td.D) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    0 ≤ C3 td hDpos hD hU hX :=
  (step3MV_byResidue td hDpos hD hU hX).C_nonneg

theorem C4_nonneg
    (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) :
    0 ≤ C4 td hU hX hD1 hXH1 :=
  (step4MV_byResidue td hU hX hD1 hXH1).C_nonneg

theorem step3MV_byResidue_bound
    (td : TubeData)
    (hDpos : 0 < td.D) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X) :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ∀ r ∈ ResiduePartition.residuesU td,
          (∑ u ∈ ResiduePartition.uClass td r, ‖innerSumUZ td ξ F u‖ ^ 2)
            ≤
          (C3 td hDpos hD hU hX) * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
            (∑ u ∈ ResiduePartition.uClass td r,
              ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)) :=
  (step3MV_byResidue td hDpos hD hU hX).bound

theorem step4MV_byResidue_bound
    (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H) :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ F : TubePoint → ℂ,
        ∀ r ∈ ResiduePartitionV.residuesV td,
          (∑ v ∈ ResiduePartitionV.vClass td r, ‖innerSumVZ td ξ F v‖ ^ 2)
            ≤
          (C4 td hU hX hD1 hXH1) * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
            (∑ v ∈ ResiduePartitionV.vClass td r,
              ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)) :=
  (step4MV_byResidue td hU hX hD1 hXH1).bound

/-- Sharpened non-fallback Step-3-by-residue constructor from the one-add-log
`uFromIndex` common-domain witness package (`hZeq` + `hEqOn`) uniformly in `F`. -/
noncomputable def step3MV_byResidue_oneAddLog_ref
    (td : TubeData)
    (hU0 : 0 ≤ td.U) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (mRef :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td → ℤ)
    (hmRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td),
        mRef r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r)
    (hZeq :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          SSU.Engines.TypeII.LargeSieve.zSet td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)))
    (hEqOn :
      ∀ (F : TubePoint → ℂ),
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSet td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                    (td := td) r (mRef r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := td) r m) z, F p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
                      (td := td) r (mRef r hr)) z, F p)) :
    Step3MontgomeryVaughanByResidue td := by
  classical
  let C : ℝ :=
    (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ) +
      (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ) := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
      have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        exact_mod_cast htoNat1
      nlinarith
    have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) :=
      Real.log_nonneg harg1
    have hmain :
        0 ≤ ((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ)
          + (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))) : ℝ) := by
      linarith
    simpa [C] using hmain
  · intro ξ hξ0 hξH F r hr
    let h3F : SSU.Engines.TypeII.Step3FiberLargeSieveByResidueFor td F :=
      SSU.Engines.TypeII.Step3FiberLargeSieveByResidueFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
        (td := td)
        (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
        (hX := hX) (hH := hH) (hXH := hXH)
        (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq)
        (hEqOn := hEqOn F)
    have hCeq : h3F.C = C := by
      simp [h3F, C,
        SSU.Engines.TypeII.Step3FiberLargeSieveByResidueFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog]
    simpa [hCeq] using (h3F.bound ξ hξ0 hξH r hr)

/-- Sharpened non-fallback Step-4-by-residue constructor from the one-add-log
`vFromIndex` common-domain witness package (`hZeq` + `hEqOn`) uniformly in `F`. -/
noncomputable def step4MV_byResidue_oneAddLog_ref
    (td : TubeData)
    (hD0 : 0 ≤ td.D) (hD1 : 1 ≤ td.D) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (mRef :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td → ℤ)
    (hmRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td),
        mRef r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r)
    (hZeq :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)))
    (hEqOn :
      ∀ (F : TubePoint → ℂ),
        ∀ (r : ℤ)
          (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
          (m : ℤ),
          m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
            ∀ z : ℤ,
              z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                    (td := td) r (mRef r hr)) →
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := td) r m) z, F p)
                  =
                (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                    (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
                      (td := td) r (mRef r hr)) z, F p)) :
    Step4MontgomeryVaughanByResidue td := by
  classical
  let C : ℝ :=
    (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ) +
      (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ) := by
      positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by nlinarith [hD0])
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
      have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        exact_mod_cast htoNat1
      nlinarith
    have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) :=
      Real.log_nonneg harg1
    have hmain :
        0 ≤ ((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ)
          + (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))) : ℝ) := by
      linarith
    simpa [C] using hmain
  · intro ξ hξ0 hξH F r hr
    let h4F : SSU.Engines.TypeII.Step4FiberLargeSieveByResidueFor td F :=
      SSU.Engines.TypeII.Step4FiberLargeSieveByResidueFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
        (td := td)
        (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
        (hX := hX) (hH := hH) (hXH := hXH)
        (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq)
        (hEqOn := hEqOn F)
    have hCeq : h4F.C = C := by
      simp [h4F, C,
        SSU.Engines.TypeII.Step4FiberLargeSieveByResidueFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog]
    simpa [hCeq] using (h4F.bound ξ hξ0 hξH r hr)

end

end LargeSieve
end TypeII
end Engines
end SSU
