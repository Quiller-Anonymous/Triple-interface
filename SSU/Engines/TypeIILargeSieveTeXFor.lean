import SSU.Engines.TypeIILargeSieveTeX
import SSU.Engines.LargeSieve.MontgomeryVaughanTypeII
import SSU.Engines.LargeSieve.TypeIIConstCoeffTeXBounds
import SSU.Engines.LargeSieve.Step34Aux
import SSU.Engines.LargeSieve.BGTubeFiberLargeSieve

/-!
“Use-site” (per-signal) versions of the TeX Step 3–4 large sieve interfaces.

`SSU.Engines.TypeIILargeSieveTeX` packages the TeX bounds as *global* hypothesis interfaces
(`∀ F : TubePoint → ℂ, ...`).  In the SSU pipeline we often only need these bounds for a single
extracted coefficient array `F`, together with extraction hypotheses (e.g. constant-coefficient
facts).

This file provides a lightweight “for a fixed `F`” wrapper, plus a constructor from the
constant-coefficient TeX Step 5 lemma.
-/

namespace SSU
namespace Engines
namespace TypeII

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

/-- Convert an interval-membership band hypothesis to an absolute-value band hypothesis. -/
private theorem abs_le_one_div_of_mem_Icc {H ξ : ℝ}
    (hξI : ξ ∈ Set.Icc (-(1 / H)) (1 / H)) :
    |ξ| ≤ 1 / H := by
  exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩

/-- Convert an absolute-value band hypothesis to interval-membership on the same dyadic band. -/
private theorem mem_Icc_of_abs_le_one_div {H ξ : ℝ}
    (hξH : |ξ| ≤ 1 / H) :
    ξ ∈ Set.Icc (-(1 / H)) (1 / H) := by
  exact abs_le.mp hξH

/-- Numeric helper: if `q ≤ D` and `q > 0` (natural numbers), then `1 ≤ D / q` over `ℝ`. -/
private theorem one_le_div_of_natCast_le {D q : ℕ}
    (hq : 0 < q) (hqD : q ≤ D) :
    (1 : ℝ) ≤ (D : ℝ) / (q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqDR : (q : ℝ) ≤ (D : ℝ) := by exact_mod_cast hqD
  exact (le_div_iff₀ hqR).2 (by simpa using hqDR)

/-- TeX Step 5 large-sieve bound, but only for a fixed coefficient array `F`. -/
structure Step34LargeSieveTeXFor (td : TubeData) (F : TubePoint → ℂ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      C *
        Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
          Real.sqrt (td.U + td.X / |ξ|) *
            Real.sqrt (td.D + td.X / |ξ|) *
              tubeEnergy td.T F

namespace Step34LargeSieveTeXFor

def mk_C (td : TubeData) (F : TubePoint → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      C *
        Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
          Real.sqrt (td.U + td.X / |ξ|) *
            Real.sqrt (td.D + td.X / |ξ|) *
              tubeEnergy td.T F) :
    Step34LargeSieveTeXFor td F :=
  ⟨C, hC, h⟩

/-- Any global `Step34LargeSieveTeX td` instance yields a use-site bound for a fixed `F`. -/
def of_global (td : TubeData) (h34 : Step34LargeSieveTeX td) (F : TubePoint → ℂ) :
    Step34LargeSieveTeXFor td F :=
  ⟨h34.C, h34.C_nonneg, fun ξ hξ0 hξH => h34.bound ξ hξ0 hξH F⟩

/-- Interval-geometry wrapper for use-site Step 5 bounds. -/
theorem bound_outerGeom (h34 : Step34LargeSieveTeXFor td F)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H)) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    h34.C *
      Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
        Real.sqrt (td.U + td.X / |ξ|) *
          Real.sqrt (td.D + td.X / |ξ|) *
            tubeEnergy td.T F := by
  exact h34.bound ξ hξ0 (abs_le_one_div_of_mem_Icc hξI)

open SSU.Engines.TypeII.LargeSieve
open SSU.Engines.TypeII.LargeSieve.ConstCoeffTeX
open SSU.Engines.TypeII.LargeSieve.ZBoxToFin
open SSU.Engines.TypeII.LargeSieve.ZBoxRewrite

/-- Build a use-site TeX Step 5 bound from the const-coefficient TeX Step 5 lemma. -/
def of_constCoeffUZFin_of_constCoeffVZFin
    (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U)
    (hXH1 : 1 ≤ td.X * td.H)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH_u : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (hXH_v : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (aU : Fin (zBoxN td) → ℂ) (aV : Fin (zBoxVN td) → ℂ)
    (hCoeffU : ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = aU)
    (hCoeffV : ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = aV) :
    Step34LargeSieveTeXFor td F := by
  classical
  -- Deterministic combined constant (this is exactly the prefactor in the const-coeff Step 5 lemma,
  -- except that we absorb the `sqrt(D/U)*sqrt(max(U/(qD),1))` inflation into `C`).
  let C3 : ℝ :=
    (((zBoxN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0) : ℝ)
  let C4 : ℝ :=
    (((zBoxVN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0) : ℝ)
  let qR : ℝ := (td.q : ℝ)
  let m : ℝ := max (td.U / (qR * td.D)) 1
  let C : ℝ := Real.sqrt (C3 * C4) * Real.sqrt (td.D / td.U) * Real.sqrt m
  refine ⟨C, ?_, ?_⟩
  · -- `C ≥ 0`.
    simp [C, mul_nonneg, Real.sqrt_nonneg]
  · intro ξ hξ0 hξH
    have h0 :=
      norm_typeIISum_sq_le_step5_teX_of_constCoeffUZFin_of_constCoeffVZFin
        (td := td) (hDq := hDq) (hD1 := hD1) (hU1 := hU1) (hXH1 := hXH1)
        (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH)
        (hXH_u := hXH_u) (hXH_v := hXH_v)
        (F := F) (aU := aU) (aV := aV) (hCoeffU := hCoeffU) (hCoeffV := hCoeffV)
    -- Fold the explicit inflation factors into `C`.
    -- (`h0` has `sqrt(C3*C4) * sqrt(D/U) * sqrt(m) * ...`; our `C` is exactly that product.)
    simpa [C, C3, C4, qR, m, mul_assoc, mul_left_comm, mul_comm] using h0

end Step34LargeSieveTeXFor

/-- TeX Step 3 large-sieve bound, but only for a fixed coefficient array `F`. -/
structure Step3LargeSieveOuterUFor (td : TubeData) (F : TubePoint → ℂ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F)

namespace Step3LargeSieveOuterUFor

/-- Any global `Step3LargeSieveOuterU td` instance yields a use-site bound for a fixed `F`. -/
def of_global (td : TubeData) (h3 : Step3LargeSieveOuterU td) (F : TubePoint → ℂ) :
    Step3LargeSieveOuterUFor td F :=
  ⟨h3.C, h3.C_nonneg, fun ξ hξ0 hξH => h3.bound ξ hξ0 hξH F⟩

/-- Build a use-site Step 3 bound from a Step 3 Montgomery–Vaughan hypothesis. -/
def of_montgomeryVaughan
    (td : TubeData)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td)
    (hD : 0 ≤ td.D) (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (F : TubePoint → ℂ) :
    Step3LargeSieveOuterUFor td F := by
  let hFiber : SSU.Engines.TypeII.LargeSieve.Step3FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h3MV) hD hU hX
  let h3 : Step3LargeSieveOuterU td :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := td) hFiber
  exact of_global td h3 F

/-- Build a use-site Step 3 bound from a per-residue Step 3 Montgomery–Vaughan hypothesis. -/
def of_montgomeryVaughan_byResidue
    (td : TubeData)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td)
    (hD : 0 ≤ td.D) (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (F : TubePoint → ℂ) :
    Step3LargeSieveOuterUFor td F := by
  exact
    of_montgomeryVaughan
      (td := td)
      (h3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue td h3MV)
      (hD := hD) (hU := hU) (hX := hX) F

/-- Build a use-site Step 3 bound from pure box geometry (`card zSet` fallback). -/
def of_box_geometry
    (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X)
    (F : TubePoint → ℂ) :
    Step3LargeSieveOuterUFor td F := by
  exact
    of_montgomeryVaughan
      (td := td)
      (h3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_box_geometry
        (td := td) (hDq := hDq) (hD := hD) (hU := hU) (hX := hX))
      (hD := hD)
      (hU := le_trans (show (0 : ℝ) ≤ 1 by norm_num) hU)
      (hX := hX)
      F

/-- Build a use-site Step 3 bound from broad box geometry with no `q ≤ D` side condition. -/
def of_general_box_geometry
    (td : TubeData)
    (hDpos : 0 < td.D) (hD : 0 ≤ td.D) (hU : 1 ≤ td.U) (hX : 0 ≤ td.X)
    (F : TubePoint → ℂ) :
    Step3LargeSieveOuterUFor td F := by
  exact
    of_montgomeryVaughan
      (td := td)
      (h3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_general_geometry
        (td := td) (hDpos := hDpos) (hD := hD) (hU := hU) (hX := hX))
      (hD := hD)
      (hU := le_trans (show (0 : ℝ) ≤ 1 by norm_num) hU)
      (hX := hX)
      F

/-- Build a use-site TeX Step 3 bound from the constant-coefficient hypothesis
`∀ u ∈ uSet, coeffUZFin td F u = a`. -/
def of_constCoeffUZFin
    (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U) (hU0 : 0 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH_u : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (aU : Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td) → ℂ)
    (hCoeffU : ∀ u : ℤ, u ∈ SSU.Engines.TypeII.LargeSieve.uSet td →
      SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F u = aU) :
    Step3LargeSieveOuterUFor td F :=
by
  classical
  -- Match the constant displayed in `norm_typeIISum_sq_le_step3_teX_of_constCoeffUZFin`.
  let C : ℝ :=
    (((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ) +
        max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0) : ℝ)
  refine ⟨C, ?_, ?_⟩
  ·
    have hN : 0 ≤ (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ) := by positivity
    have hB : 0 ≤ (max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0 : ℝ) := by
      simp
    exact add_nonneg hN hB
  · intro ξ hξ0 hξH
    -- Use the TeX-shaped Step 3 bound from the const-coeff MV bridge.
    simpa [C] using
      (SSU.Engines.TypeII.LargeSieve.ConstCoeffTeX.norm_typeIISum_sq_le_step3_teX_of_constCoeffUZFin
        (td := td)
        (hDq := hDq) (hU1 := hU1) (hU0 := hU0)
        (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH)
        (hXH := hXH_u)
        (F := F) (a := aU) (hCoeff := hCoeffU))

/-- Interval-geometry wrapper for use-site Step 3 outer-u bounds. -/
theorem bound_outerGeom (h3 : Step3LargeSieveOuterUFor td F)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H)) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    h3.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
  exact h3.bound ξ hξ0 (abs_le_one_div_of_mem_Icc hξI)

end Step3LargeSieveOuterUFor

/-- Step 3 fiber large-sieve hypothesis specialized to a fixed coefficient array `F`. -/
structure Step3FiberLargeSieveFor (td : TubeData) (F : TubePoint → ℂ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      (∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
        ≤
      C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F)

/-- Step 3 fiber large-sieve hypothesis on each residue class, specialized to fixed `F`. -/
structure Step3FiberLargeSieveByResidueFor (td : TubeData) (F : TubePoint → ℂ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
          ≤
        C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
            (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
              ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
                ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2))

namespace Step3FiberLargeSieveByResidueFor

set_option maxHeartbeats 1000000

/-- Build the fixed-`F` residue-class Step 3 fiber interface from the global residue-class
Montgomery–Vaughan hypothesis by specialization in `F`. -/
def of_montgomeryVaughanByResidue
    (td : TubeData)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td)
    (F : TubePoint → ℂ) :
    Step3FiberLargeSieveByResidueFor td F :=
  ⟨h3MV.C, h3MV.C_nonneg, fun ξ hξ0 hξH r hr => h3MV.bound ξ hξ0 hξH F r hr⟩

/-- Build a fixed-`F` residue-class Step 3 fiber interface from per-residue reference-fiber
equalities on a common `zSet` domain (the geometry-friendly `hZeq` + `hEqOn` package), using the
explicit one-add-log envelope. -/
def of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
    (td : TubeData)
    (hU0 : 0 ≤ td.U) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) z, F p)) :
    Step3FiberLargeSieveByResidueFor td F := by
  let A : ℝ := (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ)
  let B : ℝ := 1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))
  let C : ℝ := A + B
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) :=
        Real.log_nonneg harg1
      linarith
    simpa [C] using add_nonneg hA_nonneg hB_nonneg
  · intro ξ hξ0 hξH r hr
    have hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H) :=
      mem_Icc_of_abs_le_one_div hξH
    let E : ℝ :=
      ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2
    let xq : ℝ := td.X / (|ξ| * (td.q : ℝ))
    let m0 : ℤ := mRef r hr
    have hm0 : m0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r := hmRef r hr
    let u0 : ℤ := SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m0
    have hu0 : u0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r := by
      simpa [u0] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_mem_uClass_of_mem_uIndexSet
          (td := td) (r := r) (m := m0) hm0)
    have hCoeff :
        ∀ m : ℤ, m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m0) :=
      SSU.Engines.TypeII.LargeSieve.ConstCoeffFromFiber.constCoeffUZFin_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet
        (td := td) (F := F) (r := r) (m0 := m0) (_hm0 := hm0)
        (hZeq := fun m hm => hZeq r hr m hm)
        (hEqOn := fun m hm z hz => hEqOn r hr m hm z hz)
    have hindex :
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
          ≤
        (A + xq * B) *
          (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
      simpa [A, B, xq] using
        SSU.Engines.TypeII.LargeSieve.FiberFromFiniteLargeSieve.step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_one_add_log_outerGeom
          (td := td) (hU0 := hU0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
          (hξI := hξI) (hXH := hXH)
          (F := F)
          (a := SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F
            (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m0))
          (hCoeff := hCoeff)
    have hclassEq :
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
          =
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2) := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet
          (td := td) (ξ := ξ) (F := F) (r := r))
    have hcoeffEq :
        (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F u0 k‖ ^ 2)
          =
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u0 z, F p‖ ^ 2) := by
      simpa [u0] using
        (SSU.Engines.TypeII.LargeSieve.ConstCoeffMV.sum_univ_norm_coeffUZFin_sq_eq_sum_zSet_norm_fiberUZ_sum_sq
          (td := td) (F := F) (u := u0))
    have hzLe :
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u0 z, F p‖ ^ 2)
          ≤ E := by
      have hnonneg :
          ∀ u : ℤ, u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r →
            0 ≤ (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2 : ℝ) := by
        intro u hu
        refine Finset.sum_nonneg ?_
        intro z hz
        positivity
      simpa [E] using Finset.single_le_sum hnonneg hu0
    have hmain :
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
          ≤
        (A + xq * B) * E := by
      have hindex' :
          (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
              ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F u0 k‖ ^ 2) := by
        simpa [hclassEq, u0] using hindex
      have hA_nonneg : 0 ≤ A + xq * B := by
        have hA0 : 0 ≤ A := by positivity
        have hB0 : 0 ≤ B := by
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
          linarith
        have hxq0 : 0 ≤ xq := by
          have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
            exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
          exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
        exact add_nonneg hA0 (mul_nonneg hxq0 hB0)
      calc
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td F u0 k‖ ^ 2) := hindex'
        _ = (A + xq * B) *
              (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u0,
                ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u0 z, F p‖ ^ 2) := by
              rw [hcoeffEq]
        _ ≤ (A + xq * B) * E := by
              exact mul_le_mul_of_nonneg_left hzLe hA_nonneg
    have hE_nonneg : 0 ≤ E := by
      refine Finset.sum_nonneg ?_
      intro u hu
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) :=
        Real.log_nonneg harg1
      linarith
    have hxq_nonneg : 0 ≤ xq := by
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
        exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
      exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
    have hC_nonneg : 0 ≤ C := by
      simpa [C] using add_nonneg hA_nonneg hB_nonneg
    have hfactor₁ : A + xq * B ≤ C * (1 + xq) := by
      calc
        A + xq * B ≤ A + xq * B + (A * xq + B) := by
          nlinarith [hA_nonneg, hB_nonneg, hxq_nonneg]
        _ = C * (1 + xq) := by
          ring
    have hq1R : (1 : ℝ) ≤ (td.q : ℝ) := by
      exact_mod_cast hq1
    have hxOver_nonneg : 0 ≤ td.X / |ξ| := by
      exact div_nonneg (le_of_lt hX) (abs_nonneg ξ)
    have hxq_le_xOver : xq ≤ td.X / |ξ| := by
      have hxq_eq : xq = (td.X / |ξ|) / (td.q : ℝ) := by
        simp [xq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hxq_eq]
      exact div_le_self hxOver_nonneg hq1R
    have hxOver_le_DQxOver :
        td.X / |ξ| ≤ (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
      have hmul := mul_le_mul_of_nonneg_right hDq hxOver_nonneg
      simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hpart₁ : (1 : ℝ) ≤ (td.D / (td.q : ℝ)) * td.U := by
      have hDq0 : 0 ≤ td.D / (td.q : ℝ) := le_trans (by norm_num) hDq
      have hmul := mul_le_mul hDq hU1 (by norm_num) hDq0
      simpa [one_mul] using hmul
    have hpart₂ : xq ≤ (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
      exact le_trans hxq_le_xOver hxOver_le_DQxOver
    have hfactor₂ :
        1 + xq ≤ (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) := by
      have hsum :
          1 + xq ≤
            (td.D / (td.q : ℝ)) * td.U + (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
        nlinarith [hpart₁, hpart₂]
      have hmul_add :
          (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) =
            (td.D / (td.q : ℝ)) * td.U + (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
        ring
      simpa [hmul_add] using hsum
    have hfactor :
        A + xq * B ≤ C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|)) := by
      calc
        A + xq * B ≤ C * (1 + xq) := hfactor₁
        _ ≤ C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|)) := by
          exact mul_le_mul_of_nonneg_left hfactor₂ hC_nonneg
    have hmul :
        (A + xq * B) * E ≤ (C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|))) * E := by
      exact mul_le_mul_of_nonneg_right hfactor hE_nonneg
    calc
      (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
          ≤ (A + xq * B) * E := hmain
      _ ≤ (C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|))) * E := hmul
      _ =
          C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * E) := by
            ring

/-- Build a fixed-`F` residue-class Step 3 fiber interface for the BG-centered tube rank-one
coefficients, using the proved one-add-log class-energy bound. -/
def of_bgTubeRankOne_constOnUIndex_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (mRef :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRef r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRef r hr))) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step3FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let A : ℝ := (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ)
  let B : ℝ := 1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))
  let C : ℝ := A + B
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) :=
        Real.log_nonneg harg1
      linarith
    simpa [C] using add_nonneg hA_nonneg hB_nonneg
  · intro ξ hξ0 hξH r hr
    have hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H) :=
      mem_Icc_of_abs_le_one_div hξH
    let E : ℝ :=
      ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z,
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2
    let xq : ℝ := td.X / (|ξ| * (td.q : ℝ))
    have hr' : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
        (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) := by
      simpa [td] using hr
    let m0 : ℤ := mRef r hr'
    have hm0 : m0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r := by
      have hm0' := hmRef r hr'
      simpa [td, m0] using hm0'
    let u0 : ℤ := SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m0
    have hu0 : u0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r := by
      simpa [u0] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex_mem_uClass_of_mem_uIndexSet
          (td := td) (r := r) (m := m0) hm0)
    have hβconst_r :
        ∀ m : ℤ, m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)
            = β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m0) := by
      intro m hm
      have hm' : m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r := by
        simpa [td] using hm
      simpa [td, m0] using hβconst r hr' m hm'
    have hindex :
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
          ≤
        (A + xq * B) *
          (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
      simpa [A, B, xq, td] using
        SSU.Engines.TypeII.LargeSieve.BGTubeBridge.step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_one_add_log_outerGeom
          (P := P) (a := a) (q := q) hq hcop
          (ha0 := ha0) (hlower := hlower) (hupper := hupper)
          (r := r) (ξ := ξ) (hξ0 := hξ0)
          (hU0 := hU0) (hX := hX) (hH := hH) (hξI := hξI) (hXH := hXH)
          (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hβconst := hβconst_r)
    have hclassEq :
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u‖ ^ 2)
          =
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2) := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet
          (td := td) (ξ := ξ)
          (F := SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) (r := r))
    have hcoeffEq :
        (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u0 k‖ ^ 2)
          =
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u0 z,
                SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2) := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.ConstCoeffMV.sum_univ_norm_coeffUZFin_sq_eq_sum_zSet_norm_fiberUZ_sum_sq
          (td := td) (F := SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) (u := u0))
    have hzLe :
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u0 z,
                SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2)
          ≤ E := by
      have hnonneg :
          ∀ u : ℤ, u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r →
            0 ≤ (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z,
                  SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2 : ℝ) := by
        intro u hu
        refine Finset.sum_nonneg ?_
        intro z hz
        positivity
      simpa [E] using Finset.single_le_sum hnonneg hu0
    have hmain :
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u‖ ^ 2)
          ≤
        (A + xq * B) * E := by
      have hindex' :
          (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
              ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
                  (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td
                  (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u0 k‖ ^ 2) := by
        simpa [hclassEq, u0] using hindex
      have hA_nonneg : 0 ≤ A + xq * B := by
        have hA0 : 0 ≤ A := by positivity
        have hB0 : 0 ≤ B := by
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
          linarith
        have hxq0 : 0 ≤ xq := by
          have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
            exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
          exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
        exact add_nonneg hA0 (mul_nonneg hxq0 hB0)
      calc
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffUZFin td
                  (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u0 k‖ ^ 2) := hindex'
        _ = (A + xq * B) *
              (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u0,
                ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u0 z,
                    SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2) := by
              rw [hcoeffEq]
        _ ≤ (A + xq * B) * E := by
              exact mul_le_mul_of_nonneg_left hzLe hA_nonneg
    have hE_nonneg : 0 ≤ E := by
      refine Finset.sum_nonneg ?_
      intro u hu
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) :=
        Real.log_nonneg harg1
      linarith
    have hxq_nonneg : 0 ≤ xq := by
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
        exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
      exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
    have hC_nonneg : 0 ≤ C := by
      simpa [C] using add_nonneg hA_nonneg hB_nonneg
    have hfactor₁ : A + xq * B ≤ C * (1 + xq) := by
      calc
        A + xq * B ≤ A + xq * B + (A * xq + B) := by
          nlinarith [hA_nonneg, hB_nonneg, hxq_nonneg]
        _ = C * (1 + xq) := by
          ring
    have hq1R : (1 : ℝ) ≤ (td.q : ℝ) := by
      exact_mod_cast hq1
    have hxOver_nonneg : 0 ≤ td.X / |ξ| := by
      exact div_nonneg (le_of_lt hX) (abs_nonneg ξ)
    have hxq_le_xOver : xq ≤ td.X / |ξ| := by
      have hxq_eq : xq = (td.X / |ξ|) / (td.q : ℝ) := by
        simp [xq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hxq_eq]
      exact div_le_self hxOver_nonneg hq1R
    have hxOver_le_DQxOver :
        td.X / |ξ| ≤ (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
      have hmul := mul_le_mul_of_nonneg_right hDq hxOver_nonneg
      simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hpart₁ : (1 : ℝ) ≤ (td.D / (td.q : ℝ)) * td.U := by
      have hDq0 : 0 ≤ td.D / (td.q : ℝ) := le_trans (by norm_num) hDq
      have hmul := mul_le_mul hDq hU1 (by norm_num) hDq0
      simpa [one_mul] using hmul
    have hpart₂ : xq ≤ (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
      exact le_trans hxq_le_xOver hxOver_le_DQxOver
    have hfactor₂ :
        1 + xq ≤ (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) := by
      have hsum :
          1 + xq ≤
            (td.D / (td.q : ℝ)) * td.U + (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
        nlinarith [hpart₁, hpart₂]
      have hmul_add :
          (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) =
            (td.D / (td.q : ℝ)) * td.U + (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
        ring
      simpa [hmul_add] using hsum
    have hfactor :
        A + xq * B ≤ C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|)) := by
      calc
        A + xq * B ≤ C * (1 + xq) := hfactor₁
        _ ≤ C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|)) := by
          exact mul_le_mul_of_nonneg_left hfactor₂ hC_nonneg
    have hmul :
        (A + xq * B) * E ≤ (C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|))) * E := by
      exact mul_le_mul_of_nonneg_right hfactor hE_nonneg
    calc
      (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
              (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u‖ ^ 2)
          ≤ (A + xq * B) * E := hmain
      _ ≤ (C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|))) * E := hmul
      _ =
          C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * E) := by
            ring

/-- Geometry-first Step 3 constructor for BG-centered rank-one coefficients with
per-residue reference-index constancy (`constOnUIndex`) assumptions.

This version derives positivity/division side-conditions from natural-parameter hypotheses:
`q ≤ D`, `U ≥ 1`, `X > 0`, `H > 1`. -/
def of_bgTubeRankOne_constOnUIndex_oneAddLog_ofBGGeometry
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU1_nat : 1 ≤ P.U) (hqD_nat : q ≤ P.D)
    (hX_nat : 0 < P.X) (hH1_nat : 1 < P.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (α β : ℤ → ℂ)
    (mRef :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRef r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRef r hr))) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step3FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
  have hU0 : 0 ≤ td.U := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hU1 : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1_nat)
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    have hDqR : (1 : ℝ) ≤ (P.D : ℝ) / (q : ℝ) := one_le_div_of_natCast_le hq hqD_nat
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hDqR
  have hX : 0 < td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX_nat)
  have hH : 0 < td.H := by
    have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1_nat
    have hHR : (0 : ℝ) < (P.H : ℝ) := lt_trans (by norm_num) hH1R
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hHR
  have hXH_td :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH
  simpa [td] using
    (of_bgTubeRankOne_constOnUIndex_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH_td)
      (α := α) (β := β) (mRef := mRef) (hmRef := hmRef) (hβconst := hβconst))

/-- Build a fixed-`F` residue-class Step 3 fiber interface for the BG-centered tube rank-one
coefficients, using the proved one-add-log class-energy bound. -/
def of_bgTubeRankOne_modEq_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step3FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let A : ℝ := (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ)
  let B : ℝ := 1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))
  let C : ℝ := A + B
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) :=
        Real.log_nonneg harg1
      linarith
    simpa [C] using add_nonneg hA_nonneg hB_nonneg
  · intro ξ hξ0 hξH r hr
    have hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H) :=
      mem_Icc_of_abs_le_one_div hξH
    let E : ℝ :=
      ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z,
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2
    let xq : ℝ := td.X / (|ξ| * (td.q : ℝ))
    have hmain :
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u‖ ^ 2)
          ≤
        (A + xq * B) * E := by
      simpa [A, B, E, xq, td] using
        SSU.Engines.TypeII.LargeSieve.BGTubeBridge.step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_outerGeom
          (P := P) (a := a) (q := q) hq hcop
          (ha0 := ha0) (hlower := hlower) (hupper := hupper)
          (r := r) (ξ := ξ) (hξ0 := hξ0)
          (hU0 := hU0) (hX := hX) (hH := hH) (hξI := hξI) (hXH := hXH)
          (α := α) (β := β) (hβmod := hβmod)
    have hE_nonneg : 0 ≤ E := by
      refine Finset.sum_nonneg ?_
      intro u hu
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil td.U := Int.ceil_nonneg hU0
    have hsum1 : (1 : ℤ) ≤ Int.ceil td.U + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil td.U + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil td.U + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil td.U + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil td.U + td.q)) :=
        Real.log_nonneg harg1
      linarith
    have hxq_nonneg : 0 ≤ xq := by
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
        exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
      exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
    have hC_nonneg : 0 ≤ C := by
      simpa [C] using add_nonneg hA_nonneg hB_nonneg
    have hfactor₁ : A + xq * B ≤ C * (1 + xq) := by
      calc
        A + xq * B ≤ A + xq * B + (A * xq + B) := by
          nlinarith [hA_nonneg, hB_nonneg, hxq_nonneg]
        _ = C * (1 + xq) := by
          ring
    have hq1R : (1 : ℝ) ≤ (td.q : ℝ) := by
      exact_mod_cast hq1
    have hxOver_nonneg : 0 ≤ td.X / |ξ| := by
      exact div_nonneg (le_of_lt hX) (abs_nonneg ξ)
    have hxq_le_xOver : xq ≤ td.X / |ξ| := by
      have hxq_eq : xq = (td.X / |ξ|) / (td.q : ℝ) := by
        simp [xq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hxq_eq]
      exact div_le_self hxOver_nonneg hq1R
    have hxOver_le_DQxOver :
        td.X / |ξ| ≤ (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
      have hmul := mul_le_mul_of_nonneg_right hDq hxOver_nonneg
      simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hpart₁ : (1 : ℝ) ≤ (td.D / (td.q : ℝ)) * td.U := by
      have hmul := mul_le_mul hDq hU1 (by positivity) (by positivity)
      simpa [one_mul] using hmul
    have hpart₂ : xq ≤ (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
      exact le_trans hxq_le_xOver hxOver_le_DQxOver
    have hfactor₂ :
        1 + xq ≤ (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) := by
      have hsum :
          1 + xq ≤
            (td.D / (td.q : ℝ)) * td.U + (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
        nlinarith [hpart₁, hpart₂]
      have hmul_add :
          (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) =
            (td.D / (td.q : ℝ)) * td.U + (td.D / (td.q : ℝ)) * (td.X / |ξ|) := by
        ring
      simpa [hmul_add] using hsum
    have hfactor :
        A + xq * B ≤ C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|)) := by
      calc
        A + xq * B ≤ C * (1 + xq) := hfactor₁
        _ ≤ C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|)) := by
          exact mul_le_mul_of_nonneg_left hfactor₂ hC_nonneg
    have hmul :
        (A + xq * B) * E ≤ (C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|))) * E := by
      exact mul_le_mul_of_nonneg_right hfactor hE_nonneg
    calc
      (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ
              (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) u‖ ^ 2)
          ≤ (A + xq * B) * E := hmain
      _ ≤ (C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|))) * E := hmul
      _ =
          C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * E) := by
            ring

/-- Interval-geometry wrapper for residue-class Step 3 fiber bounds. -/
theorem bound_outerGeom (h3R : Step3FiberLargeSieveByResidueFor td F)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H))
    (r : ℤ)
    (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td) :
    (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
        ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
      ≤
    h3R.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
      (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2)) := by
  exact h3R.bound ξ hξ0 (abs_le_one_div_of_mem_Icc hξI) r hr

end Step3FiberLargeSieveByResidueFor

namespace Step3FiberLargeSieveFor

/-- Sum residue-class Step 3 bounds into a fixed-`F` Step 3 fiber bound. -/
def of_byResidue (td : TubeData) (F : TubePoint → ℂ)
    (hR : Step3FiberLargeSieveByResidueFor td F) :
    Step3FiberLargeSieveFor td F := by
  classical
  refine ⟨hR.C, hR.C_nonneg, ?_⟩
  intro ξ hξ0 hξH
  have hL :
      (∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
        =
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
        ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2 := by
    simpa using
      (SSU.Engines.TypeII.LargeSieve.sum_uSet_norm_innerSumUZ_sq_eq_sum_residueClasses
        (td := td) (ξ := ξ) (F := F))
  have hE :
      (∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2)
        =
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
        ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2 := by
    simpa using
      (SSU.Engines.TypeII.LargeSieve.ResiduePartition.sum_uSet_eq_sum_residueClasses
        (td := td)
        (f := fun u : ℤ =>
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2))
  have hsum :
      (∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
        ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
        ≤
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
        hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
          (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2)) := by
    refine Finset.sum_le_sum ?_
    intro r hr
    exact hR.bound ξ hξ0 hξH r hr
  calc
    (∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
        ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
        =
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
        ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2 := hL
    _ ≤
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
        hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
          (∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2)) := hsum
    _ =
      hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
        (∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td,
          ∑ u ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uClass td r,
            ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2)) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
      hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) *
        (∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2)) := by
            simpa [hE]
    _ =
      hR.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
            have hEnergy :
                (∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
                  ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSet td u,
                    ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td u z, F p‖ ^ 2)
                  = tubeEnergy td.T F := by
              simpa using
                (SSU.Engines.TypeII.LargeSieve.sum_u_z_norm_fiberUZ_sum_sq_eq_tubeEnergy
                  (td := td) (F := F))
            rw [hEnergy]

/-- Interval-geometry wrapper for fixed-`F` Step 3 fiber bounds. -/
theorem bound_outerGeom (h3F : Step3FiberLargeSieveFor td F)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H)) :
    (∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
        ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2)
      ≤
    h3F.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
  exact h3F.bound ξ hξ0 (abs_le_one_div_of_mem_Icc hξI)

end Step3FiberLargeSieveFor

namespace Step3LargeSieveOuterUFor

/-- Deterministic Step 3 reduction (`typeIISum` outer-u Cauchy step) for fixed `F`. -/
def of_fiberLargeSieveFor (td : TubeData) (F : TubePoint → ℂ)
    (hLS : Step3FiberLargeSieveFor td F) :
    Step3LargeSieveOuterUFor td F := by
  classical
  refine ⟨hLS.C * (SSU.Engines.TypeII.LargeSieve.uSet td).card,
    mul_nonneg hLS.C_nonneg (by positivity), ?_⟩
  intro ξ hξ0 hξH
  have hdecomp := SSU.Engines.TypeII.LargeSieve.typeIISum_eq_outer_u_innerUZ
    (td := td) (ξ := ξ) (F := F)
  have hcs :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      ((SSU.Engines.TypeII.LargeSieve.uSet td).card : ℝ) *
        ∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2 := by
    have hcs' :
        ‖∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
            (e (ξ * (u : ℝ) * (SSU.Engines.TypeII.LargeSieve.vResidue td u : ℝ) /
                ((td.q : ℝ) * td.X))) *
              SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2
          ≤
        ((SSU.Engines.TypeII.LargeSieve.uSet td).card : ℝ) *
          ∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
            ‖(e (ξ * (u : ℝ) * (SSU.Engines.TypeII.LargeSieve.vResidue td u : ℝ) /
                ((td.q : ℝ) * td.X))) *
                SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2 := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.norm_sum_sq_le_card_mul_sum_norm_sq
          (s := SSU.Engines.TypeII.LargeSieve.uSet td)
          (f := fun u =>
            (e (ξ * (u : ℝ) * (SSU.Engines.TypeII.LargeSieve.vResidue td u : ℝ) /
                ((td.q : ℝ) * td.X))) *
              SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u))
    have hsimp :
        ∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
            (‖e (ξ * (u : ℝ) * (SSU.Engines.TypeII.LargeSieve.vResidue td u : ℝ) /
                ((td.q : ℝ) * td.X))‖ *
                ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖) ^ 2
          =
        ∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      simp [SSU.Engines.TypeII.norm_e]
    simpa [hdecomp, hsimp] using hcs'
  have hLS' := hLS.bound ξ hξ0 hξH
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ ((SSU.Engines.TypeII.LargeSieve.uSet td).card : ℝ) *
            ∑ u ∈ SSU.Engines.TypeII.LargeSieve.uSet td,
              ‖SSU.Engines.TypeII.LargeSieve.innerSumUZ td ξ F u‖ ^ 2 := hcs
    _ ≤ ((SSU.Engines.TypeII.LargeSieve.uSet td).card : ℝ) *
          (hLS.C * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F)) := by
          exact mul_le_mul_of_nonneg_left hLS' (by positivity)
    _ = (hLS.C * (SSU.Engines.TypeII.LargeSieve.uSet td).card) *
          ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
          ring

/-- Build a Step 3 use-site bound from residue-class fiber bounds for the same fixed `F`. -/
def of_fiberLargeSieveByResidueFor (td : TubeData) (F : TubePoint → ℂ)
    (hR : Step3FiberLargeSieveByResidueFor td F) :
    Step3LargeSieveOuterUFor td F :=
  of_fiberLargeSieveFor td F (Step3FiberLargeSieveFor.of_byResidue td F hR)

/-- Build a use-site Step 3 outer-`u` bound from per-residue common-domain fiber equalities
(`hZeq` + `hEqOn`) via the one-add-log residue-class finite-large-sieve envelope. -/
def of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
    (td : TubeData)
    (hU0 : 0 ≤ td.U) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) z, F p)) :
    Step3LargeSieveOuterUFor td F :=
  of_fiberLargeSieveByResidueFor td F
    (Step3FiberLargeSieveByResidueFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
      (td := td) (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH)
      (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn))

/-- Explicit constant formula for the generic one-add-log Step-3 `hZeq`/`hEqOn` constructor. -/
theorem of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog_C_eq_formula
    (td : TubeData)
    (hU0 : 0 ≤ td.U) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) z, F p)) :
    (of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
      (td := td) (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH)
      (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn)).C
      =
    (((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ)
      + (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) : ℝ)
      * ((SSU.Engines.TypeII.LargeSieve.uSet td).card : ℝ) := by
  simp [of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog,
    of_fiberLargeSieveByResidueFor,
    of_fiberLargeSieveFor,
    Step3FiberLargeSieveFor.of_byResidue,
    Step3FiberLargeSieveByResidueFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog,
    mul_assoc, mul_left_comm, mul_comm]

/-- Canonical coefficient-independent envelope constant for the generic one-add-log Step-3
`hZeq`/`hEqOn` constructor. -/
noncomputable def sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC
    (td : TubeData) : ℝ :=
  (((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ)
      + (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) : ℝ) *
    ((SSU.Engines.TypeII.LargeSieve.uSet td).card : ℝ)

theorem sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC_nonneg
    (td : TubeData) (hU0 : 0 ≤ td.U) :
    0 ≤ sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC (td := td) := by
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
    have hz0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxN td : ℝ) := by positivity
    linarith
  exact mul_nonneg hmain (by positivity)

theorem of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog_C_le_sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC
    (td : TubeData)
    (hU0 : 0 ≤ td.U) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRef r hr)) z, F p)) :
    (of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
      (td := td) (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH)
      (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn)).C
      ≤
    sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC (td := td) := by
  exact le_of_eq <| by
    simpa [sumFiberUZ_uFromIndexEqRefOnZSetOneAddLogC] using
      (of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog_C_eq_formula
        (td := td) (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
        (hX := hX) (hH := hH) (hXH := hXH)
        (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn))

/-- Build a use-site Step 3 outer-u bound for BG-centered rank-one coefficients (modEq route),
using the proved one-add-log residue-class Step 3 fiber bound. -/
def of_bgTubeRankOne_modEq_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 :
      0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step3LargeSieveOuterUFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let hR : Step3FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) :=
    Step3FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := α) (β := β) (hβmod := hβmod)
  exact of_fiberLargeSieveByResidueFor td _ hR

/-- Geometry-first Step 3 constructor for BG-centered rank-one/modEq coefficients.

This version derives positivity/division side-conditions from natural-parameter hypotheses:
`q ≤ D`, `U ≥ 1`, `X > 0`, `H > 1`. -/
def of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU1_nat : 1 ≤ P.U) (hqD_nat : q ≤ P.D)
    (hX_nat : 0 < P.X) (hH1_nat : 1 < P.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          β u₁ = β u₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step3LargeSieveOuterUFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
  have hU0 : 0 ≤ td.U := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hU1 : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1_nat)
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    have hDqR : (1 : ℝ) ≤ (P.D : ℝ) / (q : ℝ) := one_le_div_of_natCast_le hq hqD_nat
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hDqR
  have hX : 0 < td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX_nat)
  have hH : 0 < td.H := by
    have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1_nat
    have hHR : (0 : ℝ) < (P.H : ℝ) := lt_trans (by norm_num) hH1R
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hHR
  have hXH_td :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH
  simpa [td] using
    (of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH_td)
      (α := α) (β := β) (hβmod := hβmod))

/-- The BG rank-one/modEq Step-3 constructor has a deterministic `C`
independent of `α`,`β` and `hβmod`. -/
theorem of_bgTubeRankOne_modEq_oneAddLog_C_eq
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β α' β' : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          β u₁ = β u₂)
    (hβmod' :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          β' u₁ = β' u₂) :
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := α) (β := β) (hβmod := hβmod)).C)
      =
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := α') (β := β') (hβmod := hβmod')).C) := by
  simp only [of_bgTubeRankOne_modEq_oneAddLog,
    Step3FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog,
    of_fiberLargeSieveByResidueFor,
    of_fiberLargeSieveFor,
    Step3FiberLargeSieveFor.of_byResidue]

/-- Canonical coefficient-independent envelope constant for BG rank-one/modEq Step 3. -/
noncomputable def bgRankOneModEqOneAddLogC
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H) : ℝ :=
  (of_bgTubeRankOne_modEq_oneAddLog
    (P := P) (a := a) (q := q) hq hcop
    (ha0 := ha0) (hlower := hlower) (hupper := hupper)
    (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
    (α := fun _ => (0 : ℂ)) (β := fun _ => (0 : ℂ))
    (hβmod := by intro _ _ _; simp)).C

theorem bgRankOneModEqOneAddLogC_nonneg
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H) :
    0 ≤ bgRankOneModEqOneAddLogC
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH) := by
  simpa [bgRankOneModEqOneAddLogC] using
    (of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := fun _ => (0 : ℂ)) (β := fun _ => (0 : ℂ))
      (hβmod := by intro _ _ _; simp)).C_nonneg

theorem of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          β u₁ = β u₂) :
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := α) (β := β) (hβmod := hβmod)).C)
      ≤
    bgRankOneModEqOneAddLogC
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH) := by
  have hEq :
      ((of_bgTubeRankOne_modEq_oneAddLog
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
        (α := α) (β := β) (hβmod := hβmod)).C)
        =
      bgRankOneModEqOneAddLogC
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH) := by
    simpa [bgRankOneModEqOneAddLogC] using
      of_bgTubeRankOne_modEq_oneAddLog_C_eq
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
        (α := α) (β := β) (α' := fun _ => (0 : ℂ)) (β' := fun _ => (0 : ℂ))
        (hβmod := hβmod)
        (hβmod' := by intro _ _ _; simp)
  exact le_of_eq hEq

end Step3LargeSieveOuterUFor

/-- TeX Step 4 large-sieve bound, but only for a fixed coefficient array `F`. -/
structure Step4LargeSieveOuterVFor (td : TubeData) (F : TubePoint → ℂ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F)

namespace Step4LargeSieveOuterVFor

/-- Any global `Step4LargeSieveOuterV td` instance yields a use-site bound for a fixed `F`. -/
def of_global (td : TubeData) (h4 : Step4LargeSieveOuterV td) (F : TubePoint → ℂ) :
    Step4LargeSieveOuterVFor td F :=
  ⟨h4.C, h4.C_nonneg, fun ξ hξ0 hξH => h4.bound ξ hξ0 hξH F⟩

/-- Build a use-site Step 4 bound from a Step 4 Montgomery–Vaughan hypothesis. -/
def of_montgomeryVaughan
    (td : TubeData)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td)
    (hD : 0 ≤ td.D) (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (F : TubePoint → ℂ) :
    Step4LargeSieveOuterVFor td F := by
  let hFiber : SSU.Engines.TypeII.LargeSieve.Step4FiberLargeSieve td :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := td) (hMV := h4MV) hD hU hX
  let h4 : Step4LargeSieveOuterV td :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := td) hFiber
  exact of_global td h4 F

/-- Build a use-site Step 4 bound from a per-residue Step 4 Montgomery–Vaughan hypothesis. -/
def of_montgomeryVaughan_byResidue
    (td : TubeData)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td)
    (hD : 0 ≤ td.D) (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (F : TubePoint → ℂ) :
    Step4LargeSieveOuterVFor td F := by
  exact
    of_montgomeryVaughan
      (td := td)
      (h4MV := SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue td h4MV)
      (hD := hD) (hU := hU) (hX := hX) F

/-- Build a use-site Step 4 bound from pure box geometry (`card zSetV` fallback). -/
def of_box_geometry
    (td : TubeData)
    (hU : 0 ≤ td.U) (hX : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hXH1 : 1 ≤ td.X * td.H)
    (F : TubePoint → ℂ) :
    Step4LargeSieveOuterVFor td F := by
  exact
    of_montgomeryVaughan
      (td := td)
      (h4MV := SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_box_geometry
        (td := td) (hU := hU) (hX := hX) (hD1 := hD1) (hXH1 := hXH1))
      (hD := le_trans (show (0 : ℝ) ≤ 1 by norm_num) hD1)
      (hU := hU)
      (hX := hX)
      F

/-- Build a use-site TeX Step 4 bound from the constant-coefficient hypothesis
`∀ v ∈ vSet, coeffVZFin td F v = a`. -/
def of_constCoeffVZFin
    (td : TubeData)
    (hXH1 : 1 ≤ td.X * td.H) (hD1 : 1 ≤ td.D) (hU0 : 0 ≤ td.U) (hD0 : 0 ≤ td.D)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH_v : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (aV : Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td) → ℂ)
    (hCoeffV : ∀ v : ℤ, v ∈ SSU.Engines.TypeII.LargeSieve.vSet td →
      SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F v = aV) :
    Step4LargeSieveOuterVFor td F :=
by
  classical
  let C : ℝ :=
    (((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ) +
        max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0) : ℝ)
  refine ⟨C, ?_, ?_⟩
  ·
    have hN : 0 ≤ (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ) := by positivity
    have hB : 0 ≤ (max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0 : ℝ) := by
      simp
    exact add_nonneg hN hB
  · intro ξ hξ0 hξH
    simpa [C] using
      (SSU.Engines.TypeII.LargeSieve.ConstCoeffTeX.norm_typeIISum_sq_le_step4_teX_of_constCoeffVZFin
        (td := td)
        (hXH1 := hXH1) (hD1 := hD1) (hU0 := hU0) (hD0 := hD0)
        (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH)
        (hXH := hXH_v)
        (F := F) (a := aV) (hCoeff := hCoeffV))

/-- Interval-geometry wrapper for use-site Step 4 outer-v bounds. -/
theorem bound_outerGeom (h4 : Step4LargeSieveOuterVFor td F)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H)) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    h4.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
  exact h4.bound ξ hξ0 (abs_le_one_div_of_mem_Icc hξI)

end Step4LargeSieveOuterVFor

/-- Step 4 fiber large-sieve hypothesis specialized to a fixed coefficient array `F`. -/
structure Step4FiberLargeSieveFor (td : TubeData) (F : TubePoint → ℂ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      (∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
        ≤
      C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F)

/-- Step 4 fiber large-sieve hypothesis on each residue class, specialized to fixed `F`. -/
structure Step4FiberLargeSieveByResidueFor (td : TubeData) (F : TubePoint → ℂ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ ξ : ℝ, ξ ≠ 0 → |ξ| ≤ (1 / td.H) →
      ∀ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
          ≤
        C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
            (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
              ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
                ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2))

namespace Step4FiberLargeSieveByResidueFor

set_option maxHeartbeats 1000000

/-- Build the fixed-`F` residue-class Step 4 fiber interface from the global residue-class
Montgomery–Vaughan hypothesis by specialization in `F`. -/
def of_montgomeryVaughanByResidue
    (td : TubeData)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td)
    (F : TubePoint → ℂ) :
    Step4FiberLargeSieveByResidueFor td F :=
  ⟨h4MV.C, h4MV.C_nonneg, fun ξ hξ0 hξH r hr => h4MV.bound ξ hξ0 hξH F r hr⟩

/-- Build a fixed-`F` residue-class Step 4 fiber interface from per-residue reference-fiber
equalities on a common `zSetV` domain (the geometry-friendly `hZeq` + `hEqOn` package), using the
explicit one-add-log envelope. -/
def of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
    (td : TubeData)
    (hD0 : 0 ≤ td.D) (hD1 : 1 ≤ td.D) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) z, F p)) :
    Step4FiberLargeSieveByResidueFor td F := by
  let A : ℝ := (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ)
  let B : ℝ := 1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))
  let C : ℝ := A + B
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) :=
        Real.log_nonneg harg1
      linarith
    simpa [C] using add_nonneg hA_nonneg hB_nonneg
  · intro ξ hξ0 hξH r hr
    have hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H) :=
      mem_Icc_of_abs_le_one_div hξH
    let E : ℝ :=
      ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2
    let xq : ℝ := td.X / (|ξ| * (td.q : ℝ))
    let m0 : ℤ := mRef r hr
    have hm0 : m0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r := hmRef r hr
    let v0 : ℤ := SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m0
    have hv0 : v0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r := by
      simpa [v0] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_mem_vClass_of_mem_vIndexSet
          (td := td) (r := r) (m := m0) hm0)
    have hCoeff :
        ∀ m : ℤ, m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m0) :=
      SSU.Engines.TypeII.LargeSieve.ConstCoeffFromFiber.constCoeffVZFin_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV
        (td := td) (F := F) (r := r) (m0 := m0) (_hm0 := hm0)
        (hZeq := fun m hm => hZeq r hr m hm)
        (hEqOn := fun m hm z hz => hEqOn r hr m hm z hz)
    have hindex :
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
          ≤
        (A + xq * B) *
          (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
      simpa [A, B, xq] using
        SSU.Engines.TypeII.LargeSieve.FiberFromFiniteLargeSieve.step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_one_add_log_outerGeom
          (td := td) (hD0 := hD0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
          (hξI := hξI) (hXH := hXH)
          (F := F)
          (a := SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F
            (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m0))
          (hCoeff := hCoeff)
    have hclassEq :
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
          =
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2) := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet
          (td := td) (ξ := ξ) (F := F) (r := r))
    have hcoeffEq :
        (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F v0 k‖ ^ 2)
          =
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v0 z, F p‖ ^ 2) := by
      simpa [v0] using
        (SSU.Engines.TypeII.LargeSieve.ConstCoeffMV.sum_univ_norm_coeffVZFin_sq_eq_sum_zSetV_norm_fiberVZ_sum_sq
          (td := td) (F := F) (v := v0))
    have hzLe :
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v0 z, F p‖ ^ 2)
          ≤ E := by
      have hnonneg :
          ∀ v : ℤ, v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r →
            0 ≤ (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2 : ℝ) := by
        intro v hv
        refine Finset.sum_nonneg ?_
        intro z hz
        positivity
      simpa [E] using Finset.single_le_sum hnonneg hv0
    have hmain :
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
          ≤
        (A + xq * B) * E := by
      have hindex' :
          (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
              ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F v0 k‖ ^ 2) := by
        simpa [hclassEq, v0] using hindex
      have hA_nonneg : 0 ≤ A + xq * B := by
        have hA0 : 0 ≤ A := by positivity
        have hB0 : 0 ≤ B := by
          have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
          have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
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
          linarith
        have hxq0 : 0 ≤ xq := by
          have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
            exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
          exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
        exact add_nonneg hA0 (mul_nonneg hxq0 hB0)
      calc
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td F v0 k‖ ^ 2) := hindex'
        _ = (A + xq * B) *
              (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v0,
                ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v0 z, F p‖ ^ 2) := by
              rw [hcoeffEq]
        _ ≤ (A + xq * B) * E := by
              exact mul_le_mul_of_nonneg_left hzLe hA_nonneg
    have hE_nonneg : 0 ≤ E := by
      refine Finset.sum_nonneg ?_
      intro v hv
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) :=
        Real.log_nonneg harg1
      linarith
    have hxq_nonneg : 0 ≤ xq := by
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
        exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
      exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
    have hC_nonneg : 0 ≤ C := by
      simpa [C] using add_nonneg hA_nonneg hB_nonneg
    have hfactor₁ : A + xq * B ≤ C * (1 + xq) := by
      calc
        A + xq * B ≤ A + xq * B + (A * xq + B) := by
          nlinarith [hA_nonneg, hB_nonneg, hxq_nonneg]
        _ = C * (1 + xq) := by
          ring
    have hq1R : (1 : ℝ) ≤ (td.q : ℝ) := by
      exact_mod_cast hq1
    have hD1R : (1 : ℝ) ≤ td.D := by simpa using hD1
    have hxOver_nonneg : 0 ≤ td.X / |ξ| := by
      exact div_nonneg (le_of_lt hX) (abs_nonneg ξ)
    have hxq_le_xOver : xq ≤ td.X / |ξ| := by
      have hxq_eq : xq = (td.X / |ξ|) / (td.q : ℝ) := by
        simp [xq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hxq_eq]
      exact div_le_self hxOver_nonneg hq1R
    have hxOver_le_DxOver :
        td.X / |ξ| ≤ td.D * (td.X / |ξ|) := by
      have hmul := mul_le_mul_of_nonneg_right hD1R hxOver_nonneg
      simpa [one_mul] using hmul
    have hpart₁ : (1 : ℝ) ≤ td.D * (td.U / (td.q : ℝ)) := by
      have hDq0 : 0 ≤ td.D / (td.q : ℝ) := le_trans (by norm_num) hDq
      have hmul := mul_le_mul hDq hU1 (by norm_num) hDq0
      have hmul' : (1 : ℝ) ≤ (td.D / (td.q : ℝ)) * td.U := by simpa [one_mul] using hmul
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul'
    have hpart₂ : xq ≤ td.D * (td.X / |ξ|) := by
      exact le_trans hxq_le_xOver hxOver_le_DxOver
    have hfactor₂ :
        1 + xq ≤ td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) := by
      have hsum : 1 + xq ≤ td.D * (td.U / (td.q : ℝ)) + td.D * (td.X / |ξ|) := by
        nlinarith [hpart₁, hpart₂]
      have hmul_add :
          td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)
            = td.D * (td.U / (td.q : ℝ)) + td.D * (td.X / |ξ|) := by
        ring
      simpa [hmul_add] using hsum
    have hfactor :
        A + xq * B ≤ C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)) := by
      calc
        A + xq * B ≤ C * (1 + xq) := hfactor₁
        _ ≤ C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)) := by
          exact mul_le_mul_of_nonneg_left hfactor₂ hC_nonneg
    have hmul :
        (A + xq * B) * E ≤ (C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|))) * E := by
      exact mul_le_mul_of_nonneg_right hfactor hE_nonneg
    calc
      (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
          ≤ (A + xq * B) * E := hmain
      _ ≤ (C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|))) * E := hmul
      _ = C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * E) := by
            ring

/-- Build a fixed-`F` residue-class Step 4 fiber interface for the BG-centered tube rank-one
coefficients, using the proved one-add-log class-energy bound. -/
def of_bgTubeRankOne_constOnVIndex_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (mRef :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRef r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRef r hr))) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step4FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let A : ℝ := (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ)
  let B : ℝ := 1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))
  let C : ℝ := A + B
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) :=
        Real.log_nonneg harg1
      linarith
    simpa [C] using add_nonneg hA_nonneg hB_nonneg
  · intro ξ hξ0 hξH r hr
    have hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H) :=
      mem_Icc_of_abs_le_one_div hξH
    let E : ℝ :=
      ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z,
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2
    let xq : ℝ := td.X / (|ξ| * (td.q : ℝ))
    have hr' : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
        (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) := by
      simpa [td] using hr
    let m0 : ℤ := mRef r hr'
    have hm0 : m0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r := by
      have hm0' := hmRef r hr'
      simpa [td, m0] using hm0'
    let v0 : ℤ := SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m0
    have hv0 : v0 ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r := by
      simpa [v0] using
        (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex_mem_vClass_of_mem_vIndexSet
          (td := td) (r := r) (m := m0) hm0)
    have hαconst_r :
        ∀ m : ℤ, m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)
            = α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m0) := by
      intro m hm
      have hm' : m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r := by
        simpa [td] using hm
      simpa [td, m0] using hαconst r hr' m hm'
    have hindex :
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
          ≤
        (A + xq * B) *
          (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
      simpa [A, B, xq, td] using
        SSU.Engines.TypeII.LargeSieve.BGTubeBridge.step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_one_add_log_outerGeom
          (P := P) (a := a) (q := q) hq hcop
          (ha0 := ha0) (hlower := hlower) (hupper := hupper)
          (r := r) (ξ := ξ) (hξ0 := hξ0)
          (hD0 := hD0) (hX := hX) (hH := hH) (hξI := hξI) (hXH := hXH)
          (α := α) (β := β) (m0 := m0) (hm0 := hm0) (hαconst := hαconst_r)
    have hclassEq :
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v‖ ^ 2)
          =
        (∑ m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2) := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet
          (td := td) (ξ := ξ)
          (F := SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) (r := r))
    have hcoeffEq :
        (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
            ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v0 k‖ ^ 2)
          =
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v0 z,
                SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2) := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.ConstCoeffMV.sum_univ_norm_coeffVZFin_sq_eq_sum_zSetV_norm_fiberVZ_sum_sq
          (td := td) (F := SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) (v := v0))
    have hzLe :
        (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v0,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v0 z,
                SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2)
          ≤ E := by
      have hnonneg :
          ∀ v : ℤ, v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r →
            0 ≤ (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z,
                  SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2 : ℝ) := by
        intro v hv
        refine Finset.sum_nonneg ?_
        intro z hz
        positivity
      simpa [E] using Finset.single_le_sum hnonneg hv0
    have hmain :
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v‖ ^ 2)
          ≤
        (A + xq * B) * E := by
      have hindex' :
          (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
              ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
                  (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td
                  (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v0 k‖ ^ 2) := by
        simpa [hclassEq, v0] using hindex
      have hA_nonneg : 0 ≤ A + xq * B := by
        have hA0 : 0 ≤ A := by positivity
        have hB0 : 0 ≤ B := by
          have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
          have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
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
          linarith
        have hxq0 : 0 ≤ xq := by
          have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
            exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
          exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
        exact add_nonneg hA0 (mul_nonneg hxq0 hB0)
      calc
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v‖ ^ 2)
            ≤
          (A + xq * B) *
            (∑ k ∈ (Finset.univ : Finset (Fin (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td))),
              ‖SSU.Engines.TypeII.LargeSieve.ZBoxToFin.coeffVZFin td
                  (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v0 k‖ ^ 2) := hindex'
        _ = (A + xq * B) *
              (∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v0,
                ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v0 z,
                    SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2) := by
              rw [hcoeffEq]
        _ ≤ (A + xq * B) * E := by
              exact mul_le_mul_of_nonneg_left hzLe hA_nonneg
    have hE_nonneg : 0 ≤ E := by
      refine Finset.sum_nonneg ?_
      intro v hv
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) :=
        Real.log_nonneg harg1
      linarith
    have hxq_nonneg : 0 ≤ xq := by
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
        exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
      exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
    have hC_nonneg : 0 ≤ C := by
      simpa [C] using add_nonneg hA_nonneg hB_nonneg
    have hfactor₁ : A + xq * B ≤ C * (1 + xq) := by
      calc
        A + xq * B ≤ A + xq * B + (A * xq + B) := by
          nlinarith [hA_nonneg, hB_nonneg, hxq_nonneg]
        _ = C * (1 + xq) := by
          ring
    have hq1R : (1 : ℝ) ≤ (td.q : ℝ) := by
      exact_mod_cast hq1
    have hxOver_nonneg : 0 ≤ td.X / |ξ| := by
      exact div_nonneg (le_of_lt hX) (abs_nonneg ξ)
    have hxq_le_xOver : xq ≤ td.X / |ξ| := by
      have hxq_eq : xq = (td.X / |ξ|) / (td.q : ℝ) := by
        simp [xq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hxq_eq]
      exact div_le_self hxOver_nonneg hq1R
    have hxOver_le_DxOver :
        td.X / |ξ| ≤ td.D * (td.X / |ξ|) := by
      nlinarith [hD1, hxOver_nonneg]
    have hpart₁ : (1 : ℝ) ≤ td.D * (td.U / (td.q : ℝ)) := by
      have hDq0 : 0 ≤ td.D / (td.q : ℝ) := le_trans (by norm_num) hDq
      have hmul := mul_le_mul hDq hU1 (by norm_num) hDq0
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hpart₂ : xq ≤ td.D * (td.X / |ξ|) := by
      exact le_trans hxq_le_xOver hxOver_le_DxOver
    have hfactor₂ :
        1 + xq ≤ td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) := by
      have hsum :
          1 + xq ≤
            td.D * (td.U / (td.q : ℝ)) + td.D * (td.X / |ξ|) := by
        nlinarith [hpart₁, hpart₂]
      have hmul_add :
          td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) =
            td.D * (td.U / (td.q : ℝ)) + td.D * (td.X / |ξ|) := by
        ring
      simpa [hmul_add] using hsum
    have hfactor :
        A + xq * B ≤ C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)) := by
      calc
        A + xq * B ≤ C * (1 + xq) := hfactor₁
        _ ≤ C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)) := by
          exact mul_le_mul_of_nonneg_left hfactor₂ hC_nonneg
    have hmul :
        (A + xq * B) * E ≤ (C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|))) * E := by
      exact mul_le_mul_of_nonneg_right hfactor hE_nonneg
    calc
      (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
              (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v‖ ^ 2)
          ≤ (A + xq * B) * E := hmain
      _ ≤ (C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|))) * E := hmul
      _ =
          C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * E) := by
            ring

set_option maxHeartbeats 200000

/-- Geometry-first Step 4 constructor for BG-centered rank-one coefficients with
per-residue reference-index constancy (`constOnVIndex`) assumptions.

This version derives positivity/division side-conditions from natural-parameter hypotheses:
`q ≤ D`, `D ≥ 1`, `U ≥ 1`, `X > 0`, `H > 1`. -/
def of_bgTubeRankOne_constOnVIndex_oneAddLog_ofBGGeometry
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1_nat : 1 ≤ P.D) (hU1_nat : 1 ≤ P.U) (hqD_nat : q ≤ P.D)
    (hX_nat : 0 < P.X) (hH1_nat : 1 < P.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (α β : ℤ → ℂ)
    (mRef :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRef :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRef r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRef r hr))) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step4FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
  have hD0 : 0 ≤ td.D := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hD1 : 1 ≤ td.D := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast hD1_nat)
  have hU1 : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1_nat)
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    have hDqR : (1 : ℝ) ≤ (P.D : ℝ) / (q : ℝ) := one_le_div_of_natCast_le hq hqD_nat
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hDqR
  have hX : 0 < td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX_nat)
  have hH : 0 < td.H := by
    have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1_nat
    have hHR : (0 : ℝ) < (P.H : ℝ) := lt_trans (by norm_num) hH1R
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hHR
  have hXH_td :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH
  simpa [td] using
    (of_bgTubeRankOne_constOnVIndex_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH_td)
      (α := α) (β := β) (mRef := mRef) (hmRef := hmRef) (hαconst := hαconst))

/-- Build a fixed-`F` residue-class Step 4 fiber interface for the BG-centered tube rank-one
coefficients, using the proved one-add-log class-energy bound. -/
def of_bgTubeRankOne_modEq_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step4FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let A : ℝ := (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ)
  let B : ℝ := 1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))
  let C : ℝ := A + B
  refine ⟨C, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) :=
        Real.log_nonneg harg1
      linarith
    simpa [C] using add_nonneg hA_nonneg hB_nonneg
  · intro ξ hξ0 hξH r hr
    have hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H) :=
      mem_Icc_of_abs_le_one_div hξH
    let E : ℝ :=
      ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z,
              SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β p‖ ^ 2
    let xq : ℝ := td.X / (|ξ| * (td.q : ℝ))
    have hmain :
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
                (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v‖ ^ 2)
          ≤
        (A + xq * B) * E := by
      simpa [A, B, E, xq, td] using
        SSU.Engines.TypeII.LargeSieve.BGTubeBridge.step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy_outerGeom
          (P := P) (a := a) (q := q) hq hcop
          (ha0 := ha0) (hlower := hlower) (hupper := hupper)
          (r := r) (ξ := ξ) (hξ0 := hξ0)
          (hD0 := hD0) (hX := hX) (hH := hH) (hξI := hξI) (hXH := hXH)
          (α := α) (β := β) (hαmod := hαmod)
    have hE_nonneg : 0 ≤ E := by
      refine Finset.sum_nonneg ?_
      intro v hv
      refine Finset.sum_nonneg ?_
      intro z hz
      positivity
    have hA_nonneg : 0 ≤ A := by positivity
    have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
    have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
    have hsum1 : (1 : ℤ) ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have hsum0 : 0 ≤ Int.ceil (2 * td.D) + td.q := by linarith
    have htoNat1 : (1 : ℕ) ≤ Int.toNat (Int.ceil (2 * td.D) + td.q) := by
      exact (Int.le_toNat hsum0).2 hsum1
    have hB_nonneg : 0 ≤ B := by
      have harg1 : (1 : ℝ) ≤ (2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
        have htoNatR : (1 : ℝ) ≤ (Int.toNat (Int.ceil (2 * td.D) + td.q) : ℝ) := by
          exact_mod_cast htoNat1
        nlinarith
      have hlog_nonneg : 0 ≤ Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)) :=
        Real.log_nonneg harg1
      linarith
    have hxq_nonneg : 0 ≤ xq := by
      have hden_pos : 0 < |ξ| * (td.q : ℝ) := by
        exact mul_pos (abs_pos.mpr hξ0) (by exact_mod_cast td.q_pos)
      exact div_nonneg (le_of_lt hX) (le_of_lt hden_pos)
    have hC_nonneg : 0 ≤ C := by
      simpa [C] using add_nonneg hA_nonneg hB_nonneg
    have hfactor₁ : A + xq * B ≤ C * (1 + xq) := by
      calc
        A + xq * B ≤ A + xq * B + (A * xq + B) := by
          nlinarith [hA_nonneg, hB_nonneg, hxq_nonneg]
        _ = C * (1 + xq) := by
          ring
    have hq1R : (1 : ℝ) ≤ (td.q : ℝ) := by
      exact_mod_cast hq1
    have hxOver_nonneg : 0 ≤ td.X / |ξ| := by
      exact div_nonneg (le_of_lt hX) (abs_nonneg ξ)
    have hxq_le_xOver : xq ≤ td.X / |ξ| := by
      have hxq_eq : xq = (td.X / |ξ|) / (td.q : ℝ) := by
        simp [xq, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hxq_eq]
      exact div_le_self hxOver_nonneg hq1R
    have hxOver_le_DxOver :
        td.X / |ξ| ≤ td.D * (td.X / |ξ|) := by
      have hmul := mul_le_mul_of_nonneg_right hD1 hxOver_nonneg
      simpa [one_mul] using hmul
    have hpart₁ : (1 : ℝ) ≤ td.D * (td.U / (td.q : ℝ)) := by
      have hmul := mul_le_mul hDq hU1 (by positivity) (by positivity)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hpart₂ : xq ≤ td.D * (td.X / |ξ|) := by
      exact le_trans hxq_le_xOver hxOver_le_DxOver
    have hfactor₂ :
        1 + xq ≤ td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) := by
      have hsum :
          1 + xq ≤
            td.D * (td.U / (td.q : ℝ)) + td.D * (td.X / |ξ|) := by
        nlinarith [hpart₁, hpart₂]
      have hmul_add :
          td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) =
            td.D * (td.U / (td.q : ℝ)) + td.D * (td.X / |ξ|) := by
        ring
      simpa [hmul_add] using hsum
    have hfactor :
        A + xq * B ≤ C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)) := by
      calc
        A + xq * B ≤ C * (1 + xq) := hfactor₁
        _ ≤ C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)) := by
          exact mul_le_mul_of_nonneg_left hfactor₂ hC_nonneg
    have hmul :
        (A + xq * B) * E ≤ (C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|))) * E := by
      exact mul_le_mul_of_nonneg_right hfactor hE_nonneg
    calc
      (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ
              (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) v‖ ^ 2)
          ≤ (A + xq * B) * E := hmain
      _ ≤ (C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|))) * E := hmul
      _ =
          C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * E) := by
            ring

/-- Interval-geometry wrapper for residue-class Step 4 fiber bounds. -/
theorem bound_outerGeom (h4R : Step4FiberLargeSieveByResidueFor td F)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H))
    (r : ℤ)
    (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td) :
    (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
        ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
      ≤
    h4R.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
      (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
        ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
          ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2)) := by
  exact h4R.bound ξ hξ0 (abs_le_one_div_of_mem_Icc hξI) r hr

end Step4FiberLargeSieveByResidueFor

namespace Step4FiberLargeSieveFor

/-- Sum residue-class Step 4 bounds into a fixed-`F` Step 4 fiber bound. -/
def of_byResidue (td : TubeData) (F : TubePoint → ℂ)
    (hR : Step4FiberLargeSieveByResidueFor td F) :
    Step4FiberLargeSieveFor td F := by
  classical
  refine ⟨hR.C, hR.C_nonneg, ?_⟩
  intro ξ hξ0 hξH
  have hL :
      (∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
        =
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
        ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2 := by
    simpa using
      (SSU.Engines.TypeII.LargeSieve.sum_vSet_norm_innerSumVZ_sq_eq_sum_residueClasses
        (td := td) (ξ := ξ) (F := F))
  have hE :
      (∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2)
        =
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
        ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2 := by
    simpa using
      (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.sum_vSet_eq_sum_residueClasses
        (td := td)
        (f := fun v : ℤ =>
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2))
  have hsum :
      (∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
        ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
        ≤
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
        hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2)) := by
    refine Finset.sum_le_sum ?_
    intro r hr
    exact hR.bound ξ hξ0 hξH r hr
  calc
    (∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
        ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
        =
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
        ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2 := hL
    _ ≤
      ∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
        hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
          (∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2)) := hsum
    _ =
      hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
        (∑ r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td,
          ∑ v ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vClass td r,
            ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
              ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2)) := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ =
      hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) *
        (∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
          ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
            ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2)) := by
            simpa [hE]
    _ =
      hR.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
            have hEnergy :
                (∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
                  ∑ z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td v,
                    ‖∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td v z, F p‖ ^ 2)
                  = tubeEnergy td.T F := by
              simpa using
                (SSU.Engines.TypeII.LargeSieve.sum_v_z_norm_fiberVZ_sum_sq_eq_tubeEnergy
                  (td := td) (F := F))
            rw [hEnergy]

/-- Interval-geometry wrapper for fixed-`F` Step 4 fiber bounds. -/
theorem bound_outerGeom (h4F : Step4FiberLargeSieveFor td F)
    (ξ : ℝ) (hξ0 : ξ ≠ 0)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H)) :
    (∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
        ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2)
      ≤
    h4F.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
  exact h4F.bound ξ hξ0 (abs_le_one_div_of_mem_Icc hξI)

end Step4FiberLargeSieveFor

namespace Step4LargeSieveOuterVFor

/-- Deterministic Step 4 reduction (`typeIISum` outer-v Cauchy step) for fixed `F`. -/
def of_fiberLargeSieveFor (td : TubeData) (F : TubePoint → ℂ)
    (hLS : Step4FiberLargeSieveFor td F) :
    Step4LargeSieveOuterVFor td F := by
  classical
  refine ⟨hLS.C * (SSU.Engines.TypeII.LargeSieve.vSet td).card,
    mul_nonneg hLS.C_nonneg (by positivity), ?_⟩
  intro ξ hξ0 hξH
  have hdecomp := SSU.Engines.TypeII.LargeSieve.typeIISum_eq_outer_v_innerVZ
    (td := td) (ξ := ξ) (F := F)
  have hcs :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      ((SSU.Engines.TypeII.LargeSieve.vSet td).card : ℝ) *
        ∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2 := by
    have hcs' :
        ‖∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
            (e (ξ * (SSU.Engines.TypeII.LargeSieve.uResidue td v : ℝ) * (v : ℝ) /
                ((td.q : ℝ) * td.X))) *
              SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2
          ≤
        ((SSU.Engines.TypeII.LargeSieve.vSet td).card : ℝ) *
          ∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
            ‖(e (ξ * (SSU.Engines.TypeII.LargeSieve.uResidue td v : ℝ) * (v : ℝ) /
                ((td.q : ℝ) * td.X))) *
                SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2 := by
      simpa using
        (SSU.Engines.TypeII.LargeSieve.norm_sum_sq_le_card_mul_sum_norm_sq
          (s := SSU.Engines.TypeII.LargeSieve.vSet td)
          (f := fun v =>
            (e (ξ * (SSU.Engines.TypeII.LargeSieve.uResidue td v : ℝ) * (v : ℝ) /
                ((td.q : ℝ) * td.X))) *
              SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v))
    have hsimp :
        ∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
            (‖e (ξ * (SSU.Engines.TypeII.LargeSieve.uResidue td v : ℝ) * (v : ℝ) /
                ((td.q : ℝ) * td.X))‖ *
                ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖) ^ 2
          =
        ∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
          ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [SSU.Engines.TypeII.norm_e]
    simpa [hdecomp, norm_mul, hsimp] using hcs'
  have hLS' := hLS.bound ξ hξ0 hξH
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ ((SSU.Engines.TypeII.LargeSieve.vSet td).card : ℝ) *
            ∑ v ∈ SSU.Engines.TypeII.LargeSieve.vSet td,
              ‖SSU.Engines.TypeII.LargeSieve.innerSumVZ td ξ F v‖ ^ 2 := hcs
    _ ≤ ((SSU.Engines.TypeII.LargeSieve.vSet td).card : ℝ) *
          (hLS.C * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F)) := by
          exact mul_le_mul_of_nonneg_left hLS' (by positivity)
    _ = (hLS.C * (SSU.Engines.TypeII.LargeSieve.vSet td).card) *
          (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
          ring

/-- Build a Step 4 use-site bound from residue-class fiber bounds for the same fixed `F`. -/
def of_fiberLargeSieveByResidueFor (td : TubeData) (F : TubePoint → ℂ)
    (hR : Step4FiberLargeSieveByResidueFor td F) :
    Step4LargeSieveOuterVFor td F :=
  of_fiberLargeSieveFor td F (Step4FiberLargeSieveFor.of_byResidue td F hR)

/-- Build a use-site Step 4 outer-`v` bound from per-residue common-domain fiber equalities
(`hZeq` + `hEqOn`) via the one-add-log residue-class finite-large-sieve envelope. -/
def of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
    (td : TubeData)
    (hD0 : 0 ≤ td.D) (hD1 : 1 ≤ td.D) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) z, F p)) :
    Step4LargeSieveOuterVFor td F :=
  of_fiberLargeSieveByResidueFor td F
    (Step4FiberLargeSieveByResidueFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
      (td := td) (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH)
      (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn))

/-- Explicit constant formula for the generic one-add-log Step-4 `hZeq`/`hEqOn` constructor. -/
theorem of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog_C_eq_formula
    (td : TubeData)
    (hD0 : 0 ≤ td.D) (hD1 : 1 ≤ td.D) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) z, F p)) :
    (of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
      (td := td) (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH)
      (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn)).C
      =
    (((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ)
      + (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) : ℝ)
      * ((SSU.Engines.TypeII.LargeSieve.vSet td).card : ℝ) := by
  simp [of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog,
    of_fiberLargeSieveByResidueFor,
    of_fiberLargeSieveFor,
    Step4FiberLargeSieveFor.of_byResidue,
    Step4FiberLargeSieveByResidueFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog,
    mul_assoc, mul_left_comm, mul_comm]

/-- Canonical coefficient-independent envelope constant for the generic one-add-log Step-4
`hZeq`/`hEqOn` constructor. -/
noncomputable def sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC
    (td : TubeData) : ℝ :=
  (((SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ)
      + (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) : ℝ) *
    ((SSU.Engines.TypeII.LargeSieve.vSet td).card : ℝ)

theorem sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC_nonneg
    (td : TubeData) (hD0 : 0 ≤ td.D) :
    0 ≤ sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC (td := td) := by
  have hq1 : (1 : ℤ) ≤ td.q := Int.add_one_le_iff.mpr td.q_pos
  have hceil0 : 0 ≤ Int.ceil (2 * td.D) := Int.ceil_nonneg (by linarith [hD0])
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
    have hz0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.ZBoxRewrite.zBoxVN td : ℝ) := by positivity
    linarith
  exact mul_nonneg hmain (by positivity)

theorem of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog_C_le_sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC
    (td : TubeData)
    (hD0 : 0 ≤ td.D) (hD1 : 1 ≤ td.D) (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
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
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRef r hr)) z, F p)) :
    (of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
      (td := td) (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH)
      (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn)).C
      ≤
    sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC (td := td) := by
  exact le_of_eq <| by
    simpa [sumFiberVZ_vFromIndexEqRefOnZSetVOneAddLogC] using
      (of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog_C_eq_formula
        (td := td) (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
        (hX := hX) (hH := hH) (hXH := hXH)
        (F := F) (mRef := mRef) (hmRef := hmRef) (hZeq := hZeq) (hEqOn := hEqOn))

/-- Build a use-site Step 4 outer-v bound for BG-centered rank-one coefficients (modEq route),
using the proved one-add-log residue-class Step 4 fiber bound. -/
def of_bgTubeRankOne_modEq_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 :
      0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step4LargeSieveOuterVFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let hR : Step4FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) :=
    Step4FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH)
      (hXH := hXH) (α := α) (β := β) (hαmod := hαmod)
  exact of_fiberLargeSieveByResidueFor td _ hR

/-- Geometry-first Step 4 constructor for BG-centered rank-one/modEq coefficients.

This version derives positivity/division side-conditions from natural-parameter hypotheses:
`q ≤ D`, `D ≥ 1`, `U ≥ 1`, `X > 0`, `H > 1`. -/
def of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1_nat : 1 ≤ P.D) (hU1_nat : 1 ≤ P.U) (hqD_nat : q ≤ P.D)
    (hX_nat : 0 < P.X) (hH1_nat : 1 < P.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (α β : ℤ → ℂ)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          α v₁ = α v₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step4LargeSieveOuterVFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
  have hD0 : 0 ≤ td.D := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hD1 : 1 ≤ td.D := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast hD1_nat)
  have hU1 : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1_nat)
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    have hDqR : (1 : ℝ) ≤ (P.D : ℝ) / (q : ℝ) := one_le_div_of_natCast_le hq hqD_nat
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hDqR
  have hX : 0 < td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX_nat)
  have hH : 0 < td.H := by
    have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1_nat
    have hHR : (0 : ℝ) < (P.H : ℝ) := lt_trans (by norm_num) hH1R
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hHR
  have hXH_td :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH
  simpa [td] using
    (of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH)
      (hXH := hXH_td) (α := α) (β := β) (hαmod := hαmod))

/-- The BG rank-one/modEq Step-4 constructor has a deterministic `C`
independent of `α`,`β` and `hαmod`. -/
theorem of_bgTubeRankOne_modEq_oneAddLog_C_eq
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β α' β' : ℤ → ℂ)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          α v₁ = α v₂)
    (hαmod' :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          α' v₁ = α' v₂) :
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := α) (β := β) (hαmod := hαmod)).C)
      =
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := α') (β := β') (hαmod := hαmod')).C) := by
  simp only [of_bgTubeRankOne_modEq_oneAddLog,
    Step4FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog,
    of_fiberLargeSieveByResidueFor,
    of_fiberLargeSieveFor,
    Step4FiberLargeSieveFor.of_byResidue]

/-- Canonical coefficient-independent envelope constant for BG rank-one/modEq Step 4. -/
noncomputable def bgRankOneModEqOneAddLogC
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H) : ℝ :=
  (of_bgTubeRankOne_modEq_oneAddLog
    (P := P) (a := a) (q := q) hq hcop
    (ha0 := ha0) (hlower := hlower) (hupper := hupper)
    (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
    (α := fun _ => (0 : ℂ)) (β := fun _ => (0 : ℂ))
    (hαmod := by intro _ _ _; simp)).C

theorem bgRankOneModEqOneAddLogC_nonneg
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H) :
    0 ≤ bgRankOneModEqOneAddLogC
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH) := by
  simpa [bgRankOneModEqOneAddLogC] using
    (of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := fun _ => (0 : ℂ)) (β := fun _ => (0 : ℂ))
      (hαmod := by intro _ _ _; simp)).C_nonneg

theorem of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          α v₁ = α v₂) :
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
      (α := α) (β := β) (hαmod := hαmod)).C)
      ≤
    bgRankOneModEqOneAddLogC
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH) := by
  have hEq :
      ((of_bgTubeRankOne_modEq_oneAddLog
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
        (α := α) (β := β) (hαmod := hαmod)).C)
        =
      bgRankOneModEqOneAddLogC
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH) := by
    simpa [bgRankOneModEqOneAddLogC] using
      of_bgTubeRankOne_modEq_oneAddLog_C_eq
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH)
        (α := α) (β := β) (α' := fun _ => (0 : ℂ)) (β' := fun _ => (0 : ℂ))
        (hαmod := hαmod)
        (hαmod' := by intro _ _ _; simp)
  exact le_of_eq hEq

end Step4LargeSieveOuterVFor

namespace Step34LargeSieveTeXFor

open SSU.Engines.TypeII.LargeSieve

private theorem tubeEnergy_nonneg (T : Finset TubePoint) (F : TubePoint → ℂ) :
    0 ≤ _root_.SSU.tubeEnergy T F := by
  classical
  unfold _root_.SSU.tubeEnergy
  refine Finset.sum_nonneg ?_
  intro p hp
  positivity

/--
Use-site version of the TeX Step 5 combiner: geometric mean of Step 3 and Step 4 yields the
displayed TeX Step 5 bound, with the deterministic `max(U/(qD),1)` inflation absorbed into `C`.
-/
def of_step3_step4 (td : TubeData) (F : TubePoint → ℂ)
    (h3 : Step3LargeSieveOuterUFor td F) (h4 : Step4LargeSieveOuterVFor td F)
    (hD : 0 < td.D) (hU : 0 < td.U) (hX : 0 ≤ td.X) :
    Step34LargeSieveTeXFor td F :=
by
  classical
  let qR : ℝ := (td.q : ℝ)
  let m : ℝ := max (td.U / (qR * td.D)) 1
  let C : ℝ :=
    Real.sqrt (h3.C * h4.C) *
      Real.sqrt (td.D / td.U) *
      Real.sqrt m
  refine ⟨C, ?_, ?_⟩
  · simp [C, mul_nonneg, Real.sqrt_nonneg]
  · intro ξ hξ0 hξH
    let E : ℝ := tubeEnergy td.T F
    let x : ℝ := td.X / |ξ|
    have hq : 0 < qR := by
      have : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
      simpa [qR] using this
    have hD0 : 0 ≤ td.D := le_of_lt hD
    have hU0 : 0 ≤ td.U := le_of_lt hU
    have hx0 : 0 ≤ x := div_nonneg hX (abs_nonneg ξ)
    have hE0 : 0 ≤ E := tubeEnergy_nonneg (T := td.T) (F := F)

    have hA3 :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        h3.C * ((td.D / qR) * (td.U + x) * E) := by
      simpa [x, E, qR] using h3.bound ξ hξ0 hξH
    have hA4 :
        ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
          ≤
        h4.C * (td.D * (td.U / qR + x) * E) := by
      simpa [x, E, qR] using h4.bound ξ hξ0 hξH

    -- Geometric mean.
    let A : ℝ := ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
    let B3 : ℝ := h3.C * ((td.D / qR) * (td.U + x) * E)
    let B4 : ℝ := h4.C * (td.D * (td.U / qR + x) * E)
    have hA0 : 0 ≤ A := by positivity [A]
    have hB30 : 0 ≤ B3 := by
      have hDq0 : 0 ≤ td.D / qR := div_nonneg hD0 (le_of_lt hq)
      have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
      dsimp [B3]
      exact mul_nonneg h3.C_nonneg (mul_nonneg (mul_nonneg hDq0 hUx0) hE0)
    have hsq : A ^ 2 ≤ (B3 * B4) := by
      have hmul : A * A ≤ B3 * B4 := by
        have hA_B3 : A ≤ B3 := by simpa [A, B3] using hA3
        have hA_B4 : A ≤ B4 := by simpa [A, B4] using hA4
        exact mul_le_mul hA_B3 hA_B4 hA0 hB30
      simpa [pow_two] using hmul
    have hA_le_sqrt : A ≤ Real.sqrt (B3 * B4) :=
      Real.le_sqrt_of_sq_le hsq

    have hUx_le : td.U / qR + x ≤ m * (td.D + x) := by
      simpa [m, qR] using
        (add_div_le_max_mul_add (U := td.U) (D := td.D) (q := qR) (x := x) hq hD hx0)

    -- Bound `sqrt(B3*B4)` by the TeX Step 5 RHS with the chosen `C`.
    have hsqrt_le :
        Real.sqrt (B3 * B4)
          ≤
        C *
          Real.sqrt ((td.D * td.U) / qR) *
            Real.sqrt (td.U + x) *
            Real.sqrt (td.D + x) *
              E := by
      have hR0 :
          0 ≤
            C *
              Real.sqrt ((td.D * td.U) / qR) *
                Real.sqrt (td.U + x) *
                Real.sqrt (td.D + x) *
                  E := by
        have hDUq0 : 0 ≤ (td.D * td.U) / qR := by
          have : 0 ≤ td.D * td.U := mul_nonneg hD0 hU0
          exact div_nonneg this (le_of_lt hq)
        have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
        have hDx0 : 0 ≤ td.D + x := add_nonneg hD0 hx0
        have hC0 : 0 ≤ C := by simp [C, mul_nonneg, Real.sqrt_nonneg]
        exact
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _))
            hE0
      have hsq_le' :
          (B3 * B4)
            ≤
          (C *
              Real.sqrt ((td.D * td.U) / qR) *
                Real.sqrt (td.U + x) *
                Real.sqrt (td.D + x) *
                  E) ^ 2 := by
        have hB3B4 :
            B3 * B4
              =
            (h3.C * h4.C) *
              ((td.D * td.D) / qR) *
                (td.U + x) *
                  (td.U / qR + x) *
                    (E * E) := by
          dsimp [B3, B4]
          ring_nf
        have hconst0 :
            0 ≤ (h3.C * h4.C) * ((td.D * td.D) / qR) * (td.U + x) * (E * E) := by
          have hDDq0 : 0 ≤ (td.D * td.D) / qR := by
            have : 0 ≤ td.D * td.D := mul_nonneg hD0 hD0
            exact div_nonneg this (le_of_lt hq)
          have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
          have hEE0 : 0 ≤ E * E := mul_nonneg hE0 hE0
          have hCprod0 : 0 ≤ h3.C * h4.C := mul_nonneg h3.C_nonneg h4.C_nonneg
          exact mul_nonneg (mul_nonneg (mul_nonneg hCprod0 hDDq0) hUx0) hEE0
        have hB3B4_le :
            B3 * B4
              ≤
            (h3.C * h4.C) *
              ((td.D * td.D) / qR) *
                (td.U + x) *
                  (m * (td.D + x)) *
                    (E * E) := by
          rw [hB3B4]
          have := mul_le_mul_of_nonneg_left hUx_le hconst0
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
        have hC_sq :
            C ^ 2 = (h3.C * h4.C) * (td.D / td.U) * m := by
          have hCprod0 : 0 ≤ h3.C * h4.C := mul_nonneg h3.C_nonneg h4.C_nonneg
          have hDU0 : 0 ≤ td.D / td.U := div_nonneg hD0 (le_of_lt hU)
          have hm0 : 0 ≤ m := by
            have : (0 : ℝ) ≤ 1 := by norm_num
            exact le_trans this (le_max_right _ _)
          let sC : ℝ := Real.sqrt (h3.C * h4.C)
          let sDU : ℝ := Real.sqrt (td.D / td.U)
          let sm : ℝ := Real.sqrt m
          have hsC : sC ^ 2 = h3.C * h4.C := by
            simp [sC, pow_two, Real.sq_sqrt hCprod0]
          have hsDU : sDU ^ 2 = td.D / td.U := by
            simp [sDU, pow_two, Real.sq_sqrt hDU0]
          have hsm : sm ^ 2 = m := by
            simp [sm, pow_two, Real.sq_sqrt hm0]
          have hCdef : C = sC * sDU * sm := by
            simp [C, sC, sDU, sm, mul_assoc, mul_left_comm, mul_comm]
          calc
            C ^ 2 = (sC * sDU * sm) ^ 2 := by simpa [hCdef]
            _ = (sC ^ 2) * (sDU ^ 2) * (sm ^ 2) := by
                  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
            _ = (h3.C * h4.C) * (td.D / td.U) * m := by
                  simp [hsC, hsDU, hsm, mul_assoc, mul_left_comm, mul_comm]
        have hR_sq :
            (C *
                Real.sqrt ((td.D * td.U) / qR) *
                  Real.sqrt (td.U + x) *
                  Real.sqrt (td.D + x) *
                    E) ^ 2
              =
            (h3.C * h4.C) *
              ((td.D * td.D) / qR) *
                (td.U + x) *
                  (m * (td.D + x)) *
                    (E * E) := by
          have hDUq0 : 0 ≤ (td.D * td.U) / qR := by
            have : 0 ≤ td.D * td.U := mul_nonneg hD0 hU0
            exact div_nonneg this (le_of_lt hq)
          have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
          have hDx0 : 0 ≤ td.D + x := add_nonneg hD0 hx0
          have hsqR :
              (C *
                  Real.sqrt ((td.D * td.U) / qR) *
                    Real.sqrt (td.U + x) *
                    Real.sqrt (td.D + x) *
                      E) ^ 2
                =
              (C ^ 2) *
                (((td.D * td.U) / qR)) *
                  (td.U + x) *
                    (td.D + x) *
                      (E ^ 2) := by
            -- Separate squares via `mul_pow`, then discharge the `sqrt` squares.
            -- Keep the `^2` form so `Real.sq_sqrt` can fire without needing `pow_two`.
            simpa [mul_assoc, mul_left_comm, mul_comm, mul_pow, Real.sq_sqrt hDUq0,
              Real.sq_sqrt hUx0, Real.sq_sqrt hDx0]
          -- Replace `C^2` and `E^2`.
          calc
            (C *
                Real.sqrt ((td.D * td.U) / qR) *
                  Real.sqrt (td.U + x) *
                  Real.sqrt (td.D + x) *
                    E) ^ 2
                =
              (C ^ 2) * (((td.D * td.U) / qR)) * (td.U + x) * (td.D + x) * (E ^ 2) := hsqR
            _ =
              ((h3.C * h4.C) * (td.D / td.U) * m) *
                (((td.D * td.U) / qR)) * (td.U + x) * (td.D + x) * (E ^ 2) := by
                  simp [hC_sq]
            _ =
              (h3.C * h4.C) * ((td.D * td.D) / qR) * (td.U + x) * (m * (td.D + x)) * (E * E) := by
                  -- Expand and cancel `U` in `(D/U)*(D*U/q)`; rewrite `E^2` as `E*E`.
                  have hUne : (td.U : ℝ) ≠ 0 := ne_of_gt hU
                  have hqne : qR ≠ 0 := ne_of_gt hq
                  field_simp [hUne, hqne, pow_two, mul_assoc, mul_left_comm, mul_comm]
        -- Finish the squared comparison.
        exact le_trans hB3B4_le (by simpa [hR_sq])
      exact (Real.sqrt_le_iff.2 ⟨hR0, hsq_le'⟩)

    have hfinal :
        A ≤
          C *
            Real.sqrt ((td.D * td.U) / qR) *
              Real.sqrt (td.U + td.X / |ξ|) *
                Real.sqrt (td.D + td.X / |ξ|) *
                  E := by
      -- `A ≤ √(B3*B4) ≤ RHS`.
      exact le_trans hA_le_sqrt (by
        simpa [x, E, qR] using hsqrt_le)
    -- Rewrite `A` and `E` back and `qR` back.
    simpa [A, E, qR] using hfinal

/-- Build a use-site TeX Step 5 bound by routing Step 3/4 Montgomery–Vaughan hypotheses through
the deterministic Step 3/4 reductions and then the TeX geometric-mean combiner. -/
def of_step3MV_step4MV
    (td : TubeData) (F : TubePoint → ℂ)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hD : 0 < td.D) (hU : 0 < td.U) :
    Step34LargeSieveTeXFor td F := by
  let h3 : Step3LargeSieveOuterUFor td F :=
    Step3LargeSieveOuterUFor.of_montgomeryVaughan
      (td := td) (h3MV := h3MV) (hD := hD0) (hU := hU0) (hX := hX0) F
  let h4 : Step4LargeSieveOuterVFor td F :=
    Step4LargeSieveOuterVFor.of_montgomeryVaughan
      (td := td) (h4MV := h4MV) (hD := hD0) (hU := hU0) (hX := hX0) F
  exact of_step3_step4 (td := td) (F := F) h3 h4 hD hU hX0

/-- Build a use-site TeX Step 5 bound from pure box geometry fallbacks for Step 3 and Step 4. -/
def of_box_geometry
    (td : TubeData) (F : TubePoint → ℂ)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U)
    (hXH1 : 1 ≤ td.X * td.H) :
    Step34LargeSieveTeXFor td F := by
  have h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_box_geometry
      (td := td) (hDq := hDq) (hD := hD0) (hU := hU1) (hX := hX0)
  have h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_box_geometry
      (td := td) (hU := hU0) (hX := hX0) (hD1 := hD1) (hXH1 := hXH1)
  exact
    of_step3MV_step4MV
      (td := td) (F := F) (h3MV := h3MV) (h4MV := h4MV)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hD := lt_of_lt_of_le (by norm_num) hD1)
      (hU := lt_of_lt_of_le (by norm_num) hU1)

/-- Build a use-site TeX Step 5 bound from broad box geometry (no `q ≤ D` side condition). -/
def of_general_box_geometry
    (td : TubeData) (F : TubePoint → ℂ)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U)
    (hXH1 : 1 ≤ td.X * td.H) :
    Step34LargeSieveTeXFor td F := by
  have h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_general_geometry
      (td := td)
      (hDpos := lt_of_lt_of_le (by norm_num) hD1)
      (hD := hD0) (hU := hU1) (hX := hX0)
  have h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td :=
    SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_box_geometry
      (td := td) (hU := hU0) (hX := hX0) (hD1 := hD1) (hXH1 := hXH1)
  exact
    of_step3MV_step4MV
      (td := td) (F := F) (h3MV := h3MV) (h4MV := h4MV)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hD := lt_of_lt_of_le (by norm_num) hD1)
      (hU := lt_of_lt_of_le (by norm_num) hU1)

/-- Build a use-site TeX Step 5 bound by routing per-residue Step 3/4 Montgomery–Vaughan
hypotheses through residue summation and the deterministic Step 3/4 reductions. -/
def of_step3MVByResidue_step4MVByResidue
    (td : TubeData) (F : TubePoint → ℂ)
    (h3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td)
    (h4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td)
    (hD0 : 0 ≤ td.D) (hU0 : 0 ≤ td.U) (hX0 : 0 ≤ td.X)
    (hD : 0 < td.D) (hU : 0 < td.U) :
    Step34LargeSieveTeXFor td F := by
  let h3R : Step3FiberLargeSieveByResidueFor td F :=
    Step3FiberLargeSieveByResidueFor.of_montgomeryVaughanByResidue
      (td := td) (h3MV := h3MV) F
  let h4R : Step4FiberLargeSieveByResidueFor td F :=
    Step4FiberLargeSieveByResidueFor.of_montgomeryVaughanByResidue
      (td := td) (h4MV := h4MV) F
  let h3 : Step3LargeSieveOuterUFor td F :=
    Step3LargeSieveOuterUFor.of_fiberLargeSieveByResidueFor td F h3R
  let h4 : Step4LargeSieveOuterVFor td F :=
    Step4LargeSieveOuterVFor.of_fiberLargeSieveByResidueFor td F h4R
  let _ : 0 ≤ td.D := hD0
  let _ : 0 ≤ td.U := hU0
  exact of_step3_step4 (td := td) (F := F) h3 h4 hD hU hX0

/-- Build a use-site TeX Step 5 bound from fixed-`F` residue-class Step 3/4 fiber bounds. -/
def of_step3FiberByResidueFor_step4FiberByResidueFor
    (td : TubeData) (F : TubePoint → ℂ)
    (h3R : Step3FiberLargeSieveByResidueFor td F)
    (h4R : Step4FiberLargeSieveByResidueFor td F)
    (hD : 0 < td.D) (hU : 0 < td.U) (hX : 0 ≤ td.X) :
    Step34LargeSieveTeXFor td F := by
  let h3 : Step3LargeSieveOuterUFor td F :=
    Step3LargeSieveOuterUFor.of_fiberLargeSieveByResidueFor td F h3R
  let h4 : Step4LargeSieveOuterVFor td F :=
    Step4LargeSieveOuterVFor.of_fiberLargeSieveByResidueFor td F h4R
  exact of_step3_step4 (td := td) (F := F) h3 h4 hD hU hX

/-- Build a use-site TeX Step 5 bound from per-residue common-domain fiber equalities on both
`u`- and `v`-progressions (`hZeq` + `hEqOn` packages), via one-add-log Step 3/4 envelopes. -/
def of_sumFiber_ref_on_zSet_oneAddLog
    (td : TubeData)
    (hU0 : 0 ≤ td.U) (hD0 : 0 ≤ td.D) (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hX : 0 < td.X) (hH : 0 < td.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td → ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r)
    (hZeqU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          SSU.Engines.TypeII.LargeSieve.zSet td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSet td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRefU r hr)))
    (hEqOnU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSet td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRefU r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberUZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex (td := td) r (mRefU r hr)) z, F p))
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td → ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r)
    (hZeqV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          SSU.Engines.TypeII.LargeSieve.zSetV td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m)
            =
          SSU.Engines.TypeII.LargeSieve.zSetV td
              (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRefV r hr)))
    (hEqOnV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV td)
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet (td := td) r →
          ∀ z : ℤ,
            z ∈ SSU.Engines.TypeII.LargeSieve.zSetV td
                (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRefV r hr)) →
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
                =
              (∑ p ∈ SSU.Engines.TypeII.LargeSieve.fiberVZ td
                  (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex (td := td) r (mRefV r hr)) z, F p)) :
    Step34LargeSieveTeXFor td F := by
  let h3 : Step3LargeSieveOuterUFor td F :=
    Step3LargeSieveOuterUFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog
      (td := td) (hU0 := hU0) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH_u)
      (F := F) (mRef := mRefU) (hmRef := hmRefU) (hZeq := hZeqU) (hEqOn := hEqOnU)
  let h4 : Step4LargeSieveOuterVFor td F :=
    Step4LargeSieveOuterVFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog
      (td := td) (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH := hXH_v)
      (F := F) (mRef := mRefV) (hmRef := hmRefV) (hZeq := hZeqV) (hEqOn := hEqOnV)
  have hDpos : 0 < td.D := lt_of_lt_of_le (by norm_num) hD1
  have hUpos : 0 < td.U := lt_of_lt_of_le (by norm_num) hU1
  exact of_step3_step4 (td := td) (F := F) h3 h4 hDpos hUpos (le_of_lt hX)

/-- Build a use-site TeX Step 5 bound for BG-centered rank-one coefficients, by combining the
proved one-add-log residue-class Step 3/4 fiber bounds. -/
def of_bgTubeRankOne_constOnIndex_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRefU r hr)))
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRefV r hr))) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step34LargeSieveTeXFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let h3R : Step3FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) :=
    Step3FiberLargeSieveByResidueFor.of_bgTubeRankOne_constOnUIndex_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH_u)
      (α := α) (β := β) (mRef := mRefU) (hmRef := hmRefU) (hβconst := hβconst)
  let h4R : Step4FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) :=
    Step4FiberLargeSieveByResidueFor.of_bgTubeRankOne_constOnVIndex_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH)
      (hXH := hXH_v) (α := α) (β := β) (mRef := mRefV) (hmRef := hmRefV) (hαconst := hαconst)
  have hDpos : 0 < td.D := lt_of_lt_of_le (by norm_num) hD1
  have hUpos : 0 < td.U := lt_of_lt_of_le (by norm_num) hU1
  exact
    of_step3FiberByResidueFor_step4FiberByResidueFor
      (td := td) (F := SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
      h3R h4R hDpos hUpos (le_of_lt hX)

/-- Geometry-first Step 5 constructor for BG-centered rank-one coefficients with
per-residue reference-index constancy (`constOnUIndex` + `constOnVIndex`) assumptions.

This version derives positivity/division side-conditions from natural-parameter hypotheses:
`q ≤ D`, `D ≥ 1`, `U ≥ 1`, `X > 0`, `H > 1`. -/
def of_bgTubeRankOne_constOnIndex_oneAddLog_ofBGGeometry
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1_nat : 1 ≤ P.D) (hU1_nat : 1 ≤ P.U) (hqD_nat : q ≤ P.D)
    (hX_nat : 0 < P.X) (hH1_nat : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (α β : ℤ → ℂ)
    (mRefU :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRefU :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRefU r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hβconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.residuesU
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartition.uIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        β (SSU.Engines.TypeII.LargeSieve.ResiduePartition.uFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRefU r hr)))
    (mRefV :
      ∀ r : ℤ,
        r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) →
          ℤ)
    (hmRefV :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop)),
        mRefV r hr ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r)
    (hαconst :
      ∀ (r : ℤ)
        (hr : r ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.residuesV
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop))
        (m : ℤ),
        m ∈ SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vIndexSet
          (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r →
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r m)
          =
        α (SSU.Engines.TypeII.LargeSieve.ResiduePartitionV.vFromIndex
            (td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop) r
              (mRefV r hr))) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step34LargeSieveTeXFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
  have hU0 : 0 ≤ td.U := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hD0 : 0 ≤ td.D := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hD1 : 1 ≤ td.D := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast hD1_nat)
  have hU1 : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1_nat)
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    have hDqR : (1 : ℝ) ≤ (P.D : ℝ) / (q : ℝ) := one_le_div_of_natCast_le hq hqD_nat
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hDqR
  have hX : 0 < td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX_nat)
  have hH : 0 < td.H := by
    have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1_nat
    have hHR : (0 : ℝ) < (P.H : ℝ) := lt_trans (by norm_num) hH1R
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hHR
  have hXH_u_td :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH_u
  have hXH_v_td :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH_v
  simpa [td] using
    (of_bgTubeRankOne_constOnIndex_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u_td) (hXH_v := hXH_v_td)
      (α := α) (β := β)
      (mRefU := mRefU) (hmRefU := hmRefU) (hβconst := hβconst)
      (mRefV := mRefV) (hmRefV := hmRefV) (hαconst := hαconst))

/-- Build a use-site TeX Step 5 bound for BG-centered rank-one coefficients, by combining the
proved one-add-log residue-class Step 3/4 fiber bounds. -/
def of_bgTubeRankOne_modEq_oneAddLog
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step34LargeSieveTeXFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  intro td
  let h3R : Step3FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) :=
    Step3FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH) (hXH := hXH_u)
      (α := α) (β := β) (hβmod := hβmod)
  let h4R : Step4FiberLargeSieveByResidueFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) :=
    Step4FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hD0 := hD0) (hD1 := hD1) (hDq := hDq) (hU1 := hU1) (hX := hX) (hH := hH)
      (hXH := hXH_v) (α := α) (β := β) (hαmod := hαmod)
  have hDpos : 0 < td.D := lt_of_lt_of_le (by norm_num) hD1
  have hUpos : 0 < td.U := lt_of_lt_of_le (by norm_num) hU1
  exact
    of_step3FiberByResidueFor_step4FiberByResidueFor
      (td := td) (F := SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β)
      h3R h4R hDpos hUpos (le_of_lt hX)

/-- Geometry-first Step 5 constructor for BG-centered rank-one/modEq coefficients.

This version derives positivity/division side-conditions from natural-parameter hypotheses:
`q ≤ D`, `D ≥ 1`, `U ≥ 1`, `X > 0`, `H > 1`. -/
def of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hD1_nat : 1 ≤ P.D) (hU1_nat : 1 ≤ P.U) (hqD_nat : q ≤ P.D)
    (hX_nat : 0 < P.X) (hH1_nat : 1 < P.H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (P.U : ℝ) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (P.D : ℝ)) + (q : ℤ)) : ℕ) : ℝ)) * (q : ℝ)
        ≤ (P.X : ℝ) * (P.H : ℝ))
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          β u₁ = β u₂)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] →
          α v₁ = α v₂) :
    let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
    Step34LargeSieveTeXFor td (SSU.Engines.TypeII.LargeSieve.RankOneShear.coeff td α β) := by
  let td := SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop
  have hU0 : 0 ≤ td.U := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hD0 : 0 ≤ td.D := by
    simp [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube]
  have hD1 : 1 ≤ td.D := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast hD1_nat)
  have hU1 : 1 ≤ td.U := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1_nat)
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    have hDqR : (1 : ℝ) ≤ (P.D : ℝ) / (q : ℝ) := one_le_div_of_natCast_le hq hqD_nat
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hDqR
  have hX : 0 < td.X := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using
      (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX_nat)
  have hH : 0 < td.H := by
    have hH1R : (1 : ℝ) < (P.H : ℝ) := by exact_mod_cast hH1_nat
    have hHR : (0 : ℝ) < (P.H : ℝ) := lt_trans (by norm_num) hH1R
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hHR
  have hXH_u_td :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH_u
  have hXH_v_td :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H := by
    simpa [td, SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube] using hXH_v
  simpa [td] using
    (of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u_td) (hXH_v := hXH_v_td)
      (α := α) (β := β) (hβmod := hβmod) (hαmod := hαmod))

/-- The one-add-log BG rank-one/modEq Step-5 constructor has a deterministic `C` that is
independent of coefficient choices (`α`,`β`) and modulo-invariance witnesses. -/
theorem of_bgTubeRankOne_modEq_oneAddLog_C_eq
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β α' β' : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂)
    (hβmod' :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → β' u₁ = β' u₂)
    (hαmod' :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → α' v₁ = α' v₂) :
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
      (α := α) (β := β) (hβmod := hβmod) (hαmod := hαmod)).C)
      =
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
      (α := α') (β := β') (hβmod := hβmod') (hαmod := hαmod')).C) := by
  simp only [of_bgTubeRankOne_modEq_oneAddLog,
    of_step3FiberByResidueFor_step4FiberByResidueFor,
    Step3LargeSieveOuterUFor.of_fiberLargeSieveFor,
    Step4LargeSieveOuterVFor.of_fiberLargeSieveFor,
    Step3FiberLargeSieveFor.of_byResidue,
    Step4FiberLargeSieveFor.of_byResidue,
    Step3FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog,
    Step4FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog,
    Step3LargeSieveOuterUFor.of_fiberLargeSieveByResidueFor,
    Step4LargeSieveOuterVFor.of_fiberLargeSieveByResidueFor,
    of_step3_step4]

/-- Canonical coefficient-independent envelope constant for the BG one-add-log Step-5 constructor. -/
noncomputable def bgRankOneModEqOneAddLogC
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H) : ℝ :=
  (of_bgTubeRankOne_modEq_oneAddLog
    (P := P) (a := a) (q := q) hq hcop
    (ha0 := ha0) (hlower := hlower) (hupper := hupper)
    (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
    (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
    (α := fun _ => (0 : ℂ)) (β := fun _ => (0 : ℂ))
    (hβmod := by intro _ _ _; simp)
    (hαmod := by intro _ _ _; simp)).C

/-- Nonnegativity of `bgRankOneModEqOneAddLogC`. -/
theorem bgRankOneModEqOneAddLogC_nonneg
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H) :
    0 ≤ bgRankOneModEqOneAddLogC
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v) := by
  simpa [bgRankOneModEqOneAddLogC] using
    (of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
      (α := fun _ => (0 : ℂ)) (β := fun _ => (0 : ℂ))
      (hβmod := by intro _ _ _; simp)
      (hαmod := by intro _ _ _; simp)).C_nonneg

/-- Any BG one-add-log Step-5 constructor constant is bounded by the canonical envelope constant.
The bound is an equality, proved via coefficient-independence. -/
theorem of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime a.natAbs q)
    (ha0 : 0 ≤ a)
    (hlower :
      (q : ℤ) * ((P.N : ℤ) + 1) ≤ a * ((P.D : ℤ) + 1) - (P.U : ℤ))
    (hupper :
      a * ((2 * P.D : ℕ) : ℤ) + (P.U : ℤ) ≤ (q : ℤ) * ((2 * P.N : ℕ) : ℤ))
    (hU0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hD0 : 0 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hD1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
    (hU1 : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U)
    (hDq : 1 ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D /
      ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ))
    (hX : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X)
    (hH : 0 < (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_u :
      (2 * ((2 * Int.toNat (Int.ceil (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).U
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (hXH_v :
      (2 * ((2 * Int.toNat (Int.ceil (2 * (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).D)
            + (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q) : ℕ) : ℝ))
        * ((SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q : ℝ)
          ≤ (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).X *
              (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).H)
    (α β : ℤ → ℂ)
    (hβmod :
      ∀ u₁ u₂ : ℤ,
        u₁ ≡ u₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → β u₁ = β u₂)
    (hαmod :
      ∀ v₁ v₂ : ℤ,
        v₁ ≡ v₂ [ZMOD (SSU.Engines.TypeII.LargeSieve.BGTubeBridge.tubeDataOfBGTube P a q hq hcop).q] → α v₁ = α v₂) :
    ((of_bgTubeRankOne_modEq_oneAddLog
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
      (α := α) (β := β) (hβmod := hβmod) (hαmod := hαmod)).C)
      ≤
    bgRankOneModEqOneAddLogC
      (P := P) (a := a) (q := q) hq hcop
      (ha0 := ha0) (hlower := hlower) (hupper := hupper)
      (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
      (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v) := by
  have hEq :
      ((of_bgTubeRankOne_modEq_oneAddLog
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
        (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
        (α := α) (β := β) (hβmod := hβmod) (hαmod := hαmod)).C)
        =
      bgRankOneModEqOneAddLogC
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
        (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v) := by
    simpa [bgRankOneModEqOneAddLogC] using
      of_bgTubeRankOne_modEq_oneAddLog_C_eq
        (P := P) (a := a) (q := q) hq hcop
        (ha0 := ha0) (hlower := hlower) (hupper := hupper)
        (hU0 := hU0) (hD0 := hD0) (hD1 := hD1) (hU1 := hU1) (hDq := hDq)
        (hX := hX) (hH := hH) (hXH_u := hXH_u) (hXH_v := hXH_v)
        (α := α) (β := β)
        (α' := fun _ => (0 : ℂ)) (β' := fun _ => (0 : ℂ))
        (hβmod := hβmod) (hαmod := hαmod)
        (hβmod' := by intro _ _ _; simp)
        (hαmod' := by intro _ _ _; simp)
  exact le_of_eq hEq

end Step34LargeSieveTeXFor

end

end TypeII
end Engines
end SSU
