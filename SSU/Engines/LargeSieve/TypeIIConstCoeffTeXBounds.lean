import SSU.Engines.LargeSieve.TypeIIConstCoeffMV
import SSU.Engines.LargeSieve.TypeIIIndexLargeSieve
import SSU.Engines.LargeSieve.Step34Aux

/-!
TeX-shaped Step 3/4 bounds under a *constant-coefficient* hypothesis.

This file is a small but important bridge:

* `TypeIIConstCoeffMV` gives bounds of the form `‖typeIISum‖² ≤ LS.C * tubeEnergy` provided the
  translated `Fin`-indexed coefficient arrays are constant in the outer index (`u` or `v`).
* `TypeIIIndexLargeSieve` bounds the MV constant `LS.C` by an explicit polylog expression
  `N + (X/|ξ|) * (1 + log R)`.

Here we combine them into inequalities that *match the TeX Step 3/4 shapes*:

* Step 3: `‖S(ξ)‖² ≤ C * (D/q) * (U + X/|ξ|) * ∑|F|²`
* Step 4: `‖S(ξ)‖² ≤ C * D * (U/q + X/|ξ|) * ∑|F|²`

The constant `C` is still allowed to depend on the ambient deterministic parameters (via `zBoxN`
and a `log` term); this is the intended “plumbing milestone” before the extraction layer proves
constancy for the specific coefficient arrays arising from packets.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

namespace ConstCoeffTeX

open IndexLargeSieve
open ConstCoeffMV
open ZBoxRewrite
open ZBoxToFin

/-!
## Step 3 (outer `u`) TeX-shape from constancy + MV
-/

theorem norm_typeIISum_sq_le_step3_teX_of_constCoeffUZFin
    (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hU1 : 1 ≤ td.U)
    (hU0 : 0 ≤ td.U)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxN td) → ℂ)
    (hCoeff : ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = a) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (((zBoxN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0) : ℝ) *
        ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
  classical
  -- Start from the const-coeff use-site bound `‖S‖² ≤ LS.C * tubeEnergy`.
  have h0 :=
    norm_typeIISum_sq_le_uSet_finiteLargeSieve_C_mul_tubeEnergy_of_constCoeffUZFin
      (td := td) (hU0 := hU0)
      (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := F) (a := a) hCoeff

  -- Bound the MV constant by the explicit `(1+log)` expression.
  let LS :=
    uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0)
      (hX := hX) (hH := hH) (hξH := by simpa using hξH) (hXH := hXH)
  have hC_le :
      LS.C ≤ (zBoxN td : ℝ) + (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) := by
    -- `|-ξ| = |ξ|`.
    simpa [LS, abs_neg] using
      (uSet_finiteLargeSieve_C_le_one_add_log
        (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0)
        (hX := hX) (hH := hH) (hξH := by simpa [abs_neg] using hξH) (hXH := hXH))

  -- Replace `1 + log R` by its nonnegative truncation.
  set B : ℝ := max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0
  have hB_ge : (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) ≤ B := by
    simp [B]
  have hx0 : 0 ≤ td.X / |ξ| := by
    exact div_nonneg (le_of_lt hX) (abs_nonneg ξ)
  have hC_le' :
      LS.C ≤ (zBoxN td : ℝ) + (td.X / |ξ|) * B := by
    refine hC_le.trans ?_
    gcongr

  -- Compare to the TeX expression: inflate by the factors `D/q ≥ 1` and `U + X/|ξ| ≥ 1`.
  have hU_plus : (1 : ℝ) ≤ td.U + td.X / |ξ| := by
    nlinarith [hU1, hx0]
  have hy0 : 0 ≤ td.D / (td.q : ℝ) := le_trans (by norm_num : (0 : ℝ) ≤ 1) hDq
  have hu0 : 0 ≤ td.U := le_trans (by norm_num : (0 : ℝ) ≤ 1) hU1
  have hUxp0 : 0 ≤ td.U + td.X / |ξ| := add_nonneg hu0 hx0

  -- A single deterministic factor that is ≥ 1 and ≥ X/|ξ| on the ξ-band.
  let f : ℝ := (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|)
  have hf_ge1 : (1 : ℝ) ≤ f := by
    -- `1 = 1*1 ≤ (D/q)*(U+X/|ξ|)`.
    have :
        (1 : ℝ) * (1 : ℝ) ≤ (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) :=
      mul_le_mul hDq hU_plus (by positivity) hy0
    simpa [f] using this
  have hx_le_f : td.X / |ξ| ≤ f := by
    have hx_le : td.X / |ξ| ≤ td.U + td.X / |ξ| := by
      nlinarith [hu0]
    have hUx_le : td.U + td.X / |ξ| ≤ (td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) := by
      have := le_mul_of_one_le_left hUxp0 hDq
      simpa [mul_assoc, f] using this
    exact le_trans hx_le (by simpa [f, mul_assoc, mul_left_comm, mul_comm] using hUx_le)

  have hcompare :
      (zBoxN td : ℝ) + (td.X / |ξ|) * B ≤ ((zBoxN td : ℝ) + B) * f := by
    have hB0 : 0 ≤ B := by simp [B]
    have hN0 : 0 ≤ (zBoxN td : ℝ) := by positivity
    have hN_le : (zBoxN td : ℝ) ≤ (zBoxN td : ℝ) * f :=
      le_mul_of_one_le_right hN0 hf_ge1
    have hxB_le : (td.X / |ξ|) * B ≤ B * f := by
      have := mul_le_mul_of_nonneg_right hx_le_f hB0
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hsum :
        (zBoxN td : ℝ) + (td.X / |ξ|) * B ≤ (zBoxN td : ℝ) * f + B * f :=
      add_le_add hN_le hxB_le
    -- Factor `f` on the RHS.
    have hfact : (zBoxN td : ℝ) * f + B * f = ((zBoxN td : ℝ) + B) * f := by ring
    exact hsum.trans_eq hfact

  -- Put it together.
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ LS.C * tubeEnergy td.T F := by
            simpa [LS] using h0
    _ ≤ ((zBoxN td : ℝ) + (td.X / |ξ|) * B) * tubeEnergy td.T F := by
            exact mul_le_mul_of_nonneg_right hC_le' (tubeEnergy_nonneg (T := td.T) (F := F))
    _ ≤ (((zBoxN td : ℝ) + B) * f) * tubeEnergy td.T F := by
            exact mul_le_mul_of_nonneg_right hcompare (tubeEnergy_nonneg (T := td.T) (F := F))
    _ = (((zBoxN td : ℝ) + B) : ℝ) * ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) := by
            simp [f]
            ring

/-!
## Step 4 (outer `v`) TeX-shape from constancy + MV
-/

theorem norm_typeIISum_sq_le_step4_teX_of_constCoeffVZFin
    (td : TubeData)
    (hD1 : 1 ≤ td.D) (hU0 : 0 ≤ td.U) (hXH1 : 1 ≤ td.X * td.H)
    (hD0 : 0 ≤ td.D)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxVN td) → ℂ)
    (hCoeff : ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = a) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (((zBoxVN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0) : ℝ) *
        (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
  classical
  have h0 :=
    norm_typeIISum_sq_le_vSet_finiteLargeSieve_C_mul_tubeEnergy_of_constCoeffVZFin
      (td := td) (hD0 := hD0)
      (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := F) (a := a) hCoeff

  let LS :=
    vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0)
      (hX := hX) (hH := hH) (hξH := by simpa using hξH) (hXH := hXH)
  have hC_le :
      LS.C ≤ (zBoxVN td : ℝ) + (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) := by
    simpa [LS, abs_neg] using
      (vSet_finiteLargeSieve_C_le_one_add_log
        (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0)
        (hX := hX) (hH := hH) (hξH := by simpa [abs_neg] using hξH) (hXH := hXH))

  set B : ℝ := max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0
  have hB_ge : (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) ≤ B := by
    simp [B]
  have hx0 : 0 ≤ td.X / |ξ| := div_nonneg (le_of_lt hX) (abs_nonneg ξ)
  have hC_le' :
      LS.C ≤ (zBoxVN td : ℝ) + (td.X / |ξ|) * B := by
    refine hC_le.trans ?_
    gcongr

  -- Show `1 ≤ U/q + X/|ξ|` from the ξ-band and `1 ≤ X*H`.
  have habspos : 0 < |ξ| := abs_pos.mpr hξ0
  have hrec : td.H ≤ 1 / |ξ| := by
    -- Invert `|ξ| ≤ 1/H`.
    have hbpos : 0 < (1 / td.H) := by positivity [hH]
    have h := one_div_le_one_div_of_le habspos hξH
    -- `1 / (1 / H) = H`.
    have hH0 : td.H ≠ 0 := ne_of_gt hH
    simpa [one_div, inv_inv, hH0] using h
  have hx_ge_XH : td.X * td.H ≤ td.X / |ξ| := by
    have hX0 : 0 ≤ td.X := le_of_lt hX
    -- Multiply `H ≤ 1/|ξ|` by `X ≥ 0`.
    have := mul_le_mul_of_nonneg_left hrec hX0
    -- `X * (1/|ξ|) = X/|ξ|`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hx_ge1 : (1 : ℝ) ≤ td.X / |ξ| := le_trans hXH1 hx_ge_XH
  have hUplus : (1 : ℝ) ≤ td.U / (td.q : ℝ) + td.X / |ξ| := by
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have hUq0 : 0 ≤ td.U / (td.q : ℝ) := div_nonneg hU0 (le_of_lt hq)
    nlinarith [hx_ge1, hUq0]

  have hDpos : 0 ≤ td.D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD1
  have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
  have hUq0 : 0 ≤ td.U / (td.q : ℝ) := div_nonneg hU0 (le_of_lt hq)
  have hUxp0 : 0 ≤ td.U / (td.q : ℝ) + td.X / |ξ| := add_nonneg hUq0 hx0

  let f : ℝ := td.D * (td.U / (td.q : ℝ) + td.X / |ξ|)
  have hf_ge1 : (1 : ℝ) ≤ f := by
    have : (1 : ℝ) ≤ td.U / (td.q : ℝ) + td.X / |ξ| := hUplus
    nlinarith [hD1, this]
  have hx_le_f : td.X / |ξ| ≤ f := by
    have hx_le : td.X / |ξ| ≤ td.U / (td.q : ℝ) + td.X / |ξ| := by linarith
    have hUx_le : td.U / (td.q : ℝ) + td.X / |ξ| ≤ td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) := by
      have := le_mul_of_one_le_left hUxp0 hD1
      simpa [mul_assoc, f] using this
    exact le_trans hx_le (by simpa [f, mul_assoc, mul_left_comm, mul_comm] using hUx_le)

  have hcompare :
      (zBoxVN td : ℝ) + (td.X / |ξ|) * B ≤ ((zBoxVN td : ℝ) + B) * f := by
    have hB0 : 0 ≤ B := by simp [B]
    have hN0 : 0 ≤ (zBoxVN td : ℝ) := by positivity
    have hN_le : (zBoxVN td : ℝ) ≤ (zBoxVN td : ℝ) * f :=
      le_mul_of_one_le_right hN0 hf_ge1
    have hxB_le : (td.X / |ξ|) * B ≤ B * f := by
      have := mul_le_mul_of_nonneg_right hx_le_f hB0
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hsum :
        (zBoxVN td : ℝ) + (td.X / |ξ|) * B ≤ (zBoxVN td : ℝ) * f + B * f :=
      add_le_add hN_le hxB_le
    have hfact : (zBoxVN td : ℝ) * f + B * f = ((zBoxVN td : ℝ) + B) * f := by ring
    exact hsum.trans_eq hfact

  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ LS.C * tubeEnergy td.T F := by
            simpa [LS] using h0
    _ ≤ ((zBoxVN td : ℝ) + (td.X / |ξ|) * B) * tubeEnergy td.T F := by
            exact mul_le_mul_of_nonneg_right hC_le' (tubeEnergy_nonneg (T := td.T) (F := F))
    _ ≤ (((zBoxVN td : ℝ) + B) * f) * tubeEnergy td.T F := by
            exact mul_le_mul_of_nonneg_right hcompare (tubeEnergy_nonneg (T := td.T) (F := F))
    _ = (((zBoxVN td : ℝ) + B) : ℝ) * (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) := by
            simp [f]
            ring

/-!
## Step 5 (geometric mean) TeX-shape from constancy + MV

This is the TeX Step 5 combination (geometric mean of Step 3 and Step 4), specialized to the
two “use-site” Step 3/4 lemmas in this file.

It is still conditional: it requires the same constancy hypotheses for `coeffUZFin` and
`coeffVZFin` on the chosen coefficient array `F`.
-/

set_option maxHeartbeats 800000 in
theorem norm_typeIISum_sq_le_step5_teX_of_constCoeffUZFin_of_constCoeffVZFin
    (td : TubeData)
    (hDq : 1 ≤ td.D / (td.q : ℝ)) (hD1 : 1 ≤ td.D) (hU1 : 1 ≤ td.U)
    (hXH1 : 1 ≤ td.X * td.H)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH_u : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (hXH_v : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (aU : Fin (zBoxN td) → ℂ) (aV : Fin (zBoxVN td) → ℂ)
    (hCoeffU : ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = aU)
    (hCoeffV : ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = aV) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    Real.sqrt
        ((((zBoxN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0) : ℝ) *
          (((zBoxVN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0) : ℝ)) *
      Real.sqrt (td.D / td.U) *
        Real.sqrt (max (td.U / ((td.q : ℝ) * td.D)) 1) *
          Real.sqrt ((td.D * td.U) / (td.q : ℝ)) *
            Real.sqrt (td.U + td.X / |ξ|) *
              Real.sqrt (td.D + td.X / |ξ|) *
                tubeEnergy td.T F := by
  classical
  have hU0 : 0 ≤ td.U := le_trans (by norm_num : (0 : ℝ) ≤ 1) hU1
  have hD0 : 0 ≤ td.D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD1
  have hq : 0 < (td.q : ℝ) := by
    have : (0 : ℝ) < (td.q : ℝ) := by exact_mod_cast td.q_pos
    simpa using this
  have hx0 : 0 ≤ td.X / |ξ| := div_nonneg (le_of_lt hX) (abs_nonneg ξ)
  have hE0 : 0 ≤ tubeEnergy td.T F := tubeEnergy_nonneg (T := td.T) (F := F)

  -- Step 3/4 use-site bounds (TeX shape).
  have h3 :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      (((zBoxN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0) : ℝ) *
          ((td.D / (td.q : ℝ)) * (td.U + td.X / |ξ|) * tubeEnergy td.T F) :=
    norm_typeIISum_sq_le_step3_teX_of_constCoeffUZFin
      (td := td) (hDq := hDq) (hU1 := hU1) (hU0 := hU0)
      (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH_u)
      (F := F) (a := aU) (hCoeff := hCoeffU)
  have h4 :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      (((zBoxVN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0) : ℝ) *
          (td.D * (td.U / (td.q : ℝ) + td.X / |ξ|) * tubeEnergy td.T F) :=
    norm_typeIISum_sq_le_step4_teX_of_constCoeffVZFin
      (td := td) (hD1 := hD1) (hU0 := hU0) (hXH1 := hXH1) (hD0 := hD0)
      (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH_v)
      (F := F) (a := aV) (hCoeff := hCoeffV)

  -- Abbreviations (match `TypeIIStep34CombineTeX.lean`).
  let A : ℝ := ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
  let C3 : ℝ :=
    (((zBoxN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) 0) : ℝ)
  let C4 : ℝ :=
    (((zBoxVN td : ℝ) + max (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) 0) : ℝ)
  let qR : ℝ := (td.q : ℝ)
  let x : ℝ := td.X / |ξ|
  let E : ℝ := tubeEnergy td.T F
  let m : ℝ := max (td.U / (qR * td.D)) 1
  let C : ℝ :=
    Real.sqrt (C3 * C4) * Real.sqrt (td.D / td.U) * Real.sqrt m
  let B3 : ℝ := C3 * ((td.D / qR) * (td.U + x) * E)
  let B4 : ℝ := C4 * (td.D * (td.U / qR + x) * E)

  have hA0 : 0 ≤ A := by positivity [A]
  have hB30 : 0 ≤ B3 := by
    have hDq0 : 0 ≤ td.D / qR := div_nonneg hD0 (le_of_lt hq)
    have hUx0 : 0 ≤ td.U + x := add_nonneg hU0 hx0
    dsimp [B3, C3, x, E, qR]
    exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hDq0 hUx0) hE0)

  have hA_le_B3 : A ≤ B3 := by
    simpa [A, B3, C3, qR, x, E] using h3
  have hA_le_B4 : A ≤ B4 := by
    simpa [A, B4, C4, qR, x, E] using h4

  -- Geometric mean: `A ≤ √(B3*B4)`.
  have hsq : A ^ 2 ≤ (B3 * B4) := by
    have hmul : A * A ≤ B3 * B4 :=
      mul_le_mul hA_le_B3 hA_le_B4 hA0 hB30
    simpa [pow_two] using hmul
  have hA_le_sqrt : A ≤ Real.sqrt (B3 * B4) :=
    Real.le_sqrt_of_sq_le hsq

  -- Deterministic inequality: `U/q + x ≤ m * (D + x)`.
  have hDpos : 0 < td.D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hD1
  have hUx_le : td.U / qR + x ≤ m * (td.D + x) := by
    simpa [m, qR, x] using
      (add_div_le_max_mul_add (U := td.U) (D := td.D) (q := qR) (x := x) hq hDpos hx0)

  -- Compare `√(B3*B4)` to the TeX Step 5 RHS by squaring.
  have hsqrt_le :
      Real.sqrt (B3 * B4)
        ≤
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
    have hm0 : 0 ≤ m := by simp [m]
    have hC0 : 0 ≤ C := by simp [C, mul_nonneg, Real.sqrt_nonneg]
    have hR0 :
        0 ≤
          C *
            Real.sqrt ((td.D * td.U) / qR) *
              Real.sqrt (td.U + x) *
                Real.sqrt (td.D + x) *
                  E := by
      exact
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _))
          hE0
    refine (Real.sqrt_le_iff).2 ⟨hR0, ?_⟩

    -- Expand `B3*B4`, then use monotonicity in the `(U/q + x)` factor.
    have hconst0 :
        0 ≤ (C3 * C4) * ((td.D * td.D) / qR) * (td.U + x) * (E * E) := by
      have hCprod0 : 0 ≤ C3 * C4 := by
        dsimp [C3, C4]
        positivity
      have hDDq0 : 0 ≤ (td.D * td.D) / qR := by
        have : 0 ≤ td.D * td.D := mul_nonneg hD0 hD0
        exact div_nonneg this (le_of_lt hq)
      have hEE0 : 0 ≤ E * E := mul_nonneg hE0 hE0
      exact mul_nonneg (mul_nonneg (mul_nonneg hCprod0 hDDq0) hUx0) hEE0
    have hB3B4 :
        B3 * B4
          =
        (C3 * C4) *
          ((td.D * td.D) / qR) *
            (td.U + x) *
              (td.U / qR + x) *
                (E * E) := by
      dsimp [B3, B4, qR, x, E]
      ring
    have hB3B4_le :
        B3 * B4
          ≤
        (C3 * C4) *
          ((td.D * td.D) / qR) *
            (td.U + x) *
              (m * (td.D + x)) *
                (E * E) := by
      rw [hB3B4]
      have := mul_le_mul_of_nonneg_left hUx_le hconst0
      simpa [mul_assoc, mul_left_comm, mul_comm] using this

    -- Compute `C^2` (by design).
    have hC_sq : C ^ 2 = (C3 * C4) * (td.D / td.U) * m := by
      have hDU0 : 0 ≤ td.D / td.U := div_nonneg hD0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hU1)
      -- Freeze the factors so `simp` doesn't explode.
      let sC : ℝ := Real.sqrt (C3 * C4)
      let sDU : ℝ := Real.sqrt (td.D / td.U)
      let sm : ℝ := Real.sqrt m
      have hCdef : C = sC * sDU * sm := by
        simp [C, sC, sDU, sm, mul_assoc, mul_left_comm, mul_comm]
      have hsC : sC ^ 2 = C3 * C4 := by
        have : 0 ≤ C3 * C4 := by
          dsimp [C3, C4]
          positivity
        simp [sC, pow_two, Real.sq_sqrt this]
      have hsDU : sDU ^ 2 = td.D / td.U := by
        simp [sDU, pow_two, Real.sq_sqrt hDU0]
      have hsm : sm ^ 2 = m := by
        simp [sm, pow_two, Real.sq_sqrt hm0]
      calc
        C ^ 2 = (sC * sDU * sm) ^ 2 := by simpa [hCdef]
        _ = (sC ^ 2) * (sDU ^ 2) * (sm ^ 2) := by
              simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        _ = (C3 * C4) * (td.D / td.U) * m := by
              simp [hsC, hsDU, hsm, mul_assoc, mul_left_comm, mul_comm]

    -- Expand the square of the RHS and compare to the `hB3B4_le` bound.
    have hR_sq :
        (C *
              Real.sqrt ((td.D * td.U) / qR) *
                Real.sqrt (td.U + x) *
                  Real.sqrt (td.D + x) *
                    E) ^ 2
          =
        (C3 * C4) *
          ((td.D * td.D) / qR) *
            (td.U + x) *
              (m * (td.D + x)) *
                (E * E) := by
      -- First: expand the square into squares of each factor.
      let sDUq : ℝ := Real.sqrt ((td.D * td.U) / qR)
      let sU : ℝ := Real.sqrt (td.U + x)
      let sD : ℝ := Real.sqrt (td.D + x)
      have hsDUq : sDUq ^ 2 = (td.D * td.U) / qR := by
        simp [sDUq, pow_two, Real.sq_sqrt hDUq0]
      have hsU : sU ^ 2 = td.U + x := by
        simp [sU, pow_two, Real.sq_sqrt hUx0]
      have hsD : sD ^ 2 = td.D + x := by
        simp [sD, pow_two, Real.sq_sqrt hDx0]
      have hsquare :
          (C * sDUq * sU * sD * E) ^ 2
            =
          (C ^ 2) * (sDUq ^ 2) * (sU ^ 2) * (sD ^ 2) * (E ^ 2) := by
        simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
      -- Now substitute and rearrange.
      calc
        (C *
              Real.sqrt ((td.D * td.U) / qR) *
                Real.sqrt (td.U + x) *
                  Real.sqrt (td.D + x) *
                    E) ^ 2
            =
          (C * sDUq * sU * sD * E) ^ 2 := by
              simp [sDUq, sU, sD, mul_assoc, mul_left_comm, mul_comm]
        _ =
          (C ^ 2) * ((td.D * td.U) / qR) * (td.U + x) * (td.D + x) * (E ^ 2) := by
              -- use `hsquare` then rewrite the `sqrt` squares
              rw [hsquare]
              -- rewrite the three `sqrt` squares, then close by commutativity/associativity.
              simp [hsDUq, hsU, hsD, mul_assoc, mul_left_comm, mul_comm]
        _ =
          (C3 * C4) *
            ((td.D * td.D) / qR) *
              (td.U + x) *
                (m * (td.D + x)) *
                  (E * E) := by
              -- Replace `C^2`, cancel `U` and introduce `m`.
              -- (`E^2 = E*E`.)
              have hUpos : 0 < td.U := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hU1
              have hU_ne : td.U ≠ 0 := ne_of_gt hUpos
              -- `((D/U) * (D*U/q)) = D^2/q`.
              -- Do it by `field_simp`-free ring arithmetic.
              simp [hC_sq, pow_two, div_eq_mul_inv, hU_ne, mul_assoc, mul_left_comm, mul_comm]

    -- Conclude: `B3*B4 ≤ RHS^2`.
    exact hB3B4_le.trans_eq hR_sq.symm

  -- Final assembly.
  have hmain :
      A ≤
        C *
          Real.sqrt ((td.D * td.U) / qR) *
            Real.sqrt (td.U + x) *
              Real.sqrt (td.D + x) *
                E := hA_le_sqrt.trans hsqrt_le
  -- Expand abbreviations back to the stated form.
  simpa [A, C, C3, C4, qR, x, E, m] using hmain

end ConstCoeffTeX

end
end LargeSieve
end TypeII
end Engines
end SSU
