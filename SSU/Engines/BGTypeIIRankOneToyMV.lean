import SSU.Engines.BGTypeIIRankOneSignal
import SSU.Engines.LargeSieve.TypeIIRankOneProductToyTeX
import SSU.Engines.LargeSieve.RankOneShearBoxLargeSieveTeX
import SSU.Engines.TypeIILargeSieveTeXFor
import SSU.Engines.TypeIIToeplitz

/-!
Toy MV large-sieve bound for the **rank-one Type–II box model** in the identity-shear case.

This is a deliberately low-risk micro-step toward discharging the analytic hypothesis
`Step34ProdSum`:

* we work on the full dyadic box `P.box = dRange × nRange`;
* we use the *rank-one* coefficient model `F(d,n) = α(d) β(n) W_D(d/D) W_N(n/N)`;
* we observe that, when `(a,q) = (0,1)`, the Type–II oscillatory sum is exactly the product-phase
  sum `e((ξ/X) * d * n)`;
* hence the proved MV lemma in `TypeIIRankOneProductToyTeX` applies directly.

This file does **not** attempt to optimize constants, nor to remove the `1/|ξ|` singular term
near `ξ = 0`.  Handling that singularity TeX-faithfully is part of the later “balanced-ξ” stage.
-/

namespace SSU
namespace Engines
namespace BGTypeIIRankOne

open scoped BigOperators

noncomputable section

open Complex
open SSU.Engines.TypeII
open SSU.Engines.TypeII.ProductToeplitz

set_option maxHeartbeats 4000000

namespace Input

variable (I : Input)

private def boxRadius (P : SSU.Engines.BGTube.Params) : ℕ :=
  Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))

private noncomputable def boxTubeData
    (P : SSU.Engines.BGTube.Params)
    (hU : 2 * P.N ≤ P.U) :
    SSU.Engines.TypeII.TubeData where
  X := (P.X : ℝ)
  H := (P.H : ℝ)
  a := 0
  q := 1
  q_pos := by norm_num
  coprime := by decide
  D := (P.D : ℝ)
  N := (P.N : ℝ)
  U := (P.U : ℝ)
  T := P.box
  mem_T := by
    intro p hp
    have hp' : p ∈ P.dRange.product P.nRange := by
      simpa [SSU.Engines.BGTube.Params.box] using hp
    rcases Finset.mem_product.mp hp' with ⟨hd, hn⟩
    have hdIcc := Finset.mem_Icc.mp hd
    have hnIcc := Finset.mem_Icc.mp hn
    have hdLower : (P.D : ℝ) < (p.1 : ℝ) := by
      have : (P.D : ℝ) + 1 ≤ (p.1 : ℝ) := by
        exact_mod_cast hdIcc.1
      linarith
    have hdUpper : (p.1 : ℝ) ≤ (2 * P.D : ℝ) := by
      exact_mod_cast hdIcc.2
    have hnLower : (P.N : ℝ) < (p.2 : ℝ) := by
      have : (P.N : ℝ) + 1 ≤ (p.2 : ℝ) := by
        exact_mod_cast hnIcc.1
      linarith
    have hnUpper : (p.2 : ℝ) ≤ (2 * P.N : ℝ) := by
      exact_mod_cast hnIcc.2
    have hp2Nonneg : 0 ≤ (p.2 : ℝ) := by
      linarith
    have hShear :
        |(SSU.Engines.TypeII.shearU (a := (0 : ℤ)) (q := (1 : ℤ)) p : ℝ)|
          ≤ (P.U : ℝ) := by
      calc
        |(SSU.Engines.TypeII.shearU (a := (0 : ℤ)) (q := (1 : ℤ)) p : ℝ)|
            = |(p.2 : ℝ)| := by simp [SSU.Engines.TypeII.shearU]
        _ = (p.2 : ℝ) := abs_of_nonneg hp2Nonneg
        _ ≤ (2 * P.N : ℝ) := hnUpper
        _ ≤ (P.U : ℝ) := by exact_mod_cast hU
    exact ⟨⟨hdLower, hdUpper⟩, ⟨hnLower, hnUpper⟩, hShear⟩

private noncomputable def αW (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight) :
    ℤ → ℂ :=
  fun d => I.α d * W.W_D ((d : ℝ) / (P.D : ℝ))

private noncomputable def βW (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight) :
    ℤ → ℂ :=
  fun n => I.β n * W.W_N ((n : ℝ) / (P.N : ℝ))

private theorem F_eq_rankOne_on_box
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight) (p : SSU.TubePoint) :
    I.F P W p = (αW I P W p.1) * (βW I P W p.2) := by
  -- Expand the separable cutoff `W(d/D,n/N) = W_D(d/D) * W_N(n/N)`.
  simp [Input.F, Input.W_on_point, αW, βW, SSU.Engines.BGTypeII.Cutoff.W_on_point_separable,
    mul_assoc, mul_left_comm, mul_comm]

/-- Deterministic identity: on the box, `prodSum` is the `(a,q)=(0,1)` Type–II oscillatory sum. -/
theorem prodSum_eq_typeIISum_box
    (P : SSU.Engines.BGTube.Params) (ξ : ℝ) (F : SSU.TubePoint → ℂ) :
    SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box F
      =
    SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box F := by
  classical
  -- Both sides are `∑_{(d,n)∈box} F(d,n) e((ξ/X) * d*n)`.
  simp [SSU.Engines.TypeII.ProductToeplitz.prodSum, SSU.Engines.TypeII.typeIISum,
    SSU.Engines.TypeII.ProductToeplitz.prod, SSU.Engines.TypeII.shearU,
    SSU.Engines.TypeII.shearV, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/--
MV (polylog) bound on the product-phase sum for the rank-one box coefficient model, in the
identity-shear case `(a,q)=(0,1)`.

This is the “outer-`n` / inner-`d`” large-sieve shape:
`∑_{n} β(n) * ∑_{d} α(d) e((ξ/X) * n*d)`.
-/
theorem norm_prodSum_sq_le_one_add_log_box_rankOne
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (ξ : ℝ)
    (R : ℕ)
    (hDist :
      ∀ i ∈ P.nRange, ∀ j ∈ P.nRange, SSU.Hilbert.distZ i j ≤ R)
    (ht : |(ξ / (P.X : ℝ))| * (R : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / (P.X : ℝ) ≠ 0) :
    ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
      ≤
    (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2) *
      ((P.D : ℝ) + (1 / |(ξ / (P.X : ℝ))|) * (1 + Real.log R)) *
      (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
        ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := by
  classical
  -- Rewrite `prodSum` as the `(a,q)=(0,1)` Type–II sum on a product box.
  have hprod :
      SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)
        =
      SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W) :=
    prodSum_eq_typeIISum_box (P := P) (ξ := ξ) (F := I.F P W)

  -- Replace the coefficient array by the explicit rank-one form `αW(d) * βW(n)` on the product set.
  have hF :
      (I.F P W) = fun p : SSU.TubePoint => (αW I P W p.1) * (βW I P W p.2) := by
    funext p
    simpa [F_eq_rankOne_on_box (I := I) (P := P) (W := W) (p := p)]

  -- Apply the already-proved MV bound in the identity-shear toy model.
  have hMV :=
    SSU.Engines.TypeII.LargeSieve.RankOneProductToy.norm_typeIISum_sq_le_one_add_log_Icc
      (X := (P.X : ℝ)) (ξ := ξ) (U := P.nRange)
      (a := (P.D : ℤ) + 1) (N := P.D) (α := αW I P W) (β := βW I P W)
      (R := R) (hDist := hDist) (ht := ht) (ht0 := ht0)
  -- Rewrite the product box in `hMV` into `P.box`.
  have hdRange :
      Finset.Icc ((P.D : ℤ) + 1) (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = P.dRange := by
    -- Both endpoints are the same: `((D+1)+D-1) = 2D`.
    have hub : (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = ((2 * P.D : ℕ) : ℤ) := by
      -- First simplify to `2*D` in `ℤ`, then rewrite as a nat cast.
      calc
        (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = 2 * (P.D : ℤ) := by ring
        _ = ((2 * P.D : ℕ) : ℤ) := by
              -- `((m*n : ℕ) : ℤ) = (m : ℤ) * (n : ℤ)`.
              simpa [two_mul] using (Int.natCast_mul 2 P.D).symm
    simpa [SSU.Engines.BGTube.Params.dRange, hub]
  have hbox :
      (Finset.Icc ((P.D : ℤ) + 1) (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) ×ˢ P.nRange) = P.box := by
    -- Unfold `P.box = dRange × nRange` and rewrite `dRange`.
    simpa [SSU.Engines.BGTube.Params.box, hdRange]
  have hMVbox :
      ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box
          (fun p : SSU.TubePoint => (αW I P W p.1) * (βW I P W p.2))‖ ^ 2
        ≤
      (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2) *
        ((P.D : ℝ) + (1 / |(ξ / (P.X : ℝ))|) * (1 + Real.log R)) *
          (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
            ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := by
    -- Rewrite the box in `hMV` to `P.box`.
    simpa [hbox] using hMV

  -- Convert `prodSum` to `typeIISum`, then apply the MV bound.
  calc
    ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
        =
      ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2 := by
        simpa [hprod] using congrArg (fun z : ℂ => ‖z‖ ^ 2) hprod
    _ =
      ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box
          (fun p : SSU.TubePoint => (αW I P W p.1) * (βW I P W p.2))‖ ^ 2 := by
        -- Rewrite the coefficient array using `hF`.
        simpa [hF]
    _ ≤
      (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2) *
        ((P.D : ℝ) + (1 / |(ξ / (P.X : ℝ))|) * (1 + Real.log R)) *
          (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
            ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := hMVbox

/-- Geometry-specialized version of
`norm_prodSum_sq_le_one_add_log_box_rankOne` with the deterministic interval diameter on
`P.nRange = Icc (N+1) (2N)`. -/
theorem norm_prodSum_sq_le_one_add_log_box_rankOne_geom
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (ξ : ℝ)
    (ht :
      |(ξ / (P.X : ℝ))| *
          (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / (P.X : ℝ) ≠ 0) :
    ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
      ≤
    (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2) *
      ((P.D : ℝ) +
          (1 / |(ξ / (P.X : ℝ))|) *
            (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))))) *
        (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
          ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := by
  have hprod :
      SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)
        =
      SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W) :=
    prodSum_eq_typeIISum_box (P := P) (ξ := ξ) (F := I.F P W)
  have hF :
      (I.F P W) = fun p : SSU.TubePoint => (αW I P W p.1) * (βW I P W p.2) := by
    funext p
    simpa using (F_eq_rankOne_on_box (I := I) (P := P) (W := W) (p := p))
  have hdRange :
      Finset.Icc ((P.D : ℤ) + 1) (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = P.dRange := by
    have hub : (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = ((2 * P.D : ℕ) : ℤ) := by
      calc
        (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = 2 * (P.D : ℤ) := by ring
        _ = ((2 * P.D : ℕ) : ℤ) := by
              simpa [two_mul] using (Int.natCast_mul 2 P.D).symm
    simpa [SSU.Engines.BGTube.Params.dRange, hub]
  have hbox :
      (Finset.Icc ((P.D : ℤ) + 1) (((P.D : ℤ) + 1) + (P.D : ℤ) - 1)).product P.nRange = P.box := by
    simpa [SSU.Engines.BGTube.Params.box, hdRange]
  have hMVbox :
      ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box
          (fun p : SSU.TubePoint => (αW I P W p.1) * (βW I P W p.2))‖ ^ 2
        ≤
      (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2) *
        ((P.D : ℝ) +
            (1 / |(ξ / (P.X : ℝ))|) *
              (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))))) *
        (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
          ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := by
    have hmv :=
      SSU.Engines.TypeII.LargeSieve.RankOneProductToy.norm_typeIISum_sq_le_one_add_log_Icc_outerGeom
        (X := (P.X : ℝ)) (ξ := ξ)
        (A := ((P.N : ℤ) + 1)) (B := (((2 * P.N : ℕ) : ℤ)))
        (a := ((P.D : ℤ) + 1)) (N := P.D)
        (α := αW I P W) (β := βW I P W)
        (ht := by simpa using ht) (ht0 := ht0)
    have hmv' : ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ
          ((Finset.Icc ((P.D : ℤ) + 1) (((P.D : ℤ) + 1) + (P.D : ℤ) - 1)).product P.nRange)
          (fun p : SSU.TubePoint => (αW I P W p.1) * (βW I P W p.2))‖ ^ 2
          ≤
        (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2) *
          ((P.D : ℝ) + (1 / |(ξ / (P.X : ℝ))|) *
            (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))))) *
          (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
            ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := by
      simpa [SSU.Engines.BGTube.Params.nRange] using hmv
    have hmv'' := hmv'
    rw [hbox] at hmv''
    exact hmv''
  calc
    ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
        =
      ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2 := by
          simpa [hprod] using congrArg (fun z : ℂ => ‖z‖ ^ 2) hprod
    _ =
      ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box
          (fun p : SSU.TubePoint => (αW I P W p.1) * (βW I P W p.2))‖ ^ 2 := by
          simpa [hF]
    _ ≤
      (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2) *
        ((P.D : ℝ) +
            (1 / |(ξ / (P.X : ℝ))|) *
              (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))))) *
        (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
          ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2) := hMVbox

/-- Same bound as `norm_prodSum_sq_le_one_add_log_box_rankOne_geom`, with the RHS expressed as
`tubeEnergy P.box (I.F P W)` (TeX-facing energy form). -/
theorem norm_prodSum_sq_le_one_add_log_box_rankOne_geom_tubeEnergy
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (ξ : ℝ)
    (ht :
      |(ξ / (P.X : ℝ))| *
          (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / (P.X : ℝ) ≠ 0) :
    ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
      ≤
    ((P.D : ℝ) +
        (1 / |(ξ / (P.X : ℝ))|) *
          (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))))) *
      SSU.tubeEnergy P.box (I.F P W) := by
  have hraw :=
    norm_prodSum_sq_le_one_add_log_box_rankOne_geom
      (I := I) (P := P) (W := W) (ξ := ξ) (ht := ht) (ht0 := ht0)

  let Cξ : ℝ :=
    ((P.D : ℝ) +
      (1 / |(ξ / (P.X : ℝ))|) *
        (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1)))))
  let βE : ℝ := (∑ n ∈ P.nRange, ‖βW I P W n‖ ^ 2)
  let αE : ℝ := (∑ k ∈ (Finset.univ : Finset (Fin P.D)),
    ‖αW I P W (((P.D : ℤ) + 1) + (k : ℕ))‖ ^ 2)

  have hEnergyBox :
      SSU.tubeEnergy P.box (I.F P W)
        =
      βE * αE := by
    -- First rewrite tube energy as a sum over the swapped product box.
    have hdRange :
        Finset.Icc ((P.D : ℤ) + 1) (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = P.dRange := by
      have hub : (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = ((2 * P.D : ℕ) : ℤ) := by
        calc
          (((P.D : ℤ) + 1) + (P.D : ℤ) - 1) = 2 * (P.D : ℤ) := by ring
          _ = ((2 * P.D : ℕ) : ℤ) := by
                simpa [two_mul] using (Int.natCast_mul 2 P.D).symm
      simpa [SSU.Engines.BGTube.Params.dRange, hub]
    have hboxSwap :
        SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            P.nRange ((P.D : ℤ) + 1) P.D
          = P.nRange.product P.dRange := by
      simp [SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box, hdRange]
    have hsumSwap :
        SSU.tubeEnergy P.box (I.F P W)
          =
        ∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            P.nRange ((P.D : ℤ) + 1) P.D,
          ‖βW I P W uv.1 * αW I P W uv.2‖ ^ 2 := by
      calc
        SSU.tubeEnergy P.box (I.F P W)
            = ∑ d ∈ P.dRange, ∑ n ∈ P.nRange, ‖αW I P W d * βW I P W n‖ ^ 2 := by
                simp [SSU.tubeEnergy, SSU.Engines.BGTube.Params.box, F_eq_rankOne_on_box,
                  Finset.sum_product, norm_mul, mul_pow]
        _ = ∑ n ∈ P.nRange, ∑ d ∈ P.dRange, ‖βW I P W n * αW I P W d‖ ^ 2 := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (Finset.sum_comm (s := P.dRange) (t := P.nRange)
                  (f := fun d n => ‖αW I P W d * βW I P W n‖ ^ 2))
        _ = ∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            P.nRange ((P.D : ℤ) + 1) P.D,
            ‖βW I P W uv.1 * αW I P W uv.2‖ ^ 2 := by
              simp [hboxSwap, Finset.sum_product]
    have hBoxEnergy :
        (∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            P.nRange ((P.D : ℤ) + 1) P.D,
            ‖βW I P W uv.1 * αW I P W uv.2‖ ^ 2)
          =
        βE * αE := by
      calc
        (∑ uv ∈ SSU.Engines.TypeII.LargeSieve.RankOneShearBox.box
            P.nRange ((P.D : ℤ) + 1) P.D,
            ‖βW I P W uv.1 * αW I P W uv.2‖ ^ 2)
            =
          SSU.Engines.LargeSieve.RankOneShear.boxEnergy
            P.nRange ((P.D : ℤ) + 1) P.D (αW I P W) (βW I P W) := by
              simpa using
                (SSU.Engines.TypeII.LargeSieve.RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy
                  (J := P.nRange) (a := (P.D : ℤ) + 1) (N := P.D)
                  (α := αW I P W) (β := βW I P W))
        _ = βE * αE := by
              simpa [βE, αE] using
                (SSU.Engines.LargeSieve.RankOneShear.boxEnergy_eq
                  (J := P.nRange) (a := (P.D : ℤ) + 1) (N := P.D)
                  (α := αW I P W) (β := βW I P W))
    exact hsumSwap.trans hBoxEnergy

  have hraw' :
      ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
        ≤ βE * Cξ * αE := by
    simpa [Cξ, βE, αE] using hraw

  calc
    ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
        ≤ βE * Cξ * αE := hraw'
    _ = Cξ * (βE * αE) := by ring
    _ = Cξ * SSU.tubeEnergy P.box (I.F P W) := by simp [hEnergyBox]
    _ =
      ((P.D : ℝ) +
          (1 / |(ξ / (P.X : ℝ))|) *
            (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))))) *
        SSU.tubeEnergy P.box (I.F P W) := by simp [Cξ]

/-- Type-II form of `norm_prodSum_sq_le_one_add_log_box_rankOne_geom_tubeEnergy`
in the identity-shear case `(a,q) = (0,1)` on the full dyadic box. -/
theorem norm_typeIISum_sq_le_one_add_log_box_rankOne_geom_tubeEnergy
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (ξ : ℝ)
    (ht :
      |(ξ / (P.X : ℝ))| *
          (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1)) : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : ξ / (P.X : ℝ) ≠ 0) :
    ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
      ≤
    ((P.D : ℝ) +
        (1 / |(ξ / (P.X : ℝ))|) *
          (1 + Real.log (Int.toNat (((2 * P.N : ℕ) : ℤ) - ((P.N : ℤ) + 1))))) *
      SSU.tubeEnergy P.box (I.F P W) := by
  have hProd :=
    norm_prodSum_sq_le_one_add_log_box_rankOne_geom_tubeEnergy
      (I := I) (P := P) (W := W) (ξ := ξ) (ht := ht) (ht0 := ht0)
  have hEq :
      SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)
        =
      SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W) :=
    prodSum_eq_typeIISum_box (P := P) (ξ := ξ) (F := I.F P W)
  -- Rewrite by identity-shear equality.
  simpa [hEq] using hProd

/-- A proved (non-fallback) Step 4 use-site bound for the rank-one box model on the trivial
box-as-tube geometry `(a,q,s) = (0,1,0)`, using the direct product-phase large sieve proof. -/
noncomputable def step4LargeSieveOuterVFor_box_rankOne_geom
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (hU : 2 * P.N ≤ P.U)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hX : 0 < P.X) (hH : 0 < P.H)
    (hXH_box : (2 : ℝ) * ((boxRadius P : ℕ) : ℝ) ≤ (P.X : ℝ) * (P.H : ℝ)) :
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor (boxTubeData P hU) (I.F P W) := by
  let L : ℝ := 1 + Real.log (boxRadius P)
  let C : ℝ := max ((1 : ℝ) / (P.U : ℝ)) (L / (P.D : ℝ))
  refine
    { C := C
      C_nonneg := by
        apply le_trans (show 0 ≤ (1 : ℝ) / (P.U : ℝ) by positivity)
        exact le_max_left _ _
      bound := ?_ }
  intro ξ hξ0 hξH
  have hXR : 0 < (P.X : ℝ) := by exact_mod_cast hX
  have hHR : 0 < (P.H : ℝ) := by exact_mod_cast hH
  have hDR : 0 < (P.D : ℝ) := by exact_mod_cast hD1
  have hUR : 0 < (P.U : ℝ) := by exact_mod_cast hU1
  have hR0 : 0 ≤ ((boxRadius P : ℕ) : ℝ) := by positivity
  have hξH' : |ξ| ≤ 1 / (P.H : ℝ) := by
    simpa [boxTubeData] using hξH
  have hξX_ne : ξ / (P.X : ℝ) ≠ 0 := by
    exact div_ne_zero hξ0 (by exact_mod_cast Nat.ne_of_gt hX)
  have hAbsScaled :
      |ξ / (P.X : ℝ)| ≤ 1 / ((P.X : ℝ) * (P.H : ℝ)) := by
    have hdiv :
        |ξ / (P.X : ℝ)| = |ξ| / (P.X : ℝ) := by
      rw [abs_div]
      simp [abs_of_pos hXR]
    have hraw : |ξ| / (P.X : ℝ) ≤ (1 / (P.H : ℝ)) / (P.X : ℝ) := by
      exact div_le_div_of_nonneg_right hξH' (le_of_lt hXR)
    have hrewrite : (1 / (P.H : ℝ)) / (P.X : ℝ) = 1 / ((P.X : ℝ) * (P.H : ℝ)) := by
      field_simp [ne_of_gt hXR, ne_of_gt hHR]
    simpa [hdiv, hrewrite] using hraw
  have hRbound : ((boxRadius P : ℕ) : ℝ) ≤ ((P.X : ℝ) * (P.H : ℝ)) / 2 := by
    linarith
  have ht :
      |(ξ / (P.X : ℝ))| * ((boxRadius P : ℕ) : ℝ) ≤ (1 / 2 : ℝ) := by
    have h1 :
        |(ξ / (P.X : ℝ))| * ((boxRadius P : ℕ) : ℝ)
          ≤ (1 / ((P.X : ℝ) * (P.H : ℝ))) * ((boxRadius P : ℕ) : ℝ) := by
      gcongr
    have h2 :
        (1 / ((P.X : ℝ) * (P.H : ℝ))) * ((boxRadius P : ℕ) : ℝ)
          ≤ (1 / ((P.X : ℝ) * (P.H : ℝ))) * (((P.X : ℝ) * (P.H : ℝ)) / 2) := by
      have hrecip : 0 ≤ 1 / ((P.X : ℝ) * (P.H : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_left hRbound hrecip
    have h3 :
        (1 / ((P.X : ℝ) * (P.H : ℝ))) * (((P.X : ℝ) * (P.H : ℝ)) / 2) = (1 / 2 : ℝ) := by
      field_simp [ne_of_gt hXR, ne_of_gt hHR]
    calc
      |(ξ / (P.X : ℝ))| * ((boxRadius P : ℕ) : ℝ)
          ≤ (1 / ((P.X : ℝ) * (P.H : ℝ))) * ((boxRadius P : ℕ) : ℝ) := h1
      _ ≤ (1 / ((P.X : ℝ) * (P.H : ℝ))) * (((P.X : ℝ) * (P.H : ℝ)) / 2) := h2
      _ = (1 / 2 : ℝ) := h3
  have hToy :=
    norm_typeIISum_sq_le_one_add_log_box_rankOne_geom_tubeEnergy
      (I := I) (P := P) (W := W) (ξ := ξ) (ht := ht) (ht0 := hξX_ne)
  have hInv :
      1 / |ξ / (P.X : ℝ)| = (P.X : ℝ) / |ξ| := by
    rw [abs_div]
    simp [abs_of_pos hXR, abs_ne_zero.mpr hξ0, ne_of_gt hXR]
  let Y : ℝ := (P.X : ℝ) / |ξ|
  let E : ℝ := SSU.tubeEnergy P.box (I.F P W)
  have hToy' :
      ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
        ≤ ((P.D : ℝ) + Y * L) * E := by
    simpa [Y, E, L, hInv, boxRadius] using hToy
  have hY0 : 0 ≤ Y := by
    dsimp [Y]
    exact div_nonneg (by positivity) (abs_nonneg _)
  have hC0 : 0 ≤ C := by
    exact le_trans (show 0 ≤ (1 : ℝ) / (P.U : ℝ) by positivity) (le_max_left _ _)
  have hAterm :
      (P.D : ℝ) ≤ C * (P.D : ℝ) * (P.U : ℝ) := by
    have hCU_le : ((1 : ℝ) / (P.U : ℝ)) ≤ C := le_max_left _ _
    have hCU : (1 : ℝ) ≤ C * (P.U : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hCU_le (le_of_lt hUR)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ne_of_gt hUR] using hmul
    calc
      (P.D : ℝ) = (P.D : ℝ) * 1 := by ring
      _ ≤ (P.D : ℝ) * (C * (P.U : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hCU (le_of_lt hDR)
      _ = C * (P.D : ℝ) * (P.U : ℝ) := by ring
  have hLYterm :
      L * Y ≤ C * (P.D : ℝ) * Y := by
    have hLdiv : L / (P.D : ℝ) ≤ C := le_max_right _ _
    have hLle : L ≤ C * (P.D : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hLdiv (le_of_lt hDR)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, ne_of_gt hDR] using hmul
    calc
      L * Y ≤ (C * (P.D : ℝ)) * Y := by
        gcongr
      _ = C * (P.D : ℝ) * Y := by ring
  have hLinear :
      (P.D : ℝ) + Y * L ≤ C * (P.D : ℝ) * ((P.U : ℝ) + Y) := by
    linarith [hAterm, hLYterm]
  have hE0 : 0 ≤ E := by
    unfold E SSU.tubeEnergy
    refine Finset.sum_nonneg ?_
    intro p hp
    positivity
  have hMain :
      ((P.D : ℝ) + Y * L) * E ≤ (C * (P.D : ℝ) * ((P.U : ℝ) + Y)) * E := by
    exact mul_le_mul_of_nonneg_right hLinear hE0
  calc
    ‖SSU.Engines.TypeII.typeIISum (boxTubeData P hU).a
          (boxTubeData P hU).q
          (boxTubeData P hU).X ξ
          (boxTubeData P hU).T (I.F P W)‖ ^ 2
        = ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2 := by
            simp [boxTubeData]
    _ ≤ ((P.D : ℝ) + Y * L) * E := hToy'
    _ ≤ (C * (P.D : ℝ) * ((P.U : ℝ) + Y)) * E := hMain
    _ = C *
          ((boxTubeData P hU).D *
            ((boxTubeData P hU).U / ((boxTubeData P hU).q : ℝ) +
                (boxTubeData P hU).X / |ξ|) *
            SSU.tubeEnergy (boxTubeData P hU).T (I.F P W)) := by
          simp [boxTubeData, E, Y, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- A mixed Step 3/4 use-site bound for the rank-one box model: the Step 3 side still uses the
deterministic box-geometry fallback, while the Step 4 side is discharged by the proved direct
product-phase large-sieve bound above. -/
noncomputable def step34LargeSieveTeXFor_box_rankOne_geom
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (hU : 2 * P.N ≤ P.U)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hX : 0 < P.X) (hH : 0 < P.H)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_box : (2 : ℝ) * ((boxRadius P : ℕ) : ℝ) ≤ (P.X : ℝ) * (P.H : ℝ)) :
    SSU.Engines.TypeII.Step34LargeSieveTeXFor (boxTubeData P hU) (I.F P W) := by
  let td := boxTubeData P hU
  have hDq : 1 ≤ td.D / (td.q : ℝ) := by
    simpa [td, boxTubeData] using (show (1 : ℝ) ≤ (P.D : ℝ) by exact_mod_cast hD1)
  have hD0 : 0 ≤ td.D := by
    exact le_of_lt (by simpa [td, boxTubeData] using (show (0 : ℝ) < (P.D : ℝ) by exact_mod_cast hD1))
  have hU0 : 0 ≤ td.U := by
    exact le_of_lt (by simpa [td, boxTubeData] using (show (0 : ℝ) < (P.U : ℝ) by exact_mod_cast hU1))
  have hX0 : 0 ≤ td.X := by
    exact le_of_lt (by simpa [td, boxTubeData] using (show (0 : ℝ) < (P.X : ℝ) by exact_mod_cast hX))
  have hDpos : 0 < td.D := by
    simpa [td, boxTubeData] using (show (0 : ℝ) < (P.D : ℝ) by exact_mod_cast hD1)
  have hUpos : 0 < td.U := by
    simpa [td, boxTubeData] using (show (0 : ℝ) < (P.U : ℝ) by exact_mod_cast hU1)
  let h3 :
      SSU.Engines.TypeII.Step3LargeSieveOuterUFor td (I.F P W) :=
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_box_geometry
      (td := td)
      (hDq := hDq) (hD := hD0) (hU := by simpa [td, boxTubeData] using (show (1 : ℝ) ≤ (P.U : ℝ) by exact_mod_cast hU1))
      (hX := hX0) (F := I.F P W)
  let h4 :
      SSU.Engines.TypeII.Step4LargeSieveOuterVFor td (I.F P W) :=
    step4LargeSieveOuterVFor_box_rankOne_geom
      (I := I) (P := P) (W := W)
      (hU := hU) (hD1 := hD1) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH_box := hXH_box)
  exact
    SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
      (td := td) (F := I.F P W) h3 h4 hDpos hUpos hX0

/-- A genuinely uniform fixed-signal Step 3–4 package for the rank-one box model.

This removes the TeX `X / |ξ|` singularity by splitting the ξ-band into:

* a small neighborhood `|ξ| ≤ 1 / (2H)`, handled by the deterministic `Step34ProdSum.trivial`;
* the complementary band, where `|ξ| > 1 / (2H)` makes `X / |ξ| ≤ 2 X H`, so the proved
  TeX-style `step34LargeSieveTeXFor_box_rankOne_geom` becomes uniform.

This is still only a fixed-array (`Step34ProdSumFor`) result for `I.F P W`, not a global
`Step34ProdSum` over arbitrary coefficient arrays on the box.
-/
noncomputable def step34ProdSumFor_box_rankOne_uniform
    (P : SSU.Engines.BGTube.Params) (W : SSU.Engines.TFA.SeparableWeight)
    (hU : 2 * P.N ≤ P.U)
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hX : 0 < P.X) (hH : 0 < P.H)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hXH_box : (2 : ℝ) * ((boxRadius P : ℕ) : ℝ) ≤ (P.X : ℝ) * (P.H : ℝ)) :
    let F : SSU.TubePoint → ℂ := fun p => I.F P W p
    SSU.Engines.TypeIIToeplitz.Step34ProdSumFor (P.X : ℝ) (P.H : ℝ) P.box F := by
  dsimp
  let hTriv :
      SSU.Engines.TypeIIToeplitz.Step34ProdSum (P.X : ℝ) (P.H : ℝ) P.box :=
    SSU.Engines.TypeIIToeplitz.Step34ProdSum.trivial (P.X : ℝ) (P.H : ℝ) P.box
      (by exact_mod_cast hX) (by exact_mod_cast hH)
  let hTrivFor :
      SSU.Engines.TypeIIToeplitz.Step34ProdSumFor (P.X : ℝ) (P.H : ℝ) P.box (I.F P W) :=
    SSU.Engines.TypeIIToeplitz.Step34ProdSumFor.of_global
      (P.X : ℝ) (P.H : ℝ) P.box hTriv (I.F P W)
  let h34 :=
    step34LargeSieveTeXFor_box_rankOne_geom
      (I := I) (P := P) (W := W)
      (hU := hU) (hD1 := hD1) (hU1 := hU1)
      (hX := hX) (hH := hH) (hXH1 := hXH1) (hXH_box := hXH_box)
  let E : ℝ := SSU.tubeEnergy P.box (I.F P W)
  let B : ℝ :=
    h34.C *
      Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
        Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) *
          Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))
  let Cbig : ℝ := B * Real.sqrt ((P.X : ℝ) / (P.H : ℝ))
  let C : ℝ := max hTriv.C Cbig
  refine
    { C := C
      C_nonneg := by
        have hTriv0 : 0 ≤ hTriv.C := hTriv.C_nonneg
        exact le_trans hTriv0 (le_max_left _ _)
      bound := ?_ }
  intro ξ hξBand
  have hXR : 0 < (P.X : ℝ) := by exact_mod_cast hX
  have hHR : 0 < (P.H : ℝ) := by exact_mod_cast hH
  have hDR : 0 < (P.D : ℝ) := by exact_mod_cast hD1
  have hUR : 0 < (P.U : ℝ) := by exact_mod_cast hU1
  have hE0 : 0 ≤ E := by
    unfold E SSU.tubeEnergy
    refine Finset.sum_nonneg ?_
    intro p hp
    positivity
  have hsqrtHX0 : 0 ≤ Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) := by positivity
  have hsqrtXH0 : 0 ≤ Real.sqrt ((P.X : ℝ) / (P.H : ℝ)) := by positivity
  have hsqrt_cancel :
      Real.sqrt ((P.X : ℝ) / (P.H : ℝ)) * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) = 1 := by
    have hpos : 0 ≤ (P.X : ℝ) / (P.H : ℝ) := by positivity
    calc
      Real.sqrt ((P.X : ℝ) / (P.H : ℝ)) * Real.sqrt ((P.H : ℝ) / (P.X : ℝ))
          = Real.sqrt (((P.X : ℝ) / (P.H : ℝ)) * ((P.H : ℝ) / (P.X : ℝ))) := by
              simpa using (Real.sqrt_mul hpos ((P.H : ℝ) / (P.X : ℝ))).symm
      _ = Real.sqrt (1 : ℝ) := by
            congr 1
            field_simp [ne_of_gt hXR, ne_of_gt hHR]
      _ = 1 := by simp
  by_cases hsmall : |ξ| ≤ 1 / (2 * (P.H : ℝ))
  · have hbase :=
      hTrivFor.bound ξ hξBand
    have hC_le : hTriv.C ≤ C := le_max_left _ _
    have hmul :
        hTriv.C * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E
          ≤ C * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := by
      have hfac : 0 ≤ Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := mul_nonneg hsqrtHX0 hE0
      have htmp := mul_le_mul_of_nonneg_right hC_le hfac
      calc
        hTriv.C * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E
            = hTriv.C * (Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E) := by ring
        _ ≤ C * (Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E) := htmp
        _ = C * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := by ring
    exact le_trans hbase hmul
  · have hhalf_pos : 0 < 1 / (2 * (P.H : ℝ)) := by positivity
    have hlarge : 1 / (2 * (P.H : ℝ)) < |ξ| := lt_of_not_ge hsmall
    have hξabs_pos : 0 < |ξ| := lt_trans hhalf_pos hlarge
    have hξ0 : ξ ≠ 0 := by
      exact abs_pos.mp hξabs_pos
    have h34raw :
        ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
          ≤
        h34.C *
          Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
            Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
              Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) *
                E := by
      simpa [boxTubeData, E, mul_assoc, mul_left_comm, mul_comm] using
        (h34.bound ξ hξ0 (by simpa [boxTubeData] using hξBand))
    have hrecip :
        1 / |ξ| ≤ 2 * (P.H : ℝ) := by
      have hrecip' :
          1 / |ξ| ≤ 1 / (1 / (2 * (P.H : ℝ))) := by
        exact one_div_le_one_div_of_le hhalf_pos (le_of_lt hlarge)
      have hrewrite : 1 / (1 / (2 * (P.H : ℝ))) = 2 * (P.H : ℝ) := by
        field_simp [ne_of_gt hHR]
      simpa [hrewrite] using hrecip'
    have hXdiv :
        (P.X : ℝ) / |ξ| ≤ 2 * (P.X : ℝ) * (P.H : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hrecip (le_of_lt hXR)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have hsqrtU :
        Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) ≤
          Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hsqrtD :
        Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) ≤
          Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hA0 :
        0 ≤ h34.C * Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) := by
      exact mul_nonneg h34.C_nonneg (by positivity)
    have hgeom :
        h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|)
          ≤ B := by
      have h1 :
          h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|)
            ≤
          h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsqrtU hA0
      have h2 :
          (h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
              Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|)
            ≤
          (h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
              Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
        have hleft0 :
            0 ≤ h34.C *
              Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
                Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := by
          positivity
        exact mul_le_mul_of_nonneg_left hsqrtD hleft0
      calc
        h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|)
            ≤
        (h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) := by
                  simpa [mul_assoc] using mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤
        (h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ))) *
                Real.sqrt ((P.D : ℝ) + 2 * (P.X : ℝ) * (P.H : ℝ)) := h2
        _ = B := by simp [B, mul_assoc]
    have hbig0 :
        ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2 ≤ B * E := by
      have hEq :=
        prodSum_eq_typeIISum_box (P := P) (ξ := ξ) (F := I.F P W)
      calc
        ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
            =
        ‖SSU.Engines.TypeII.typeIISum (a := (0 : ℤ)) (q := (1 : ℤ)) (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2 := by
              rw [hEq]
        _ ≤
          h34.C *
            Real.sqrt ((P.D : ℝ) * (P.U : ℝ)) *
              Real.sqrt ((P.U : ℝ) + (P.X : ℝ) / |ξ|) *
                Real.sqrt ((P.D : ℝ) + (P.X : ℝ) / |ξ|) *
                  E := h34raw
        _ ≤ B * E := by
              have hgeomE := mul_le_mul_of_nonneg_right hgeom hE0
              simpa [mul_assoc, mul_left_comm, mul_comm] using hgeomE
    have hCBigFactor :
        B = Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) := by
      calc
        B = B * (Real.sqrt ((P.X : ℝ) / (P.H : ℝ)) * Real.sqrt ((P.H : ℝ) / (P.X : ℝ))) := by
              rw [hsqrt_cancel]
              ring
        _ = Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) := by
              simp [Cbig, mul_assoc, mul_left_comm, mul_comm]
    have hCBig :
        B * E = Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := by
      calc
        B * E = (Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ))) * E := by rw [hCBigFactor]
        _ = Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := by ring
    have hCbig_le : Cbig ≤ C := le_max_right _ _
    have hinflate :
        Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E
          ≤ C * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := by
      have hfac : 0 ≤ Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := mul_nonneg hsqrtHX0 hE0
      have htmp := mul_le_mul_of_nonneg_right hCbig_le hfac
      calc
        Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E
            = Cbig * (Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E) := by ring
        _ ≤ C * (Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E) := htmp
        _ = C * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := by ring
    calc
      ‖SSU.Engines.TypeII.ProductToeplitz.prodSum (P.X : ℝ) ξ P.box (I.F P W)‖ ^ 2
          ≤ B * E := hbig0
      _ = Cbig * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := hCBig
      _ ≤ C * Real.sqrt ((P.H : ℝ) / (P.X : ℝ)) * E := hinflate

end Input

end

end BGTypeIIRankOne
end Engines
end SSU
