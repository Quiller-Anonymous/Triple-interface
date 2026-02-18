import SSU.Engines.BGTypeIIRankOneSignal
import SSU.Engines.LargeSieve.TypeIIRankOneProductToyTeX
import SSU.Engines.LargeSieve.RankOneShearBoxLargeSieveTeX

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

namespace Input

variable (I : Input)

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

end Input

end

end BGTypeIIRankOne
end Engines
end SSU
