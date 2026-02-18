import SSU.Engines.LargeSieve.TypeIIFiberLargeSieveFromFiniteLargeSieve
import SSU.Engines.LargeSieve.TypeIIFiberEnergy

/-!
Helpers: discharge a TeX Step 3/4 *use-site* bound from the proved MV engine, under a
“constant-coefficient” hypothesis.

This is intentionally a **micro-step** toward the real SSU Type–II extraction:
the Montgomery–Vaughan inequality is already proved and packaged as `FiniteLargeSieve` instances
on `uSet td` / `vSet td`, but applying it requires an algebraic hypothesis that the translated
`Fin`-indexed coefficient arrays are independent of the outer index.

Once a later extraction layer proves that constancy (for the specific `F` coming from packets),
the lemmas in this file give a clean bound on `‖typeIISum‖²` in terms of `tubeEnergy` (no extra
cardinality loss).
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

namespace ConstCoeffMV

open ZBoxRewrite
open ZBoxToFin
open FiberFromFiniteLargeSieve
open IndexLargeSieve

/-!
## Deterministic energy identity for the translated `Fin` coefficient arrays
-/

/-- Step 3 coefficient energy: sum over `zBox` equals sum over `zSet` (extra fibers are empty). -/
private theorem sum_zBox_norm_fiberUZ_sum_sq_eq_sum_zSet_norm_fiberUZ_sum_sq
    (td : TubeData) (F : TubePoint → ℂ) (u : ℤ) :
    (∑ z ∈ IndexBounds.zBox td, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
      =
    (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
  classical
  have hsub : zSet td u ⊆ IndexBounds.zBox td := by
    intro z hz
    exact IndexBounds.mem_zSet_imp_mem_zBox (td := td) (u := u) (z := z) hz
  have hzero :
      ∀ z ∈ IndexBounds.zBox td, z ∉ zSet td u →
        ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 = 0 := by
    intro z _hzBox hzNot
    have : (∑ p ∈ fiberUZ td u z, F p) = 0 :=
      sum_fiberUZ_eq_zero_of_not_mem_zSet (td := td) (F := F) (u := u) (z := z) hzNot
    simp [this]
  -- Extend the `zSet` sum to `zBox` using `sum_subset`.
  -- (We orient it so the RHS is the extended sum.)
  have hsum :
      (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        =
      ∑ z ∈ IndexBounds.zBox td, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 := by
    refine (Finset.sum_subset (s₁ := zSet td u) (s₂ := IndexBounds.zBox td)
      (f := fun z : ℤ => ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) hsub ?_)
    intro z hzBox hzNot
    exact hzero z hzBox hzNot
  exact hsum.symm

/-- Step 4 coefficient energy: sum over `zBoxV` equals sum over `zSetV`. -/
private theorem sum_zBoxV_norm_fiberVZ_sum_sq_eq_sum_zSetV_norm_fiberVZ_sum_sq
    (td : TubeData) (F : TubePoint → ℂ) (v : ℤ) :
    (∑ z ∈ IndexBounds.zBoxV td, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
      =
    (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
  classical
  have hsub : zSetV td v ⊆ IndexBounds.zBoxV td := by
    intro z hz
    exact IndexBounds.mem_zSetV_imp_mem_zBoxV (td := td) (v := v) (z := z) hz
  have hzero :
      ∀ z ∈ IndexBounds.zBoxV td, z ∉ zSetV td v →
        ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 = 0 := by
    intro z _hzBox hzNot
    have : (∑ p ∈ fiberVZ td v z, F p) = 0 :=
      sum_fiberVZ_eq_zero_of_not_mem_zSetV (td := td) (F := F) (v := v) (z := z) hzNot
    simp [this]
  have hsum :
      (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        =
      ∑ z ∈ IndexBounds.zBoxV td, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 := by
    refine (Finset.sum_subset (s₁ := zSetV td v) (s₂ := IndexBounds.zBoxV td)
      (f := fun z : ℤ => ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) hsub ?_)
    intro z hzBox hzNot
    exact hzero z hzBox hzNot
  exact hsum.symm

private theorem sum_univ_norm_coeffUZFin_sq_eq_sum_zBox_norm_fiberUZ_sum_sq
    (td : TubeData) (F : TubePoint → ℂ) (u : ℤ) :
    (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2)
      =
    (∑ z ∈ IndexBounds.zBox td, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
  classical
  -- `zBox` is an `Ioc`, and `sum_zBox_eq_sum_range` gives the translated `range` sum.
  -- Then `Finset.sum_fin_eq_sum_range` turns `Finset.univ` into that `range`.
  have hrange :
      (∑ z ∈ IndexBounds.zBox td, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        =
      ∑ n ∈ Finset.range (zBoxN td),
        ‖∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p‖ ^ 2 := by
    -- `sum_zBox_eq_sum_range` is oriented `sum_zBox = sum_range`.
    simpa using (sum_zBox_eq_sum_range (td := td)
      (f := fun z : ℤ => ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2))
  -- Now rewrite the `Finset.univ` sum to the `range` sum and unfold `coeffUZFin`.
  have huniv :
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2)
        =
      ∑ n ∈ Finset.range (zBoxN td),
        ‖∑ p ∈ fiberUZ td u (zBoxA td + 1 + n), F p‖ ^ 2 := by
    classical
    let g : Fin (zBoxN td) → ℝ := fun k => ‖coeffUZFin td F u k‖ ^ 2
    have h0 := (Finset.sum_fin_eq_sum_range (n := zBoxN td) (c := g))
    have hFin :
        (∑ k : Fin (zBoxN td), g k)
          =
        ∑ x ∈ Finset.range (zBoxN td), ‖∑ p ∈ fiberUZ td u (zBoxA td + 1 + x), F p‖ ^ 2 := by
      refine h0.trans ?_
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxlt : x < zBoxN td := Finset.mem_range.1 hx
      simp [g, coeffUZFin, hxlt]
    -- Convert `∑ k ∈ univ` to `∑ k : Fin`, then unfold `g` and `coeffUZFin`.
    -- (On `⟨x,hxlt⟩` we have `(⟨x,hxlt⟩ : ℕ) = x`.)
    simpa [g] using (by
      -- `simp` rewrites `∑ k ∈ univ` into `∑ k : Fin`.
      simpa using hFin)
  -- Combine.
  exact huniv.trans hrange.symm

private theorem sum_univ_norm_coeffVZFin_sq_eq_sum_zBoxV_norm_fiberVZ_sum_sq
    (td : TubeData) (F : TubePoint → ℂ) (v : ℤ) :
    (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2)
      =
    (∑ z ∈ IndexBounds.zBoxV td, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
  classical
  have hrange :
      (∑ z ∈ IndexBounds.zBoxV td, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        =
      ∑ n ∈ Finset.range (zBoxVN td),
        ‖∑ p ∈ fiberVZ td v (zBoxVA td + n), F p‖ ^ 2 := by
    simpa using (sum_zBoxV_eq_sum_range (td := td)
      (f := fun z : ℤ => ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2))
  have huniv :
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2)
        =
      ∑ n ∈ Finset.range (zBoxVN td),
        ‖∑ p ∈ fiberVZ td v (zBoxVA td + n), F p‖ ^ 2 := by
    classical
    let g : Fin (zBoxVN td) → ℝ :=
      fun k => ‖coeffVZFin td F v k‖ ^ 2
    have h0 := (Finset.sum_fin_eq_sum_range (n := zBoxVN td) (c := g))
    have hFin :
        (∑ k : Fin (zBoxVN td), g k)
          =
        ∑ x ∈ Finset.range (zBoxVN td), ‖∑ p ∈ fiberVZ td v (zBoxVA td + x), F p‖ ^ 2 := by
      refine h0.trans ?_
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxlt : x < zBoxVN td := Finset.mem_range.1 hx
      simp [g, coeffVZFin, hxlt]
    simpa [g] using (by
      simpa using hFin)
  exact huniv.trans hrange.symm

/-- Per-`u` Step 3 coefficient energy identity:
the translated finite-array energy equals the fiber energy over `zSet td u`. -/
theorem sum_univ_norm_coeffUZFin_sq_eq_sum_zSet_norm_fiberUZ_sum_sq
    (td : TubeData) (F : TubePoint → ℂ) (u : ℤ) :
    (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2)
      =
    (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) := by
  calc
    (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2)
        =
      (∑ z ∈ IndexBounds.zBox td, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) :=
      sum_univ_norm_coeffUZFin_sq_eq_sum_zBox_norm_fiberUZ_sum_sq
        (td := td) (F := F) (u := u)
    _ =
      (∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2) :=
      sum_zBox_norm_fiberUZ_sum_sq_eq_sum_zSet_norm_fiberUZ_sum_sq
        (td := td) (F := F) (u := u)

/-- Per-`v` Step 4 coefficient energy identity:
the translated finite-array energy equals the fiber energy over `zSetV td v`. -/
theorem sum_univ_norm_coeffVZFin_sq_eq_sum_zSetV_norm_fiberVZ_sum_sq
    (td : TubeData) (F : TubePoint → ℂ) (v : ℤ) :
    (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2)
      =
    (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) := by
  calc
    (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2)
        =
      (∑ z ∈ IndexBounds.zBoxV td, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) :=
      sum_univ_norm_coeffVZFin_sq_eq_sum_zBoxV_norm_fiberVZ_sum_sq
        (td := td) (F := F) (v := v)
    _ =
      (∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2) :=
      sum_zBoxV_norm_fiberVZ_sum_sq_eq_sum_zSetV_norm_fiberVZ_sum_sq
        (td := td) (F := F) (v := v)

/-- Total Step 3 coefficient energy, expressed via `coeffUZFin`. -/
theorem sum_u_sum_univ_norm_coeffUZFin_sq_eq_tubeEnergy (td : TubeData) (F : TubePoint → ℂ) :
    (∑ u ∈ uSet td,
        ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2)
      =
    tubeEnergy td.T F := by
  classical
  -- Convert the `Fin`-indexed energy to the `zBox` energy.
  have h1 :
      (∑ u ∈ uSet td,
          ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2)
        =
      ∑ u ∈ uSet td,
        ∑ z ∈ IndexBounds.zBox td, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    simpa using (sum_univ_norm_coeffUZFin_sq_eq_sum_zBox_norm_fiberUZ_sum_sq (td := td) (F := F) (u := u))
  -- Replace `zBox` by `zSet` (extra fibers are empty).
  have h2 :
      (∑ u ∈ uSet td,
          ∑ z ∈ IndexBounds.zBox td, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2)
        =
      ∑ u ∈ uSet td,
        ∑ z ∈ zSet td u, ‖∑ p ∈ fiberUZ td u z, F p‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    simpa using
      (sum_zBox_norm_fiberUZ_sum_sq_eq_sum_zSet_norm_fiberUZ_sum_sq (td := td) (F := F) (u := u))
  -- Now use the deterministic fiber energy identity.
  simpa [h1, h2] using (sum_u_z_norm_fiberUZ_sum_sq_eq_tubeEnergy (td := td) (F := F))

/-- Total Step 4 coefficient energy, expressed via `coeffVZFin`. -/
theorem sum_v_sum_univ_norm_coeffVZFin_sq_eq_tubeEnergy (td : TubeData) (F : TubePoint → ℂ) :
    (∑ v ∈ vSet td,
        ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2)
      =
    tubeEnergy td.T F := by
  classical
  have h1 :
      (∑ v ∈ vSet td,
          ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2)
        =
      ∑ v ∈ vSet td,
        ∑ z ∈ IndexBounds.zBoxV td, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    simpa using (sum_univ_norm_coeffVZFin_sq_eq_sum_zBoxV_norm_fiberVZ_sum_sq (td := td) (F := F) (v := v))
  have h2 :
      (∑ v ∈ vSet td,
          ∑ z ∈ IndexBounds.zBoxV td, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2)
        =
      ∑ v ∈ vSet td,
        ∑ z ∈ zSetV td v, ‖∑ p ∈ fiberVZ td v z, F p‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    simpa using
      (sum_zBoxV_norm_fiberVZ_sum_sq_eq_sum_zSetV_norm_fiberVZ_sum_sq (td := td) (F := F) (v := v))
  simpa [h1, h2] using (sum_v_z_norm_fiberVZ_sum_sq_eq_tubeEnergy (td := td) (F := F))

/-!
## Step 3/4 use-site bounds from constancy + MV

These are not the final TeX Step 3/4 interfaces: they are the clean “if the extracted coefficient
arrays are constant, then MV directly bounds `‖typeIISum‖²` by `tubeEnergy`” helper lemmas.
-/

theorem norm_typeIISum_sq_le_uSet_finiteLargeSieve_C_mul_tubeEnergy_of_constCoeffUZFin
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxN td) → ℂ)
    (hCoeff : ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = a) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
        (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
      tubeEnergy td.T F := by
  classical
  -- Outer-`u` Cauchy–Schwarz.
  have hdecomp := typeIISum_eq_outer_u_innerUZ (td := td) (ξ := ξ) (F := F)
  have hcs :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      ((uSet td).card : ℝ) * ∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2 := by
    -- Same argument as `step3OuterU_of_fiberLargeSieve`, but we keep it local.
    have hcs' :
        ‖∑ u ∈ uSet td,
            (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * innerSumUZ td ξ F u‖ ^ 2
          ≤
        ((uSet td).card : ℝ) *
          ∑ u ∈ uSet td,
            ‖(e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * innerSumUZ td ξ F u‖ ^ 2 := by
      simpa using
        (norm_sum_sq_le_card_mul_sum_norm_sq (s := uSet td)
          (f := fun u =>
            (e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))) * innerSumUZ td ξ F u))
    have hsimp :
        ∑ u ∈ uSet td,
            (‖e (ξ * (u : ℝ) * (vResidue td u : ℝ) / ((td.q : ℝ) * td.X))‖ *
                ‖innerSumUZ td ξ F u‖) ^ 2
          =
        ∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      simp [norm_e]
    simpa [hdecomp, hsimp] using hcs'
  -- Apply MV on `uSet` to bound the inner square-sum.
  have hLS :=
    step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_finiteLargeSieve
      (td := td) (hU0 := hU0)
      (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := F) (a := a) (hCoeff := hCoeff)
  -- Convert the coefficient energy into `tubeEnergy` and cancel the outer `card(uSet)` factor.
  have hEnergy :
      ((uSet td).card : ℝ) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2)
        =
      tubeEnergy td.T F := by
    have hEcoeff := (sum_u_sum_univ_norm_coeffUZFin_sq_eq_tubeEnergy (td := td) (F := F))
    have hErewrite :
        (∑ u ∈ uSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2)
          =
        (∑ u ∈ uSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro u hu
      have hu' := hCoeff u hu
      have : (fun k => coeffUZFin td F u k) = a := by
        funext k
        simpa using congrArg (fun f => f k) hu'
      simpa [this]
    have hEsum :
        (∑ u ∈ uSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2)
          =
        ((uSet td).card : ℝ) * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
      simp [Finset.sum_const]
    -- `card * energy = tubeEnergy` by rewriting the coefficient-energy identity.
    calc
      ((uSet td).card : ℝ) * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2)
          =
        (∑ u ∈ uSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
              simpa using hEsum.symm
      _ =
        (∑ u ∈ uSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖coeffUZFin td F u k‖ ^ 2) := by
              simpa using hErewrite.symm
      _ = tubeEnergy td.T F := hEcoeff
  -- Finish.
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ ((uSet td).card : ℝ) * ∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2 := hcs
    _ ≤ ((uSet td).card : ℝ) *
          ((uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
              (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
              (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
            (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hLS (by positivity)
    _ = (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
            (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
            (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
          tubeEnergy td.T F := by
          -- reassociate and use `hEnergy`
          have : ((uSet td).card : ℝ) *
              ((uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
                  (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
                  (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
                (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2))
              =
              (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
                  (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
                  (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
                (((uSet td).card : ℝ) *
                  (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2)) := by
            ring
          simpa [this, hEnergy, mul_assoc] using rfl

theorem norm_typeIISum_sq_le_vSet_finiteLargeSieve_C_mul_tubeEnergy_of_constCoeffVZFin
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxVN td) → ℂ)
    (hCoeff : ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = a) :
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
      ≤
    (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
        (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
      tubeEnergy td.T F := by
  classical
  have hdecomp := typeIISum_eq_outer_v_innerVZ (td := td) (ξ := ξ) (F := F)
  have hcs :
      ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤
      ((vSet td).card : ℝ) * ∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2 := by
    have hcs' :
        ‖∑ v ∈ vSet td,
            (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * innerSumVZ td ξ F v‖ ^ 2
          ≤
        ((vSet td).card : ℝ) *
          ∑ v ∈ vSet td,
            ‖(e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * innerSumVZ td ξ F v‖ ^ 2 := by
      simpa using
        (norm_sum_sq_le_card_mul_sum_norm_sq (s := vSet td)
          (f := fun v =>
            (e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))) * innerSumVZ td ξ F v))
    have hsimp :
        ∑ v ∈ vSet td,
            (‖e (ξ * (uResidue td v : ℝ) * (v : ℝ) / ((td.q : ℝ) * td.X))‖ *
                ‖innerSumVZ td ξ F v‖) ^ 2
          =
        ∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simp [norm_e]
    simpa [hdecomp, hsimp] using hcs'
  have hLS :=
    step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff_vSet_finiteLargeSieve
      (td := td) (hD0 := hD0)
      (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
      (F := F) (a := a) (hCoeff := hCoeff)
  have hEnergy :
      ((vSet td).card : ℝ) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2)
        =
      tubeEnergy td.T F := by
    have hEcoeff := (sum_v_sum_univ_norm_coeffVZFin_sq_eq_tubeEnergy (td := td) (F := F))
    have hErewrite :
        (∑ v ∈ vSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2)
          =
        (∑ v ∈ vSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      have hv' := hCoeff v hv
      have : (fun k => coeffVZFin td F v k) = a := by
        funext k
        simpa using congrArg (fun f => f k) hv'
      simpa [this]
    have hEsum :
        (∑ v ∈ vSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2)
          =
        ((vSet td).card : ℝ) * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
      simp [Finset.sum_const]
    calc
      ((vSet td).card : ℝ) * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2)
          =
        (∑ v ∈ vSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
              simpa using hEsum.symm
      _ =
        (∑ v ∈ vSet td,
            ∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖coeffVZFin td F v k‖ ^ 2) := by
              simpa using hErewrite.symm
      _ = tubeEnergy td.T F := hEcoeff
  calc
    ‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2
        ≤ ((vSet td).card : ℝ) * ∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2 := hcs
    _ ≤ ((vSet td).card : ℝ) *
          ((vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
              (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
              (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
            (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hLS (by positivity)
    _ = (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
            (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
            (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
          tubeEnergy td.T F := by
          have : ((vSet td).card : ℝ) *
              ((vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
                  (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
                  (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
                (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2))
              =
              (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
                  (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
                  (hξH := by simpa [abs_neg] using hξH) (hXH := hXH)).C *
                (((vSet td).card : ℝ) *
                  (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2)) := by
            ring
          simpa [this, hEnergy, mul_assoc] using rfl

end ConstCoeffMV

end

end LargeSieve
end TypeII
end Engines
end SSU
