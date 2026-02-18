import SSU.Engines.LargeSieve.TypeIIZBoxToFin
import SSU.Engines.LargeSieve.MontgomeryVaughanHypothesis
import SSU.Engines.LargeSieve.TypeIIIndexLargeSieve
import SSU.Engines.LargeSieve.TypeIIResidueIndexLargeSieve
import SSU.Engines.LargeSieve.TypeIIConstCoeffFromFiber
import SSU.Engines.LargeSieve.TypeIIStep3Reduce
import SSU.Engines.LargeSieve.TypeIIStep4Reduce

/-!
Bridging lemmas: apply a `FiniteLargeSieve` bound to the (TeX Step 3/4) fiber sums,
*after* deterministic `zBox` rewriting.

This file intentionally does **not** try to prove the analytic hypotheses needed for SSU.
Instead it packages the clean algebra:

* if the `Fin`-indexed coefficient array is (provably) independent of the fiber index, then
  `innerSumUZ` / `innerSumVZ` match the canonical exponential sums used by the MV engine;
* hence any `FiniteLargeSieve` instance with the matching phase gives a bound on the
  sum of squared norms.

The application-specific step “why the coefficients become independent” is part of the later
Type–II extraction layer (rank-one signals / Toeplitz reduction).
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace FiberFromFiniteLargeSieve

open SSU.Engines.LargeSieve
open ZBoxToFin
open ZBoxRewrite
open IndexLargeSieve
open ResidueIndexLargeSieve

variable {td : TubeData}

/-!
## Step 3 (`u`-fibers): `innerSumUZ`
-/

/-- If the `Fin`-indexed coefficient array for `innerSumUZ` is constant in `u`, then the Step 3
`u`-fiber square-sum is bounded by any matching `FiniteLargeSieve` instance. -/
theorem step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff
    (ξ : ℝ) (F : TubePoint → ℂ)
    (a : Fin (zBoxN td) → ℂ)
    (LS : SSU.Engines.LargeSieve.FiniteLargeSieve ℤ (Fin (zBoxN td)))
    (hI : LS.I = uSet td)
    (hK : LS.K = (Finset.univ : Finset (Fin (zBoxN td))))
    (hCoeff : ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = a)
    (hPhase :
      ∀ (u : ℤ) (k : Fin (zBoxN td)),
        LS.phase u k = (ξ * (u : ℝ) * ((k : ℕ) : ℝ)) / td.X) :
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
      ≤
    LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) :=
by
  classical
  -- Rewrite `innerSumUZ` as the `Fin`-indexed exponential sum with coefficient array `a`.
  have hrewrite (u : ℤ) (hu : u ∈ uSet td) :
      ‖innerSumUZ td ξ F u‖
        =
      ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          a k * SSU.Engines.TypeII.e (LS.phase u k)‖ := by
    have h0 :=
      norm_innerSumUZ_eq_norm_sum_univ_coeffUZFin (td := td) (ξ := ξ) (F := F) (u := u)
    -- Replace the coefficient array, then rewrite the phase via `hPhase`.
    have ha : coeffUZFin td F u = a := hCoeff u hu
    -- First rewrite coefficients.
    have h0' :
        ‖innerSumUZ td ξ F u‖
          =
        ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            a k * SSU.Engines.TypeII.e (ξ * (u : ℝ) * ((k : ℕ) : ℝ) / td.X)‖ := by
      simpa [ha] using h0
    -- Then rewrite `e(ξ*u*k/X)` as `e(LS.phase u k)`.
    refine h0'.trans ?_
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [hPhase u k]

  -- Convert the LHS square-sum into the `FiniteLargeSieve` shape.
  have hLHS :
      (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        =
      (∑ u ∈ LS.I, ‖∑ k ∈ LS.K, a k * SSU.Engines.TypeII.e (LS.phase u k)‖ ^ 2) := by
    -- Rewrite `LS.I`/`LS.K` to the concrete sets, then use the pointwise norm rewrite.
    -- (`subst` does not work on projections like `LS.I`.)
    rw [hI, hK]
    refine Finset.sum_congr rfl ?_
    intro u hu
    have := hrewrite u hu
    simpa [this] using congrArg (fun t => t ^ 2) this

  -- Apply the `FiniteLargeSieve` bound.
  have hBound := LS.bound a
  -- `LS.bound` is a sum over `LS.I`; rewrite it using `hI`/`hK` and then transport via `hLHS`.
  have hBound' :
      (∑ u ∈ uSet td, ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            a k * SSU.Engines.TypeII.e (LS.phase u k)‖ ^ 2)
        ≤
      LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
    simpa [hI, hK] using hBound
  -- Finish.
  calc
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
        =
      (∑ u ∈ uSet td, ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            a k * SSU.Engines.TypeII.e (LS.phase u k)‖ ^ 2) := by
        simpa [hLHS, hI, hK]
    _ ≤ LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := hBound'

/-!
## Step 4 (`v`-fibers): `innerSumVZ`
-/

/-- Step 4 analogue of `step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff`. -/
theorem step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff
    (ξ : ℝ) (F : TubePoint → ℂ)
    (a : Fin (zBoxVN td) → ℂ)
    (LS : SSU.Engines.LargeSieve.FiniteLargeSieve ℤ (Fin (zBoxVN td)))
    (hI : LS.I = vSet td)
    (hK : LS.K = (Finset.univ : Finset (Fin (zBoxVN td))))
    (hCoeff : ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = a)
    (hPhase :
      ∀ (v : ℤ) (k : Fin (zBoxVN td)),
        LS.phase v k = (ξ * ((k : ℕ) : ℝ) * (v : ℝ)) / td.X) :
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
      ≤
    LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) :=
by
  classical
  have hrewrite (v : ℤ) (hv : v ∈ vSet td) :
      ‖innerSumVZ td ξ F v‖
        =
      ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          a k * SSU.Engines.TypeII.e (LS.phase v k)‖ := by
    have h0 :=
      norm_innerSumVZ_eq_norm_sum_univ_coeffVZFin (td := td) (ξ := ξ) (F := F) (v := v)
    have ha : coeffVZFin td F v = a := hCoeff v hv
    have h0' :
        ‖innerSumVZ td ξ F v‖
          =
        ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            a k * SSU.Engines.TypeII.e (ξ * ((k : ℕ) : ℝ) * (v : ℝ) / td.X)‖ := by
      simpa [ha] using h0
    refine h0'.trans ?_
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [hPhase v k]

  have hLHS :
      (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
        =
      (∑ v ∈ LS.I, ‖∑ k ∈ LS.K, a k * SSU.Engines.TypeII.e (LS.phase v k)‖ ^ 2) := by
    rw [hI, hK]
    refine Finset.sum_congr rfl ?_
    intro v hv
    have := hrewrite v hv
    simpa [this] using congrArg (fun t => t ^ 2) this

  have hBound := LS.bound a
  have hBound' :
      (∑ v ∈ vSet td, ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            a k * SSU.Engines.TypeII.e (LS.phase v k)‖ ^ 2)
        ≤
      LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
    simpa [hI, hK] using hBound
  calc
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
        =
      (∑ v ∈ vSet td, ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            a k * SSU.Engines.TypeII.e (LS.phase v k)‖ ^ 2) := by
        simpa [hLHS, hI, hK]
    _ ≤ LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := hBound'

/-!
## Specializations: discharge `hPhase` using `uSet_finiteLargeSieve_phase` / `vSet_finiteLargeSieve_phase`

These lemmas are the “wiring” micro-step: once a later extraction layer proves the *coefficient
constancy* hypothesis, the MV engine can be applied without any manual phase unfolding.

We apply the MV engine to `ξ ↦ -ξ` so that its built-in `-t*i*n` phase matches TeX’s `+ξ*i*n/X`.
-/

/-- Step 3: apply the MV `FiniteLargeSieve` on `uSet td` (with `ξ ↦ -ξ`) under the
coefficient-constancy hypothesis. -/
theorem step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_finiteLargeSieve
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxN td) → ℂ)
    (hCoeff : ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = a) :
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
      ≤
    (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH) (hξH := by simpa using hξH)
        (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) :=
by
  classical
  let LS :=
    uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
      (hξH := by simpa using hξH) (hXH := hXH)
  have hI : LS.I = uSet td := by
    simp [LS, uSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]
  have hK : LS.K = (Finset.univ : Finset (Fin (zBoxN td))) := by
    simp [LS, uSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]
  have hPhase :
      ∀ (u : ℤ) (k : Fin (zBoxN td)),
        LS.phase u k = (ξ * (u : ℝ) * ((k : ℕ) : ℝ)) / td.X := by
    intro u k
    have h0 :=
      uSet_finiteLargeSieve_phase (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH) (u := u) (k := k)
    -- `-((-ξ)/X) = ξ/X`.
    -- Put the result into the requested `ξ*u*k/X` shape.
    simpa [LS, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h0
  simpa [LS] using
    (step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff (td := td) (ξ := ξ) (F := F) (a := a)
      (LS := LS) (hI := hI) (hK := hK) (hCoeff := hCoeff) (hPhase := hPhase))

/-- Step 4: analogue of `step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_finiteLargeSieve`. -/
theorem step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff_vSet_finiteLargeSieve
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxVN td) → ℂ)
    (hCoeff : ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = a) :
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
      ≤
    (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH) (hξH := by simpa using hξH)
        (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) :=
by
  classical
  let LS :=
    vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
      (hξH := by simpa using hξH) (hXH := hXH)
  have hI : LS.I = vSet td := by
    simp [LS, vSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]
  have hK : LS.K = (Finset.univ : Finset (Fin (zBoxVN td))) := by
    simp [LS, vSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]
  have hPhase :
      ∀ (v : ℤ) (k : Fin (zBoxVN td)),
        LS.phase v k = (ξ * ((k : ℕ) : ℝ) * (v : ℝ)) / td.X := by
    intro v k
    have h0 :=
      vSet_finiteLargeSieve_phase (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH) (v := v) (k := k)
    simpa [LS, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h0
  simpa [LS] using
    (step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff (td := td) (ξ := ξ) (F := F) (a := a)
      (LS := LS) (hI := hI) (hK := hK) (hCoeff := hCoeff) (hPhase := hPhase))

/-!
## Residue-class variants: apply MV on the progression parameter `m`

These are more TeX-faithful for Step 3/4: after splitting (say) `u = u₀(r) + m*q`, we apply the
additive large sieve in the parameter `m` over the progression-index set `uIndexSet td r`.

At this plumbing stage we still assume a coefficient-constancy hypothesis along the progression.
We absorb the residue-dependent phase into the coefficient array (its norm is unchanged since
`‖e(·)‖ = 1`).
-/

/-- Step 3, residue-class form: apply MV on `uIndexSet td r` under coefficient constancy along
`uFromIndex r m`. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_finiteLargeSieve
    (td : TubeData) (hU0 : 0 ≤ td.U) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxN td) → ℂ)
    (hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) = a) :
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) :=
by
  classical
  let LS :=
    uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
      (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
      (hξH := by simpa using hξH) (hXH := hXH)
  -- Absorb the residue-dependent phase into the coefficient array.
  let aR : Fin (zBoxN td) → ℂ :=
    fun k => a k * SSU.Engines.TypeII.e (ξ * (uResidue td r : ℝ) * ((k : ℕ) : ℝ) / td.X)

  have hI : LS.I = ResiduePartition.uIndexSet (td := td) r := by
    simp [LS, uIndexSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]
  have hK : LS.K = (Finset.univ : Finset (Fin (zBoxN td))) := by
    simp [LS, uIndexSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]

  have hPhase :
      ∀ (m : ℤ) (k : Fin (zBoxN td)),
        LS.phase m k = (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ)) / td.X := by
    intro m k
    have h0 :=
      uIndexSet_finiteLargeSieve_phase (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH) (m := m) (k := k)
    -- `-(((-ξ)*q)/X) = (ξ*q)/X`, and rewrite into the `(m*q)*k` shape.
    simpa [LS, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h0

  -- Pointwise rewrite into the `FiniteLargeSieve` shape.
  have hrewrite (m : ℤ) (hm : m ∈ ResiduePartition.uIndexSet (td := td) r) :
      ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖
        =
      ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ := by
    have h0 :=
      ZBoxToFin.norm_innerSumUZ_uFromIndex_eq_norm_sum_univ_phaseSplit (td := td) (ξ := ξ) (F := F)
        (r := r) (m := m)
    have ha : coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) = a := hCoeff m hm
    -- Replace coefficients and then rewrite the `m`-phase via `hPhase`.
    have h0' :
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖
          =
        ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
            a k *
              SSU.Engines.TypeII.e (ξ * (uResidue td r : ℝ) * ((k : ℕ) : ℝ) / td.X) *
              SSU.Engines.TypeII.e (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ) / td.X)‖ := by
      simpa [ha] using h0
    refine h0'.trans ?_
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    -- Absorb the residue phase into `aR`, and rewrite the progression phase using `hPhase`.
    simp [aR, hPhase m k, mul_assoc, mul_left_comm, mul_comm]

  have hLHS :
      (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
        =
      (∑ m ∈ LS.I, ‖∑ k ∈ LS.K, aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ ^ 2) := by
    rw [hI, hK]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have := hrewrite m hm
    simpa [this] using congrArg (fun t => t ^ 2) this

  have hBound := LS.bound aR
  have hBound' :
      (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
              aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ ^ 2)
        ≤
      LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖aR k‖ ^ 2) := by
    simpa [hI, hK] using hBound

  have hNormCoeff :
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖aR k‖ ^ 2)
        =
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [aR, norm_mul, SSU.Engines.TypeII.norm_e]

  calc
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
        =
      (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
          ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
              aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ ^ 2) := by
          simpa [hLHS, hI, hK]
    _ ≤ LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖aR k‖ ^ 2) := hBound'
    _ = LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
          simpa [hNormCoeff]

/-- Step 3, residue-class form: deduce coefficient constancy on `uIndexSet td r` from equality of
all fiber coefficient sums against a fixed reference index. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_finiteLargeSieve
    (td : TubeData) (hU0 : 0 ≤ td.U) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (m0 : ℤ) (_hm0 : m0 ∈ ResiduePartition.uIndexSet (td := td) r)
    (hEq :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        ∀ k : Fin (zBoxN td),
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m)
              (zBoxA td + 1 + (k : ℕ)), F p)
            =
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0)
              (zBoxA td + 1 + (k : ℕ)), F p)) :
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  have hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m)
          =
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0) := by
    intro m hm
    funext k
    simpa [coeffUZFin] using (hEq m hm k)
  simpa using
    (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_finiteLargeSieve
      (td := td) (hU0 := hU0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F)
      (a := coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0))
      (hCoeff := hCoeff))

/-- Step 3, residue-class form: same as
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_finiteLargeSieve`,
but with the weaker (and geometry-friendly) hypothesis package:
`zSet`-domain equality along the progression plus fiber-sum equality only on that common domain. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet_finiteLargeSieve
    (td : TubeData) (hU0 : 0 ≤ td.U) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (m0 : ℤ) (hm0 : m0 ∈ ResiduePartition.uIndexSet (td := td) r)
    (hZeq :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        zSet td (ResiduePartition.uFromIndex (td := td) r m)
          = zSet td (ResiduePartition.uFromIndex (td := td) r m0))
    (hEqOn :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        ∀ z : ℤ, z ∈ zSet td (ResiduePartition.uFromIndex (td := td) r m0) →
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m) z, F p)
            =
          (∑ p ∈ fiberUZ td (ResiduePartition.uFromIndex (td := td) r m0) z, F p)) :
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))),
          ‖coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  have hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m)
          =
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0) :=
    ConstCoeffFromFiber.constCoeffUZFin_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet
      (td := td) (F := F) (r := r) (m0 := m0) (_hm0 := hm0) (hZeq := hZeq) (hEqOn := hEqOn)
  simpa using
    (step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_finiteLargeSieve
      (td := td) (hU0 := hU0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F)
      (a := coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m0))
      (hCoeff := hCoeff))

/-- Step 4, residue-class form: analogue of
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_finiteLargeSieve`. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_finiteLargeSieve
    (td : TubeData) (hD0 : 0 ≤ td.D) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxVN td) → ℂ)
    (hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) = a) :
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) :=
by
  classical
  let LS :=
    vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
      (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
      (hξH := by simpa using hξH) (hXH := hXH)
  let aR : Fin (zBoxVN td) → ℂ :=
    fun k => a k * SSU.Engines.TypeII.e (ξ * ((k : ℕ) : ℝ) * (vResidue td r : ℝ) / td.X)

  have hI : LS.I = ResiduePartitionV.vIndexSet (td := td) r := by
    simp [LS, vIndexSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]
  have hK : LS.K = (Finset.univ : Finset (Fin (zBoxVN td))) := by
    simp [LS, vIndexSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound]

  have hPhase :
      ∀ (m : ℤ) (k : Fin (zBoxVN td)),
        LS.phase m k = (ξ * ((m : ℝ) * (td.q : ℝ)) * ((k : ℕ) : ℝ)) / td.X := by
    intro m k
    have h0 :=
      vIndexSet_finiteLargeSieve_phase (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH) (m := m) (k := k)
    simpa [LS, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h0

  have hrewrite (m : ℤ) (hm : m ∈ ResiduePartitionV.vIndexSet (td := td) r) :
      ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖
        =
      ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ := by
    have h0 :=
      ZBoxToFin.norm_innerSumVZ_vFromIndex_eq_norm_sum_univ_phaseSplit (td := td) (ξ := ξ) (F := F)
        (r := r) (m := m)
    have ha : coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) = a := hCoeff m hm
    have h0' :
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖
          =
        ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
            a k *
              SSU.Engines.TypeII.e (ξ * ((k : ℕ) : ℝ) * (vResidue td r : ℝ) / td.X) *
              SSU.Engines.TypeII.e (ξ * ((k : ℕ) : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X)‖ := by
      simpa [ha] using h0
    refine h0'.trans ?_
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k hk
    have : SSU.Engines.TypeII.e (ξ * ((k : ℕ) : ℝ) * ((m : ℝ) * (td.q : ℝ)) / td.X)
        = SSU.Engines.TypeII.e (LS.phase m k) := by
      congr 1
      simpa [hPhase m k, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    -- Avoid `simp`-cancellation on a common `a k` factor; rewrite the phase and reassociate.
    dsimp [aR]
    rw [this]

  have hLHS :
      (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
        =
      (∑ m ∈ LS.I, ‖∑ k ∈ LS.K, aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ ^ 2) := by
    rw [hI, hK]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have := hrewrite m hm
    simpa [this] using congrArg (fun t => t ^ 2) this

  have hBound := LS.bound aR
  have hBound' :
      (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
              aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ ^ 2)
        ≤
      LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖aR k‖ ^ 2) := by
    simpa [hI, hK] using hBound

  have hNormCoeff :
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖aR k‖ ^ 2)
        =
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [aR, norm_mul, SSU.Engines.TypeII.norm_e]

  calc
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
        =
      (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
          ‖∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
              aR k * SSU.Engines.TypeII.e (LS.phase m k)‖ ^ 2) := by
          simpa [hLHS, hI, hK]
    _ ≤ LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖aR k‖ ^ 2) := hBound'
    _ = LS.C * (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
          simpa [hNormCoeff]

/-- Step 4, residue-class form: deduce coefficient constancy on `vIndexSet td r` from equality of
all fiber coefficient sums against a fixed reference index. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_sum_fiberVZ_vFromIndex_eq_ref_finiteLargeSieve
    (td : TubeData) (hD0 : 0 ≤ td.D) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (m0 : ℤ) (_hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := td) r)
    (hEq :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        ∀ k : Fin (zBoxVN td),
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m)
              (zBoxVA td + (k : ℕ)), F p)
            =
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0)
              (zBoxVA td + (k : ℕ)), F p)) :
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  have hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m)
          =
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0) := by
    intro m hm
    funext k
    simpa [coeffVZFin] using (hEq m hm k)
  simpa using
    (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_finiteLargeSieve
      (td := td) (hD0 := hD0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F)
      (a := coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0))
      (hCoeff := hCoeff))

/-- Step 4 analogue of
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet_finiteLargeSieve`.
-/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_finiteLargeSieve
    (td : TubeData) (hD0 : 0 ≤ td.D) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ)
    (m0 : ℤ) (hm0 : m0 ∈ ResiduePartitionV.vIndexSet (td := td) r)
    (hZeq :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        zSetV td (ResiduePartitionV.vFromIndex (td := td) r m)
          = zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0))
    (hEqOn :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        ∀ z : ℤ, z ∈ zSetV td (ResiduePartitionV.vFromIndex (td := td) r m0) →
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m) z, F p)
            =
          (∑ p ∈ fiberVZ td (ResiduePartitionV.vFromIndex (td := td) r m0) z, F p)) :
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
        (hξ0 := by simpa using (neg_ne_zero.2 hξ0)) (hX := hX) (hH := hH)
        (hξH := by simpa using hξH) (hXH := hXH)).C *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))),
          ‖coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0) k‖ ^ 2) := by
  classical
  have hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m)
          =
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0) :=
    ConstCoeffFromFiber.constCoeffVZFin_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV
      (td := td) (F := F) (r := r) (m0 := m0) (_hm0 := hm0) (hZeq := hZeq) (hEqOn := hEqOn)
  simpa using
    (step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_finiteLargeSieve
      (td := td) (hD0 := hD0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F)
      (a := coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m0))
      (hCoeff := hCoeff))

/-!
### TeX-friendly corollaries: replace `LS.C` by an explicit `(1+log)` bound (per residue class)

These are the progression-index analogues of
`step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_one_add_log` /
`step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff_vSet_one_add_log`.
-/

/-- Step 3, residue-class form, with the MV constant replaced by an explicit polylog expression. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_one_add_log
    (td : TubeData) (hU0 : 0 ≤ td.U) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxN td) → ℂ)
    (hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) = a) :
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    ((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) :=
by
  classical
  have hmain :=
    step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_finiteLargeSieve
      (td := td) (hU0 := hU0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F) (a := a) (hCoeff := hCoeff)
  have hC :=
    (ResidueIndexLargeSieve.uIndexSet_finiteLargeSieve_C_le_one_add_log
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
    -- Replace `|-ξ|` by `|ξ|`.
    simpa [abs_neg] using hC
  have hmul :
      (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := zBoxN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2)
        ≤
      ((zBoxN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_right hC' ?_
    positivity
  exact hmain.trans hmul

/-- Interval-geometry wrapper for
`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_one_add_log`.

It derives `|ξ| ≤ 1/H` from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_one_add_log_outerGeom
    (td : TubeData) (hU0 : 0 ≤ td.U) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxN td) → ℂ)
    (hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartition.uIndexSet (td := td) r →
        coeffUZFin td F (ResiduePartition.uFromIndex (td := td) r m) = a) :
    (∑ m ∈ ResiduePartition.uIndexSet (td := td) r,
        ‖innerSumUZ td ξ F (ResiduePartition.uFromIndex (td := td) r m)‖ ^ 2)
      ≤
    ((zBoxN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q)))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
  have hξH : |ξ| ≤ 1 / td.H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  exact
    step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_one_add_log
      (td := td) (hU0 := hU0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F) (a := a) (hCoeff := hCoeff)

/-- Step 4, residue-class form, with the MV constant replaced by an explicit polylog expression. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_one_add_log
    (td : TubeData) (hD0 : 0 ≤ td.D) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxVN td) → ℂ)
    (hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) = a) :
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    ((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) :=
by
  classical
  have hmain :=
    step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_finiteLargeSieve
      (td := td) (hD0 := hD0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F) (a := a) (hCoeff := hCoeff)
  have hC :=
    (ResidueIndexLargeSieve.vIndexSet_finiteLargeSieve_C_le_one_add_log
      (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
      (hξH := by simpa using hξH) (hXH := hXH))
  have hC' :
      (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C
        ≤
      (zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))) := by
    simpa [abs_neg] using hC
  have hmul :
      (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2)
        ≤
      ((zBoxVN td : ℝ) +
          (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_right hC' ?_
    positivity
  exact hmain.trans hmul

/-- Interval-geometry wrapper for
`step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_one_add_log`.

It derives `|ξ| ≤ 1/H` from `ξ ∈ [-(1/H), 1/H]`. -/
theorem step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_one_add_log_outerGeom
    (td : TubeData) (hD0 : 0 ≤ td.D) (r : ℤ)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxVN td) → ℂ)
    (hCoeff :
      ∀ m : ℤ, m ∈ ResiduePartitionV.vIndexSet (td := td) r →
        coeffVZFin td F (ResiduePartitionV.vFromIndex (td := td) r m) = a) :
    (∑ m ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ‖innerSumVZ td ξ F (ResiduePartitionV.vFromIndex (td := td) r m)‖ ^ 2)
      ≤
    ((zBoxVN td : ℝ) +
        (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q)))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
  have hξH : |ξ| ≤ 1 / td.H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  exact
    step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_one_add_log
      (td := td) (hD0 := hD0) (r := r) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH)
      (hξH := hξH) (hXH := hXH) (F := F) (a := a) (hCoeff := hCoeff)

/-!
## TeX-friendly corollaries: explicit `(1+log)` bounds for the MV constant

These corollaries keep the same hypotheses as the MV specializations above, but replace the raw
`LS.C` constant by an explicit polylog expression. This is closer to the TeX bookkeeping, and
avoids having to unfold MV’s Crow sum constants in downstream SSU bounds.

They are still conditional on the (later) coefficient-constancy hypothesis.
-/

/-- Step 3, with `LS.C` replaced by the explicit polylog bound
`(zBoxN td) + (X/|ξ|)*(1+log R)` (for `R = 2*toNat(ceil U)`). -/
theorem step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_one_add_log
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxN td) → ℂ)
    (hCoeff : ∀ u : ℤ, u ∈ uSet td → coeffUZFin td F u = a) :
    (∑ u ∈ uSet td, ‖innerSumUZ td ξ F u‖ ^ 2)
      ≤
    ((zBoxN td : ℝ) +
        (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U)))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) :=
by
  classical
  -- Start from the MV specialization (with `ξ ↦ -ξ`).
  have hmain :=
    step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_finiteLargeSieve
      (td := td) (hU0 := hU0) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH)
      (hXH := hXH) (F := F) (a := a) (hCoeff := hCoeff)
  -- Bound the MV constant `LS.C` by a `(1+log)` expression.
  have hC :=
    (IndexLargeSieve.uSet_finiteLargeSieve_C_le_one_add_log
      (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0)
      (hX := hX) (hH := hH) (hξH := by simpa using hξH) (hXH := hXH))
  -- Replace `| -ξ |` by `|ξ|` in the bound.
  have hC' :
      (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C
        ≤
      (zBoxN td : ℝ) + (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) := by
    simpa [abs_neg] using hC
  -- Multiply by the nonnegative coefficient-energy term.
  have hmul :
      (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := zBoxN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2)
        ≤
      ((zBoxN td : ℝ) + (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U)))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxN td))), ‖a k‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_right hC' ?_
    positivity
  exact hmain.trans hmul

/-- Step 4, with `LS.C` replaced by the explicit polylog bound
`(zBoxVN td) + (X/|ξ|)*(1+log R)` (for `R = 2*toNat(ceil (2D))`). -/
theorem step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff_vSet_one_add_log
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H) (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (F : TubePoint → ℂ) (a : Fin (zBoxVN td) → ℂ)
    (hCoeff : ∀ v : ℤ, v ∈ vSet td → coeffVZFin td F v = a) :
    (∑ v ∈ vSet td, ‖innerSumVZ td ξ F v‖ ^ 2)
      ≤
    ((zBoxVN td : ℝ) +
        (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D))))) *
      (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) :=
by
  classical
  have hmain :=
    step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff_vSet_finiteLargeSieve
      (td := td) (hD0 := hD0) (ξ := ξ) (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH)
      (hXH := hXH) (F := F) (a := a) (hCoeff := hCoeff)
  have hC :=
    (IndexLargeSieve.vSet_finiteLargeSieve_C_le_one_add_log
      (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
      (hξ0 := by simpa using neg_ne_zero.2 hξ0)
      (hX := hX) (hH := hH) (hξH := by simpa using hξH) (hXH := hXH))
  have hC' :
      (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C
        ≤
      (zBoxVN td : ℝ) + (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) := by
    simpa [abs_neg] using hC
  have hmul :
      (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := zBoxVN td) (ξ := -ξ)
          (hξ0 := by simpa using neg_ne_zero.2 hξ0) (hX := hX) (hH := hH)
          (hξH := by simpa using hξH) (hXH := hXH)).C *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2)
        ≤
      ((zBoxVN td : ℝ) + (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D))))) *
          (∑ k ∈ (Finset.univ : Finset (Fin (zBoxVN td))), ‖a k‖ ^ 2) := by
    refine mul_le_mul_of_nonneg_right hC' ?_
    positivity
  exact hmain.trans hmul

end FiberFromFiniteLargeSieve

end
end LargeSieve
end TypeII
end Engines
end SSU
