import SSU.Engines.LargeSieve.MVFiniteLargeSieveZInterface
import SSU.Engines.LargeSieve.TypeIIIndexBounds

/-!
MV large sieve, packaged on the concrete Type–II index sets `uSet td` and `vSet td`.

This file is **plumbing**: it produces `FiniteLargeSieve` instances once we have:
* a uniform distance bound on the index set (proved in `TypeIIIndexBounds`), and
* a “small phase” condition `|t| * R ≤ 1/2`, derived from the ξ-band and a size hypothesis.

It does not attempt to prove TeX Step 3/4 bounds (which require additional reductions).
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace IndexLargeSieve

open SSU.Engines.LargeSieve

/-!
## Phase normalization lemmas

The MV interface `FiniteLargeSieve` is packaged with phase

`phase i n := -t * i * n`.

In TeX Step 3/4 the inner sums use `e( (ξ/X) * i * n )`. To match signs, we typically apply the
MV engine with `t := -ξ/X`. The following lemmas record the phase explicitly so downstream code
does not need to unfold the `FiniteLargeSieve` object.
-/

/-- Finite large sieve instance on `uSet td` for phases `i,n ↦ -(ξ/td.X) * i * n`.

Assumptions are deliberately minimal and “regime-style”:
* `0 < td.X`, `0 < td.H`;
* ξ-band: `|ξ| ≤ 1/td.H`;
* size: `2R ≤ td.X * td.H`, where `R = 2 * toNat (ceil td.U)`.

The output is a ready-to-use `FiniteLargeSieve ℤ (Fin N)` object (MV engine). -/
def uSet_finiteLargeSieve
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H) :
    FiniteLargeSieve ℤ (Fin N) :=
by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil td.U)
  have hDist : ∀ i ∈ uSet td, ∀ j ∈ uSet td, SSU.Hilbert.distZ i j ≤ R :=
    IndexBounds.distZ_le_two_mul_toNat_ceilU_on_uSet (td := td) (hU0 := hU0)
  let t : ℝ := ξ / td.X
  have ht0 : t ≠ 0 := by
    intro ht0
    have hX0 : td.X ≠ 0 := ne_of_gt hX
    have : ξ = 0 := by
      -- `ξ / X = 0` and `X ≠ 0`.
      have : ξ = 0 ∨ td.X = 0 := (div_eq_zero_iff).1 ht0
      exact this.resolve_right hX0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    have hXpos : 0 < |td.X| := abs_pos.2 (ne_of_gt hX)
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    -- `|t| = |ξ| / X` since `X > 0`.
    have habs : |t| = |ξ| / td.X := by
      simp [t, abs_div, abs_of_pos hX]
    -- Bound `|ξ|/X ≤ (1/H)/X`.
    have hx : |ξ| / td.X ≤ (1 / td.H) / td.X :=
      div_le_div_of_nonneg_right hξH (le_of_lt hX)
    -- Multiply by `R`.
    have h1 : |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := by
      have := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ (R : ℝ))
      simpa [habs, mul_assoc] using this
    -- Rewrite RHS as `R / (XH)`.
    have h2 : ((1 / td.H) / td.X) * (R : ℝ) = (R : ℝ) / (td.X * td.H) := by
      -- `((1/H)/X) * R = R / (X*H)`.
      -- (Uses `mul_inv_rev : (a*b)⁻¹ = b⁻¹*a⁻¹`.)
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev]
    -- From `2R ≤ XH`, conclude `R/(XH) ≤ 1/2`.
    have h3 : (R : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hR : (R : ℝ) ≤ (td.X * td.H) / 2 := by
        -- Divide `2R ≤ XH` by `2`.
        nlinarith
          [show (2 * (R : ℝ)) ≤ td.X * td.H from
              (by simpa [R, Nat.cast_mul, Nat.cast_ofNat] using hXH)]
      have hdiv : (R : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hR (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        -- `((XH)/2)/(XH) = (XH)/(2*XH) = 1/2`.
        have eq1 :
            ((td.X * td.H) / 2) / (td.X * td.H) = (td.X * td.H) / (2 * (td.X * td.H)) := by
          simp [div_div]
        -- Clear denominators.
        -- `field_simp` uses the nonzero hypothesis on `XH`.
        -- After clearing, `ring` closes the goal.
        -- (We keep this explicit rather than relying on simp-normal forms.)
        -- `field_simp` works over `ℝ`.
        have eq2 : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        exact eq1.trans eq2
      exact le_trans hdiv (le_of_eq hfrac)
    have h1' : |t| * (R : ℝ) ≤ (R : ℝ) / (td.X * td.H) := by
      calc
        |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := h1
        _ = (R : ℝ) / (td.X * td.H) := h2
    exact h1'.trans h3
  exact
    MV.finiteLargeSieve_of_distBound (J := uSet td) (N := N) (t := t) (R := R)
      (hDist := hDist) (ht := ht) (ht0 := ht0)

/-- Unfold the phase of `uSet_finiteLargeSieve`. -/
theorem uSet_finiteLargeSieve_phase
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H)
    (u : ℤ) (k : Fin N) :
    (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).phase u k
      =
    - (ξ / td.X) * (u : ℝ) * ((k : ℕ) : ℝ) := by
  -- `uSet_finiteLargeSieve` is defined by `MV.finiteLargeSieve_of_distBound` with this phase.
  simp [uSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound, mul_assoc]

/-- Finite large sieve instance on `vSet td` for phases `i,n ↦ -(ξ/td.X) * i * n`.

Here `R = 2 * toNat (ceil (2*td.D))` is the `distZ` diameter bound on `vSet td`. -/
def vSet_finiteLargeSieve
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H) :
    FiniteLargeSieve ℤ (Fin N) :=
by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil (2 * td.D))
  have hDist : ∀ i ∈ vSet td, ∀ j ∈ vSet td, SSU.Hilbert.distZ i j ≤ R :=
    IndexBounds.distZ_le_two_mul_toNat_ceilTwoD_on_vSet (td := td) (hD0 := hD0)
  let t : ℝ := ξ / td.X
  have ht0 : t ≠ 0 := by
    intro ht0
    have hX0 : td.X ≠ 0 := ne_of_gt hX
    have : ξ = 0 := by
      have : ξ = 0 ∨ td.X = 0 := (div_eq_zero_iff).1 ht0
      exact this.resolve_right hX0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    have habs : |t| = |ξ| / td.X := by
      simp [t, abs_div, abs_of_pos hX]
    have hx : |ξ| / td.X ≤ (1 / td.H) / td.X :=
      div_le_div_of_nonneg_right hξH (le_of_lt hX)
    have h1 : |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := by
      have := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ (R : ℝ))
      simpa [habs, mul_assoc] using this
    have h2 : ((1 / td.H) / td.X) * (R : ℝ) = (R : ℝ) / (td.X * td.H) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev]
    have h3 : (R : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hR : (R : ℝ) ≤ (td.X * td.H) / 2 := by
        nlinarith
          [show (2 * (R : ℝ)) ≤ td.X * td.H from
              (by simpa [R, Nat.cast_mul, Nat.cast_ofNat] using hXH)]
      have hdiv : (R : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hR (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        have : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        -- `simp [div_div]` turns `((XH)/2)/(XH)` into `XH/(2*XH)`.
        simpa [div_div] using this
      exact le_trans hdiv (le_of_eq hfrac)
    have h1' : |t| * (R : ℝ) ≤ (R : ℝ) / (td.X * td.H) := by
      calc
        |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := h1
        _ = (R : ℝ) / (td.X * td.H) := h2
    exact h1'.trans h3
  exact
    MV.finiteLargeSieve_of_distBound (J := vSet td) (N := N) (t := t) (R := R)
      (hDist := hDist) (ht := ht) (ht0 := ht0)

/-- Unfold the phase of `vSet_finiteLargeSieve`. -/
theorem vSet_finiteLargeSieve_phase
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H)
    (v : ℤ) (k : Fin N) :
    (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).phase v k
      =
    - (ξ / td.X) * (v : ℝ) * ((k : ℕ) : ℝ) := by
  simp [vSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound, mul_assoc]

/-- Optional polylog bound on the MV constant `C` for `uSet_finiteLargeSieve`.

This is a TeX-facing convenience lemma: it rewrites the generic MV bound
`C ≤ N + (1/|t|) * (1+log R)` into the `ξ/X` normalization used by SSU:
`1/|t| = X/|ξ|` for `t = ξ/X` (with `X > 0`). -/
theorem uSet_finiteLargeSieve_C_le_one_add_log
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U) : ℕ) : ℝ)) ≤ td.X * td.H) :
    (uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).C
      ≤
    (N : ℝ) +
      (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U))) := by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil td.U)
  let t : ℝ := ξ / td.X
  have hDist : ∀ i ∈ uSet td, ∀ j ∈ uSet td, SSU.Hilbert.distZ i j ≤ R :=
    IndexBounds.distZ_le_two_mul_toNat_ceilU_on_uSet (td := td) (hU0 := hU0)
  have ht0 : t ≠ 0 := by
    intro ht0
    have hX0 : td.X ≠ 0 := ne_of_gt hX
    have : ξ = 0 := by
      have : ξ = 0 ∨ td.X = 0 := (div_eq_zero_iff).1 ht0
      exact this.resolve_right hX0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    -- This is the same “small phase” inequality proved inside `uSet_finiteLargeSieve`.
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    have habs : |t| = |ξ| / td.X := by
      simp [t, abs_div, abs_of_pos hX]
    have hx : |ξ| / td.X ≤ (1 / td.H) / td.X :=
      div_le_div_of_nonneg_right hξH (le_of_lt hX)
    have h1 : |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := by
      have := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ (R : ℝ))
      simpa [habs, mul_assoc] using this
    have h2 : ((1 / td.H) / td.X) * (R : ℝ) = (R : ℝ) / (td.X * td.H) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev]
    have h3 : (R : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hR : (R : ℝ) ≤ (td.X * td.H) / 2 := by
        nlinarith
          [show (2 * (R : ℝ)) ≤ td.X * td.H from
              (by simpa [R, Nat.cast_mul, Nat.cast_ofNat] using hXH)]
      have hdiv : (R : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hR (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        have : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        simpa [div_div] using this
      exact le_trans hdiv (le_of_eq hfrac)
    have h1' : |t| * (R : ℝ) ≤ (R : ℝ) / (td.X * td.H) := by
      calc
        |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := h1
        _ = (R : ℝ) / (td.X * td.H) := h2
    exact h1'.trans h3

  have hC :=
    MV.finiteLargeSieve_of_distBound_C_le_one_add_log (J := uSet td) (N := N) (t := t) (R := R)
      (hDist := hDist) (ht := ht) (ht0 := ht0)
  -- `uSet_finiteLargeSieve` is exactly this MV instance.
  have hEq :
      uSet_finiteLargeSieve (td := td) (hU0 := hU0) (N := N) (ξ := ξ)
          (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        =
      MV.finiteLargeSieve_of_distBound (J := uSet td) (N := N) (t := t) (R := R)
        (hDist := hDist) (ht := ht) (ht0 := ht0) := by
    -- unfold both constructions
    simp [uSet_finiteLargeSieve, R, t, MV.finiteLargeSieve_of_distBound]
  -- Rewrite `1/|t|` as `X/|ξ|` (TeX normalization).
  have hinv : (1 / |t| : ℝ) = td.X / |ξ| := by
    have hX0 : (td.X : ℝ) ≠ 0 := ne_of_gt hX
    have hξabs0 : (|ξ| : ℝ) ≠ 0 := by
      simpa [abs_eq_zero] using hξ0
    have habs : |t| = |ξ| / td.X := by
      simp [t, abs_div, abs_of_pos hX]
    calc
      (1 / |t| : ℝ) = 1 / (|ξ| / td.X) := by simp [habs]
      _ = (td.X : ℝ) / |ξ| := by
        field_simp [hX0, hξabs0]
  -- Finish.
  -- (Use `hEq` to replace the `uSet_finiteLargeSieve` constant by the MV one, then normalize `t`.)
  simpa [hEq, hinv, R, t, mul_assoc, mul_left_comm, mul_comm] using hC

/-- Optional polylog bound on the MV constant `C` for `vSet_finiteLargeSieve`. -/
theorem vSet_finiteLargeSieve_C_le_one_add_log
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D)) : ℕ) : ℝ)) ≤ td.X * td.H) :
    (vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).C
      ≤
    (N : ℝ) +
      (td.X / |ξ|) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D)))) := by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil (2 * td.D))
  let t : ℝ := ξ / td.X
  have hDist : ∀ i ∈ vSet td, ∀ j ∈ vSet td, SSU.Hilbert.distZ i j ≤ R :=
    IndexBounds.distZ_le_two_mul_toNat_ceilTwoD_on_vSet (td := td) (hD0 := hD0)
  have ht0 : t ≠ 0 := by
    intro ht0
    have hX0 : td.X ≠ 0 := ne_of_gt hX
    have : ξ = 0 := by
      have : ξ = 0 ∨ td.X = 0 := (div_eq_zero_iff).1 ht0
      exact this.resolve_right hX0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    -- Same “small phase” inequality as in `vSet_finiteLargeSieve`.
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    have habs : |t| = |ξ| / td.X := by
      simp [t, abs_div, abs_of_pos hX]
    have hx : |ξ| / td.X ≤ (1 / td.H) / td.X :=
      div_le_div_of_nonneg_right hξH (le_of_lt hX)
    have h1 : |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := by
      have := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ (R : ℝ))
      simpa [habs, mul_assoc] using this
    have h2 : ((1 / td.H) / td.X) * (R : ℝ) = (R : ℝ) / (td.X * td.H) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev]
    have h3 : (R : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hR : (R : ℝ) ≤ (td.X * td.H) / 2 := by
        nlinarith
          [show (2 * (R : ℝ)) ≤ td.X * td.H from
              (by simpa [R, Nat.cast_mul, Nat.cast_ofNat] using hXH)]
      have hdiv : (R : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hR (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        have : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        simpa [div_div] using this
      exact le_trans hdiv (le_of_eq hfrac)
    have h1' : |t| * (R : ℝ) ≤ (R : ℝ) / (td.X * td.H) := by
      calc
        |t| * (R : ℝ) ≤ ((1 / td.H) / td.X) * (R : ℝ) := h1
        _ = (R : ℝ) / (td.X * td.H) := h2
    exact h1'.trans h3

  have hC :=
    MV.finiteLargeSieve_of_distBound_C_le_one_add_log (J := vSet td) (N := N) (t := t) (R := R)
      (hDist := hDist) (ht := ht) (ht0 := ht0)
  have hEq :
      vSet_finiteLargeSieve (td := td) (hD0 := hD0) (N := N) (ξ := ξ)
          (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        =
      MV.finiteLargeSieve_of_distBound (J := vSet td) (N := N) (t := t) (R := R)
        (hDist := hDist) (ht := ht) (ht0 := ht0) := by
    simp [vSet_finiteLargeSieve, R, t, MV.finiteLargeSieve_of_distBound]
  have hinv : (1 / |t| : ℝ) = td.X / |ξ| := by
    have hX0 : (td.X : ℝ) ≠ 0 := ne_of_gt hX
    have hξabs0 : (|ξ| : ℝ) ≠ 0 := by
      simpa [abs_eq_zero] using hξ0
    have habs : |t| = |ξ| / td.X := by
      simp [t, abs_div, abs_of_pos hX]
    calc
      (1 / |t| : ℝ) = 1 / (|ξ| / td.X) := by simp [habs]
      _ = (td.X : ℝ) / |ξ| := by
        field_simp [hX0, hξabs0]
  simpa [hEq, hinv, R, t, mul_assoc, mul_left_comm, mul_comm] using hC

end IndexLargeSieve

end

end LargeSieve
end TypeII
end Engines
end SSU
