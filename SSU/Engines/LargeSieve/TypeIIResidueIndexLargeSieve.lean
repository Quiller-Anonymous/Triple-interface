import SSU.Engines.LargeSieve.MVFiniteLargeSieveZInterface
import SSU.Engines.LargeSieve.TypeIIResiduePartition

/-!
MV large sieve, packaged on the *progression index* sets `uIndexSet td r` and `vIndexSet td r`.

This is TeX Step 3/4 bookkeeping: after splitting `u = u₀(r) + m*q` (or `v = v₀(r) + m*q`) we
want to apply a 1D additive large sieve in the parameter `m`.

This file is plumbing: it only builds `FiniteLargeSieve` objects from deterministic diameter bounds
on the progression-index sets plus a “small phase” assumption from the ξ-band.
-/

namespace SSU
namespace Engines
namespace TypeII
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace ResidueIndexLargeSieve

open SSU.Engines.LargeSieve

/-- MV finite large sieve instance on `uIndexSet td r` for phases `m,n ↦ -(ξ*q/td.X) * m * n`.

This is the progression-index analogue of `IndexLargeSieve.uSet_finiteLargeSieve`. -/
def uIndexSet_finiteLargeSieve
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H) :
    FiniteLargeSieve ℤ (Fin N) :=
by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil td.U + td.q)
  have hDist :
      ∀ i ∈ ResiduePartition.uIndexSet (td := td) r,
        ∀ j ∈ ResiduePartition.uIndexSet (td := td) r,
          SSU.Hilbert.distZ i j ≤ R := by
    intro i hi j hj
    simpa [R, Nat.mul_assoc] using
      (ResiduePartition.distZ_le_two_mul_toNat_ceilU_add_q_on_uIndexSet
        (td := td) (hU0 := hU0) (r := r) i hi j hj)
  let t : ℝ := (ξ * (td.q : ℝ)) / td.X
  have ht0 : t ≠ 0 := by
    have hq0 : (td.q : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt td.q_pos)
    intro ht0
    have : ξ * (td.q : ℝ) = 0 := by
      have hX0 : td.X ≠ 0 := ne_of_gt hX
      exact (div_eq_zero_iff).1 ht0 |>.resolve_right hX0
    have : ξ = 0 := by
      have := mul_eq_zero.mp this
      exact this.resolve_right hq0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have habs : |t| = |ξ| * (td.q : ℝ) / td.X := by
      -- `q > 0` so `|q| = q`.
      simp [t, abs_div, abs_mul, abs_of_pos hq, abs_of_pos hX, mul_assoc]
    have hstep :
        |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := by
      have hx : |ξ| * (td.q : ℝ) / td.X ≤ (1 / td.H) * (td.q : ℝ) / td.X := by
        have := mul_le_mul_of_nonneg_right hξH (by positivity : 0 ≤ (td.q : ℝ))
        exact div_le_div_of_nonneg_right this (le_of_lt hX)
      have := mul_le_mul_of_nonneg_right (le_trans (le_of_eq habs) hx) (by positivity : 0 ≤ (R : ℝ))
      simpa [mul_assoc] using this
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    have hRq : (R : ℝ) * (td.q : ℝ) ≤ (td.X * td.H) / 2 := by
      have : (2 * ((R : ℝ) * (td.q : ℝ))) ≤ td.X * td.H := by
        -- `hXH` is stated with `2*(2*toNat)*q`; rewrite to `2*(R*q)`.
        simpa [R, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hXH
      nlinarith
    have hRq_div : (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hdiv :
          (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hRq (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        have : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        simpa [div_div] using this
      exact le_trans hdiv (le_of_eq hfrac)
    have hrewrite :
        ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := by
      -- `((1/H)*q/X)*R = (R*q)/(X*H)`.
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := hstep
      _ = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := hrewrite
      _ ≤ (1 / 2 : ℝ) := hRq_div
  exact
    MV.finiteLargeSieve_of_distBound (J := ResiduePartition.uIndexSet (td := td) r) (N := N)
      (t := t) (R := R) (hDist := hDist) (ht := ht) (ht0 := ht0)

/-- Unfold the phase of `uIndexSet_finiteLargeSieve`. -/
theorem uIndexSet_finiteLargeSieve_phase
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (m : ℤ) (k : Fin N) :
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).phase m k
      =
    - ((ξ * (td.q : ℝ)) / td.X) * (m : ℝ) * ((k : ℕ) : ℝ) := by
  simp [uIndexSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound, mul_assoc]

/-- Optional polylog bound on the MV constant `C` for `uIndexSet_finiteLargeSieve`.

This mirrors `TypeIIIndexLargeSieve.uSet_finiteLargeSieve_C_le_one_add_log`, but for the
progression-index set `uIndexSet td r` and phase `t = (ξ*q)/X`.

In particular, `1/|t| = X/(|ξ|*q)` (with `q > 0`). -/
theorem uIndexSet_finiteLargeSieve_C_le_one_add_log
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H) :
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).C
      ≤
    (N : ℝ) +
      (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))) := by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil td.U + td.q)
  let t : ℝ := (ξ * (td.q : ℝ)) / td.X
  have hDist :
      ∀ i ∈ ResiduePartition.uIndexSet (td := td) r,
        ∀ j ∈ ResiduePartition.uIndexSet (td := td) r, SSU.Hilbert.distZ i j ≤ R := by
    intro i hi j hj
    simpa [R, Nat.mul_assoc] using
      (ResiduePartition.distZ_le_two_mul_toNat_ceilU_add_q_on_uIndexSet
        (td := td) (hU0 := hU0) (r := r) i hi j hj)
  have ht0 : t ≠ 0 := by
    have hq0 : (td.q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt td.q_pos)
    intro ht0
    have hX0 : td.X ≠ 0 := ne_of_gt hX
    have : ξ * (td.q : ℝ) = 0 := by
      exact (div_eq_zero_iff).1 ht0 |>.resolve_right hX0
    have : ξ = 0 := (mul_eq_zero.mp this).resolve_right hq0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    -- This is the same “small phase” inequality proved inside `uIndexSet_finiteLargeSieve`.
    -- We just reuse the hypothesis `hXH` plus the ξ-band bound.
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have habs : |t| = |ξ| * (td.q : ℝ) / td.X := by
      simp [t, abs_div, abs_mul, abs_of_pos hq, abs_of_pos hX, mul_assoc]
    have hx : |ξ| * (td.q : ℝ) / td.X ≤ (1 / td.H) * (td.q : ℝ) / td.X := by
      have := mul_le_mul_of_nonneg_right hξH (by positivity : 0 ≤ (td.q : ℝ))
      exact div_le_div_of_nonneg_right this (le_of_lt hX)
    have h1 : |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := by
      have := mul_le_mul_of_nonneg_right (le_trans (le_of_eq habs) hx) (by positivity : 0 ≤ (R : ℝ))
      simpa [mul_assoc] using this
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    have hRq : (R : ℝ) * (td.q : ℝ) ≤ (td.X * td.H) / 2 := by
      have : (2 * ((R : ℝ) * (td.q : ℝ))) ≤ td.X * td.H := by
        simpa [R, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hXH
      nlinarith
    have hRq_div : (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hdiv :
          (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hRq (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        have : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        simpa [div_div] using this
      exact le_trans hdiv (le_of_eq hfrac)
    have hrewrite :
        ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := h1
      _ = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := hrewrite
      _ ≤ (1 / 2 : ℝ) := hRq_div

  have hC :=
    MV.finiteLargeSieve_of_distBound_C_le_one_add_log
      (J := ResiduePartition.uIndexSet (td := td) r) (N := N) (t := t) (R := R)
      (hDist := hDist) (ht := ht) (ht0 := ht0)
  have hEq :
      uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := N) (ξ := ξ)
          (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        =
      MV.finiteLargeSieve_of_distBound (J := ResiduePartition.uIndexSet (td := td) r) (N := N)
        (t := t) (R := R) (hDist := hDist) (ht := ht) (ht0 := ht0) := by
    simp [uIndexSet_finiteLargeSieve, R, t, MV.finiteLargeSieve_of_distBound]
  have hinv : (1 / |t| : ℝ) = td.X / (|ξ| * (td.q : ℝ)) := by
    have hX0 : (td.X : ℝ) ≠ 0 := ne_of_gt hX
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have hq0 : (td.q : ℝ) ≠ 0 := ne_of_gt hq
    have hξabs0 : (|ξ| : ℝ) ≠ 0 := by simpa [abs_eq_zero] using hξ0
    have habs : |t| = |ξ| * (td.q : ℝ) / td.X := by
      simp [t, abs_div, abs_mul, abs_of_pos hq, abs_of_pos hX, mul_assoc]
    calc
      (1 / |t| : ℝ) = 1 / (|ξ| * (td.q : ℝ) / td.X) := by simp [habs]
      _ = (td.X : ℝ) / (|ξ| * (td.q : ℝ)) := by
        field_simp [hX0, hξabs0, hq0]
  -- Finish.
  simpa [hEq, hinv, R] using hC

/-- Interval-geometry wrapper for `uIndexSet_finiteLargeSieve_C_le_one_add_log`.

This removes an explicit `|ξ| ≤ 1/H` argument by deriving it from
`ξ ∈ [-(1/H), 1/H]`. -/
theorem uIndexSet_finiteLargeSieve_C_le_one_add_log_outerGeom
    (td : TubeData) (hU0 : 0 ≤ td.U)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H))
    (hXH : (2 * ((2 * Int.toNat (Int.ceil td.U + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H) :
    (uIndexSet_finiteLargeSieve (td := td) (hU0 := hU0) (r := r) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH)
        (hξH := by
          exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩)
        (hXH := hXH)).C
      ≤
    (N : ℝ) +
      (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil td.U + td.q))) := by
  have hξH : |ξ| ≤ 1 / td.H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (uIndexSet_finiteLargeSieve_C_le_one_add_log
      (td := td) (hU0 := hU0) (r := r) (N := N) (ξ := ξ)
      (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH))

/-- MV finite large sieve instance on `vIndexSet td r` for phases `m,n ↦ -(ξ*q/td.X) * m * n`. -/
def vIndexSet_finiteLargeSieve
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H) :
    FiniteLargeSieve ℤ (Fin N) :=
by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil (2 * td.D) + td.q)
  have hDist :
      ∀ i ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ∀ j ∈ ResiduePartitionV.vIndexSet (td := td) r,
          SSU.Hilbert.distZ i j ≤ R := by
    intro i hi j hj
    simpa [R, Nat.mul_assoc] using
      (ResiduePartitionV.distZ_le_two_mul_toNat_ceilTwoD_add_q_on_vIndexSet
        (td := td) (hD0 := hD0) (r := r) i hi j hj)
  let t : ℝ := (ξ * (td.q : ℝ)) / td.X
  have ht0 : t ≠ 0 := by
    have hq0 : (td.q : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt td.q_pos)
    intro ht0
    have : ξ * (td.q : ℝ) = 0 := by
      have hX0 : td.X ≠ 0 := ne_of_gt hX
      exact (div_eq_zero_iff).1 ht0 |>.resolve_right hX0
    have : ξ = 0 := by
      have := mul_eq_zero.mp this
      exact this.resolve_right hq0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have habs : |t| = |ξ| * (td.q : ℝ) / td.X := by
      simp [t, abs_div, abs_mul, abs_of_pos hq, abs_of_pos hX, mul_assoc]
    have hstep :
        |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := by
      have hx : |ξ| * (td.q : ℝ) / td.X ≤ (1 / td.H) * (td.q : ℝ) / td.X := by
        have := mul_le_mul_of_nonneg_right hξH (by positivity : 0 ≤ (td.q : ℝ))
        exact div_le_div_of_nonneg_right this (le_of_lt hX)
      have := mul_le_mul_of_nonneg_right (le_trans (le_of_eq habs) hx) (by positivity : 0 ≤ (R : ℝ))
      simpa [mul_assoc] using this
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    have hRq : (R : ℝ) * (td.q : ℝ) ≤ (td.X * td.H) / 2 := by
      have : (2 * ((R : ℝ) * (td.q : ℝ))) ≤ td.X * td.H := by
        simpa [R, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hXH
      nlinarith
    have hRq_div : (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hdiv :
          (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hRq (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        have : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        simpa [div_div] using this
      exact le_trans hdiv (le_of_eq hfrac)
    have hrewrite :
        ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := hstep
      _ = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := hrewrite
      _ ≤ (1 / 2 : ℝ) := hRq_div
  exact
    MV.finiteLargeSieve_of_distBound (J := ResiduePartitionV.vIndexSet (td := td) r) (N := N)
      (t := t) (R := R) (hDist := hDist) (ht := ht) (ht0 := ht0)

/-- Unfold the phase of `vIndexSet_finiteLargeSieve`. -/
theorem vIndexSet_finiteLargeSieve_phase
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH : (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H)
    (m : ℤ) (k : Fin N) :
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).phase m k
      =
    - ((ξ * (td.q : ℝ)) / td.X) * (m : ℝ) * ((k : ℕ) : ℝ) := by
  simp [vIndexSet_finiteLargeSieve, MV.finiteLargeSieve_of_distBound, mul_assoc]

/-- Optional polylog bound on the MV constant `C` for `vIndexSet_finiteLargeSieve`.

Same as `uIndexSet_finiteLargeSieve_C_le_one_add_log`, but for `vIndexSet td r`. -/
theorem vIndexSet_finiteLargeSieve_C_le_one_add_log
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξH : |ξ| ≤ 1 / td.H)
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H) :
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)).C
      ≤
    (N : ℝ) +
      (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))) := by
  classical
  let R : ℕ := 2 * Int.toNat (Int.ceil (2 * td.D) + td.q)
  let t : ℝ := (ξ * (td.q : ℝ)) / td.X
  have hDist :
      ∀ i ∈ ResiduePartitionV.vIndexSet (td := td) r,
        ∀ j ∈ ResiduePartitionV.vIndexSet (td := td) r, SSU.Hilbert.distZ i j ≤ R := by
    intro i hi j hj
    simpa [R, Nat.mul_assoc] using
      (ResiduePartitionV.distZ_le_two_mul_toNat_ceilTwoD_add_q_on_vIndexSet
        (td := td) (hD0 := hD0) (r := r) i hi j hj)
  have ht0 : t ≠ 0 := by
    have hq0 : (td.q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt td.q_pos)
    intro ht0
    have hX0 : td.X ≠ 0 := ne_of_gt hX
    have : ξ * (td.q : ℝ) = 0 := by
      exact (div_eq_zero_iff).1 ht0 |>.resolve_right hX0
    have : ξ = 0 := (mul_eq_zero.mp this).resolve_right hq0
    exact hξ0 this
  have ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ) := by
    -- Same argument as in the `uIndexSet` case.
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have habs : |t| = |ξ| * (td.q : ℝ) / td.X := by
      simp [t, abs_div, abs_mul, abs_of_pos hq, abs_of_pos hX, mul_assoc]
    have hx : |ξ| * (td.q : ℝ) / td.X ≤ (1 / td.H) * (td.q : ℝ) / td.X := by
      have := mul_le_mul_of_nonneg_right hξH (by positivity : 0 ≤ (td.q : ℝ))
      exact div_le_div_of_nonneg_right this (le_of_lt hX)
    have h1 : |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := by
      have := mul_le_mul_of_nonneg_right (le_trans (le_of_eq habs) hx) (by positivity : 0 ≤ (R : ℝ))
      simpa [mul_assoc] using this
    have hXHpos : 0 < td.X * td.H := mul_pos hX hH
    have hRq : (R : ℝ) * (td.q : ℝ) ≤ (td.X * td.H) / 2 := by
      have : (2 * ((R : ℝ) * (td.q : ℝ))) ≤ td.X * td.H := by
        simpa [R, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hXH
      nlinarith
    have hRq_div : (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ (1 / 2 : ℝ) := by
      have hdiv :
          (R : ℝ) * (td.q : ℝ) / (td.X * td.H) ≤ ((td.X * td.H) / 2) / (td.X * td.H) :=
        div_le_div_of_nonneg_right hRq (le_of_lt hXHpos)
      have hne : (td.X * td.H) ≠ 0 := ne_of_gt hXHpos
      have hfrac : ((td.X * td.H) / 2) / (td.X * td.H) = (1 / 2 : ℝ) := by
        have : (td.X * td.H) / (2 * (td.X * td.H)) = (1 / 2 : ℝ) := by
          field_simp [hne]
        simpa [div_div] using this
      exact le_trans hdiv (le_of_eq hfrac)
    have hrewrite :
        ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := by
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      |t| * (R : ℝ) ≤ ((1 / td.H) * (td.q : ℝ) / td.X) * (R : ℝ) := h1
      _ = (R : ℝ) * (td.q : ℝ) / (td.X * td.H) := hrewrite
      _ ≤ (1 / 2 : ℝ) := hRq_div

  have hC :=
    MV.finiteLargeSieve_of_distBound_C_le_one_add_log
      (J := ResiduePartitionV.vIndexSet (td := td) r) (N := N) (t := t) (R := R)
      (hDist := hDist) (ht := ht) (ht0 := ht0)
  have hEq :
      vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := N) (ξ := ξ)
          (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH)
        =
      MV.finiteLargeSieve_of_distBound (J := ResiduePartitionV.vIndexSet (td := td) r) (N := N)
        (t := t) (R := R) (hDist := hDist) (ht := ht) (ht0 := ht0) := by
    simp [vIndexSet_finiteLargeSieve, R, t, MV.finiteLargeSieve_of_distBound]
  have hinv : (1 / |t| : ℝ) = td.X / (|ξ| * (td.q : ℝ)) := by
    have hX0 : (td.X : ℝ) ≠ 0 := ne_of_gt hX
    have hq : 0 < (td.q : ℝ) := by exact_mod_cast td.q_pos
    have hq0 : (td.q : ℝ) ≠ 0 := ne_of_gt hq
    have hξabs0 : (|ξ| : ℝ) ≠ 0 := by simpa [abs_eq_zero] using hξ0
    have habs : |t| = |ξ| * (td.q : ℝ) / td.X := by
      simp [t, abs_div, abs_mul, abs_of_pos hq, abs_of_pos hX, mul_assoc]
    calc
      (1 / |t| : ℝ) = 1 / (|ξ| * (td.q : ℝ) / td.X) := by simp [habs]
      _ = (td.X : ℝ) / (|ξ| * (td.q : ℝ)) := by
        field_simp [hX0, hξabs0, hq0]
  simpa [hEq, hinv, R] using hC

/-- Interval-geometry wrapper for `vIndexSet_finiteLargeSieve_C_le_one_add_log`.

This removes an explicit `|ξ| ≤ 1/H` argument by deriving it from
`ξ ∈ [-(1/H), 1/H]`. -/
theorem vIndexSet_finiteLargeSieve_C_le_one_add_log_outerGeom
    (td : TubeData) (hD0 : 0 ≤ td.D)
    (r : ℤ) (N : ℕ) (ξ : ℝ) (hξ0 : ξ ≠ 0) (hX : 0 < td.X) (hH : 0 < td.H)
    (hξI : ξ ∈ Set.Icc (-(1 / td.H)) (1 / td.H))
    (hXH :
      (2 * ((2 * Int.toNat (Int.ceil (2 * td.D) + td.q) : ℕ) : ℝ)) * (td.q : ℝ) ≤ td.X * td.H) :
    (vIndexSet_finiteLargeSieve (td := td) (hD0 := hD0) (r := r) (N := N) (ξ := ξ)
        (hξ0 := hξ0) (hX := hX) (hH := hH)
        (hξH := by
          exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩)
        (hXH := hXH)).C
      ≤
    (N : ℝ) +
      (td.X / (|ξ| * (td.q : ℝ))) * (1 + Real.log (2 * Int.toNat (Int.ceil (2 * td.D) + td.q))) := by
  have hξH : |ξ| ≤ 1 / td.H := by
    exact abs_le.mpr ⟨by simpa using hξI.1, by simpa using hξI.2⟩
  simpa [hξH] using
    (vIndexSet_finiteLargeSieve_C_le_one_add_log
      (td := td) (hD0 := hD0) (r := r) (N := N) (ξ := ξ)
      (hξ0 := hξ0) (hX := hX) (hH := hH) (hξH := hξH) (hXH := hXH))

end ResidueIndexLargeSieve

end
end LargeSieve
end TypeII
end Engines
end SSU
