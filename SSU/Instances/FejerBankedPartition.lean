import SSU.Instances.TorusDyadicShell
import SSU.Hilbert.CrowZ

import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.Holder

/-!
Fejér-banked tube partition → dyadic-shell multipliers (`05b_SSU.tex`, “Tube overlap …”).

This file does **not** attempt to formalize the full geometric construction of tubes on `𝕋`.
Instead, it packages the *outputs* of that construction as explicit hypotheses:

* fixed-`j` bounded overlap (Lemma “Bounded multiplicity at fixed j”),
* global overlap bound `Λ` (Proposition “Tube overlap (T1)”),
* a bounded Fejér window `Φ_H`.

From these, we build the SSU primitive multipliers

`ψ_j := (∑_k P_{U_{j,k}}) * Φ_H`

and prove the deterministic pointwise sum-of-squares bound needed by
`SSU.Instances.TorusDyadicShell.MultiplierModel`.
-/

namespace SSU
namespace Instances
namespace FejerBankedPartition

open scoped BigOperators ENNReal

open MeasureTheory
open SSU.Torus
open SSU.Instances.TorusDyadicShell

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/--
Hypothesis package corresponding to the “Fejér-banked partition” in `05b_SSU.tex`.

The core data are fixed real-valued projectors `P_{U_{j,k}} : 𝕋 → ℝ` with `0 ≤ P ≤ 1`,
organized by an outer dyadic shell index `j : ℤ` and an internal tube index `k ∈ K j`.

The library’s SSU primitive is the already-summed dyadic-shell multiplier
`ψ_j := (∑_k P_{U_{j,k}}) * Φ_H`.
-/
structure Data (κ : Type*) [DecidableEq κ] where
  /-- The large parameter `X` from the notes (window length). -/
  X : ℝ
  /-- The short-shift bandwidth parameter `H` from the notes. -/
  H : ℝ
  /-- The dyadic shell indices used in the application (finite for the SSU engine). -/
  J : Finset ℤ
  /-- Tube indices available at each shell. -/
  K : ℤ → Finset κ
  /-- Fixed tube projectors `P_{U_{j,k}}` (real-valued cutoffs). -/
  P : ℤ → κ → UC → ℝ
  /-- Each projector is essentially bounded (needed to form `L^∞` multipliers). -/
  hP : ∀ j : ℤ, ∀ k : κ, MemLp (P j k) (∞ : ℝ≥0∞) μ
  /-- Pointwise positivity (TeX: `0 ≤ P_{U_{j,k}} ≤ 1`). -/
  P_nonneg : ∀ j : ℤ, ∀ k : κ, ∀ x : UC, 0 ≤ P j k x
  /-- Pointwise upper bound by `1` (TeX: `0 ≤ P_{U_{j,k}} ≤ 1`). -/
  P_le_one : ∀ j : ℤ, ∀ k : κ, ∀ x : UC, P j k x ≤ 1
  /-- Fejér window multiplier `Φ_H` (frequency-side). -/
  Φ : UC → ℂ
  /-- `Φ_H ∈ L^∞`. -/
  hΦ : MemLp Φ (∞ : ℝ≥0∞) μ
  /-- A pointwise `L^∞` bound `‖Φ_H‖_∞ ≤ Φmax`. -/
  Φmax : ℝ
  Φmax_nonneg : 0 ≤ Φmax
  Φ_bound : ∀ x : UC, ‖Φ x‖ ≤ Φmax
  /-- Fixed-`j` overlap constant (TeX Lemma “Bounded multiplicity at fixed j”). -/
  M : ℝ
  M_nonneg : 0 ≤ M
  fixed_j_overlap : ∀ j : ℤ, ∀ x : UC, (∑ k ∈ K j, P j k x) ≤ M
  /-- Global overlap constant (TeX Proposition “Tube overlap (T1)”). -/
  ΛP : ℝ
  ΛP_nonneg : 0 ≤ ΛP
  global_overlap : ∀ x : UC, (∑ j ∈ J, ∑ k ∈ K j, P j k x) ≤ ΛP

namespace Data

variable {κ : Type*} [DecidableEq κ] (D : Data κ)

/-- The dyadic-shell sum `S_j := ∑_k P_{U_{j,k}}` (real-valued). -/
noncomputable def shellSum (j : ℤ) : UC → ℝ :=
  fun x => ∑ k ∈ D.K j, D.P j k x

/-- The SSU primitive multiplier `ψ_j := (∑_k P_{U_{j,k}}) * Φ_H`. -/
noncomputable def ψ (j : ℤ) : UC → ℂ :=
  fun x => ((D.shellSum j x : ℝ) : ℂ) * D.Φ x

theorem memLp_shellSum (j : ℤ) : MemLp (D.shellSum j) (∞ : ℝ≥0∞) μ := by
  classical
  -- Use the generic finset-sum closure lemma.
  have h :=
    MeasureTheory.memLp_finset_sum (μ := μ) (p := (∞ : ℝ≥0∞)) (s := D.K j)
      (f := fun k x => D.P j k x) (hf := fun k _hk => D.hP j k)
  simpa [Data.shellSum] using h

theorem memLp_ψ (j : ℤ) : MemLp (D.ψ j) (∞ : ℝ≥0∞) μ := by
  have hS : MemLp (D.shellSum j) (∞ : ℝ≥0∞) μ := D.memLp_shellSum j
  have hS' : MemLp (fun x : UC => ((D.shellSum j x : ℝ) : ℂ)) (∞ : ℝ≥0∞) μ :=
    hS.ofReal (K := ℂ)
  -- `L^∞ * L^∞ ⊆ L^∞` (Hölder with `∞,∞,∞`).
  -- `MemLp.mul` is written as `φ * f`; take `f := Φ` and `φ := shellSum`.
  simpa [Data.ψ, mul_assoc] using
    (D.hΦ.mul (p := (∞ : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)) (r := (∞ : ℝ≥0∞)) hS')

/-- A convenient bound on the shell sum: `0 ≤ S_j(x)`. -/
theorem shellSum_nonneg (j : ℤ) (x : UC) : 0 ≤ D.shellSum j x := by
  classical
  -- Finite sum of nonnegative terms.
  refine Finset.sum_nonneg ?_
  intro k hk
  simpa using D.P_nonneg j k x

/--
Pointwise sum-of-squares overlap for the dyadic-shell multipliers.

This is the deterministic bridge:
fixed-`j` overlap + global overlap + `L^∞` bound on `Φ_H`
`⇒` pointwise `∑_j ‖ψ_j‖² ≤ Φmax² * M * ΛP`.
-/
theorem sum_norm_sq_ψ_le (x : UC) :
    (∑ j ∈ D.J, ‖D.ψ j x‖ ^ 2) ≤ (D.Φmax ^ 2) * D.M * D.ΛP := by
  classical
  -- First, bound each term `‖ψ_j(x)‖² ≤ Φmax² * M * shellSum j x`.
  have hterm :
      ∀ j ∈ D.J, ‖D.ψ j x‖ ^ 2 ≤ (D.Φmax ^ 2) * D.M * (D.shellSum j x) := by
    intro j _hj
    have hS0 : 0 ≤ D.shellSum j x := D.shellSum_nonneg j x
    have hSle : D.shellSum j x ≤ D.M := D.fixed_j_overlap j x
    have hΦle : ‖D.Φ x‖ ≤ D.Φmax := D.Φ_bound x
    -- `‖((S : ℂ) * Φ)‖² = S² * ‖Φ‖²`.
    have hnormS : ‖((D.shellSum j x : ℝ) : ℂ)‖ = D.shellSum j x := by
      simpa [RCLike.norm_ofReal, abs_of_nonneg hS0]
    have hnormψ :
        ‖D.ψ j x‖ ^ 2 = (D.shellSum j x) ^ 2 * ‖D.Φ x‖ ^ 2 := by
      have hnorm1 : ‖D.ψ j x‖ = D.shellSum j x * ‖D.Φ x‖ := by
        calc
          ‖D.ψ j x‖ = ‖((D.shellSum j x : ℝ) : ℂ) * D.Φ x‖ := by
              simp [Data.ψ]
          _ = ‖((D.shellSum j x : ℝ) : ℂ)‖ * ‖D.Φ x‖ := by
              simpa [norm_mul]
          _ = D.shellSum j x * ‖D.Φ x‖ := by
              -- Avoid `simp` here: it can unfold `Complex.norm_eq_abs` and introduce side goals.
              simpa using congrArg (fun t => t * ‖D.Φ x‖) hnormS
      calc
        ‖D.ψ j x‖ ^ 2 = (D.shellSum j x * ‖D.Φ x‖) ^ 2 := by
            simpa [hnorm1]
        _ = (D.shellSum j x) ^ 2 * ‖D.Φ x‖ ^ 2 := by
            simp [mul_pow]
    -- Use `S² ≤ M*S` and `‖Φ‖² ≤ Φmax²`.
    have hSsq : (D.shellSum j x) ^ 2 ≤ D.M * (D.shellSum j x) := by
      -- `S² ≤ M*S` since `0 ≤ S` and `S ≤ M`.
      have : D.shellSum j x * D.shellSum j x ≤ D.M * D.shellSum j x :=
        mul_le_mul_of_nonneg_right hSle hS0
      simpa [pow_two, mul_assoc] using this
    have hΦsq : ‖D.Φ x‖ ^ 2 ≤ D.Φmax ^ 2 := by
      exact pow_le_pow_left₀ (by positivity : 0 ≤ ‖D.Φ x‖) hΦle 2
    calc
      ‖D.ψ j x‖ ^ 2 = (D.shellSum j x) ^ 2 * ‖D.Φ x‖ ^ 2 := hnormψ
      _ ≤ (D.M * D.shellSum j x) * (D.Φmax ^ 2) := by
            have hnonnegC : 0 ≤ ‖D.Φ x‖ ^ 2 := by positivity
            have hnonnegB : 0 ≤ D.M * D.shellSum j x := mul_nonneg D.M_nonneg hS0
            -- Multiply the inequalities `S² ≤ M*S` and `‖Φ‖² ≤ Φmax²`.
            have :=
              mul_le_mul hSsq hΦsq hnonnegC hnonnegB
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
      _ = (D.Φmax ^ 2) * D.M * (D.shellSum j x) := by ring
  -- Sum the termwise bounds, then use the global overlap bound.
  have hsum1 :
      (∑ j ∈ D.J, ‖D.ψ j x‖ ^ 2)
        ≤ ∑ j ∈ D.J, ((D.Φmax ^ 2) * D.M) * (D.shellSum j x) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have := hterm j hj
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hsum1' :
      (∑ j ∈ D.J, ((D.Φmax ^ 2) * D.M) * (D.shellSum j x))
        = ((D.Φmax ^ 2) * D.M) * (∑ j ∈ D.J, D.shellSum j x) := by
    simpa using
      (Finset.mul_sum (s := D.J) (f := fun j => D.shellSum j x) (a := ((D.Φmax ^ 2) * D.M))).symm
  have hsum :
      (∑ j ∈ D.J, ‖D.ψ j x‖ ^ 2)
        ≤ ((D.Φmax ^ 2) * D.M) * (∑ j ∈ D.J, D.shellSum j x) := by
    simpa [hsum1'] using hsum1
  have hOverlap : (∑ j ∈ D.J, D.shellSum j x) ≤ D.ΛP := by
    simpa [Data.shellSum] using D.global_overlap x
  have hconst : 0 ≤ (D.Φmax ^ 2) * D.M := by
    have h0 : 0 ≤ D.Φmax ^ 2 := by nlinarith [D.Φmax_nonneg]
    exact mul_nonneg h0 D.M_nonneg
  have hsum2 :
      ((D.Φmax ^ 2) * D.M) * (∑ j ∈ D.J, D.shellSum j x)
        ≤ ((D.Φmax ^ 2) * D.M) * D.ΛP :=
    mul_le_mul_of_nonneg_left hOverlap hconst
  have hfinal : (∑ j ∈ D.J, ‖D.ψ j x‖ ^ 2) ≤ ((D.Φmax ^ 2) * D.M) * D.ΛP :=
    le_trans (le_trans hsum hsum2) (le_rfl)
  simpa [mul_assoc] using hfinal

noncomputable def Λψ : ℝ :=
  (D.Φmax ^ 2) * D.M * D.ΛP

theorem Λψ_nonneg : 0 ≤ D.Λψ := by
  have h0 : 0 ≤ D.Φmax ^ 2 := by nlinarith [D.Φmax_nonneg]
  exact mul_nonneg (mul_nonneg h0 D.M_nonneg) D.ΛP_nonneg

theorem overlap_sq_ψ :
    (∀ᵐ x : UC ∂μ,
      (∑ j ∈ D.J,
          ‖(Torus.toLinf (φ := D.ψ j) (hφ := D.memLp_ψ j) x)‖ ^ 2) ≤ D.Λψ) := by
  classical
  -- First: ensure we are on an a.e. set where every `toLinf` agrees with the underlying function.
  have hEqAll :
      (∀ᵐ x : UC ∂μ,
        ∀ j ∈ D.J,
          (Torus.toLinf (φ := D.ψ j) (hφ := D.memLp_ψ j) x) = D.ψ j x) := by
    classical
    refine D.J.induction_on ?_ ?_
    · refine Filter.Eventually.of_forall ?_
      intro x j hj
      exact (Finset.notMem_empty j hj).elim
    · intro a s ha hs
      have haEq :
          (∀ᵐ x : UC ∂μ,
            (Torus.toLinf (φ := D.ψ a) (hφ := D.memLp_ψ a) x) = D.ψ a x) := by
        -- `Torus.toLinf` is `MemLp.toLp`.
        have h := (D.memLp_ψ a).coeFn_toLp (μ := μ) (p := (∞ : ℝ≥0∞)) (f := D.ψ a)
        -- Convert `=ᵐ` to `∀ᵐ` equality and unfold `toLinf`.
        simpa [Torus.toLinf] using h
      refine (haEq.and hs).mono ?_
      rintro x ⟨hxA, hxS⟩ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact hxA
      · exact hxS j hj'
  -- Now: use `hEqAll` to replace each `toLinf` term by `ψ`, then apply the pointwise bound.
  refine hEqAll.mono ?_
  intro x hx
  have hrewrite :
      (∑ j ∈ D.J,
          ‖(Torus.toLinf (φ := D.ψ j) (hφ := D.memLp_ψ j) x)‖ ^ 2)
        =
      (∑ j ∈ D.J, ‖D.ψ j x‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp [hx j hj]
  -- Apply the pointwise sum-of-squares bound.
  simpa [Data.Λψ, hrewrite] using D.sum_norm_sq_ψ_le x

/--
Build a `TorusDyadicShell.MultiplierModel` from the Fejér-banked partition hypotheses.

This is the canonical bridge from the “Tube overlap …” section of `05b_SSU.tex` into the SSU core.
-/
noncomputable def toMultiplierModel : TorusDyadicShell.MultiplierModel where
  X := D.X
  H := D.H
  J := D.J
  ψ := D.ψ
  hψ := fun j => D.memLp_ψ j
  Λ := D.Λψ
  Λ_nonneg := D.Λψ_nonneg
  overlap_sq := D.overlap_sq_ψ

/-- The SSU core packet family on `ℓ²(ℤ)` obtained from this partition (via Fourier conjugation). -/
noncomputable def corePacketFamily : SSU.Global.PacketFamily :=
  (D.toMultiplierModel.corePacketFamily)

/--
Deterministic Crow / row-sum bound for any decay function `a`, using the finite-set bound
`SSU.Hilbert.crowBound` (max over `i ∈ J` of the two-points-per-distance estimate).
-/
theorem rowSumBound_of_crowBound (a : ℕ → NNReal) :
    SSU.Global.RowSumBound D.corePacketFamily a (SSU.Hilbert.crowBound a D.J) := by
  intro i hi
  -- `corePacketFamily.J = D.J`; use the deterministic lemma in `SSU.Hilbert.CrowZ`.
  simpa [Data.corePacketFamily, TorusDyadicShell.MultiplierModel.corePacketFamily, SSU.Global.RowSumBound]
    using (SSU.Hilbert.rowSum_le_crowBound (a := a) (J := D.J) i hi)

/--
Assemble an end-to-end SSU contract for this partition, assuming only the SSU heart
`SSU.Interzone.GramHypothesis` (ledger-friendly cross-packet Gram decay).

We use the deterministic choice `Crow := SSU.Hilbert.crowBound h.a D.J`.
-/
noncomputable def contract_of_gramHypothesis
    (h : SSU.Interzone.GramHypothesis D.J (D.corePacketFamily.T)) :
    SSU.Global.SSUContract D.corePacketFamily :=
  (D.toMultiplierModel).contract_of_gramHypothesis
    (h := h)
    (Crow := SSU.Hilbert.crowBound h.a D.J)
    (hRow := D.rowSumBound_of_crowBound (a := h.a))
    (hCrow := SSU.Hilbert.crowBound_nonneg (a := h.a) (J := D.J))

theorem opNorm_sum_le_of_gramHypothesis
    (h : SSU.Interzone.GramHypothesis D.J (D.corePacketFamily.T)) :
    ‖∑ i ∈ D.corePacketFamily.J, D.corePacketFamily.T i‖
      ≤ Real.sqrt ((SSU.Hilbert.crowBound h.a D.J) * ((‖(D.toMultiplierModel).normFactor‖ ^ 2) * D.Λψ)) := by
  -- This is just `SSU.Global.opNorm_sum_le_of_contract` applied to the assembled contract.
  simpa [Data.corePacketFamily, Data.contract_of_gramHypothesis]
    using (SSU.Global.opNorm_sum_le_of_contract (C := D.contract_of_gramHypothesis h))

end Data

end

end FejerBankedPartition
end Instances
end SSU
