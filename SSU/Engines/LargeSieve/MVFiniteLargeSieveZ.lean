import SSU.Engines.LargeSieve.MVExponentialGram
import SSU.Engines.LargeSieve.DualSieveFromInterzoneZ
import SSU.Engines.LargeSieve.AnalysisFromSynthesis
import SSU.Hilbert.CrowZ
import Mathlib.Data.NNReal.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
Montgomery–Vaughan (additive large sieve) — a usable ℤ-indexed finite inequality.

This file packages the deterministic exponential Gram bounds from `MVExponentialGram` into a
row-sum/Crow bound on a finite index set `J : Finset ℤ`, and then applies
`DualSieveFromInterzoneZ` to obtain a “dual large sieve” inequality.

We deliberately keep the Crow constant in a *finite sum* form (no `log` simplifications yet).
This is enough for SSU plumbing and for later TeX-facing simplification steps (polylog losses
are allowed).
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

open Complex

local notation "⟪" x ", " y "⟫" => inner ℂ x y

namespace MV

/-!
## A nonnegative distance weight `a(d)` matching the Dirichlet-kernel bound

For `d = distZ i j` the Gram entry obeys

`‖⟪expVec N t i, expVec N t j⟫‖ ≤ min (N) (1 / (2*|t|*d))`

whenever the “small phase” assumption `|t|*d ≤ 1/2` holds.
-/

def aMV (N : ℕ) (t : ℝ) (d : ℕ) : NNReal :=
  if d = 0 then (N : NNReal) else
    min (N : NNReal) (Real.toNNReal (1 / (2 * |t| * (d : ℝ))))

theorem aMV_nonneg (N : ℕ) (t : ℝ) (d : ℕ) : 0 ≤ (aMV N t d : ℝ) := by
  classical
  by_cases hd : d = 0
  · simp [aMV, hd]
  · simp [aMV, hd]

theorem norm_inner_expVec_le_aMV_of_smallPhase
    (N : ℕ) (t : ℝ) {i j : ℤ}
    (ht : |t| * (SSU.Hilbert.distZ i j : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : t ≠ 0) :
    ‖⟪expVec N t i, expVec N t j⟫‖ ≤ (aMV N t (SSU.Hilbert.distZ i j) : ℝ) := by
  classical
  by_cases hij : i = j
  · subst hij
    -- Diagonal: the Gram entry is exactly `N`.
    have hinner : ⟪expVec N t i, expVec N t i⟫ = (N : ℂ) := by
      -- `j-i = 0`, so the range sum is `∑ 1 = N`.
      rw [inner_expVec_eq_sum_range (N := N) (t := t) (i := i) (j := i)]
      simp [SSU.Engines.TypeII.e]
    have hnorm : ‖⟪expVec N t i, expVec N t i⟫‖ = (N : ℝ) := by
      rw [hinner]
      simp
    -- `distZ i i = 0` and `aMV N t 0 = N`.
    rw [hnorm]
    simp [aMV]
  · -- Off-diagonal: use the Dirichlet-kernel bound on the range sum.
    have hEq :
        |t * ((j - i : ℤ) : ℝ)| = |t| * (SSU.Hilbert.distZ i j : ℝ) := by
      simpa using (abs_mul_sub_eq_abs_mul_distZ (t := t) (i := i) (j := j))
    have hmul : |t * ((j - i : ℤ) : ℝ)| ≤ (1 / 2 : ℝ) := by
      calc
        |t * ((j - i : ℤ) : ℝ)| = |t| * (SSU.Hilbert.distZ i j : ℝ) := hEq
        _ ≤ (1 / 2 : ℝ) := ht
    have hmul0 : t * ((j - i : ℤ) : ℝ) ≠ 0 := by
      have hji : (j - i : ℤ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
      have : ((j - i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hji
      exact mul_ne_zero ht0 this
    have hmin :=
      norm_inner_expVec_le_min (N := N) (t := t) (i := i) (j := j) hmul hmul0
    have hd0 : SSU.Hilbert.distZ i j ≠ 0 := by
      intro hd
      have habs : (i - j).natAbs = 0 := by simpa [SSU.Hilbert.distZ] using hd
      have : i - j = 0 := Int.natAbs_eq_zero.mp habs
      exact hij (sub_eq_zero.mp this)

    -- Rewrite the analytic term using `distZ`.
    have habs :
        (1 / (2 * |t * ((j - i : ℤ) : ℝ)|)) =
          1 / (2 * |t| * (SSU.Hilbert.distZ i j : ℝ)) := by
      rw [hEq]
      simp [mul_assoc]

    -- Evaluate `toNNReal` at a nonnegative real.
    set r : ℝ := (1 / (2 * |t| * (SSU.Hilbert.distZ i j : ℝ)))
    have hr : 0 ≤ r := by
      have : 0 ≤ (2 * |t| * (SSU.Hilbert.distZ i j : ℝ)) := by positivity
      simpa [r] using (one_div_nonneg.2 this)
    have ha : (aMV N t (SSU.Hilbert.distZ i j) : ℝ) = min (N : ℝ) r := by
      have hrdef :
          (1 / (2 * |t| * (SSU.Hilbert.distZ i j : ℝ))) = r := (rfl : r = _).symm
      have hcoe : (Real.toNNReal r : ℝ) = r := Real.coe_toNNReal r hr
      simp [aMV, hd0, hrdef, hcoe]

    -- Conclude.
    have : ‖⟪expVec N t i, expVec N t j⟫‖ ≤ min (N : ℝ) r := by
      have habs' : (1 / (2 * |t * ((j - i : ℤ) : ℝ)|)) = r := by
        simpa [r] using habs
      calc
        ‖⟪expVec N t i, expVec N t j⟫‖ ≤ min (N : ℝ) (1 / (2 * |t * ((j - i : ℤ) : ℝ)|)) := hmin
        _ = min (N : ℝ) r := by
              simpa using congrArg (fun x => min (N : ℝ) x) habs'
    simpa [ha] using this

/-!
## A “dual large sieve” inequality on a finite `J : Finset ℤ`

We assume a uniform distance bound `distZ i j ≤ R` on `J` (coming from deterministic geometry,
e.g. `J ⊆ Icc (-U) U` gives `R = 2U`).

We *do not* simplify the Crow constant here.
-/

theorem dual_largeSieve_of_distBound
    (J : Finset ℤ) (N : ℕ) (t : ℝ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : t ≠ 0) :
    ∀ c : ℤ → ℂ,
      ‖∑ i ∈ J, c i • expVec N t i‖ ^ 2
        ≤
      ((aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))) *
        (∑ i ∈ J, ‖c i‖ ^ 2) := by
  classical
  intro c
  -- Gram bound under the uniform small-phase hypothesis.
  have hGram :
      ∀ i ∈ J, ∀ j ∈ J,
        ‖⟪expVec N t i, expVec N t j⟫‖ ≤ (aMV N t (SSU.Hilbert.distZ i j) : ℝ) := by
    intro i hi j hj
    have hd : (SSU.Hilbert.distZ i j : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast hDist i hi j hj
    have htij : |t| * (SSU.Hilbert.distZ i j : ℝ) ≤ (1 / 2 : ℝ) := by
      have : |t| * (SSU.Hilbert.distZ i j : ℝ) ≤ |t| * (R : ℝ) := by
        gcongr
      exact this.trans ht
    exact norm_inner_expVec_le_aMV_of_smallPhase (N := N) (t := t) (i := i) (j := j) htij ht0

  -- Row-sum bound: “two points per distance” + enlarge to the interval `Icc 1 R`.
  have hRow :
      ∀ i ∈ J,
        (∑ j ∈ J, (aMV N t (SSU.Hilbert.distZ i j) : ℝ))
          ≤ (aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)) := by
    intro i hi
    have hCrow :=
      SSU.Hilbert.rowSum_le_a0_add_two_sum_image_erase_zero (a := fun d => aMV N t d) (J := J) i
    set distSet : Finset ℕ := (J.image fun j => SSU.Hilbert.distZ i j).erase 0
    have hsub : distSet ⊆ Finset.Icc 1 R := by
      intro d hd
      have hd' : d ≠ 0 ∧ d ∈ (J.image fun j => SSU.Hilbert.distZ i j) := by
        simpa [distSet] using (Finset.mem_erase.mp hd)
      rcases Finset.mem_image.mp hd'.2 with ⟨j, hjJ, rfl⟩
      have hpos : 1 ≤ SSU.Hilbert.distZ i j := Nat.pos_of_ne_zero hd'.1
      have hle : SSU.Hilbert.distZ i j ≤ R := hDist i hi j hjJ
      simpa [Finset.mem_Icc] using And.intro hpos hle
    have hsum_le :
        (∑ d ∈ distSet, (aMV N t d : ℝ))
          ≤ ∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro d hdIcc hdNot
      exact aMV_nonneg (N := N) (t := t) (d := d)
    have :
        (∑ j ∈ J, (aMV N t (SSU.Hilbert.distZ i j) : ℝ))
          ≤ (aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)) := by
      calc
        (∑ j ∈ J, (aMV N t (SSU.Hilbert.distZ i j) : ℝ))
            ≤ (aMV N t 0 : ℝ) + 2 * (∑ d ∈ distSet, (aMV N t d : ℝ)) := by
              simpa [distSet] using hCrow
        _ ≤ (aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)) := by
              gcongr
    exact this

  -- Apply the Hilbert-space interzone-to-dual-sieve lemma.
  simpa using
    (SSU.Engines.LargeSieve.norm_sum_smul_sq_le_of_rowSum_gram_boundZ
      (J := J) (v := fun i => expVec N t i) (a := fun d => aMV N t d)
      (Crow := (aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)))
      (hGram := hGram) (hRow := hRow) c)

/-!
## “Primal” / analysis-side inequality (Bessel form)

This is the form used in TeX Step 3/4 after Cauchy–Schwarz in the outer sum: for a fixed
coefficient vector `x` (length `N`), we bound the sum over frequencies `i ∈ J` of the squared
modulus of the exponential sum `⟪expVec N t i, x⟫`.

We derive it from the dual/synthesis form by a sharp finite “analysis from synthesis” lemma.
-/

theorem primal_largeSieve_of_distBound
    (J : Finset ℤ) (N : ℕ) (t : ℝ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : t ≠ 0) :
    ∀ x : EuclideanSpace ℂ (Fin N),
      (∑ i ∈ J, ‖⟪expVec N t i, x⟫‖ ^ 2)
        ≤
      ((aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))) * ‖x‖ ^ 2 := by
  classical
  -- Start from the dual/synthesis inequality.
  have hSynth :=
    dual_largeSieve_of_distBound (J := J) (N := N) (t := t) (R := R)
      (hDist := hDist) (ht := ht) (ht0 := ht0)
  -- The Crow constant is nonnegative.
  have hCrow_nonneg :
      0 ≤ ((aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))) := by
    have h0 : 0 ≤ (aMV N t 0 : ℝ) := by exact aMV_nonneg (N := N) (t := t) (d := 0)
    have hsum : 0 ≤ (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)) := by
      refine Finset.sum_nonneg ?_
      intro d hd
      exact aMV_nonneg (N := N) (t := t) (d := d)
    nlinarith
  -- Apply analysis-from-synthesis.
  intro x
  simpa using
    (SSU.Engines.LargeSieve.sum_norm_inner_sq_le_of_synthesisBound
      (J := J) (v := fun i => expVec N t i)
      (C := ((aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))))
      hCrow_nonneg hSynth x)

/-!
## Optional simplification: bounding the finite Crow sum by a harmonic/log term

This is the first “polylog is OK” simplification step: we bound
`∑_{d=1..R} aMV(d)` by a multiple of the harmonic sum.
-/

theorem sum_aMV_Icc_le_harmonic (N : ℕ) (t : ℝ) (R : ℕ) (ht0 : t ≠ 0) :
    (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))
      ≤
    (1 / (2 * |t|)) * (harmonic R) := by
  classical
  -- Pointwise bound: for `d ≥ 1`, `aMV(d) ≤ 1 / (2*|t|*d)`.
  have hle (d : ℕ) (hd : d ∈ Finset.Icc 1 R) :
      (aMV N t d : ℝ) ≤ 1 / (2 * |t| * (d : ℝ)) := by
    have hd0 : d ≠ 0 := by
      have : 1 ≤ d := (Finset.mem_Icc.1 hd).1
      have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one this
      exact Nat.ne_of_gt hdpos
    -- Unfold `aMV` at `d ≠ 0`.
    have ha :
        (aMV N t d : ℝ) =
          min (N : ℝ) (Real.toNNReal (1 / (2 * |t| * (d : ℝ)))) := by
      -- `d ≠ 0` makes the `if` branch choose the `min`.
      simp [aMV, hd0]
    -- `min ≤ rhs`.
    have hmin : (aMV N t d : ℝ) ≤ (Real.toNNReal (1 / (2 * |t| * (d : ℝ))) : ℝ) := by
      -- `min a b ≤ b`.
      simpa [ha] using (min_le_right (N : ℝ) (Real.toNNReal (1 / (2 * |t| * (d : ℝ)))))
    -- Convert `toNNReal` to a real number.
    have htpos : 0 < |t| := abs_pos.2 ht0
    have hden_nonneg : 0 ≤ (2 * |t| * (d : ℝ)) := by positivity
    have hr : 0 ≤ (1 / (2 * |t| * (d : ℝ)) : ℝ) := by
      exact one_div_nonneg.2 hden_nonneg
    have hcoe :
        (Real.toNNReal (1 / (2 * |t| * (d : ℝ))) : ℝ) = (1 / (2 * |t| * (d : ℝ)) : ℝ) :=
      Real.coe_toNNReal _ hr
    exact hmin.trans_eq hcoe

  -- Sum the pointwise bounds and rewrite the RHS via the harmonic sum.
  have hsum :
      (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))
        ≤
      ∑ d ∈ Finset.Icc 1 R, (1 / (2 * |t| * (d : ℝ)) : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    exact hle d hd
  -- Factor out `1/(2*|t|)` and identify the harmonic sum.
  calc
    (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))
        ≤
      ∑ d ∈ Finset.Icc 1 R, (1 / (2 * |t| * (d : ℝ)) : ℝ) := hsum
    _ =
      (1 / (2 * |t|)) * (∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹) := by
      have htabs0 : (|t| : ℝ) ≠ 0 := abs_ne_zero.2 ht0
      have hconst : (1 / (2 * |t|) : ℝ) = |t|⁻¹ * (2 : ℝ)⁻¹ := by
        field_simp [htabs0]
      -- Factor out the scalar `|t|⁻¹ * 2⁻¹` and rewrite.
      calc
        (∑ d ∈ Finset.Icc 1 R, (1 / (2 * |t| * (d : ℝ)) : ℝ))
            =
          ∑ d ∈ Finset.Icc 1 R, (|t|⁻¹ * ((d : ℝ)⁻¹ * (2 : ℝ)⁻¹) : ℝ) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ =
          (|t|⁻¹ * (2 : ℝ)⁻¹) * (∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹) := by
            -- Pull out `|t|⁻¹`, then pull out `2⁻¹`.
            calc
              (∑ d ∈ Finset.Icc 1 R, (|t|⁻¹ * ((d : ℝ)⁻¹ * (2 : ℝ)⁻¹) : ℝ))
                  =
                |t|⁻¹ * (∑ d ∈ Finset.Icc 1 R, ((d : ℝ)⁻¹ * (2 : ℝ)⁻¹ : ℝ)) := by
                  simpa [Finset.mul_sum] using
                    (Finset.mul_sum (|t|⁻¹ : ℝ) (s := Finset.Icc 1 R)
                      (f := fun d => ((d : ℝ)⁻¹ * (2 : ℝ)⁻¹ : ℝ))).symm
              _ =
                |t|⁻¹ * ((∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹) * (2 : ℝ)⁻¹) := by
                  congr 1
                  simpa [Finset.sum_mul] using
                    (Finset.sum_mul (s := Finset.Icc 1 R) (f := fun d => (d : ℝ)⁻¹)
                      (a := (2 : ℝ)⁻¹)).symm
              _ =
                (|t|⁻¹ * (2 : ℝ)⁻¹) * (∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹) := by
                  -- commutativity/associativity
                  simp [mul_assoc, mul_left_comm, mul_comm]
        _ = (1 / (2 * |t|)) * (∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹) := by
          simpa [hconst, mul_assoc, mul_left_comm, mul_comm]
    _ = (1 / (2 * |t|)) * (harmonic R) := by
      simp [harmonic_eq_sum_Icc]

theorem sum_aMV_Icc_le_one_add_log (N : ℕ) (t : ℝ) (R : ℕ) (ht0 : t ≠ 0) :
    (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))
      ≤
    (1 / (2 * |t|)) * (1 + Real.log R) := by
  classical
  have h1 := sum_aMV_Icc_le_harmonic (N := N) (t := t) (R := R) ht0
  have htpos : 0 < (1 / (2 * |t|) : ℝ) := by
    have : 0 < |t| := abs_pos.2 ht0
    have : 0 < (2 * |t| : ℝ) := by positivity
    simpa using (one_div_pos.2 this)
  have hmul :
      (1 / (2 * |t|)) * harmonic R ≤ (1 / (2 * |t|)) * (1 + Real.log R) := by
    have hle : harmonic R ≤ 1 + Real.log R := harmonic_le_one_add_log R
    exact mul_le_mul_of_nonneg_left hle (le_of_lt htpos)
  exact h1.trans hmul

end MV

end
end LargeSieve
end Engines
end SSU
