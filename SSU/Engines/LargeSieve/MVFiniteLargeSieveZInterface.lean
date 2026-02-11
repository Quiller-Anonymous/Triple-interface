import SSU.Engines.LargeSieve.MVFiniteLargeSieveZ
import SSU.Engines.LargeSieve.MontgomeryVaughanHypothesis
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Bridges from the proved finite ℤ-indexed MV large sieve (`MVFiniteLargeSieveZ`) to the generic
`FiniteLargeSieve` interface.

This is a small “plumbing” file: it does not yet prove the TeX Step 3/4 fiber bounds, but it
packages the finished MV inequality into a reusable interface, so downstream reductions can depend
only on `FiniteLargeSieve`.
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

namespace MV

open Complex
open scoped ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner ℂ x y

theorem inner_expVec_eq_sum_univ (N : ℕ) (t : ℝ) (z : ℤ) (x : EuclideanSpace ℂ (Fin N)) :
    ⟪expVec N t z, x⟫
      =
    ∑ n : Fin N, (SSU.Engines.TypeII.e (-t * (z : ℝ) * ((n : ℕ) : ℝ))) * x n := by
  classical
  -- Expand the inner product of `WithLp` vectors.
  have star_e (r : ℝ) : star (SSU.Engines.TypeII.e r) = SSU.Engines.TypeII.e (-r) := by
    simpa using (SSU.Engines.TypeII.AdmissibleKernel.conj_e r)
  -- `EuclideanSpace.inner_eq_star_dotProduct` rewrites the inner product as a `Fin`-sum.
  -- Then `star (e(..)) = e(-..)` does the conjugation.
  simp [EuclideanSpace.inner_eq_star_dotProduct, expVec, dotProduct, star_e,
    mul_assoc, mul_left_comm, mul_comm]

/-- Package `MV.primal_largeSieve_of_distBound` as a `FiniteLargeSieve` instance, using the phase
`(i,n) ↦ -t * i * n` so that the exponential sum is literally `⟪expVec N t i, x⟫`. -/
def finiteLargeSieve_of_distBound
    (J : Finset ℤ) (N : ℕ) (t : ℝ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : t ≠ 0) :
    SSU.Engines.LargeSieve.FiniteLargeSieve ℤ (Fin N) :=
by
  classical
  refine
    { I := J
      K := Finset.univ
      phase := fun i n => -t * (i : ℝ) * ((n : ℕ) : ℝ)
      C := ((aMV N t 0 : ℝ) + 2 * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)))
      C_nonneg := ?_
      bound := ?_ }
  · -- Nonnegativity of the Crow constant.
    have h0 : 0 ≤ (aMV N t 0 : ℝ) := aMV_nonneg (N := N) (t := t) (d := 0)
    have hsum : 0 ≤ (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)) := by
      refine Finset.sum_nonneg ?_
      intro d hd
      exact aMV_nonneg (N := N) (t := t) (d := d)
    nlinarith
  · intro a
    -- Apply the proved primal inequality to `x := toLp 2 a`.
    let x : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 a
    have hprimal :=
      primal_largeSieve_of_distBound (J := J) (N := N) (t := t) (R := R)
        (hDist := hDist) (ht := ht) (ht0 := ht0) (x := x)
    -- Rewrite both sides into the `FiniteLargeSieve` shape.
    -- LHS: `⟪expVec, a⟫` becomes an explicit exponential sum with phase `-t*i*n`.
    have hLHS :
        (∑ i ∈ J, ‖⟪expVec N t i, x⟫‖ ^ 2)
          =
        (∑ i ∈ J,
          ‖∑ n ∈ (Finset.univ : Finset (Fin N)),
              a n * SSU.Engines.TypeII.e (-t * (i : ℝ) * ((n : ℕ) : ℝ))‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hinner :
          ⟪expVec N t i, x⟫
            =
          ∑ n : Fin N, SSU.Engines.TypeII.e (-t * (i : ℝ) * ((n : ℕ) : ℝ)) * a n := by
        -- `x n = a n` since `x = toLp 2 a`.
        simpa [x, mul_comm, mul_left_comm, mul_assoc] using
          (inner_expVec_eq_sum_univ (N := N) (t := t) (z := i) (x := x))
      -- Convert the `Fin`-sum to a `Finset.univ` sum.
      have hsum (f : Fin N → ℂ) :
          (∑ n : Fin N, f n) = ∑ n ∈ (Finset.univ : Finset (Fin N)), f n := by
        simp
      -- Also commute the scalar factors so the summand matches `a n * e(phase i n)`.
      have hinner' :
          ⟪expVec N t i, x⟫
            =
          ∑ n ∈ (Finset.univ : Finset (Fin N)),
            a n * SSU.Engines.TypeII.e (-t * (i : ℝ) * ((n : ℕ) : ℝ)) := by
        -- First rewrite via `hinner`, then switch `∑ n : Fin N` to `∑ n ∈ univ`,
        -- and finally commute the product in the summand.
        calc
          ⟪expVec N t i, x⟫
              = ∑ n : Fin N, SSU.Engines.TypeII.e (-t * (i : ℝ) * ((n : ℕ) : ℝ)) * a n := hinner
          _ = ∑ n ∈ (Finset.univ : Finset (Fin N)),
                SSU.Engines.TypeII.e (-t * (i : ℝ) * ((n : ℕ) : ℝ)) * a n := by
                simpa using (hsum (fun n => SSU.Engines.TypeII.e (-t * (i : ℝ) * ((n : ℕ) : ℝ)) * a n)).symm
          _ = ∑ n ∈ (Finset.univ : Finset (Fin N)),
                a n * SSU.Engines.TypeII.e (-t * (i : ℝ) * ((n : ℕ) : ℝ)) := by
                refine Finset.sum_congr rfl ?_
                intro n hn
                ring
      simpa [hinner']
    -- RHS: `‖a‖^2` is a sum of squares in Euclidean space.
    have hRHS :
        ‖x‖ ^ 2 = ∑ n : Fin N, ‖a n‖ ^ 2 := by
      simpa [x] using (EuclideanSpace.norm_sq_eq (x := x))
    -- Finish.
    -- (Unfold `FiniteLargeSieve.bound` target and use the two rewrites.)
    -- The remaining `Finset.univ` sums are definitional.
    simpa [hLHS, hRHS, FiniteLargeSieve] using hprimal

/-- Optional simplification: the Crow constant `C` in `finiteLargeSieve_of_distBound` admits a
polylog-style bound via `harmonic_le_one_add_log`.

This is not used by the core SSU plumbing yet, but it is convenient when matching the TeX-style
`(1 + log R)` losses. -/
theorem finiteLargeSieve_of_distBound_C_le_one_add_log
    (J : Finset ℤ) (N : ℕ) (t : ℝ) (R : ℕ)
    (hDist : ∀ i ∈ J, ∀ j ∈ J, SSU.Hilbert.distZ i j ≤ R)
    (ht : |t| * (R : ℝ) ≤ (1 / 2 : ℝ))
    (ht0 : t ≠ 0) :
    (finiteLargeSieve_of_distBound (J := J) (N := N) (t := t) (R := R)
        (hDist := hDist) (ht := ht) (ht0 := ht0)).C
      ≤
    (N : ℝ) + (1 / |t|) * (1 + Real.log R) := by
  classical
  -- Expand `C` and bound the `∑_{d=1..R} aMV` term by `((1/(2|t|))*(1+log R))`.
  have hsum :=
    MV.sum_aMV_Icc_le_one_add_log (N := N) (t := t) (R := R) ht0
  have htabs0 : (|t| : ℝ) ≠ 0 := abs_ne_zero.2 ht0
  have htwo : (2 : ℝ) * (1 / (2 * |t|)) = (1 / |t| : ℝ) := by
    field_simp [htabs0]
  have hsum2 :
      (2 : ℝ) * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))
        ≤
      (2 : ℝ) * ((1 / (2 * |t|)) * (1 + Real.log R)) := by
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hsum' :
      (2 : ℝ) * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ))
        ≤
      (1 / |t|) * (1 + Real.log R) := by
    set L : ℝ := (1 + Real.log R)
    have hrew :
        (2 : ℝ) * ((1 / (2 * |t|)) * L)
          =
        (1 / |t|) * L := by
      have hcong :
          ((2 : ℝ) * (1 / (2 * |t|))) * L = (1 / |t|) * L := by
        simpa [mul_assoc] using congrArg (fun c : ℝ => c * L) htwo
      calc
        (2 : ℝ) * ((1 / (2 * |t|)) * L)
            =
          ((2 : ℝ) * (1 / (2 * |t|))) * L := by
            simpa [mul_assoc] using (mul_assoc (2 : ℝ) (1 / (2 * |t|)) L).symm
        _ = (1 / |t|) * L := hcong
    exact hsum2.trans (le_of_eq hrew)

  have hC :
      (finiteLargeSieve_of_distBound (J := J) (N := N) (t := t) (R := R)
          (hDist := hDist) (ht := ht) (ht0 := ht0)).C
        =
      (N : ℝ) + (2 : ℝ) * (∑ d ∈ Finset.Icc 1 R, (aMV N t d : ℝ)) := by
    simp [finiteLargeSieve_of_distBound, aMV, add_assoc, mul_assoc]

  -- Combine `hC` with `hsum'`.
  -- (The diagonal term is exactly `N` since `aMV N t 0 = N` by definition.)
  rw [hC]
  exact add_le_add_left hsum' (N : ℝ)

end MV

end
end LargeSieve
end Engines
end SSU
