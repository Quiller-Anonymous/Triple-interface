import SSU.Engines.LargeSieve.AdditiveMV
import SSU.Hilbert.DistZ
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Montgomery–Vaughan (additive large sieve) — exponential Gram bounds.

This file is the next “analytic micro-step” after `AdditiveMV`:
we bound the Gram entries of the exponential vectors on an integer interval `Icc a b`.

This is TeX-faithful in the sense that it produces the `min(N, 1/(|t|*d))`-type decay in the
index difference, which is then fed into the deterministic `ℤ` row-sum/Crow machinery.
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

namespace MV

open scoped ComplexConjugate

/-!
## Interval exponential sums
-/

/-- Rewrite an `Icc`-sum as a `range`-sum via the canonical `Int` interval map. -/
theorem sum_Icc_eq_sum_range {α : Type*} [AddCommMonoid α]
    (a b : ℤ) (f : ℤ → α) :
    (∑ u ∈ (Finset.Icc a b), f u)
      =
    ∑ n ∈ Finset.range (b + 1 - a).toNat, f (a + n) := by
  classical
  -- Expand `Icc` as a mapped `range` (`Mathlib.Data.Int.Interval`).
  -- The embedding sends `n` to `a + n`.
  simpa [Int.Icc_eq_finset_map, Finset.sum_map, Function.Embedding.trans_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]

/-- A norm bound for the exponential sum over `Icc a b`. -/
theorem norm_sum_Icc_e_mul_le_min (a b : ℤ) (t : ℝ) (h : ℤ)
    (ht : |t * ((h : ℤ) : ℝ)| ≤ (1 / 2 : ℝ)) (ht0 : t * ((h : ℤ) : ℝ) ≠ 0) :
    ‖∑ u ∈ (Finset.Icc a b), e (t * ((u : ℤ) : ℝ) * ((h : ℤ) : ℝ))‖
      ≤ min ((b + 1 - a).toNat : ℝ) (1 / (2 * |t * ((h : ℤ) : ℝ)|)) := by
  classical
  -- Rewrite to a `range` sum with a unimodular prefactor, then apply the `range` lemma.
  have hsum :
      (∑ u ∈ (Finset.Icc a b), e (t * ((u : ℤ) : ℝ) * ((h : ℤ) : ℝ)))
        =
      e (t * (a : ℝ) * (h : ℝ)) *
        (∑ n ∈ Finset.range (b + 1 - a).toNat, e (t * (h : ℝ) * (n : ℝ))) := by
    -- Use `sum_Icc_eq_sum_range` and factor out the constant phase.
    have :
        (∑ u ∈ (Finset.Icc a b), e (t * ((u : ℤ) : ℝ) * ((h : ℤ) : ℝ)))
          =
        ∑ n ∈ Finset.range (b + 1 - a).toNat,
          e (t * ((a + n : ℤ) : ℝ) * ((h : ℤ) : ℝ)) := by
      simpa [sum_Icc_eq_sum_range] using (sum_Icc_eq_sum_range (a := a) (b := b)
        (f := fun u => e (t * ((u : ℤ) : ℝ) * ((h : ℤ) : ℝ))))
    -- Now simplify the phase: `t*(a+n)*h = t*a*h + t*h*n`.
    -- Pull out `e(t*a*h)` using `Finset.mul_sum`.
    -- (All arithmetic is in `ℝ`, then in the exponent of `e`.)
    -- `e(x+y)=e(x)*e(y)` is available as `e_add`.
    -- We use `simp` to turn `e (x+y)` into `e x * e y`.
    calc
      (∑ u ∈ (Finset.Icc a b), e (t * ((u : ℤ) : ℝ) * ((h : ℤ) : ℝ)))
          =
        ∑ n ∈ Finset.range (b + 1 - a).toNat,
          e (t * ((a + n : ℤ) : ℝ) * ((h : ℤ) : ℝ)) := this
      _ =
        ∑ n ∈ Finset.range (b + 1 - a).toNat,
          e (t * (a : ℝ) * (h : ℝ) + t * (h : ℝ) * (n : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            -- cast `(a+n)` to `ℝ` and expand
            simp [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
              add_comm]
      _ =
        ∑ n ∈ Finset.range (b + 1 - a).toNat,
          (e (t * (a : ℝ) * (h : ℝ)) * e (t * (h : ℝ) * (n : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            simp [TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
      _ =
        e (t * (a : ℝ) * (h : ℝ)) *
          (∑ n ∈ Finset.range (b + 1 - a).toNat, e (t * (h : ℝ) * (n : ℝ))) := by
            simp [Finset.mul_sum, mul_assoc]
  -- Drop the unimodular prefactor in the norm and apply the `range` lemma.
  have hnorm :
      ‖∑ u ∈ (Finset.Icc a b), e (t * ((u : ℤ) : ℝ) * ((h : ℤ) : ℝ))‖
        =
      ‖∑ n ∈ Finset.range (b + 1 - a).toNat, e (t * (h : ℝ) * (n : ℝ))‖ := by
    -- `‖e(...)‖ = 1`.
    have : ‖e (t * (a : ℝ) * (h : ℝ))‖ = 1 := by simp [norm_e]
    simpa [hsum, this] using (norm_mul (e (t * (a : ℝ) * (h : ℝ)))
      (∑ n ∈ Finset.range (b + 1 - a).toNat, e (t * (h : ℝ) * (n : ℝ))))
  -- Now apply the `range` estimate.
  -- (Rewrite the goal to the `range`-sum using `hnorm`.)
  rw [hnorm]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (SSU.Engines.LargeSieve.norm_sum_range_e_mul_le_min
      (N := (b + 1 - a).toNat) (t := t * (h : ℝ)) (ht := ht) (ht0 := ht0))

/-!
## Exponential vectors and their Gram entries

For the additive large sieve, a basic object is the exponential vector
`n ↦ e(t*z*n)` over a finite interval in `n`. The Gram entry is a Dirichlet kernel evaluated at
the difference `z-z'`.
-/

open Complex

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The exponential vector `n ↦ e(t*z*n)` in `EuclideanSpace` (so we have an inner product). -/
def expVec (N : ℕ) (t : ℝ) (z : ℤ) : EuclideanSpace ℂ (Fin N) :=
  -- `EuclideanSpace` is `WithLp 2`, so build it via `WithLp.toLp`.
  WithLp.toLp 2 (fun n : Fin N => e (t * (z : ℝ) * ((n : ℕ) : ℝ)))

theorem inner_expVec_eq_sum_range (N : ℕ) (t : ℝ) (i j : ℤ) :
    ⟪expVec N t i, expVec N t j⟫
      =
    ∑ n ∈ Finset.range N, e (t * ((j - i : ℤ) : ℝ) * (n : ℝ)) := by
  classical
  -- `⟪toLp 2 x, toLp 2 y⟫ = dotProduct y (star x)`.
  -- Simplify `e(t*j*n) * star(e(t*i*n)) = e(t*(j-i)*n)` and rewrite the `Fin`-sum as `range`.
  have star_e (x : ℝ) : star (e x) = e (-x) := by
    simpa using (SSU.Engines.TypeII.AdmissibleKernel.conj_e x)
  have e_add (x y : ℝ) : e x * e y = e (x + y) := by
    -- `e x = exp(2π i x)`.
    simp [SSU.Engines.TypeII.e, Complex.exp_add, mul_add, add_mul, mul_assoc, mul_left_comm,
      mul_comm, add_assoc, add_left_comm, add_comm]

  -- Expand the inner product into a `range` sum.
  -- `inner_toLp_toLp` gives a dot product over `Fin N`.
  have hinnerFin :
      ⟪expVec N t i, expVec N t j⟫
        =
      ∑ n : Fin N,
        e (t * (j : ℝ) * ((n : ℕ) : ℝ)) * star (e (t * (i : ℝ) * ((n : ℕ) : ℝ))) := by
    simp [expVec, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_assoc, mul_left_comm, mul_comm]
  -- Convert the `Fin N` sum into a `range N` sum.
  have hinner :
      ⟪expVec N t i, expVec N t j⟫
        =
      ∑ n ∈ Finset.range N,
        e (t * (j : ℝ) * (n : ℝ)) * star (e (t * (i : ℝ) * (n : ℝ))) := by
    let f : ℕ → ℂ := fun n =>
      e (t * (j : ℝ) * (n : ℝ)) * star (e (t * (i : ℝ) * (n : ℝ)))
    calc
      ⟪expVec N t i, expVec N t j⟫
          =
        ∑ n : Fin N, f (n : ℕ) := by
          -- Just rewrite the summand into `f (n:ℕ)`.
          simpa [f] using hinnerFin
      _ = ∑ n ∈ Finset.range N, f n := by
          -- `Fin.sum_univ_eq_sum_range` is exactly this rewrite.
          simpa using (Fin.sum_univ_eq_sum_range f N)
      _ = ∑ n ∈ Finset.range N,
            e (t * (j : ℝ) * (n : ℝ)) * star (e (t * (i : ℝ) * (n : ℝ))) := by
          simp [f]

  -- Simplify the summand pointwise.
  -- `e(t*j*n) * star(e(t*i*n)) = e(t*(j-i)*n)`.
  refine hinner.trans ?_
  refine Finset.sum_congr rfl ?_
  intro n hn
  have :
      e (t * (j : ℝ) * (n : ℝ)) * star (e (t * (i : ℝ) * (n : ℝ)))
        =
      e (t * ((j - i : ℤ) : ℝ) * (n : ℝ)) := by
    calc
      e (t * (j : ℝ) * (n : ℝ)) * star (e (t * (i : ℝ) * (n : ℝ)))
          =
        e (t * (j : ℝ) * (n : ℝ)) * e (-(t * (i : ℝ) * (n : ℝ))) := by
          simp [star_e]
      _ =
        e ((t * (j : ℝ) * (n : ℝ)) + (-(t * (i : ℝ) * (n : ℝ)))) := by
          simpa [e_add] using (e_add (t * (j : ℝ) * (n : ℝ)) (-(t * (i : ℝ) * (n : ℝ)))).symm
      _ = e (t * ((j - i : ℤ) : ℝ) * (n : ℝ)) := by
          -- linearity in `j-i`
          simp [sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  simpa [this]

theorem norm_inner_expVec_le_min (N : ℕ) (t : ℝ) (i j : ℤ)
    (ht : |t * ((j - i : ℤ) : ℝ)| ≤ (1 / 2 : ℝ)) (ht0 : t * ((j - i : ℤ) : ℝ) ≠ 0) :
    ‖⟪expVec N t i, expVec N t j⟫‖
      ≤ min (N : ℝ) (1 / (2 * |t * ((j - i : ℤ) : ℝ)|)) := by
  -- Reduce to the `range` exponential-sum bound.
  have hinner := inner_expVec_eq_sum_range (N := N) (t := t) (i := i) (j := j)
  -- `‖∑ e( (t*(j-i)) * n )‖` is exactly the `AdditiveMV` estimate.
  simpa [hinner, mul_assoc, mul_left_comm, mul_comm] using
    (SSU.Engines.LargeSieve.norm_sum_range_e_mul_le_min
      (N := N) (t := t * ((j - i : ℤ) : ℝ)) (ht := ht) (ht0 := ht0))

/-!
## Converting `|t * (j-i)|` into `|t| * distZ(i,j)`

This is the algebraic normalization needed to package the Gram entry bounds in the SSU
`distZ`-style interface (weights depending only on `Int.natAbs (i-j)`).
-/

theorem abs_mul_sub_eq_abs_mul_distZ (t : ℝ) (i j : ℤ) :
    |t * ((j - i : ℤ) : ℝ)| = |t| * (SSU.Hilbert.distZ i j : ℝ) := by
  -- Convert the distance into a real absolute value of the integer difference.
  have hdist : (SSU.Hilbert.distZ i j : ℝ) = |((j - i : ℤ) : ℝ)| := by
    -- `distZ i j = (i-j).natAbs = (j-i).natAbs`.
    have hnat : SSU.Hilbert.distZ i j = (j - i).natAbs := by
      -- `j - i = -(i - j)` and `natAbs (-x) = natAbs x`.
      dsimp [SSU.Hilbert.distZ]
      calc
        (i - j).natAbs = (-(i - j)).natAbs := by
          simpa using (Int.natAbs_neg (i - j)).symm
        _ = (j - i).natAbs := by
          have : (-(i - j) : ℤ) = j - i := by abel
          simpa [this]
    -- Cast `natAbs` to `ℝ` as `abs` of the cast.
    -- `Nat.cast_natAbs` gives `↑(natAbs) = ↑|·|` and `Int.cast_abs` gives `↑|·| = |↑·|`.
    calc
      (SSU.Hilbert.distZ i j : ℝ)
          = ((j - i).natAbs : ℝ) := by simpa [hnat]
      _ = (|j - i| : ℝ) := by simpa using (Nat.cast_natAbs (j - i) : ((j - i).natAbs : ℝ) = _)
      _ = |((j - i : ℤ) : ℝ)| := by simpa using (Int.cast_abs (a := (j - i)) : ((|j - i| : ℤ) : ℝ) = _)
  -- Finish.
  simp [abs_mul, hdist, mul_assoc, mul_left_comm, mul_comm]

end MV

end
end LargeSieve
end Engines
end SSU
