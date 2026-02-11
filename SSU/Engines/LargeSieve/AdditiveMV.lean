import SSU.Engines.TypeII
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Additive (Montgomery–Vaughan style) large sieve: starter lemmas.

This file begins the TeX-strength proof effort for `05b_SSU.tex` Steps 3–4.
We start with the one-dimensional exponential-sum estimates needed to control the Gram matrix of
the exponential system `u ↦ e(u * θ)`.

Design goals:
* stay in the real-frequency convention used by the SSU Type-II engine (`SSU.Engines.TypeII.e`);
* avoid `X^ε`; allow polylog losses later via crude harmonic sums;
* keep hypotheses explicit (e.g. “no wrap-around” bounds like `|θ| ≤ 1/2`).
-/

namespace SSU
namespace Engines
namespace LargeSieve

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

/-!
## Basic bounds for `‖e(t) - 1‖`

For `|t| ≤ 1/2` we have the clean lower bound `‖e(t) - 1‖ ≥ 4 * |t|`,
coming from `‖exp(Ix) - 1‖ = ‖2 * sin(x/2)‖` and Jordan’s inequality.
-/

theorem norm_e_sub_one_eq (t : ℝ) :
    ‖e t - (1 : ℂ)‖ = 2 * |Real.sin (Real.pi * t)| := by
  -- `‖exp (I * x) - 1‖ = ‖2 * sin (x/2)‖` with `x = 2πt`.
  have h := (Complex.norm_exp_I_mul_ofReal_sub_one (x := (2 * Real.pi * t)))
  -- Rewrite the LHS into the `e` convention, and the RHS as `2*|sin(πt)|`.
  have hlhs :
      Complex.exp (Complex.I * (2 * Real.pi * t)) = e t := by
    -- purely commutative ring arithmetic in the exponent
    simp [TypeII.e, mul_assoc, mul_left_comm, mul_comm]
  have hrhs :
      ‖(2 * Real.sin ((2 * Real.pi * t) / 2))‖ = 2 * |Real.sin (Real.pi * t)| := by
    -- `‖r‖ = |r|` for `r : ℝ`, and `(2πt)/2 = πt`.
    simp [Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm, mul_comm, mul_div_assoc]
  -- Combine.
  simpa [hlhs, hrhs, sub_eq_add_neg] using h

theorem norm_e_sub_one_lower_of_abs_le_half {t : ℝ} (ht : |t| ≤ (1 / 2 : ℝ)) :
    (4 * |t|) ≤ ‖e t - (1 : ℂ)‖ := by
  -- Rewrite via `sin(π t)` and apply Jordan on `|π t| ≤ π/2`.
  have hpi : |Real.pi * t| ≤ Real.pi / 2 := by
    -- multiply `|t| ≤ 1/2` by `π ≥ 0`.
    have hπ : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have := mul_le_mul_of_nonneg_left ht hπ
    simpa [abs_mul, abs_of_nonneg hπ, mul_assoc, mul_left_comm, mul_comm] using this
  have hsin : (2 / Real.pi) * |Real.pi * t| ≤ |Real.sin (Real.pi * t)| :=
    Real.mul_abs_le_abs_sin (x := Real.pi * t) hpi
  have hsin' : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    -- simplify `(2/π) * |π t| = 2*|t|`.
    have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    calc
      2 * |t| = (2 / Real.pi) * (Real.pi * |t|) := by
        field_simp [hπ0]
      _ = (2 / Real.pi) * |Real.pi * t| := by
        simp [abs_mul, abs_of_pos Real.pi_pos, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ |Real.sin (Real.pi * t)| := hsin
  -- Finish by converting to the complex norm statement.
  calc
    4 * |t| = 2 * (2 * |t|) := by ring
    _ ≤ 2 * |Real.sin (Real.pi * t)| := by gcongr
    _ = ‖e t - (1 : ℂ)‖ := by
          simpa [norm_e_sub_one_eq, Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm, mul_comm]

/-!
## Geometric-sum bound for `∑_{n < N} e(n*t)`

We record the standard estimate
`‖∑_{n=0}^{N-1} e(n*t)‖ ≤ min N (1 / (2*|t|))` under `|t| ≤ 1/2` and `t ≠ 0`.

This is the basic analytic input for the additive large sieve via row-sum / Schur bounds.
-/

theorem norm_sum_range_e_mul_le_min (N : ℕ) {t : ℝ} (ht : |t| ≤ (1 / 2 : ℝ)) (ht0 : t ≠ 0) :
    ‖∑ n ∈ Finset.range N, e (t * n)‖
      ≤ min (N : ℝ) (1 / (2 * |t|)) := by
  classical
  -- Trivial bound by triangle inequality: `≤ N`.
  have htriv : ‖∑ n ∈ Finset.range N, e (t * n)‖ ≤ (N : ℝ) := by
    have h1 :
        ‖∑ n ∈ Finset.range N, e (t * (n : ℝ))‖
          ≤ ∑ n ∈ Finset.range N, ‖e (t * (n : ℝ))‖ := by
            simpa using norm_sum_le (Finset.range N) (fun n => e (t * (n : ℝ)))
    -- `‖e(·)‖ = 1`.
    have h2 : (∑ n ∈ Finset.range N, ‖e (t * (n : ℝ))‖) = N := by
      simp [norm_e]
    exact h1.trans (by simpa [h2])
  -- Nontrivial bound via geometric sum formula.
  have hz1 : (e t : ℂ) ≠ 1 := by
    intro h
    have hlow : (4 * |t|) ≤ ‖e t - (1 : ℂ)‖ := norm_e_sub_one_lower_of_abs_le_half (t := t) ht
    have hn0 : ‖e t - (1 : ℂ)‖ = 0 := by simpa [h]
    have hle0 : 4 * |t| ≤ 0 := le_trans hlow (by simpa [hn0])
    have habs_nonneg : 0 ≤ |t| := abs_nonneg t
    have habs_le0 : |t| ≤ 0 := by nlinarith
    have : |t| = 0 := le_antisymm habs_le0 habs_nonneg
    exact ht0 (by simpa [abs_eq_zero] using this)
  have hgeom :
      (∑ n ∈ Finset.range N, e (t * n)) =
        ((e t) ^ N - 1) / ((e t) - 1) := by
    -- `∑_{n < N} (e t)^n = ( (e t)^N - 1)/(e t - 1)`.
    -- Also `e (t*n) = (e t)^n`.
    have hepow : ∀ n : ℕ, e (t * (n : ℝ)) = (e t) ^ n := by
      intro n
      -- `e (t*n) = exp(2π i t)^n` via `exp (n * z) = (exp z)^n`.
      unfold TypeII.e
      calc
        Complex.exp (2 * Real.pi * Complex.I * (↑(t * (n : ℝ)) : ℂ))
            = Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I * t)) := by
                -- rearrange and push the `n` into the scalar factor
                congr 1
                simp [mul_assoc, mul_left_comm, mul_comm]
        _ = Complex.exp (2 * Real.pi * Complex.I * t) ^ n := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (Complex.exp_nat_mul (2 * Real.pi * Complex.I * t) n)
    -- Rewrite the sum to a geometric sum and apply `geom_sum_eq`.
    calc
      (∑ n ∈ Finset.range N, e (t * (n : ℝ)))
          = ∑ n ∈ Finset.range N, (e t : ℂ) ^ n := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              simpa [hepow n]
      _ = ((e t : ℂ) ^ N - 1) / ((e t : ℂ) - 1) := by
            simpa [sub_eq_add_neg] using (geom_sum_eq (x := (e t : ℂ)) (by
              -- `x ≠ 1`:
              simpa using hz1) N)
  have hnontriv :
      ‖∑ n ∈ Finset.range N, e (t * n)‖ ≤ 1 / (2 * |t|) := by
    -- Use the geometric formula and bound numerator by `2`, denominator below by `4|t|`.
    have hden :
        (4 * |t|) ≤ ‖(e t : ℂ) - 1‖ := by
      -- `‖e t - 1‖ ≥ 4|t|`, and `e t - 1 = (e t : ℂ) - 1`.
      simpa using (norm_e_sub_one_lower_of_abs_le_half (t := t) ht)
    have htpos : 0 < |t| := abs_pos.2 ht0
    have hdenpos : 0 < ‖(e t : ℂ) - 1‖ :=
      lt_of_lt_of_le (by nlinarith [htpos]) hden
    -- Bound numerator.
    have hnum : ‖((e t : ℂ) ^ N - 1)‖ ≤ 2 := by
      -- `‖z^N - 1‖ ≤ ‖z^N‖ + ‖1‖ = 1 + 1`.
      have hz : ‖(e t : ℂ) ^ N‖ = 1 := by
        -- `‖e t‖ = 1`.
        simpa [norm_e] using (norm_pow (e t) N)
      calc
        ‖(e t : ℂ) ^ N - 1‖ ≤ ‖(e t : ℂ) ^ N‖ + ‖(1 : ℂ)‖ := by
          simpa [sub_eq_add_neg] using norm_add_le ((e t : ℂ) ^ N) (-1)
        _ = 2 := by
          -- `‖z^N‖ = 1` and `‖1‖ = 1`.
          calc
            (‖(e t : ℂ) ^ N‖ + ‖(1 : ℂ)‖ : ℝ) = 1 + 1 := by simp [hz, norm_one]
            _ = 2 := by norm_num
    -- Put together using `‖a/b‖ = ‖a‖/‖b‖`.
    have : ‖((e t : ℂ) ^ N - 1) / ((e t : ℂ) - 1)‖ ≤ 2 / (4 * |t|) := by
      -- `‖a / b‖ = ‖a‖ / ‖b‖`.
      have hdiv :
          ‖((e t : ℂ) ^ N - 1) / ((e t : ℂ) - 1)‖ =
            ‖(e t : ℂ) ^ N - 1‖ / ‖(e t : ℂ) - 1‖ := by
        simpa using (norm_div ((e t : ℂ) ^ N - 1) ((e t : ℂ) - 1))
      rw [hdiv]
      -- First bound numerator by `2`.
      have hnum' : ‖(e t : ℂ) ^ N - 1‖ / ‖(e t : ℂ) - 1‖ ≤ 2 / ‖(e t : ℂ) - 1‖ := by
        have : ‖(e t : ℂ) ^ N - 1‖ ≤ 2 := hnum
        exact (div_le_div_of_nonneg_right this (le_of_lt hdenpos))
      -- Then bound `1/‖den‖` by `1/(4|t|)` using `4|t| ≤ ‖den‖`.
      have hrecip :
          1 / ‖(e t : ℂ) - 1‖ ≤ 1 / (4 * |t|) := by
        have ht4 : 0 < 4 * |t| := by nlinarith [htpos]
        -- `4|t| ≤ ‖den‖` gives `1/‖den‖ ≤ 1/(4|t|)`.
        simpa [one_div] using (one_div_le_one_div_of_le ht4 hden)
      have hden' : 2 / ‖(e t : ℂ) - 1‖ ≤ 2 / (4 * |t|) := by
        -- Multiply the reciprocal inequality by `2`.
        have : (2 : ℝ) * (1 / ‖(e t : ℂ) - 1‖) ≤ (2 : ℝ) * (1 / (4 * |t|)) := by
          gcongr
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      exact hnum'.trans hden'
    -- Use `hgeom` to rewrite the sum and simplify `2/(4|t|) = 1/(2|t|)`.
    have hs : ‖∑ n ∈ Finset.range N, e (t * n)‖ =
        ‖((e t) ^ N - 1) / ((e t) - 1)‖ := by
      simp [hgeom]
    have : ‖∑ n ∈ Finset.range N, e (t * n)‖ ≤ 2 / (4 * |t|) := by simpa [hs] using this
    -- simplify RHS
    have hconst : (2 / (4 * |t|) : ℝ) = 1 / (2 * |t|) := by
      field_simp
      ring
    simpa [hconst] using this
  -- Combine into a `min`.
  exact le_min htriv hnontriv

/-- A convenience specialization for differences: apply `norm_sum_range_e_mul_le_min` to `t*(i-j)`. -/
theorem norm_sum_range_e_mul_sub_le_min (N : ℕ) (t : ℝ) (i j : ℤ)
    (ht : |t * ((i - j : ℤ) : ℝ)| ≤ (1 / 2 : ℝ)) (ht0 : t * ((i - j : ℤ) : ℝ) ≠ 0) :
    ‖∑ n ∈ Finset.range N, e (t * ((i - j : ℤ) : ℝ) * n)‖
      ≤ min (N : ℝ) (1 / (2 * |t * ((i - j : ℤ) : ℝ)|)) := by
  -- just reassociate to match the previous lemma’s `t * n` form
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (norm_sum_range_e_mul_le_min (N := N) (t := t * ((i - j : ℤ) : ℝ)) ht ht0)

end

end LargeSieve
end Engines
end SSU
