import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic

/-!
03_TFA.tex — weight / cutoff interface (TeX-faithful).

In the TeX, the cutoff `W(d/D, n/N)` is treated as a fixed smooth compactly-supported function on
`ℝ²`, equal to `1` on the working dyadic box and supported in a slightly larger box (typically
`[1/2,2]²`). It is introduced in the “TFA” section and then reused in 05_BG.tex and 05b_SSU.tex.

For SSU, we *do not* commit to a closed-form definition of `W`. We package exactly the properties
used downstream (support, normalization, measurability/boundedness) and treat `W` as data.
-/

namespace SSU
namespace Engines
namespace TFA

open scoped BigOperators

noncomputable section

/-- A TeX-style smooth cutoff `W : ℝ×ℝ → ℂ`, packaged by the properties SSU uses. -/
structure Weight where
  /-- The cutoff as a function on `ℝ²` (TeX: `W(d/D, n/N)`). -/
  W : (ℝ × ℝ) → ℂ
  /-- Support control (TeX: `W ∈ C_c^∞([1/2,2]²)`; we only record the set inclusion). -/
  support_subset :
    Function.support W ⊆ Set.prod (Set.Icc ((1 : ℝ) / 2) 2) (Set.Icc ((1 : ℝ) / 2) 2)
  /-- Normalization: `W = 1` on the working dyadic box `[1,2]²`. -/
  one_on :
    ∀ x : ℝ × ℝ, x.1 ∈ Set.Icc (1 : ℝ) 2 → x.2 ∈ Set.Icc (1 : ℝ) 2 → W x = 1

/--
Separable (product) dyadic cutoff, matching the standard “product of 1D bumps” convention:

`W(x,y) = W_D(x) * W_N(y)`.

This is the additional hypothesis needed for the exact Toeplitz regrouping lemma in `05_BG.tex`
(the “group-by-product” step can require swapping the `n` and `n'` indices, which must not change
the weight).

We record separability by providing explicit factors `W_D, W_N` and the definitional equation.
We intentionally keep the *same* support/normalization fields as `Weight` (2D), so downstream
proofs can depend only on `Weight` while the Toeplitz identity lemma can demand `SeparableWeight`.
-/
structure SeparableWeight extends Weight where
  /-- The `d`-side 1D cutoff factor. -/
  W_D : ℝ → ℂ
  /-- The `n`-side 1D cutoff factor. -/
  W_N : ℝ → ℂ
  /-- Separable factorization. -/
  W_eq : ∀ x : ℝ × ℝ, W x = W_D x.1 * W_N x.2

namespace SeparableWeight

variable (W : SeparableWeight)

theorem W_eq_mul (x : ℝ × ℝ) : W.W x = W.W_D x.1 * W.W_N x.2 :=
  W.W_eq x

end SeparableWeight

/-
## Balanced bank mask (03_TFA.tex, Eq. (balanced-bank))

The TeX defines a “double-centered” mask `𝓑(d,n)` from a dyadic weight `W(d/D,n/N)` by subtracting
its averages in the `d` and `n` directions, and adding back the global average.

This is purely finite-sum algebra; no smoothness is used in the cancellation lemmas.
-/

namespace BalancedBank

/-- Swap a double `Finset` sum (deterministic, avoids `Finset.sum_comm` in this toolchain). -/
theorem sum_sum_swap {𝓓 𝓝 : Finset ℤ} (f : ℤ → ℤ → ℂ) :
    (∑ d ∈ 𝓓, ∑ n ∈ 𝓝, f d n) = ∑ n ∈ 𝓝, ∑ d ∈ 𝓓, f d n := by
  classical
  -- Prove by induction on `𝓓`.
  refine 𝓓.induction_on ?base ?step
  · simp
  · intro a s ha hs
    -- Expand both sides for `insert a s` and use the induction hypothesis on `s`.
    simp [ha, hs, Finset.sum_add_distrib]

/--
Balanced mask associated to a discrete weight `W(d,n)` on a rectangle `𝓓 × 𝓝`:

`B(d,n) := W(d,n)
  - (1/#𝓓) * ∑_{d'∈𝓓} W(d',n)
  - (1/#𝓝) * ∑_{n'∈𝓝} W(d,n')
  + (1/(#𝓓#𝓝)) * ∑_{d'∈𝓓} ∑_{n'∈𝓝} W(d',n')`.

This mirrors `03_TFA.tex` Eq. `(balanced-bank)`, with `#` = `Finset.card`.
-/
noncomputable def mask (𝓓 𝓝 : Finset ℤ) (W : ℤ → ℤ → ℂ) (d n : ℤ) : ℂ :=
  W d n
    - ((𝓓.card : ℂ)⁻¹) * (∑ d' ∈ 𝓓, W d' n)
    - ((𝓝.card : ℂ)⁻¹) * (∑ n' ∈ 𝓝, W d n')
    + (((𝓓.card : ℂ) * (𝓝.card : ℂ))⁻¹) * (∑ d' ∈ 𝓓, ∑ n' ∈ 𝓝, W d' n')

/-!
TODO(03_TFA.tex, Lemma `alias-delta2`):
prove the “alias suppression” identities for `mask`, i.e.

* `∑_{n∈𝓝} mask(d,n) = 0` for every `d`, and
* `∑_{d∈𝓓} mask(d,n) = 0` for every `n`,

and the induced orthogonality to weights depending only on one variable.

These are deterministic finite-sum identities. We prove them in
`SSU/Engines/TFAWeightAliasSuppression.lean` to keep this file’s imports lightweight.
-/

end BalancedBank

end

end TFA
end Engines
end SSU
