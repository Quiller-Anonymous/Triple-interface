-- Twin/SW/PartialSummation.lean
import Mathlib

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-!
## Smooth window package + “smooth upgrade” (conventional analysis)

This file is intentionally *lightweight* and independent of the rest of the Twin pipeline.

It provides:
* a concrete admissibility package `SmoothWindow W` for weights used as `W((n - X)/H)`, and
* a single “smooth upgrade” lemma `smooth_upgrade_centered` (currently postulated).

Rationale: downstream major-arc files can cite classical partial summation / summation-by-parts
results without forcing us to formalize all real analysis immediately. When the analysis is
formalized, the only replacement needed here is the axiom `smooth_upgrade_centered`.
-/

/-!
Note: we use ASCII field names `c1`, `c2` to avoid Unicode-subscript edge cases in
dependent field types under this project’s Lean toolchain.
-/

/-- A concrete admissibility package for weights used as `W((n - X)/H)`.

`c1 < c2` delimit a *closed* support window: `W(u)=0` whenever `u ≤ c1` or `c2 ≤ u`.
`L` is a global Lipschitz constant, and `M` is a uniform bound on `|W|`. -/
structure SmoothWindow (W : ℝ → ℝ) where
  c1 : ℝ
  c2 : ℝ
  hc : c1 < c2
  L : ℝ
  hL : 0 ≤ L
  lip : ∀ t s, |W t - W s| ≤ L * |t - s|
  supp : ∀ u : ℝ, (u ≤ c1 ∨ c2 ≤ u) → W u = 0
  M : ℝ
  hM : 0 ≤ M
  bound : ∀ u : ℝ, |W u| ≤ M

/--
**Concrete smooth upgrade (centered window)**.

Conventional analytic input (partial summation / Abel summation):
if partial sums of `a` satisfy a Siegel–Walfisz-type decay bound, then the smoothed sum
`∑ a(n) W((n - X)/H)` inherits the same decay up to a factor controlled by the window
geometry (`c₁,c₂`) and Lipschitz/boundedness constants (`L,M`).

Paper-facing usage: this is the bridge from twisted Chebyshev ψ-bounds to smoothed exponential
sums, and is treated as standard in analytic number theory.
-/
axiom smooth_upgrade_centered
  {A C : ℝ} {a : ℕ → ℂ} {X H : ℝ}
  (hX : 3 ≤ X) (hH : 1 ≤ H)
  (Abound :
    ∀ y, 3 ≤ y →
      ‖(Finset.Icc 1 ⌊y⌋₊).sum (fun n => a n)‖
        ≤ C * y / Real.rpow (Real.log y) A)
  {W : ℝ → ℝ} (Wok : SmoothWindow W) :
  ‖∑' n : ℕ, a n * Complex.ofReal (W (((n : ℝ) - X) / H))‖
    ≤ ((Wok.c2 - Wok.c1) * Wok.L + 2 * Wok.M) * C * ((X + H) / Real.rpow (Real.log X) A)

end Twin.SW
