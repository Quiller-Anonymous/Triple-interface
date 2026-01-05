-- Twin/SW/SmoothMajorArc.lean
import Mathlib
import Twin.SW.PartialSummation
import Twin.SW.SiegelWalfisz
import Twin.SW.Characters

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-!
## Siegel–Walfisz ⇒ smoothed twist (conventional analysis)

This file records the “SW ⇒ smoothed windowed twist” upgrade used in major-arc analysis.

Status: conventional.  We keep the statement in Lean (so it can be referenced uniformly),
but postulate it for now.  The intended derivation is:
`SiegelWalfisz.bound` (twisted ψ) + `PartialSummation.smooth_upgrade_centered`.
-/

/--
**Siegel–Walfisz ⇒ smoothed twisted bound (per character).**

Fix `A,B > 0`. Assume uniform Siegel–Walfisz for the twisted Chebyshev function `ψ(x,χ)`
in the range `1 ≤ q ≤ (log X)^B`. Then for any character `χ mod q`, any `X ≥ 3`, any scale
`H ≥ 1`, and any admissible window `W` (compact support + Lipschitz, packaged as
`SmoothWindow W`), the smoothed sum satisfies a decay bound of the same shape.

This statement is used as a standard intermediate brick in the classical major-arc evaluation.
-/
axiom SW_to_smoothed_twist
  {A B : ℝ} [SW : SiegelWalfisz A B]
  {q : ℕ} (χ : DirichletCharacter q)
  {X H : ℝ} (hX : 3 ≤ X) (hH : 1 ≤ H)
  (hq : 1 ≤ q ∧ (q : ℝ) ≤ Real.rpow (Real.log X) B)
  {W : ℝ → ℝ} (Wok : SmoothWindow W) :
  ‖∑' n : ℕ,
      (Complex.ofReal (ArithmeticFunction.vonMangoldt n) * χ.evalNat n)
        * Complex.ofReal (W (((n : ℝ) - X) / H))‖
    ≤ ((Wok.c2 - Wok.c1) * Wok.L + 2 * Wok.M)
      * SW.C
      * (X / Real.rpow (Real.log X) A)

end Twin.SW

