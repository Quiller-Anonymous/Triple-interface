# Turnkey major arc audit (Steps 1–2)

This note records the **current remaining obligations** to eliminate the remaining major-arc
assumptions and end with a certificate-checked proof.

## What “done” means

`Goldbach/Cert/TurnkeyMajorArcCanonSpec.lean` now constructs `turnkeyMajorArcCanon`
from the `Q0` certificate route. The remaining analytic assumptions are isolated as axioms in:

- `Goldbach/Cert/MajorArcModules/Q0TwoBoundsSpec.lean` (`q0Minor_energy`, `q0Major_bound`).

You can confirm this directly with:

`lake env lean --stdin`:

```lean
import Goldbach.Cert.MajorArcEvalOnWindowCanonSpec
import Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec

#print axioms Goldbach.Cert.MajorArcEvalOnWindowCanonSpec.major_arc_eval_on_window_canon
```

which currently reports (in addition to standard classical/propext/trust axioms) the two
project-specific axioms:
`Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.q0Major_bound` and
`Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.q0Minor_energy`.

## Fixed reduction route (Step 2)

We commit to the `Q0` route with canonical parameter:

- `Δ = 1` (see `Goldbach/Cert/MajorArcModules/TurnkeyRouteQ0.lean:31`).

The turnkey proof is reduced using:

- `Goldbach/Cert/MajorArcModules/TurnkeyFromQ0.lean`
- `Goldbach/Cert/MajorArcModules/TurnkeyFromCorrIntegral.lean`

to two uniform analytic bounds `ε₁, ε₂` plus the purely numeric inequality
`(1/135200) * (ε₁+ε₂) ≤ δ_major_canon`.

## Remaining analytic obligations (Step 1)

At `Δ = 1`, the only missing analytic content to get `TurnkeyMajorArcCanon` is:

1. **`ε₁` (Q0-complement / minor piece):**
   A uniform bound on `‖corr_integral X N - corr_integral_major_Q0 X N Δ‖`
   on the canonical window.

2. **`ε₂` (Q0 major deviation):**
   A uniform bound on `‖corr_integral_major_Q0 X N Δ - corrModel N‖`
   on the canonical window.

These are packaged as a single interface in:

- `Goldbach/Cert/MajorArcModules/TurnkeyRouteQ0.lean:58` (`TwoBounds`).

For `ε₁`, `Goldbach/Cert/MajorArcModules/Q0MinorBound.lean` now supports two certificate-friendly
routes:
- pointwise bounds on `expSum` on `(majorArcSetQ0)ᶜ` (legacy, very strong), and
- an `ℓ²`/TT* “energy” bound over the finite `N`-window (often a better match for large-sieve/AO-style engines).

## Certificate boundary (numbers only)

The “generated artifact” side is intended to stay purely in `ℚ`:

- `Goldbach/Cert/MajorArcModules/Q0Certificate.lean`

The generator should output a `Q0Cert` and a proof `cert.Valid` by `native_decide`.
No `Real.log` should appear in generated data; the only stable `Real.log` facts are re-exported in:

- `Goldbach/Cert/MajorArcModules/NumericFacts.lean`.

## Notes

- The BMOR ψ-bound itself is still recorded as a conventional axiom in
  `Goldbach/Cert/ExplicitPNTinAP_BMOR.lean`. This audit is only about eliminating the *project*
  major-arc boundary axiom (`turnkeyMajorArcCanon`).
