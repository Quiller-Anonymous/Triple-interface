# Turnkey major arc audit (Steps 1–2)

This note records the **current remaining obligations** to eliminate the final major-arc axiom
`Goldbach/Cert/TurnkeyMajorArcCanonSpec.lean` and replace it by a certificate-checked proof.

## What “done” means

Replace:

- `Goldbach/Cert/TurnkeyMajorArcCanonSpec.lean:26` (`axiom turnkeyMajorArcCanon`)

by an axiom-free definition/theorem producing:

- `Goldbach.Cert.MajorArcModules.TurnkeyCanon.TurnkeyMajorArcCanon`.

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

