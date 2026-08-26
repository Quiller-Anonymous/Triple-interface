# Route A Post-Cert Integration Audit

Date: 2026-08-24

## Current Build Target

The live CI target is:

`Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert`

This module exports two top-level Route A surfaces:

- `centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_routeA_remaining_certificates`
- `centeredNormalizedSigmaTruncWindowEnergyTargetAt_X0_of_routeA_tail_and_boundary_certificates`

Both prove:

`CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795`

The direct imports are:

- `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainFinal`
- `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualFinal`

## Static Import Audit

A local source-level import-closure scan of
`Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert` found:

- No missing project-source imports.
- No import cycles.
- The source archive manifest count matches the archive count:
  `111422` listed generated source paths and `111422` archived source paths.

This removes the most common avoidable CI failure class: missing generated sources or local import
cycles inside the current Route A target.

## Key Integration Finding

No non-generated higher-level Goldbach module currently imports
`Q0MinorZeroModeNormalizedAverageX0Cert`.

That means completion of the current cert target is necessary but not automatically sufficient for
the higher Goldbach route. After the target builds, we still need an explicit bridge from the
Route A/Q0 window-energy theorem into the existing turnkey major-arc path.

## Existing Turnkey Route

The public certificate-facing major-arc hook is:

`Goldbach.Cert.TurnkeyMajorArcCanonSpec.turnkeyMajorArcCanon`

This delegates to:

`Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec.turnkeyMajorArcCanon`

`Q0TwoBoundsSpec` proves the turnkey major-arc statement from two pieces:

- `q0Minor_bound`, supplied through `Q0MinorEnergyBoundProvider.q0Minor_energyBound16`
- `q0Major_bound`, supplied by the Q0 major-side certificate route

The current minor provider is:

`Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider.q0Minor_energyBound16`

That provider goes through the split SSU/Type-I route:

- SSU/nonzero mode: `Q0MinorSSUUpperBoundCoarse.nonzeroModeEnergyBound_80`
- Type-I/zero mode: `Q0MinorTypeIUpperBoundRouteA.zeroModeEnergyBound_72000000`

## Main Remaining Bridge

The current cert target proves a pointwise pinned-window object:

`CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795`

The existing turnkey Q0 route consumes a uniform energy object:

`Q0MinorEnergyBound Δ_canon 16`

Those are different theorem surfaces. There is currently no discovered downstream module that turns
the former into the latter.

So the next proof-engineering job after the cert finishes is not another generated certificate by
default. It is to create or identify the bridge:

`CenteredNormalizedSigmaTruncWindowEnergyTargetAt X0 1795`
`=>`
`Q0MinorEnergyBound Δ_canon 16`

or to insert it one level lower into the split route, for example as a replacement for or sharpening
of:

`Q0MinorTypeIUpperBoundRouteA.zeroModeEnergyBound_72000000`

## Post-Cert Work Sequence

1. Let the current CI target finish:
   `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert`.

2. If it succeeds, build the immediate cert wrapper target again only if needed:
   `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainFinal`.

3. Add a small bridge module, probably under `Goldbach/Cert/MajorArcModules`, that imports:
   `Q0MinorZeroModeNormalizedAverageX0Cert`
   and the relevant Q0 minor energy/spec modules.

4. In that bridge module, try to prove the minimal useful target first:
   either a direct `Q0MinorEnergyBound Δ_canon 16`, or a narrower theorem that plugs into
   `Q0MinorEnergyBoundProvider`.

5. Patch `Q0MinorEnergyBoundProvider` to prefer the Route A bridge once it exists.

6. Rebuild:
   `Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec`.

7. Rebuild:
   `Goldbach.Cert.TurnkeyMajorArcCanonSpec`.

8. Rebuild:
   `Goldbach.GoldFunX_OptionB_Cert`
   and the relevant axiom audit modules.

## Risk Register

- The current cert target may close cleanly but still not imply the uniform Q0 minor-energy surface
  without a nontrivial scaling or normalization bridge.
- The cert is pinned at `X0`; the turnkey route is uniform for all `X >= X0`.
- The existing coarse SSU/Type-I route already closes `Q0TwoBoundsSpec`; replacing it with Route A
  is only useful if Route A gives a stronger or less assumption-laden bridge.
- If Route A is meant to replace the coarse provider, the exact mathematical statement needed is:
  why the normalized centered window-energy target at the pinned top window controls the
  Q0-complement energy used by `Q0MinorEnergyBound`.

## Practical Next Step

When the current CI target succeeds, do not immediately start a broad final build. First create the
small bridge target and test only that bridge. The highest-value next build target should be the
new bridge module, followed by `Q0TwoBoundsSpec`, not the full `Goldbach` target.

## Prepared Bridge Probe

Prepared module:

`Goldbach.Cert.MajorArcModules.Q0RouteAPostCertBridgeProbe`

This module imports the current Route A cert surface and the existing Q0 turnkey route, then names
the exact post-cert bridge surfaces:

- `RouteAWindowEnergyCertificateAtX0`
- `RouteAWindowEnergyToQ0MinorEnergy`
- `RouteAWindowEnergyToQ0MinorDeviation`

It also contains sanity wrappers for:

- the existing coarse provider:
  `current_provider_q0Minor_energyBound16`
- the existing turnkey route:
  `current_q0TwoBounds_turnkey`
- the current Route A window-energy theorem:
  `routeA_windowEnergy_from_tail_boundary_certificates`

It now also locks the conditional downstream surfaces that should become the replacement minor
provider path once the post-cert bridge is proved:

- `routeA_q0Minor_energyBound16_from_windowEnergy`
- `routeA_q0Minor_deviationBound4_from_windowEnergy`
- `routeA_q0Minor_energyBound16_from_tail_boundary_certificates`
- `routeA_q0Minor_deviationBound4_from_tail_boundary_certificates`

After the current cert target succeeds, this should be the first narrow target to build before
patching `Q0MinorEnergyBoundProvider` or attempting any broad final build.
