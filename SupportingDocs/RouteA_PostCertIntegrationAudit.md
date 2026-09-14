# Route A Post-Cert Integration Audit

Date: 2026-09-06

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
- The current source-archive audit command is:
  `python3 scripts/ci/route_a_source_archive_audit.py --target Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert --manifest .github/route_a_smoke/*_missing_sources.txt --archive .github/route_a_smoke/*.tar.gz`
- As of 2026-09-06, after the row-front split/archive refresh, that audit reports:
  `local_modules=203062`, `external_imports=89`, `required_untracked_sources=201630`,
  `manifest_entries=201630`, `archive_entries=201630`, and `ok=true`.

This removes the most common avoidable CI failure class: missing generated sources or local import
cycles inside the current Route A target.

The audit is now wired into `.github/workflows/route_a_linux_smoke.yml` before the expensive build
step. It should fail fast if a clean GitHub runner would be missing an ignored/generated source file
needed by the selected target.

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

3. Build the prepared narrow bridge probe:
   `Goldbach.Cert.MajorArcModules.Q0RouteAPostCertBridgeProbe`.
   This checks the theorem names and downstream surfaces without immediately starting a broad
   end-to-end build.

4. In the bridge/probe layer, prove the minimal useful target first:
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

## Immediate Certificate Payload Surface

After the current periodic-main/nonzero certificate target builds, the top Route A wrapper still
has these explicit payload inputs unless separate modules are imported to provide them:

- `TailChunk000Sub000SupportExplicit` sum equals
  `surrogateDiagTailX0RatChunk000Sub000First5000`.
- `TailChunk000Sub001SupportExplicit` sum equals
  `surrogateDiagTailX0RatChunk000Sub001First5000`.
- `TailChunk001Sub000SupportExplicit` sum equals
  `surrogateDiagTailX0RatChunk001Sub000First5000`.
- `TailChunk001Sub001SupportExplicit` sum equals
  `surrogateDiagTailX0RatChunk001Sub001First3211`.
- `CenteredNormalizedSigmaTruncBoundaryActiveSignedRatCertificateAtX0`.
- `CenteredNormalizedSigmaTruncBoundaryInactiveCorrectionRatCertificateAtX0`.

The periodic-main equality itself is intended to be discharged inside
`Q0MinorZeroModeNormalizedAverageX0PeriodicMainFinal` by
`periodicMainCert_true_of_nonzeroFinal` and
`centeredNormalizedSigmaTruncSurrogatePeriodicMainExactCheckedRatCertificateAtX0_certified`.

## Pre-Close CI Guards

The current workflow now performs these cheap checks before spending hours in Lean compilation:

- Restores the current Route A `q0cert` generated-source tarball and verifies its checksum.
- Runs `route_a_source_archive_audit.py` against the selected target.
- Verifies that every required untracked/generated source in the target import closure is present
  in the restored source archives.
- Prints source-restore, archive-audit, Lean setup, dependency-fetch, cache-restore, and
  target-verification outcomes if a run fails before the build starts.
- Resolves final build status from `route-a-build-status.txt` or
  `route-a-direct-build-status.json` if GitHub loses the build step output.
- Runs direct mode with `use_force_rebuild_list=false` by default.  The historical force list is now
  opt-in because applying it against an old unstamped artifact cache can mark most of the target
  closure dirty.
- Aborts before compilation with exit code `86` if direct mode sees fewer than
  `min_initial_skipped` restored modules.  For the full
  `Q0MinorZeroModeNormalizedAverageX0Cert` target, the default floor is `100000`, which prevents a
  nearly cold or poisoned cache from becoming the new baseline.
- Provides an optional `cache_restore_key` workflow input.  Leave it blank for normal continuation,
  but paste a known-good `Cache restore matched key` from an earlier high-skip run if GitHub keeps
  selecting a newer weak cache.
- Keeps broad same-toolchain cache fallback off by default via `allow_broad_cache_restore=false`.
  A broad fallback can restore a small cache from another Route A target and leave the full Q0Cert
  build with only a few thousand skipped modules.
- Lists matching project artifact cache candidates before restore, including cache ID, size, creation
  time, last access time, and key.
- The direct builder writes only `.olean` artifacts; `.ilean` files are not needed for this CI
  import-chain build and are pruned before cache save.  This is intended to keep checkpoints below
  the GitHub Actions cache eviction threshold.
- Uploads `route-a-source-archive-audit.json` with the normal smoke-log artifact.

This does not prove the target, but it should prevent another delayed failure caused by a missing
ignored source file.

## Source Archive Policy

Only these Route A smoke support files should remain under `.github/route_a_smoke/`:

- `q0cert_extra_missing_sources.tar.gz`
- `q0cert_extra_missing_sources.tar.gz.sha256`
- `q0cert_extra_missing_sources.txt`
- `q0cert_force_rebuild_modules.txt`

The older `acc5`, `acc721`, `core_residual`, and `periodic_main_final` source archives were
superseded by the current `q0cert` archive.  On 2026-09-06, the `q0cert` archive alone was audited
successfully against these targets:

- `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert`
- `Goldbach.Cert.MajorArcModules.Q0RouteAPostCertBridgeProbe`
- `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainFinal`
- `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualFinal`
- `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainZeroNonCoprimeCoreResidualLeftOnlyThreeFinalAcc721`

Do not reintroduce the older archives unless a target outside the current Route A closure actually
requires them.  Restoring stale archives slows CI and can obscure which generated-source bundle is
authoritative.

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

For the ongoing full-cert CI run, use these default settings unless debugging a specific stale
interface:

- `target=Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0Cert`
- `build_mode=direct`
- `direct_workers=4` by workflow default while the build is crossing the slow non-dyadic frontier.
  Use `6` only as a monitored throughput experiment.  Avoid `8` unless a run has enough headroom to
  reach cache-save cleanup reliably.
- `direct_checkpoint_margin_minutes=35`.  This is intentionally larger than the old five-minute
  margin so the direct builder can stop, terminate Lean children, write status, prune artifacts, and
  reach cache-save steps before GitHub's outer timeout kills the job.
- `use_force_rebuild_list=false`
- `min_initial_skipped=0` only for the current controlled rebuild from a weak cache baseline.  Once
  a run times out after useful progress, the workflow's auto-continuation should raise the next
  `min_initial_skipped` floor to at least `skipped + built` from
  `route-a-direct-build-status.json`.
- `cache_restore_key=` blank unless recovering from a known bad latest cache
- `allow_broad_cache_restore=false`
- `run_post_success_probe=true`

If the run aborts with exit code `86`, inspect the cache restore key before rerunning.  That means
the restored artifact cache is too cold for productive continuation.  If the log shows a weak latest
cache was selected, either delete that cache in GitHub Actions or rerun with `cache_restore_key`
set to a prior known-good matched key.  The `[freshness]` line distinguishes missing artifacts from
stamp mismatches, which decides whether the cache is absent/partial or merely stale.

Run `196` was the observed flip point.  Run `195` saved a roughly 10 GB project artifact cache and
run `196` then failed to restore that cache, effectively restarting from a much smaller checkpoint.
That is consistent with GitHub cache thrashing at the default repository cache limit rather than a
Lean theorem failure.

During the controlled rebuild, monitor the cache lineage by comparing `skipped + built` at the end
of a run with the next run's `initial_skipped`.  If the next run starts far below that number, treat
it as a cache-continuation failure rather than a mathematical failure.

If the log ends with `Terminated` / exit code `143` but does not print cache-save or final-status
lines, the build step was killed too close to the outer timeout.  Do not rerun with the same timing
inputs.  Use the patched workflow with the larger direct checkpoint margin, or manually set
`build_timeout_minutes=200` and keep `direct_checkpoint_margin_minutes=35`.

If the cache save succeeds but the automatic continuation dispatch fails with a GitHub API `500`,
that is an infrastructure failure after the checkpoint accounting has already succeeded.  Manually
start a new workflow run using the `next_min_initial_skipped` printed in the continuation cache
guard.  The workflow now retries transient dispatch failures and records
`route-a-continuation-dispatch.json` for diagnosis.

If a run on SHA `269bbc694` or later still ends early with exit code `143` but no signal-handler or
cache-save lines, treat it as GitHub runner loss/termination rather than a normal timeout.  Restart
from the last successful checkpoint with `direct_workers=4`.  If early loss repeats even at four
workers, shorten the run interval manually by lowering `build_timeout_minutes`; this saves smaller
checkpoints before the runner enters the observed failure window.

The recommended post-cert build order is:

1. `Goldbach.Cert.MajorArcModules.Q0RouteAPostCertBridgeProbe`
2. `Goldbach.Cert.MajorArcModules.Q0MinorZeroModeNormalizedAverageX0PeriodicMainFinal`
3. `Goldbach.Cert.MajorArcModules.Q0MinorEnergyBoundProvider`, only after a real Route A bridge is
   available or an explicit replacement theorem has been written.
4. `Goldbach.Cert.MajorArcModules.Q0TwoBoundsSpec`
5. `Goldbach.Cert.TurnkeyMajorArcCanonSpec`

If step 1 fails after the cert target succeeds, treat it as an integration/name-surface bug first,
not as evidence that the certificate payload failed.

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
- the periodic-main exact-checked certificate:
  `routeA_periodicMain_exactChecked_certificate_surface`
- the periodic-main final equality:
  `routeA_periodicMain_eq_cert_surface`
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

The GitHub smoke workflow now has `run_post_success_probe=true` by default.  If the selected target
finishes with exit code `0`, the workflow immediately attempts a short direct build of
`Goldbach.Cert.MajorArcModules.Q0RouteAPostCertBridgeProbe` while the restored artifact cache is
hot.  This is diagnostic only: a probe failure should be treated as a post-cert integration/name
surface bug, not as evidence that the main certificate target failed.
