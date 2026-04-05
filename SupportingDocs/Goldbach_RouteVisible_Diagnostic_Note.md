# Route-Visible Minor Diagnostic Note

Date: 2026-03-28

## Executive Summary

The old `coeffArith` / subspace program should now be regarded as a diagnostic of hidden structure, not as the live bridge into the route-facing Goldbach closure problem.

The exact Lean decomposition and the new diagnostics now support a stronger, route-facing hierarchy:

```text
routeVisible = zeroMode + meanChannel
           = G_formula
           + SS_formula
           + R_formula
```

where:

- `G_formula` is a fixed geometric mean-channel witness,
- `SS_formula` is a fixed singular-series zero-mode witness,
- `R_formula` is the exact route-facing residual.

The important consequence is that the conservative Vaughan-facing target should no longer be formulated around the old nonzero-family subspace object. The natural target is now a route-facing approximation theorem for the exact scalar witness itself.

## Exact Formal Picture

The exact route-visible object is formalized in:

- [Q0MinorRouteVisibleAnalysis.lean](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleAnalysis.lean)
- [Q0MinorWeightedChannelBridge.lean](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorWeightedChannelBridge.lean)
- [Q0MinorZeroModeAnalysis.lean](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorZeroModeAnalysis.lean)
- [Q0MinorRouteVisibleDecomposition.lean](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleDecomposition.lean)

The key exact identities are:

- [routeVisibleSlice_eq_rankTwo_basis](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleAnalysis.lean#L107)
- [routeVisibleValue_eq_minorResidual](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleAnalysis.lean#L119)
- [routeVisibleSliceSum_eq_routeVisibleValue](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleAnalysis.lean#L127)

So the live route-facing family is literally rank-two in the shift variable `t`:

```text
routeVisibleSlice(X,N,t)
  = zeroModeCoeff(X,N) * 1_{t=0}
  + meanChannelCoeff(X,N) * 1_{t in ambient, t ≠ 0}.
```

This is the formal reason the old `coeffArith`-only bridge was mis-targeted.

The current fixed route-facing witness is packaged in:

- [frozenRouteVisibleModel](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleDecomposition.lean)

with the exact decomposition theorem:

- [routeVisibleScalar_eq_frozenModel_add_residual](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleDecomposition.lean)

and the theorem-facing residual target surface:

- [RouteVisibleResidualTarget](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleDecomposition.lean)
- [FrozenRouteVisibleApproximationTarget](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleDecomposition.lean)

## Diagnostic Battery

The new diagnostics are:

- [exp_q0_minor_route_visible_surrogate.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_route_visible_surrogate.py)
- [exp_q0_minor_route_visible_residual.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_route_visible_residual.py)
- [exp_q0_minor_zero_mode_refinement.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_zero_mode_refinement.py)
- [exp_q0_minor_zero_mode_post_ss_residual.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_zero_mode_post_ss_residual.py)
- [exp_q0_minor_route_visible_exact_decomp.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_route_visible_exact_decomp.py)
- [exp_q0_minor_zero_mode_sigma_diagnostic.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_zero_mode_sigma_diagnostic.py)
- [exp_q0_minor_ss_envelope_sweep.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_ss_envelope_sweep.py)

All runs below use the exact `Q0` weight and the canonical window.

## Main Findings

### 1. The route-visible family is mostly geometric

Using the interval-convolution surrogate on `routeVisible = zeroMode + meanChannel`:

- `X = 100000`: scalar capture `85.60%`, family capture `89.28%`
- `X = 300000`: scalar capture `90.55%`, family capture `91.12%`
- `X = 1000000`: scalar capture `90.29%`, family capture `90.54%`

The residual norms over `10^5` to `10^6` decay roughly like:

- scalar residual: `X^-0.213`
- family residual: `X^-0.215`

So at the route-visible level, the dominant contribution is already geometric.

### 2. The post-surrogate residual is overwhelmingly zero-mode

After subtracting the best channelwise geometric fit, the residual family energy is only about `9%` to `11%` of the original route-visible family energy:

- `X = 100000`: `10.72%`
- `X = 300000`: `8.88%`
- `X = 1000000`: `9.46%`

That residual is extremely low-rank across the sampled centers `N`, but more importantly it is numerically concentrated at `t = 0`. The nonzero coordinates are many orders of magnitude smaller than the zero coordinate.

Interpretation:

- the old nonzero-family subspace story survives only as reconnaissance,
- the live arithmetic refinement problem is now overwhelmingly a zero-mode problem.

### 3. The zero-mode residual is mostly singular-series modulation

On a dense even window `N ∈ [X, X+H]`, compare three fits for the exact zero mode:

1. geometric only,
2. geometric + singular-series modulation,
3. geometric + smooth quadratic envelope correction.

Results:

- geometric-only capture: about `86%`
- geometric + singular-series capture:
  - `99.515%` at `X = 100000`
  - `99.314%` at `X = 300000`
  - `99.002%` at `X = 1000000`
- geometric + quadratic-envelope capture: still about `86%`

Residual correlation with the singular-series profile:

- `0.9819` at `X = 100000`
- `0.9745` at `X = 300000`
- `0.9636` at `X = 1000000`

So the first arithmetic correction to the geometric route-visible main term is not a generic smooth drift. It is a genuinely arithmetic zero-mode modulation of singular-series type.

### 4. After removing the singular-series correction, no strong second structure appears

The post-singular-series zero-mode residual is already tiny:

- energy ratio about `0.49%`, `0.69%`, `1.00%` at `X = 10^5, 3·10^5, 10^6`

Testing secondary explanations on that tiny residual:

- smooth drift captures very little,
- a small-prime arithmetic dictionary captures essentially nothing,
- the combined fit still captures only a few percent of that already tiny residual.

So the current data does **not** indicate a robust second arithmetic layer after the singular-series modulation is removed.

### 5. The first frozen formulas failed, but in a diagnosable way

The first strict fixed-formula witness was too large in the actual route scalar norm. Measured against the normalized route budget, it produced a growing residual with fitted slope about `+1.11`.

The important point is that this was not repaired by adding projection machinery. Instead, the exact route-facing norm isolated the failure:

- `||mean - G||² / budget` was already decaying,
- the positive slope lived on the zero side.

So the defect was structural and localized.

### 6. The `q0NormFactor(N)` envelope fixed the catastrophic scale mismatch

Adding the normalization-seam factor `q0NormFactor(N)` to both frozen pieces changed the route-facing picture completely:

- residual/budget dropped from the `10^1` to `10^2` range
- to the `10^-9` to `10^-8` range on `X = 10^5, 3·10^5, 10^6`

This was a genuine structural correction, not a cosmetic improvement.

### 7. The remaining zero-side miss is mostly an `X`-envelope, not an `N`-shape error

The normalized zero observable

```text
Z(X,N)
  = zeroModeScalar(X,N)
    / (q0NormFactor(N) * geometricWeightedMinorCoeff(X,N,0))
```

has very high correlation with the singular-series shape:

- `0.9976` at `X = 100000`
- `0.9966` at `X = 300000`
- `0.9950` at `X = 1000000`

and the best-fit envelope `E(X)` drifts mainly with `X`, not with `N`.

That showed the local arithmetic shape was basically right and that the remaining defect belonged in a frozen `X`-envelope multiplying the singular-series factor.

### 8. Promoting the log-squared envelope produces a frozen route-facing witness

The explicit envelope sweep selected the route-aligned candidate

```text
sigmaEnvelopeFormula(X)
  = 4.089173283623e-04 / log(X + H)^2
```

as the first frozen witness component.

With

```text
G_formula(X,N)
  = q0NormFactor(N) * geometricMeanChannelScalar(X,N)

SS_formula(X,N)
  = q0NormFactor(N)
    * geometricWeightedMinorCoeff(X,N,0)
    * sigmaEnvelopeFormula(X)
    * sigmaNormalizedSeries(N),
```

the exact route-facing residual now satisfies:

- residual/budget `≈ 5.91e-11` at `X = 100000`
- residual/budget `≈ 2.04e-11` at `X = 300000`
- residual/budget `≈ 4.44e-12` at `X = 1000000`

with fitted slope about `-1.1257`.

So the current frozen witness behaves correctly in the only norm that matters for the route.

### 9. Honest caveat on the zero-side diagnostic

The zero-side diagnostic `||zero - SS||² / budget` still shows a positive fitted slope, but the absolute levels are around `10^-22` to `10^-21`. That is far below the scale that is currently operationally meaningful for the route-facing bridge. So it is recorded, but not currently treated as a live obstruction.

### 10. The zero-mode envelope uses the same normalization seam as the route floor

The next frontier is no longer structural. It is analytic provenance of the zero-mode `X`-envelope.

This seam is now packaged in:

- [Q0MinorZeroModeEnvelope.lean](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorZeroModeEnvelope.lean)

The key formal identity is:

```text
sigmaEnvelopeFormula(X)
  = ((800 * kappa)) * routeVisibleWindowNormFloor(X),
```

where

```text
routeVisibleWindowNormFloor(X)
  = (1 / 800) / log(X + H)^2.
```

So the promoted singular-series envelope is not an unrelated extra factor. It uses exactly the same
`log(X + H)^(-2)` seam already present in the canonical route normalization floor `c_X`, up to one
fixed scalar multiplier.

The corresponding dense-window provenance diagnostic is now:

- [exp_q0_minor_zero_mode_envelope_origin.py](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/scripts/experiments/exp_q0_minor_zero_mode_envelope_origin.py)

On `X = 10^5, 3·10^5, 10^6`, the fitted zero-mode envelope `E(X)` satisfies:

- `E(X) / c_X(log(X+H)) ≈ 2.70e-06, 2.72e-06, 2.59e-06`

with fitted exponent about `-0.019`, i.e. essentially flat over the sampled range.

So the current evidence is:

- the `N`-shape is singular-series,
- the `X`-envelope tracks the same `log(X + H)^(-2)` seam as the route normalization floor,
- the remaining analytic question is to explain the constant and its precise zero-mode bookkeeping.

## Revised Hierarchy

The current best route-facing description is:

```text
routeVisible
  = G_formula + SS_formula + R_formula
```

where:

- `G_formula` is a fixed geometric route-visible main term,
- `SS_formula` is a fixed singular-series-driven zero-mode correction,
- `R_formula` is an exact residual whose route-facing norm is empirically strongly decaying on the sampled range.

This is a materially different picture from the earlier one centered on `coeffArith`.

## Consequence For The Vaughan Path

The conservative next bridge should now be formulated as a route-facing approximation theorem target:

```text
routeVisibleScalar(X,N)
  = G_formula(X,N)
  + SS_formula(X,N)
  + R_formula(X,N),
```

with `R_formula` controlled in the normalized route scalar window norm. The theorem-facing target is packaged in:

- [FrozenRouteVisibleApproximationTarget](/Users/benjaminnelson/Desktop/nerd%20shit/goldbach/builds/Goldbach/Goldbach/Cert/MajorArcModules/Q0MinorRouteVisibleDecomposition.lean)

Current status:

- formal decomposition: done
- frozen witness: done
- empirical route-norm validation: strong
- analytic derivation of the envelope/constants: pending

This does not by itself close Goldbach. But it now gives a concrete route-facing bridge witness instead of a diagnostic surrogate.

## Honest Caveat

These diagnostics are exact on the current `Q0` object and canonical window, but they are still diagnostics. They do not by themselves prove the asymptotic theorem surface needed for Goldbach. Their role is now narrower and sharper: they identify a specific frozen route-facing bridge witness that the next proof phase should justify.

At present, the evidence strongly suggests:

- the old subspace bridge is not the closure bridge,
- the live route-visible object is simpler than expected,
- the first non-geometric correction is a singular-series zero-mode effect,
- and the first frozen bridge witness is now mature enough to be treated as an actual theorem target rather than only a diagnostic story.
