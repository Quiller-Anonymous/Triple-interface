# Route A fixed-bank obstruction and redesign gate

## Decision

The generated `X0` certificate is no longer a prerequisite for Route A. It remains useful as a
finite diagnostic of modulus families and cancellation at `X0`, but it cannot establish the
universal positive-mean statement required by the current route. No further compute is required
for Route A closure; a nearly complete run may still be finished as a diagnostic and regression
artifact. Existing generated sources and durable checkpoints should be retained unless storage
costs require a separate archival decision.

This conclusion does not invalidate the uniform truncation theorem or the raw weighted zero-mode
upper bound. It invalidates the attempt to obtain a uniformly positive PSB mean from the current
fixed-width bank.

## Results of the six-step audit

### 1. Formal empty-bank theorem

`RouteAFixedBankObstruction.lean` defines

```text
F_h = (2h+2)!
X_{h,k} = 2(k F_h + h + 2).
```

For every positive `k`, every integer in the radius-`h` interval around `X_{h,k}/2` is composite.
At `h = BG_Bank.H`, this proves that every coefficient of the canonical bank vanishes at those
arbitrarily large scales. The theorem `exists_empty_fixedBank_scale_ge` states the unbounded form
directly: beyond every prescribed bound there is an empty canonical bank.

The same module transports that fact through the exact definitions. It proves that
`weightedMinorCoeff`, `routeVisibleScalar`, and its even-window sum vanish. It also proves the exact
empty-bank cancellation

```text
G_formula X N + R_formula X N = -SS_formula X N.
```

### 2. The current universal positive-mean target is impossible

`RouteAPSBMeanObstruction.lean` proves

```text
no_uniformly_positive_routeAVisibleDyadicMeanLowerBound
```

for the exact `RouteAVisibleDyadicMeanLowerBound` structure used by the PSB source layer. This is a
Lean theorem, not a numerical extrapolation. A larger finite certificate cannot repair it.

### 3. Growing support prototype

`RouteAGrowingBankPrototype.lean` deliberately leaves `BG_Bank.wX` unchanged and defines a candidate
support `[X/2+1, X]`. The production bank is not changed until the replacement passes the full
coverage and budget gates. The paired difference band also grows with `X`; widening support while
retaining a fixed effective pair band would reproduce the same defect in another form.

### 4. Coefficient mass by normalization

The prototype normalizes the von Mangoldt weight by its exact mass on the growing support. Lean
proves both

```text
sum growingPrimeCoefficient = 1
sum |growingPrimeCoefficient| = 1.
```

Thus the support may grow without making the coefficient L1 mass grow. This is the intended
replacement for controlling the analysis by an `O(1)` support width.

### 5. Coverage theorem and the remaining coverage gap

Bertrand's theorem proves that the growing support contains a prime for every `X >= 2`. Lean also
proves a diagonal prime-pair witness whose even sum lies in the dyadic interval `(X,2X]` and whose
difference lies in the growing pair band.

This is not the short-window theorem required by the current endpoint. The still-missing contract is
`ShortWindowPairCoverage`: a prime pair with sum in `[X,X+H]` for every large `X`. That statement is
essentially the Goldbach coverage that Route A is meant to prove, so it cannot be assumed as an
input without circularity. Production integration therefore requires either a different observable
with a provable short-window lower bound or a justified change to the route quantifiers.

### 6. PSB numerical gate

`scripts/experiments/route_a_bank_redesign_feasibility.py` reconstructs the current explicit main
profile and error allowances from the Lean definitions. At `X0 = 1000000`, it reproduces a main
lower profile of about `5.58e-28`. The `C3 = 4` zero-mode Cauchy allowance alone is about `3.08e-10`,
and the explicit `G_formula` allowance is about `5.42e-2`. The comparison fails before adding any
residual allowance.

The numerical gap is a feasibility diagnostic. The fixed-bank impossibility in steps 1-2 is the
formal structural result.

## Production integration gate

The preferred production replacement is now the exact broad pointwise convolution documented in
`RouteABroadPrimeConvolutionPlan.md`, rather than the growing-bank prototype by itself. The
prototype remains evidence that support growth and mass normalization are compatible, but its
dyadic diagonal witness does not solve exact-center coverage.

Do not replace `BG_Bank.wX` or regenerate the large certificate graph until all of the following
hold:

1. A non-circular coverage theorem matches the actual output windows used downstream, or the route
   is reformulated with quantifiers that the dyadic coverage theorem can support.
2. The support and effective pair/kernel band grow together, with a precise replacement observable.
3. Uniform coefficient-mass and energy estimates are proved for that observable.
4. The PSB main-minus-error inequality is recomputed and has a documented safety margin.
5. A small Lean integration probe reaches the Route A endpoint before any bulk certificate is
   generated.

Until those gates pass, the correct next problem is proof design for coverage and positivity, not
completion of the old `X0` certificate.
