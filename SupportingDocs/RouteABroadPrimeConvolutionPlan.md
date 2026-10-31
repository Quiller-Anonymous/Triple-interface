# Route A broad-prime-convolution plan

## Status

The fixed-width arithmetic bank cannot be the universal Goldbach observable.  It is empty at
arbitrarily large scales, so no theorem can give its route-visible mean a fixed positive lower bound
for every sufficiently large `X`.

The corrected endpoint is now implemented in
`Goldbach/Cert/MajorArcModules/RouteABroadPrimeConvolution.lean`.  Lean checks that positivity of
the complete finite convolution at the exact integer `N` is equivalent to `GoldbachRep N`.  The
same module packages the exact main-minus-error theorem that would close the large-number route and
combines it with the existing finite base.

The exact unrestricted circle identity is implemented in `RouteABroadPrimeCircle.lean`. Lean checks

```text
C_raw(N) = integral S_N(alpha)^2 e(-N alpha) d alpha,
```

where `S_N` contains every candidate in `[2,N-2]`. `RouteABroadPrimeCircleProgram.lean` then splits
that exact integral into textbook major and minor arcs and proves that three quantitative fields
close Goldbach: major-arc approximation to the raw Hardy--Littlewood main, a minor-arc norm bound,
and a strict main-minus-errors budget. These modules prove their generic Fourier and measure facts
directly below the old banked certificate chain.

The production route now keeps the complete von Mangoldt weight through the circle analysis and
removes higher prime powers only at the final convolution. Lean checks the exact identity

```text
C_VM(N) = C_raw(N) + P_pp(N),
```

where `P_pp(N)` is an explicit sum of two prime/higher-power cross terms and one
higher-power/higher-power term. The higher-power weight is nonnegative and is positive exactly on
non-prime prime powers. A parity compression of the exponent gives

```text
# {higher prime powers in [2,N-2]} <= 2 (sqrt(N) + 1),
P_pp(N) <= (5/2) (sqrt(N) + 1) log(N)^2.
```

All of these statements are now checked in `RouteABroadPrimeVonMangoldt.lean`,
`RouteABroadPrimePowerBound.lean`, and `RouteABroadPrimePowerCount.lean`. The reduced final wrapper
`RouteABroadVonMangoldtClosure.lean` therefore has only two open analytic fields: the complete
von-Mangoldt major estimate and minor estimate.

A second, conservative integration surface is now checked for compatibility with the published
BMOR progression estimate. `RouteABalancedBMORPrototype.lean` restricts both summands to the
symmetric growing interval `[L,N-L]`. This is not a fixed-width bank: its width grows with `N`, and
positivity of its exact-center convolution still proves `GoldbachRep N`. Choosing `L-1 >= 10^6`
allows `RouteABalancedBMORBridge.lean` to apply the existing BMOR theorem without a million-term
low-prefix error. `RouteABalancedQ0CircleSplit.lean` proves an exact finite-`Q0` split on `[0,1]`,
but that representative interval cuts the principal arc centered at zero. The production split is
therefore `RouteABalancedQ0SeamSafeSplit.lean`, which translates the length-one interval so the
principal arc is contiguous. `RouteABalancedFiniteCutoffCircle.lean` then exposes the exact sum of
the rational arcs with `q <= Q` plus an exact remainder. Its final
`BalancedFiniteCutoffAnalyticCertificate` has the same three honest obligations: integrated major
approximation, remainder norm, and a strict budget. This finite-cutoff seam-safe surface is the
preferred major-arc adapter; it does not yet solve either analytic obligation.

The output-sequence projector modules remain checked exploratory infrastructure, but they are no
longer the preferred route. A direct numerical test at scales `65535` and `1048575` found that their
global, unnormalized complementary `l2` term overwhelms the pointwise main by orders of magnitude.
That negative result is recorded in `RouteABroadPrimeFourierFeasibility.md`. It does not rule out
every localized projector method, but it rules out the current hard cyclic selector as a plausible
production budget.

This establishes the correct logical destination.  It does not establish the missing analytic
estimate.

## Exact endpoint

For each `N`, define

```text
C_raw(N) = sum_{2 <= p <= N-2} Lambda_p(p) Lambda_p(N-p),
C(N)     = C_raw(N) / log(N)^2,
```

where `Lambda_p(n) = log n` on primes and is zero otherwise.  For `N >= 2`, the normalizing factor
is positive.  Lean proves

```text
C_raw(N) > 0  <->  Rep.R(N) > 0  <->  GoldbachRep(N),
C(N) > 0      <->  GoldbachRep(N).
```

This endpoint has three useful properties:

1. It includes every possible prime pair summing to `N`.
2. It is evaluated at `N`, not averaged over a neighboring output window.
3. Its `log(N)^-2` normalization is on the same scale as the existing Hardy-Littlewood main term.

## Exact closure contract

`BroadPrimeConvolutionCertificate Xmin main error` requires, for every even `N >= Xmin`,

```text
C(N) = main(N) + error(N),
0 < main(N),
|error(N)| < main(N).
```

These facts imply `C(N) > 0`, hence `GoldbachRep N`.  Together with
`FiniteBaseUpTo Xmin`, the checked theorem
`goldbach_of_finiteBase_and_broadPrimeConvolutionCertificate` proves the full Goldbach statement.

This contract is intentionally strict.  A bound for a banked proxy, a positive average, or a
representation at some nearby integer does not inhabit it.

## What existing objects do not satisfy this contract

`BG_Identity.conv_full` is not `C`.  It contains all of the following additional restrictions or
weights:

- the fixed arithmetic support `BG_Bank.wX`;
- an offset band `bandU`;
- tent weights;
- the repository-specific `1/800` normalization.

Likewise, `BG_Identity.R_bank_tenorPrime` is a prime-only banked convolution, not the full
convolution.  Its existing positivity-to-representation theorem remains correct, but the factorial
counterexample prevents universal positivity for that fixed bank.

The nearly complete `X0` certificate therefore remains useful only as a finite diagnostic and
regression artifact.  It can reveal the modulus families and cancellations of the old surrogate at
`X0`; it cannot fill the broad pointwise certificate above.

## Live analytic route

The paper's frequency decomposition can be retained. What must be removed is the later substitution
of a fixed arithmetic prime support for a spectral decomposition. The canonical proof shape is the
circle-variable split applied first to the complete von Mangoldt sum:

```text
C_VM(N)  = I_major_VM(N) + I_minor_VM(N),
C_raw(N) = C_VM(N) - P_pp(N),
I_major_VM(N) = sigma(N) N + E_major(N),
C_raw(N) >= sigma(N) N - |E_major(N)| - ||I_minor_VM(N)|| - P_pp(N).
```

The checked circle certificate closes if the following statements hold uniformly for every even
`N` beyond the finite base:

1. The real part of `I_major_VM(N)` differs from `sigma(N) N` by at most `E_major(N)`.
2. `||I_minor_VM(N)|| <= E_minor(N)`.
3. `E_major(N) + E_minor(N) + (5/2)(sqrt(N)+1)log(N)^2 < sigma(N) N`.

The algebra, endpoint, and prime-power transfer are now complete. The refined proof uses the fact
that a non-prime prime power `p^k`, `k >= 2`, carries weight `log p <= (1/2) log N`. At `N = 10^6`,
the explicit prime-power allowance is approximately `4.77648e5`, while the elementary
singular-series main floor from `C2 > 0.66` is `1.32e6`; about `8.42352e5` remains for major and
minor errors. None of the old Q0 numerical bounds supplies the two remaining estimates because its
coefficient `aTerm` already contains `BG_Bank.wX`. Steps 2--5 of the older major-arc development are
more promising: they act on the complete von Mangoldt weight before the bad Step 19 disposal.
The balanced adapter now makes that reuse exact: Steps 2--5 apply to `[L,N-L]`, the real and circle
exponential sums are identified, and the square-error estimate is checked. The circle integral is
split on a seam-safe fundamental interval and its low-denominator arcs are extracted exactly. A
diagnostic ledger shows why the cutoff must remain small: summing the published BMOR error through
`Q0 = 30000` is impossible. After correcting the ledger to use the genuinely `q`-dependent
geometric kernels and residue classes, it no longer selects a single cutoff: `Q = 2` maximizes the
reserve before the remainder estimate, while roughly `Q = 8..10` captures more rational peaks.
This is feasibility evidence, not a uniform theorem. The pointwise BMOR bound has now been
integrated through arbitrary finite `Q`, and the model has been identified exactly as a signed
Ramanujan arithmetic sum multiplied by nonnegative geometric kernel masses. What remains is to
control the exact complementary remainder and prove the resulting strict budget uniformly.
The existing Q0 SSU tower is not yet a broad minor-arc proof: it still contains abstract packet
transforms and explicit oscillatory/overlap axioms, and its current placeholder `minorArc` is the
whole real line. Any reuse must begin with a new extraction whose input is visibly the complete von
Mangoldt sum.

## Paper corrections required

The current manuscript contains two invalid pointwise upgrades that cannot remain load-bearing:

1. A statement that most grid points are good does not imply that every center is close to a good
   grid point.  Bernstein continuity cannot repair arbitrarily located bad-grid gaps without an
   additional thickness theorem.
2. Positivity of a nonnegative sum over `[N-H,N+H]` proves a representation somewhere in that
   window, not at `N`.

The direct pointwise projection route avoids both errors because it lower-bounds the exact value
`C(N)`.

## Ordered next work

1. Completed: define the full pointwise convolution and prove positivity equivalent to
   `GoldbachRep`.
2. Completed: prove the exact unrestricted broad circle identity.
3. Completed: split that exact identity into broad textbook major and minor integrals.
4. Completed: build `BroadPrimeCircleCertificate` and its finite-base Goldbach wrapper.
5. Completed: audit portability and reject the current output-DFT budget numerically before
   commissioning another certificate.
6. Completed: transfer the circle program to complete von Mangoldt weights and prove an exact,
   sparse prime-power correction bounded by `(5/2)(sqrt(N)+1)log(N)^2`.
7. Completed: define the balanced growing support, prove its positivity-to-Goldbach implication,
   and bridge its real exponential sum to the published BMOR estimate.
8. Completed: repair the circle seam by translating the fundamental interval and extract the
   balanced `q <= Q0` major integral exactly into reduced `(q,a)` arc integrals.
9. Completed: expose an exact finite-cutoff major sum `q <= Q` plus algebraic remainder, and run a
   diagnostic ledger. Full-`Q0` BMOR accumulation is rejected; `Q = 2` and `Q = 8..10` are the
   current diagnostic alternatives, not theorem-level selections.
10. Completed: integrate the quadratic BMOR approximation through arbitrary finite `Q`, with the
    explicit error `balancedBMORIntegratedMajorError`.
11. Completed: identify the finite-cutoff model exactly as
    `sum_{q <= Q} muSq(q) * c_q(N) / phi(q)^2 * K_q(L,N)`, prove `K_q(L,N) >= 0`, and prove that the
    model integral is real.
12. Completed in algebraic form: express the finite-cutoff remainder as the integral of the exact
    von Mangoldt integrand minus the low-denominator model mask. The remaining analytic task is a
    cancellation bound for `balancedVonMangoldtAfterMajorUpToRemainder`; the existing Q0 SSU tower
    does not supply it because its concrete coefficients are banked and its abstract extraction is
    incomplete.
13. Close the threshold gap introduced by `L - 1 >= 10^6`: either extend the finite base through
    the first scale where `[L,N-L]` is useful, or prove a separate intermediate-range estimate.
14. Select `Q` jointly with the remainder theorem and prove the scale-uniform strict budget
    `majorError + remainderError + primePowerError < balancedFiniteCutoffMain`.
15. Instantiate `BalancedFiniteCutoffClosureCertificate`. Its checked wrapper then combines the
    analytic facts with the finite base and proves `GoldbachRep` for every even `N >= 4`.

No new bulk certificate should be generated for this corrected route before steps 12-14 pass
analytically and numerically. The exact collaborator-facing target and acceptance tests are recorded
in `SupportingDocs/RouteABalancedRemainderTheoremSpec.md`.
