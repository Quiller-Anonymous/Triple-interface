# Independent review: small-cofactor cancellation

Date: 2026-10-29

## Verdict

The independent paper review returned **PASS** for both of the following theorems, kept as separate
claims:

```text
Delta_(10^-8)(N) > -0.001609*S(N)*N,

M_A(N) > 0.91*S(N)*N,
```

for every admissible even `N>=exp(exp(100))`.

No numerical correction was required.  The review rederived the finite-sieve denominator, the
common-factor and reflected-prime-power rows, the signed retained projection, the threshold errors,
the active-main convolution, and the active-support return to the exact discrete main.

These remain paper theorems.  They have not been formalized in Lean.

## What is now established

The small-cofactor theorem controls the exact part of the hard discrepancy supported on

```text
n=p*r,
p>u prime,
r<=N^(10^-8),
```

after combining all large-divisor terms attached to the same integer.  On that support,

```text
h_u(p*r)=-Lambda(r).
```

The proof includes both the full reflected-prime convolution and the actual `P=Q=100` retained
projection.  It does not infer a correlation estimate from coefficient mass.

The separately reviewed active-main theorem is normalized by the Goldbach singular factor:

```text
M_A(N)>0.91*S(N)*N.
```

It supersedes the weaker `0.9*N` active-main input for any later normalized ledger.

## What is not yet established

The review did not independently recheck all other Stage 1 estimates.  In particular, it did not by
itself certify the combined statement

```text
R_major(N)>0.708*S(N)*N.
```

That statement also uses the denominator-row lower bound, complete Type-I error, major-model
approximation error, and prime-power allowance from the earlier Stage 1 report.  Their normalization,
signs, and identity with the same `P=Q=100` object must be reconciled in one ledger before the
normalized reserve is treated as reviewed.

The theorem also does not control the adjacent range

```text
N^(10^-8)<r<=u.
```

The exact coefficient there is still `-Lambda(r)`, but the existing nonnegative sieve envelope grows
too quickly to reach a macroscopic exponent.

## Numerical consequence of the present constants

Ignoring threshold errors, the verified proof gives the general envelope

```text
b(eta)=160000*eta/(1-eta)^2+800*eta.
```

The current normalized reserve `0.708` would be exhausted at approximately

```text
eta=0.00000440294649539.
```

For reference:

| `eta` | `b(eta)` | `0.708-b(eta)` |
|---:|---:|---:|
| `10^-8` | `0.001608000032...` | `0.706391999968...` |
| `10^-6` | `0.160800320000...` | `0.547199679999...` |
| `4*10^-6` | `0.643205120030...` | `0.064794879969...` |
| `10^-5` | `1.608032000480...` | negative |

Merely increasing `eta` under the same envelopes is therefore not a completion strategy.

## Subsequent gate outcome

The subsequent bounded paper investigation was

```text
SupportingDocs/RouteAOneLargePrimeCompletionFeasibilityAssignment.md
```

Independent review confirms the **UNRESOLVED** verdict.  The normalized Stage 1 reserve and
retained-model positivity survive, but no verified theorem controls the actual fixed-center averaged
prime-pair convolution with the required constant.  See
`SupportingDocs/RouteAOneLargePrimeCompletionIndependentReview.md`.

