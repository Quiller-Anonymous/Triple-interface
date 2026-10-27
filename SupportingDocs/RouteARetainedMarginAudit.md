# Route A retained-margin audit

## Status

This audit concerns the balanced Vaughan fixed-center route after the revised short Type-I error
estimate. It does not reopen Route A as a proof-completion project. Its purpose is to identify the
correct signed quantity that must be positive before any further Type-II formalization is justified.

The revised short Type-I allowance is numerically feasible at the deliberately enormous threshold
`N >= exp(exp 100)`. That result controls the difference between the exact Type-I--prime
convolution and its active discrete main. It does **not** by itself establish a positive main
margin.

## Exact recombination

Write

```text
S = balanced von Mangoldt weight,
A = mu_<=u * log,
hard = S - A,
J(F,G) = retained q=1,2 integral,
H(F,G) = complementary integral.
```

The checked identities give

```text
H(S,S) = H(A,S) + H(hard,S),
H(A,S) = C(A,S) - J(A,S),
C(S,S) = J(S,S) + H(S,S).
```

Consequently a Type-I estimate, a retained-pair lower estimate, and a lower estimate for the hard
complement combine as

```text
C(S,S)
  >= M_A + (J_SS_main - J_AS_main)
       - TypeI_full_error
       - TypeI_retained_error
       - retained_pair_error
       - hard_allowance.
```

This is now recorded in Lean as
`RouteABalancedVaughanTypeIInterface.balancedFullCorrelation_lower_bound`.

The usable main is therefore

```text
M_A + (J_SS_main - J_AS_main),
```

not the complementary expression `M_A - J_AS_main` in isolation.

## Why the negative complementary constant is not an obstruction

Let

```text
kappa = integral_{-1}^{1} sinc(t)^2 dt
      + integral_{-1/2}^{1/2} sinc(t)^2 dt
      = 1.67651834...,
```

with `sinc(t) = sin(pi*t)/(pi*t)`. For fixed lower cutoff and even `N`, the prime number theorem
predicts

```text
J(S,S) / N -> kappa.
```

For the Type-I main, consider the Dirichlet series

```text
F_N(s) = sum_{(d,N)=1} mu(d) / (phi(d) d^s)
       = product_{p not dividing N} (1 - 1 / ((p-1) p^s)).
```

Factoring out `1 / zeta(1+s)` gives

```text
F_N(s) = zeta(1+s)^(-1) H_N(s),
H_N(0) = 2 C2 * product_{p|N, p>2} (p-1)/(p-2),
```

where `C2` is the twin-prime constant. Thus the expected logarithmically smoothed Type-I main is
the usual Goldbach singular series

```text
S(N) = 2 C2 * product_{p|N, p>2} (p-1)/(p-2).
```

The same principal/parity model predicts `J(A,S)/N -> kappa`. Hence

```text
H(A,S) / N -> S(N) - kappa.
```

For powers of two this limit is

```text
2 C2 - kappa = -0.3561947... .
```

That negative constant is expected: it is what remains after deliberately removing the positive
`q=1,2` arcs. Restoring `J(S,S)` cancels `kappa`, leaving the positive baseline
`S(N) >= 2 C2 = 1.3203236...`. A proof target requiring `H(A,S)` itself to be positive would be
wrong.

## Finite diagnostic

The diagnostic

```text
scripts/experiments/route_a_retained_margin_feasibility.cpp
```

constructs the exact finite coefficient

```text
A(n) = sum_{d|n, d<=u} mu(d) log(n/d),
```

the balanced von Mangoldt coefficient, the exact full convolutions, and the exact retained arc
integrals. The arc integrals are evaluated from the convolution coefficients and the closed-form
integral of each Fourier mode, not by quadrature. It also evaluates the active discrete main with
the natural-number division appearing in Lean.

Selected power-of-two results with `L=2` and `u=floor(N^(1/3))` are:

| `N` | `M_A/N` | `J(S,S)/N` | `J(A,S)/N` | restored model margin / `N` |
| ---: | ---: | ---: | ---: | ---: |
| 65,536 | 1.291683 | 1.674186 | 2.192179 | 0.772288 |
| 1,048,576 | 1.197442 | 1.676224 | 1.934271 | 0.939232 |
| 4,194,304 | 1.296738 | 1.676581 | 1.921217 | 1.052139 |

Here the restored model margin is

```text
M_A + J(S,S) - J_A_model.
```

The finite values are not monotone because the truncated Mobius sum converges slowly. The
Type-I retained model itself is already accurate: at `N=4,194,304`, its difference from the exact
retained `J(A,S)` is about `3.6e-5 N`. This supports the algebraic model but does not prove a
uniform lower bound.

At the old finite cutoff scale `N=3,200,000`, `L=1,000,001`, the same diagnostic gives restored
model margin `0.605504 N`. This is only finite evidence and has no bearing on the enormous analytic
threshold without a theorem.

## The actual paper-math gate

Before formalizing the published character estimates, establish an explicit theorem of the form

```text
M_A(N) + J_SS_main(N) - J_AS_main(N) >= c_main * N
```

for every even `N` beyond a computable threshold, with `c_main > 0`. A natural target is any
constant safely below `2 C2`; optimizing it is unnecessary.

This breaks into three declaration-specific estimates:

1. **Active-main lower bound.** Control the finite sums

   ```text
   sum_{d<=u, (d,N)=1} mu(d)/phi(d)
   ```

   and their logarithmic smoothing strongly enough to compare the exact active discrete main with
   `S(N) N`. The estimate must be uniform in the prime factors of `N`. The follow-up kernel audit
   now gives a viable paper proof and a safe target `M_A >= 0.9 N`; see
   `RouteAActiveMainKernelAudit.md`.

2. **Retained Type-I matching.** Prove that the principal and parity local models of `A` match the
   corresponding prime models on the full seam-safe `q=1,2` arcs. Equivalently, bound
   `J(S,S)-J(A,S)` directly. Bounding the two large retained integrals independently is less
   efficient. The follow-up audit now gives the direct paper bound
   `|J(S,S)-J(A,S)| < 0.49 N`; see `RouteARetainedHardAudit.md`.

3. **Seam alignment.** The intended retained set contains both halves of the principal arc. The
   current generic bilinear set integral is written on `[0,1]`, while the established balanced
   major-arc machinery uses `[-1/N,1-1/N]`. The final adapter must use a translated bilinear
   interval or an explicitly wrapped principal arc; `majorArcSetUpTo N 2 1` inserted naively into
   the `[0,1]` integral omits the half near `1`.

The active-main argument does not require conjectural termwise nonnegativity. The exact signed
Mobius/totient kernel reduces it to Ramaré's explicit estimates for the ordinary harmonic Mobius
sum and its logarithmic smoothing, while a Rankin tail bound handles the conductor dependence.
That component is now a formalization task rather than an unresolved feasibility question.

## Decision rule

Do not start the Type-II formalization merely because the revised Type-I **error** is tiny.

The active-main and retained-hard audits now leave more than `0.40 N` before the complementary
hard term at paper level. The remaining analytic target is the one-sided estimate

```text
H(hard,S).re >= -hardAllowance(N)
```

with a commissioning target `hardAllowance <= 0.35 N`. If the exact hard coefficient does not
admit that saving, stop this decomposition rather than building more conditional closure
infrastructure.
