# Route C variable-principal-arc feasibility audit

Date: 2026-10-28

## Verdict

**UNRESOLVED.**  Replacing the fixed principal arc by an arc of radius

```text
A * log(N) / N,    1 <= A <= 8,
```

is mathematically consistent and affordable on the inherited paper inputs, but it does not produce
a materially narrower fixed-center theorem.  Under the stopping rule in
`RouteCVariablePrincipalArcFeasibilityAssignment.md`, this candidate is not a Route C architecture
to advance to Lean or certificate generation.

Two results survive independently:

1. the isolated prime companion loses its negative `N * log(N)` average after the principal arc is
   widened; and
2. the complete hard discrepancy changes by less than `0.000061 * N`.

The second result is decisive for the project decision.  It shows that the combined Mobius--prime
problem after widening is quantitatively almost the same as the old one.

## Exact geometry

Put

```text
ell = log N,
R = A * ell,
```

and keep every rational arc with denominator `2 <= q <= 100` unchanged.  At the frozen threshold,
the widened principal arc is disjoint from all of those arcs.  Its exact Fourier kernel is

```text
W_(A,N)(0)
  = 2*R/N + (200/N) * sum_(2 <= q <= 100) phi(q)/q,

W_(A,N)(j)
  = sin(2*pi*R*j/N)/(pi*j)
    + sum_(2 <= q <= 100) c_q(j)
        * sin(200*pi*j/(q*N))/(pi*j),       j != 0.
```

The retained set is invariant under negation, so the kernel is real and even.  If

```text
K_(A,N)(j) = 1_(j=0) - W_(A,N)(j),
```

then the exact complementary discrepancy is

```text
Delta_A(N)
  = sum_(d>u, L<=d*m<=U) sum_(L<=b<=U)
      mu(d) * log(m) * Lambda(N-b) * K_(A,N)(d*m-b).
```

No approximation is used in these identities.

## Phase 1: prime companion

For the positive prime-divisor coefficient `P_N`, the exact sign identity remains

```text
Delta_(P,A)(N) = -C_N(P_N,S_N) + J_(M_A)(P_N,S_N).
```

The growing-frequency calculation gives, for each fixed `A` in `[1,8]`,

```text
  sum_(X<N<=2X, N even) Delta_(P,A)(N)
  ------------------------------------
       sum_(X<N<=2X, N even) N

    -> -(log(3) - 2/3)/(pi^2*A).
```

The adverse constant is less than `0.044/A`.  Thus the fixed-mask negative `N * log(N)` average is
removed.  This is an average over centers, however; it is not a pointwise `O(N)` allowance and
cannot be subtracted from a pointwise retained-main reserve.

The paper derivation supplies explicit growing-frequency PNT, discretization, endpoint, and
unchanged nonprincipal-arc errors.  Those details should be retained if this result is later
formalized as a standalone theorem.

## Phase 2: retained budget

The widened principal arc does not consume the provisional retained margin.  Recomputing, rather
than reusing, its Type-I and prime approximation errors gives

```text
R_(major,A)(N) > 0.699 * N
```

uniformly for `1 <= A <= 8`, on the inherited active-main and short-Type-I paper inputs.  The new
principal approximation errors are negligible at the frozen threshold, and the `q >= 2` rows are
unchanged.

This remains a paper-level conditional ledger.  In particular, the inherited active-main and
complete short-Type-I estimates were not independently re-proved by this feasibility study.

## Phase 3: decisive comparison

Let `Delta_old` denote the complete discrepancy for the original `P=Q=100` mask.  Only the added
principal annulus differs, so

```text
Delta_A(N) = Delta_old(N) - G_A(N).
```

Estimating the added annulus with the combined Mobius coefficient, rather than the isolated prime
companion, gives the uniform paper bound

```text
|G_A(N)| < 0.000061 * N,
```

and therefore

```text
|Delta_A(N) - Delta_old(N)| < 0.000061 * N.
```

This proves that the widening exposes real cancellation in the newly retained strip, but does not
control the remaining cross-correlation.  For example,

```text
Delta_A(N) >= -0.69*N
```

would already imply

```text
Delta_old(N) >= -0.690061*N.
```

That is essentially the old Goldbach-level fixed-center demand, not a substantially weaker
arithmetic theorem.

## Residual test

The exact prime/composite decomposition remains

```text
h_u = -P_N + H_(comp,N),
Delta_A = Delta_(P,A) + Delta_(comp,A).
```

No pointwise sign or adequate independent estimate was obtained for the composite contribution.
The factorability obstruction is also unchanged because widening a Fourier arc does not alter the
raw Mobius interval weight.

A worked balanced block, with coefficient collisions and prime powers restored, gives only

```text
|B_(D,A)| <= D^2 * (24*log(N) + 4),
```

and the global forecast is

```text
Delta_A(N)/N
  >= -[6*log(N)*(1+log(N)) + 0.201
       + 32*N^(-1/6)*log(N)^2].
```

The forecast misses the required constant scale by an unabsorbed `log(N)^2`, not by a small
numerical margin.  Almost-all-center results cannot supply the required estimate for every fixed
even center.

The remaining theorem is therefore still the full fixed-center signed Mobius--reflected-prime
correlation

```text
sum_(d>u, L<=d*m<=U) mu(d)*log(m)
  * [Lambda(N-d*m)
     - sum_(L<=b<=U) Lambda(N-b)*W_(A,N)(d*m-b)]
  >= -d_A*N,
```

with `d_A < 0.699`.  No independently controlled smaller coefficient family emerged.

## Project decision

The three feasibility gates have the following status:

| Gate | Outcome |
|---|---|
| Growing-frequency prime-companion calculation | Passed as an averaged theorem |
| Recomputed retained-main budget | Passed conditionally on inherited paper inputs |
| Materially narrower complementary theorem | Failed |

Accordingly:

* do not commission a Route C Lean development or finite certificate;
* preserve the growing-arc prime-companion average and the `0.000061*N` comparison as standalone
  paper results;
* do not interpret the averaged companion constant as a pointwise Goldbach allowance; and
* treat the currently identified Triple-Interface Goldbach endgames as exhausted unless a genuinely
  new joint fixed-center estimate or a different proof architecture is supplied.

This verdict does not disprove Goldbach and does not show that Triple Interface has no other
possible applications.  It closes this specific variable-principal-arc candidate under the
assignment's predeclared stopping rule.

## Subsequent bounded investigation

A later structural observation identifies a proper subproblem that is not obtained by widening the
mask: combine all large divisors belonging to the same integer before estimating them.  On the
one-large-prime/small-cofactor region this gives the exact identity

```text
h_u(p*r) = -Lambda(r).
```

The corresponding effective fixed-center sieve and retained-projection calculation have not been
proved.  They are specified, with normalization and common-factor safeguards, in
`SupportingDocs/RouteASmallCofactorCancellationFeasibilityAssignment.md`.  This is a bounded
research test, not an authorized Route C continuation or a named replacement route.
