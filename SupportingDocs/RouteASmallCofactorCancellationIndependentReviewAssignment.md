# Independent review assignment: small-cofactor cancellation theorem

Date: 2026-10-29

## Outcome

**PASS for both paper theorems.**  Independent review accepted, without changing constants,

```text
Delta_(10^-8)(N)>-0.001609*S(N)*N,

M_A(N)>0.91*S(N)*N.
```

The combined `0.708*S(N)*N` Stage 1 reserve was not part of this verdict because it also depends on
other inherited Stage 1 estimates.  The result and its remaining boundary are recorded in
`SupportingDocs/RouteASmallCofactorCancellationIndependentReview.md`.  The next assignment is
`SupportingDocs/RouteAOneLargePrimeCompletionFeasibilityAssignment.md`.

## Review question

Independently determine whether the claimed paper theorem

```text
Delta_(10^-8)(N) > -0.001609*S(N)*N
```

holds for every even `N>=exp(exp(100))` under the exact hard coefficient, balanced support, and
fixed `P=Q=100` retained mask.

This is a verification assignment, not an invitation to replace the proof with a different
heuristic.  Recompute the critical identities and constants.  Report **PASS**, **REVISE**, or
**FAIL** and identify the first invalid line if the proof breaks.

Read:

```text
SupportingDocs/RouteASmallCofactorCancellationFeasibilityAssignment.md
SupportingDocs/RouteASmallCofactorCancellationAudit.md
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
```

The small-cofactor theorem must be reviewed separately from the proposed normalized Stage 1
comparison.

## 1. Exact algebra and support

Verify directly from `vaughanHardArithmetic_apply` that

```text
h_u(p*r) = -Lambda(r)
```

when `p>u` is prime and `r<=u`.  Check:

* the use of `(p,r)=1`;
* the bijection between large divisors and `p*s`, `s|r`;
* uniqueness of the representation;
* floors in `u=floor(N^(1/3))` and `y=floor(N^eta)`;
* the lower and upper balanced endpoints; and
* the exact disjoint split of `Delta` into `Delta_eta` and its complement.

Do not infer the identity merely from numerical examples.

## 2. Coefficient-mass calculation

Reproduce

```text
sum_(n in U_eta(N)) |h_u(n)|
  = sum_(r<=y) Lambda(r)*[pi(U/r)-pi(u)].
```

Verify the uniform PNT asymptotic and the effective bound

```text
sum_(n in U_eta(N)) |h_u(n)|
  <= [3*eta/(1-eta)]*N.
```

Confirm that the subtraction term and every endpoint are present even when later discarded in an
upper bound.

## 3. Finite Selberg upper sieve

Re-derive, rather than quote, the following steps for each coprime prime-power cofactor
`r=lambda^k`:

1. the local root count for `t*(N-r*t)`;
2. the singular product

   ```text
   S(N,r) = S(N)*(lambda-1)/(lambda-2) <= 2*S(N);
   ```

3. the exact Selberg weights and `lambda_1=1`;
4. the quadratic diagonalization giving `1/G(z)`;
5. the bound on the residue-count remainder;
6. the probabilistic/Euler-product lower bound

   ```text
   G(z) >= log(z)^2/[400*S(N,r)];
   ```

7. the resulting `40000` sieve constant after `z=X^(1/10)`; and
8. restoration of `Lambda(r)` and `Lambda(N-r*p)`.

Check that all uses of `log z>=40`, `p>u>z`, and `X=N/r` hold uniformly at the frozen threshold.

Then independently verify the disjoint treatment of:

* reflected proper prime powers;
* `(r,N)>1`, including the fact that the reflected value must be a power of the common prime;
* small reflected primes; and
* the finite sieve remainder.

The required Phase 2 result is

```text
C_eta(N)
  <= [160000*eta/(1-eta)^2]*S(N)*N + E_C(N,eta),
```

with the claimed explicit bound on `E_C`.

## 4. Signed retained projection

Independently derive the Fourier approximation for the grouped coefficient on every reduced
`a/q`, `q<=100`.  In particular check:

* why the modulus becomes `q/(q,r)`;
* coprimality of the reduced numerator;
* the use of the `pi` rather than `psi` progression estimate for the prime variable;
* strict `p>u` endpoints;
* the constants `20000` and `2000` in the grouped-coefficient error;
* the `10*N/log N` error for the reflected von Mangoldt factor, including `q=1,2`;
* total retained measure; and
* the integrated product-error calculation.

Reproduce the exact signed model

```text
J_eta^0(N)
  = sum_(q<=100) c_q(N)*rho_q
      * integral g_(eta,q)(t)*w_q(t) dt.
```

Verify the coefficient table separately when the prime base of `r`:

1. does not divide `q`;
2. divides `q` but not `N`; and
3. divides both `q` and `N`.

Confirm that nonsquarefree rows vanish only in the model and that their actual contribution is
covered by the approximation error.

The required lower bound is

```text
J_eta(N) >= -800*eta*N - E_J(N,eta).
```

## 5. Threshold and numerical ledger

For `eta=10^-8`, verify with outward rounding:

```text
160000*eta/(1-eta)^2 + 800*eta
  = 0.00160800003200000048...
  < 0.001609.
```

Check every monotonic estimate used to show

```text
E_C/(S(N)*N) + E_J/(S(N)*N)
  < 0.000000999967...
```

at `log N>=exp(100)`.  Do not rely on floating-point evaluation of `N` itself.

Confirm independently that

```text
S(N)>=1.
```

The final PASS must retain the singular-series normalization.  It must not report
`-0.001609*N`.

## 6. Separate normalized active-main claim

Review the proposed statement

```text
M_A(N) > 0.91*S(N)*N
```

as a separate theorem.  Verify:

* the convolution `f_N=(mu/n)*g_N` prime-power by prime-power;
* the signed mass of `g_N`;
* both absolute-mass bounds for `g_N`;
* the finite truncation and tail split;
* the `0.033` profile error;
* the short `t<u` interval; and
* conversion from the pointwise profile to the exact active-main object.

A failure here does not by itself invalidate the small-cofactor theorem.  It invalidates only the
claimed comparison with a `0.708*S(N)*N` retained reserve.

## Required verdict

### PASS

State separately:

1. whether the small-cofactor theorem passes;
2. whether the normalized active-main strengthening passes; and
3. which claims remain paper-level rather than Lean-checked.

### REVISE

Give a corrected constant and theorem if the architecture is valid but one inequality, endpoint,
or normalization needs repair.  Recompute the final ledger.

### FAIL

Identify the first false identity or estimate and determine whether it destroys the fixed-center
gain or only changes its numerical coefficient.

## Prohibited shortcuts

The review does not pass if it:

1. checks only the final decimal;
2. treats coefficient mass as a correlation estimate;
3. omits the retained projection;
4. averages over centers;
5. assumes coprimality in the common-factor rows;
6. suppresses prime powers;
7. spends a singular-series-scaled error against an `N`-scaled reserve; or
8. accepts a citation as a substitute for deriving its exact application.

## Consequence

If the small-cofactor theorem receives an independent PASS, preserve it as a standalone theorem
and begin a bounded range-expansion study: improve the sieve/model constants and determine the
largest explicit `eta` for which the normalized gain remains useful.  Do not start with the full
remaining hard correlation.
