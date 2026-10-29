# Small-cofactor cancellation audit

Date: 2026-10-29

## Status

**Independent paper-level PASS for the defined proper subproblem.**  A second review rederived the
finite sieve, common-factor and prime-power rows, signed retained projection, threshold ledger, and
final constant without correction.  The review separately passed the normalized active-main theorem
`M_A(N)>0.91*S(N)*N`.

Neither result is formalized in Lean.  The review did not independently recertify every other Stage 1
estimate, so the combined `0.708*S(N)*N` reserve remains a separate reconciliation gate.  These
results do not close Route A, reopen Route C, or establish a new Route D.  See
`SupportingDocs/RouteASmallCofactorCancellationIndependentReview.md`.

## Exact structural input

For

```text
h_u(n) = sum_(d|n, d>u) mu(d)*log(n/d),
```

if

```text
n = p*r,
p>u is prime,
1<=r<=u,
```

then all large divisors are exactly `p*s` with `s|r`, and

```text
h_u(p*r)
  = -sum_(s|r) mu(s)*log(r/s)
  = -Lambda(r).
```

The representation is unique because a second prime factor exceeding `u` would divide `r<=u`.
This identity agrees with the checked source theorem `vaughanHardArithmetic_apply`; the specialized
small-cofactor theorem itself is not yet in Lean.

For a fixed `eta` in `(0,1/3]`, put

```text
y = floor(N^eta),
U_eta(N) = {p*r in [L,U] : p>u prime, r<=y}.
```

The exact split is

```text
Delta(N) = Delta_eta(N) + Delta_remaining_eta(N),
Delta_eta(N) = -C_eta(N) + J_eta(N),
```

where `C_eta` is the full nonnegative reflected-prime convolution and `J_eta` is its signed retained
projection under the fixed `P=Q=100` mask.

## Coefficient mass

The exact mass is

```text
sum_(n in U_eta(N)) |h_u(n)|
  = sum_(r<=y) Lambda(r) * [pi(U/r)-pi(u)].
```

The paper derivation gives

```text
sum_(n in U_eta(N)) |h_u(n)|
  = (log(1/(1-eta)) + o(1))*N
```

for fixed `eta`, together with the effective envelope

```text
sum_(n in U_eta(N)) |h_u(n)|
  <= [3*eta/(1-eta)]*N.
```

This is used only as a structural diagnostic, not as a substitute for the correlation estimate.

## Full convolution estimate

For coprime `r=lambda^k`, the two linear forms are

```text
p,
N-r*p.
```

Their local singular factor is

```text
S(N,r) = S(N)*(lambda-1)/(lambda-2) <= 2*S(N).
```

The report derives a finite Selberg upper sieve from exact polynomial root counts.  With

```text
X=N/r,
z=X^(1/10),
```

its deliberately coarse bound is

```text
#{t<=X : (t*(N-r*t), product_(p<=z) p)=1}
  <= 40000*S(N,r)*X/log(X)^2 + X^(3/5).
```

After restoring all logarithmic weights and summing the prime-power cofactors,

```text
C_eta(N)
  <= [160000*eta/(1-eta)^2]*S(N)*N + E_C(N,eta).
```

The report separately treats:

* proper prime powers in `Lambda(N-r*p)`;
* `(r,N)>1`, where the reflected value must be a power of the common prime; and
* the finite sieve remainder and small reflected primes.

It claims

```text
E_C(N,eta)/N < exp(-300)
```

throughout the frozen range.

## Retained projection

The retained calculation uses the actual fixed rational arcs.  For `q<=100`, it defines

```text
g_(eta,q)(t)
  = sum_(r<=y) Lambda(r)/(r*log(t/r))
      * rho_(q/(q,r)) * 1_(r*u<t<=U).
```

The quotient `q/(q,r)` preserves common factors between the cofactor and the arc denominator.
Using the published fixed-modulus prime estimates, the report obtains an explicit approximation to
the Fourier transform of the grouped coefficient and the ordinary prime factor.

The signed model is

```text
J_eta^0(N)
  = sum_(q<=100) c_q(N)*rho_q
      * integral_L^U g_(eta,q)(t)*w_q(t) dt.
```

The report displays the coefficient sign in all squarefree rows, including whether the prime base
of `r` divides `q` or `N`; nonsquarefree rows vanish in the model because `rho_q=0`.  Only after that
signed expansion does it take a lower envelope:

```text
J_eta^0(N) >= -800*eta*N.
```

The integrated approximation errors give

```text
J_eta(N) >= -800*eta*N - E_J(N,eta),
```

with an explicit `E_J` claimed below `10^(-40)*N` for the selected parameter.

## Concrete theorem

The general paper estimate is

```text
Delta_eta(N)
  >= -[160000*eta/(1-eta)^2]*S(N)*N
     -800*eta*N
     -E_C(N,eta)-E_J(N,eta).
```

The singular factor satisfies `S(N)>=1`.  At

```text
eta = 1/100000000,
```

the leading normalized coefficient is

```text
160000*eta/(1-eta)^2 + 800*eta
  = 0.00160800003200000048...
  < 0.001609.
```

The resulting claimed theorem is

```text
Delta_(10^-8)(N) > -0.001609*S(N)*N
```

for every admissible even `N`.

This is a singular-series-normalized result.  It is not the stronger statement
`Delta_eta(N)>-0.001609*N`.

## Separation from the Stage 1 ledger

The small-cofactor theorem does not depend on the provisional Stage 1 reserve.

The report separately proposes a strengthened active-main estimate

```text
M_A(N) > 0.91*S(N)*N.
```

If that estimate and the inherited Stage 1 hard-model, Type-I, and prime-power allowances all pass
independent review, then one obtains the conditional bookkeeping comparison

```text
R_major(N) > 0.708*S(N)*N,
```

leaving more than

```text
0.706391*S(N)*N
```

for the exact complement after subtracting the new small-cofactor allowance.

This normalized Stage 1 comparison is not part of the unconditional small-cofactor PASS.  It has a
separate verification burden and must not be reported as checked.

## Remaining support

The report gives an exact factorization-based partition of the complement.  The main rows are:

| Region | Surviving coefficient |
|---|---|
| `n=p*r`, `p>u`, `r<=N^eta` | `-Lambda(r)`; controlled by the theorem |
| `n=p*r`, `p>u`, `N^eta<r<=u` | `-Lambda(r)`; same structure, not controlled at useful scale by the current constant |
| Exactly one large prime and `r>u` | `h_u(r)+log(p)*R_u(r)-Lambda(r)` |
| Two distinct large primes, `r=1` | `-log(p*q)` |
| Two distinct large primes, `r>1` | `-Lambda(r)` |
| Repeated large prime, `r=1` | `-log p` |
| Repeated large prime, `r>1` | `-Lambda(r)` |
| No large prime factor | The original truncated-divisor expression |

No favorable fixed-center sign follows for these remaining rows merely from the partition.

## Verification outcome and remaining boundary

Independent review has now passed the finite Selberg weight and denominator, common-factor and
proper-prime-power classification, rational-arc constants, signed retained model, threshold errors,
and the separate `0.91*S(N)*N` active-main strengthening.

Before a closure ledger is used, the remaining paper boundary is the other inherited Stage 1
estimates: the denominator-row lower total, complete Type-I error, major-model approximation error,
and prime-power allowance must be reconciled with the newly normalized active main on one exact
decomposition.  Lean formalization remains downstream of that paper gate.

## Project consequence

This is the first post-obstruction paper result to remove a proper, explicitly defined part of the
hard coefficient with a uniform fixed-center bound after restoring the retained projection.  It is
real progress, but its chosen range `r<=N^(10^-8)` is very narrow and the complement still contains
the principal unresolved arithmetic difficulty.

Do not start a full-complement certificate or call this Route D.  The next bounded paper gate is
`SupportingDocs/RouteAOneLargePrimeCompletionFeasibilityAssignment.md`.  It first reconciles the
normalized Stage 1 reserve and then tests the entire one-large-prime row.  Merely increasing `eta`
within the present microscopic range is not a completion strategy.
