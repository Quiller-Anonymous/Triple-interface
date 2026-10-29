# Route A one-large-prime completion feasibility assignment

Date: 2026-10-29

## Outcome

**Provisional paper-level UNRESOLVED.**  Gate 0 reconciles the normalized reserve, the complete row
has local-model coefficient `log(3/2)`, and the retained projection has a uniformly positive main
term.  No verified fixed-center averaged prime-pair theorem controls the actual convolution with the
required constant.

Sharper summation of the reviewed finite sieve proves the safe fallback

```text
Delta_(17699/10^9)(N)>-0.707972531*S(N)*N,
```

but `17699/10^9<10^-4`, so the assignment's stopping rule applies.  The outcome is recorded in
`SupportingDocs/RouteAOneLargePrimeCompletionAudit.md`; the next and final gate for these new claims
is the bounded independent review in
`SupportingDocs/RouteAOneLargePrimeCompletionIndependentReviewAssignment.md`.

## Decision question

Can the reviewed same-integer cancellation be extended from the microscopic range

```text
r<=N^(10^-8)
```

to the complete one-large-prime range

```text
n=p*r,
p>u prime,
1<=r<=u=floor(N^(1/3)),
```

with a fixed-center, singular-series-normalized discrepancy bound that fits inside the reviewed
major-arc reserve?

This is a bounded paper-mathematics test.  It is not permission to start a new certificate, a Lean
formalization, or an open-ended search for progressively larger microscopic exponents.

Read:

```text
SupportingDocs/RouteASmallCofactorCancellationAudit.md
SupportingDocs/RouteASmallCofactorCancellationIndependentReview.md
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
SupportingDocs/RouteAEnlargedMajorArcStage1SpecialistReport.md
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanActiveMain.lean
```

## Fixed objects

For every even integer

```text
N>=exp(exp(100)),
```

retain

```text
L=1,000,001,
U=N-L,
u=floor(N^(1/3)),
P=Q=100.
```

The hard arithmetic coefficient is

```text
h_u(n)=sum_(d|n, d>u) mu(d)*log(n/d).
```

For `0<eta<=1/3`, put

```text
y=floor(N^eta),
U_eta={p*r in [L,U] : p>u prime, r<=y}.
```

The exact same-integer identity is

```text
h_u(p*r)=-Lambda(r)
```

on this support.  Define the associated fixed-center discrepancy by

```text
Delta_eta(N)=-C_eta(N)+J_eta(N),
```

where `C_eta` is the full reflected-prime convolution and `J_eta` is its actual signed retained
projection under the fixed `P=Q=100` mask.

The endpoint `eta=1/3` is the complete one-large-prime row.  Floors and the condition `p>u` must be
kept exact.

## Reviewed inputs

The following are independent paper-level PASS results:

```text
M_A(N)>0.91*S(N)*N,

Delta_(10^-8)(N)>-0.001609*S(N)*N.
```

They are not Lean theorems.

The previous Stage 1 report also claims the denominator-row lower bound and the following
`N`-scaled errors:

```text
major-model row sum       >= -0.200982*N,
complete Type-I error      < 5*10^-15*N,
major-model error          < 10^-37*N,
prime-power allowance      < 10^-130*N.
```

Those inherited estimates must pass Gate 0 below before a normalized reserve may be spent.

## Gate 0: reconcile the normalized Stage 1 ledger

Independently verify that all five terms refer to the same exact balanced support, Fourier
normalization, retained mask, and sign convention.  In particular, check that the `-0.200982*N`
row total is an additive lower contribution and that none of its terms is already included in the
active-main estimate.

Using `S(N)>=1`, establish or correct the comparison

```text
R_major(N)
  > [0.91-0.200982-5*10^-15-10^-37-10^-130]*S(N)*N
  > 0.708*S(N)*N.
```

The conversion of an `N`-scaled negative allowance to an `S(N)*N`-scaled allowance must be written
with the inequality in the correct direction.

### Gate 0 stopping rule

If the components do not belong to one exact decomposition, if a term is double-counted, or if the
normalization conversion is invalid, return **REVISE** or **FAIL** immediately.  Do not perform the
range-expansion study against a reserve that has not been reconciled.

## Gate 1: establish the true scale of the full row

For general fixed `eta<=1/3`, derive the leading model for `C_eta` without importing the crude
constant `160000`.  Treat separately:

1. coprime prime-power cofactors `r=lambda^k`;
2. `(r,N)>1`;
3. reflected proper prime powers;
4. endpoint ranges created by `L`, `U`, `u`, and `floor(N^eta)`; and
5. the subtraction caused by the strict condition `p>u`.

The expected coprime prime-pair scale is approximately

```text
S(N)*N*log(1/(1-eta)),
```

which at `eta=1/3` is

```text
log(3/2)*S(N)*N = 0.4054651081...*S(N)*N.
```

This heuristic is not an allowed input.  Confirm, correct, or reject it from the exact local factors
and weights.  State the actual leading coefficient and every secondary term.

## Gate 2: couple the full correlation to the retained projection

The microscopic proof separately used

```text
C_eta <= [160000*eta/(1-eta)^2]*S(N)*N + E_C,

J_eta >= -800*eta*N-E_J.
```

At `eta=1/3` this costs more than `120000*S(N)*N` and is useless.  Do not attempt to finish the
assignment by merely optimizing those two constants independently.

Instead, derive compatible main models

```text
C_eta=C_eta^0+E_full,

J_eta=J_eta^0+E_retained,
```

and compare

```text
-C_eta^0+J_eta^0
```

before taking absolute values.  The retained model must preserve:

```text
q/(q,r),
c_q(N),
rho_q,
the exact rational-arc kernel,
common factors between q and r,
and the squarefree/nonsquarefree distinction.
```

Supply either an exact finite expression or a rigorously bounded integral/Euler-product expression
for the signed model at `eta=1/3`.  A blanket estimate such as `J_eta>=-A*eta*N` is only a diagnostic;
it does not pass this gate.

## Gate 3: identify and test the required averaged prime-pair theorem

The full term has the schematic arithmetic form

```text
sum_(r<=u) Lambda(r)
  sum_(u<p<=U/r, p prime) Lambda(N-r*p).
```

The needed estimate is at one prescribed even center `N`, but it averages over the prime-power
cofactor `r`.  Determine whether a published unconditional theorem, or a derivation from explicit
published inputs, gives a sufficiently sharp asymptotic or upper bound for this exact average.

For every candidate theorem:

1. quote its exact statement and range;
2. map its variables to `r`, `p`, and `N-r*p`;
3. verify whether it is uniform at each fixed `N` or only on average over `N`;
4. restore the `Lambda(r)` weight, prime powers, common factors, and endpoints;
5. state its singular-series normalization;
6. calculate every coefficient after summing all dyadic ranges; and
7. combine its error with the signed retained model from Gate 2.

Generic Brun--Titchmarsh, a pointwise dimension-two upper sieve, or an average over centers does not
pass unless the final fixed-center constant fits the ledger.

As a feasibility diagnostic, if the full model coefficient is `log(3/2)` and the retained model
does not help, the multiplicative upper-bound factor must be strictly below

```text
0.708/log(3/2)=1.7461428513...
```

just to avoid exhausting the reserve.  A factor `2` is insufficient.  Recompute this threshold if
Gate 1 or Gate 2 changes the model.

## Gate 4: final full-row inequality

The target is

```text
Delta_(1/3)(N)>-c_one_large*S(N)*N
```

uniformly for every admissible even `N`, with all errors explicit.

Report two thresholds:

```text
row-compatible: c_one_large<0.708,

strategically useful: c_one_large<=0.600.
```

The first threshold means only that this row does not consume the entire candidate Stage 1 reserve;
it is not Route A closure.  The second threshold leaves at least `0.108*S(N)*N` for the remaining
factorization rows.  Passing only the first threshold removes the one-large-prime row but may leave
too little budget to finish the route; state that distinction explicitly.

## Gate 5: bounded fallback and stopping rule

If the complete row cannot be proved, determine the largest explicit exponent `eta_*` supported by
the same reviewed theorem.  At minimum report outward-rounded values at

```text
eta=10^-8,
eta=10^-6,
eta=10^-4,
eta=10^-2,
eta=1/3.
```

For each value give:

```text
full-correlation allowance,
retained-model contribution,
total discrepancy constant,
remaining normalized reserve,
and the theorem used.
```

### Required stopping rule

If the argument controls only `eta<10^-4`, or if it still requires the complete fixed-center
Goldbach discrepancy as an input, return **UNRESOLVED** and stop.  A larger microscopic exponent is
not enough to authorize a new route or formalization project.

An exponent at least `10^-2` counts as a meaningful partial result only if the proof mechanism can
be iterated over the remaining cofactor ranges without spending the reserve once per interval.
Explain that mechanism explicitly.  Otherwise classify it as a local theorem, not a completion
architecture.

## Required verdict

### PASS

Supply:

1. a reconciled `0.708*S(N)*N` Stage 1 reserve;
2. the exact full one-large-prime decomposition;
3. the coupled full/retained main calculation;
4. a fixed-center theorem controlling the averaged prime-pair error;
5. all common-factor, prime-power, and endpoint allowances; and
6. a final `c_one_large<0.708`, with the strategically useful threshold reported separately.

### PARTIAL

Use this only for a rigorously proved macroscopic exponent together with a concrete, nonduplicative
iteration mechanism.  State exactly which cofactor range remains.

### UNRESOLVED

Identify the first missing theorem and state it as a standalone fixed-center inequality with all
weights, ranges, and constants.  Record the best proved `eta_*`, but do not begin incremental
certificate or Lean work.

### FAIL

Give a contradiction or a rigorous lower barrier showing that this architecture cannot fit inside
the normalized reserve, even with optimal treatment of the retained model.

## Prohibited shortcuts

The investigation does not pass if it:

1. treats the expected `log(1/(1-eta))` main as a proved asymptotic;
2. uses a theorem averaged over `N` for the required fixed center;
3. separates `C_eta` and `J_eta` by absolute values before comparing their main models;
4. drops `q/(q,r)` or assumes `(q,r)=1`;
5. suppresses reflected prime powers or `(r,N)>1`;
6. spends an `N`-scaled allowance against an `S(N)*N` reserve in the wrong direction;
7. reports a succession of microscopic exponents as Route A progress; or
8. begins formalization before the full-row feasibility decision is known.

## Interpretation

The reviewed `eta=10^-8` theorem proves that the same-integer cancellation is analytically usable.
This assignment asks whether it scales far enough to remove a complete structural row.  If it does
not, the proper conclusion is that the local theorem should be preserved independently while Route A
remains suspended.

