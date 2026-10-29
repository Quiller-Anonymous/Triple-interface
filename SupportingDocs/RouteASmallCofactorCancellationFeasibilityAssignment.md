# Small-cofactor cancellation feasibility assignment

Date: 2026-10-28

## Outcome

**Provisional paper-level PASS for the proper subproblem.**  The specialist derives, for
`eta=10^-8`, the uniform fixed-center bound

```text
Delta_eta(N) > -0.001609*S(N)*N.
```

The full reflected-prime convolution, common-factor and prime-power rows, signed retained model,
and integrated approximation errors are included.  The result retains its singular-series
normalization and is not charged against the old `0.699*N` reserve.

This outcome is not yet independently reviewed or Lean-checked.  The audit is
`SupportingDocs/RouteASmallCofactorCancellationAudit.md`; the next gate is
`SupportingDocs/RouteASmallCofactorCancellationIndependentReviewAssignment.md`.  Do not widen the
range, start a certificate, or call this Route D before that review.

## Status and decision boundary

This is a bounded paper-mathematics investigation of a proper subproblem of the fixed-center hard
correlation.  It is not Route D, does not reopen fixed-mask Route A or variable-arc Route C, and
does not authorize Lean formalization, certificate generation, or a claim of progress toward an
unconditional Goldbach endpoint.

The candidate is worth testing because it first combines all large-divisor terms attached to the
same integer `n`.  This preserves an exact algebraic cancellation that was destroyed by the
isolated-prime-modulus decomposition.

The investigation passes only if it produces an effective, uniform, fixed-center estimate for the
defined small-cofactor contribution whose gain survives the retained projection and recombination.
An asymptotic coefficient-mass calculation alone is not a pass.

Read:

```text
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
SupportingDocs/RouteAPrimeCompanionObstruction.md
SupportingDocs/RouteAComplementaryCrossStage2Audit.md
SupportingDocs/RouteAFactorableDispersionAudit.md
SupportingDocs/RouteCVariablePrincipalArcAudit.md
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
```

## Fixed objects

For every admissible even integer `N`, retain

```text
L = 1,000,001,
U = N-L,
u = floor(N^(1/3)).
```

Use the fixed `P=Q=100` retained mask and its exact real kernel `W_N`; the variable-principal-arc
audit proved that widening the principal arc changes the complete discrepancy by less than
`0.000061*N` and does not narrow the remaining theorem.

The hard arithmetic coefficient is

```text
h_u(n) = sum_(d|n, d>u) mu(d) * log(n/d).
```

This is exactly the coefficient represented in Lean by

```text
vaughanHardArithmetic u v n
```

through `vaughanHardArithmetic_apply`; it is independent of the auxiliary cutoff `v`.

Define

```text
E_N(n)
  = Lambda(N-n)
    - sum_(L<=b<=U) Lambda(N-b) * W_N(n-b),

Delta(N) = sum_(L<=n<=U) h_u(n) * E_N(n).
```

All regrouping must occur before taking absolute values.  Since every divisor contribution for a
fixed `n` multiplies the same `E_N(n)`, this regrouping is exact and kernel-independent.

## Phase 0: exact small-cofactor decomposition

### Required algebraic lemma

Prove that if

```text
n = p*r,
p > u is prime,
1 <= r <= u,
```

then

```text
h_u(p*r) = -Lambda(r).
```

The proof must explicitly use `p>r`, hence `(p,r)=1`, and identify every divisor of `p*r` exceeding
`u` as `p*s` with `s|r`.  Then

```text
h_u(p*r)
  = -sum_(s|r) mu(s)*log(r/s)
  = -Lambda(r).
```

Record uniqueness: an integer `n=p*r` with `p>u` and `r<=u` cannot have a second prime divisor
exceeding `u`.

### Exact support split

For a fixed rational `eta` with `0 < eta <= 1/3`, define

```text
U_eta(N)
  = {n in [L,U] : n=p*r, p>u prime, r<=N^eta}.
```

At the frozen threshold, state and prove all floor and endpoint conditions needed to replace
`L<=p*r` by an automatic consequence of `p>u`; otherwise retain the lower endpoint explicitly.

Define

```text
Delta_eta(N)
  = -sum_(r<=N^eta) Lambda(r)
      * sum_(p>u prime, L<=p*r<=U) E_N(p*r),
```

and prove the exact disjoint decomposition

```text
Delta(N) = Delta_eta(N) + Delta_remaining_eta(N).
```

No contribution may be dropped or counted twice.  Because `Lambda(r)` is nonzero only for prime
powers, expose `r=ell^k` at the next analytic stage rather than treating `r` as an arbitrary dense
coefficient.

### Phase 0 stopping condition

Stop and report **FAIL** if the claimed identity or uniqueness does not hold under the repository's
actual cutoff, balanced support, or arithmetic-function conventions.

## Phase 1: effective coefficient-mass theorem

First establish the asymptotic diagnostic

```text
sum_(n in U_eta(N)) |h_u(n)|
  = (log(1/(1-eta)) + o(1)) * N.
```

For `eta=1/3`, the constant is `log(3/2)`.  The count must retain

```text
pi((N-L)/r) - pi(u)
```

and justify uniform PNT use for all `r<=N^eta`.  Include the subtraction term involving `pi(u)` and
the balanced endpoints.

Then replace `o(1)` by an explicit upper bound valid at the frozen threshold.  Produce a function

```text
M_eta(N)
```

such that

```text
sum_(n in U_eta(N)) |h_u(n)| <= M_eta(N) * N,
```

with a displayed uniform bound and `M_eta -> 0` as `eta -> 0` in the intended parameter regime.

This phase is diagnostic only.  Do not multiply the mass by `sup Lambda <= log N` and call that the
required correlation estimate.

### Phase 1 stopping condition

Stop with **REVISE** if no effective version is available at the frozen threshold.  Do not advance
to numerical budget claims using only an ineffective asymptotic.

## Phase 2: unretained small-cofactor convolution

Write the full nonnegative term as

```text
C_eta(N)
  = sum_(r<=N^eta) Lambda(r)
      * sum_(p>u prime, L<=p*r<=U) Lambda(N-p*r).
```

The negative sign in `Delta_eta` makes an upper-bound sieve relevant to this term.  The sieve may be
applied only after the exact same-`n` cancellation from Phase 0.

### Required arithmetic split

Since `r` is a prime power, separate:

1. `(r,N)=1`, where the two linear forms are `p` and `N-r*p` and the ordinary local factors apply;
2. `(r,N)>1`, where `N-r*p` has a forced common prime divisor and is nonzero under `Lambda` only in
   exceptional prime-power cases; and
3. proper prime powers in `Lambda(N-r*p)`, which must be bounded explicitly rather than silently
   identified with primes.

For `(r,N)=1`, verify the local root count prime by prime.  In particular, the statement

```text
nu_ell = 1 when ell | r*N
```

is valid only under the coprimality split.  If `ell` divides both `r` and `N`, the second form is
identically zero modulo `ell`, so that case must not be put into the generic singular-series row.

Use an explicit upper-bound sieve to obtain a completely specified estimate.  The natural output
may have the form

```text
C_eta(N) <= B_eta(N) * S(N) * N + PP_eta(N),
```

where `S(N)` is the Goldbach singular factor and `PP_eta` is the prime-power/common-factor
allowance.  Show the dependence on `eta`, all endpoint changes, the sieve level, exceptional-zero
terms, and every logarithmic weight.

The explicit Chen literature is a source of methods and constants, not a theorem that can be cited
as if it directly proved this weighted sum.  The application must be derived for these exact linear
forms and ranges.

### Phase 2 stopping condition

Stop with **UNRESOLVED** if the resulting coefficient does not tend to zero with `eta`, if the
common-factor or prime-power rows lose the gain, or if the sieve estimate requires the missing
Goldbach correlation as an input.

## Phase 3: retained projection and signed recombination

Evaluate, with its actual sign,

```text
J_eta(N)
  = sum_(r<=N^eta) Lambda(r)
      * sum_(p>u prime, L<=p*r<=U)
          sum_(L<=b<=U) Lambda(N-b) * W_N(p*r-b).
```

Then

```text
Delta_eta(N) = -C_eta(N) + J_eta(N).
```

Do not bound the full hard coefficient by a sieve majorant.  The upper sieve controls only the
nonnegative `C_eta` after the exact support split.  The retained projection must be calculated from
the fixed rational arcs, including its main term, endpoint errors, prime powers, common divisors,
and signs.

The preferred output is an effective fixed-center lower bound

```text
Delta_eta(N) >= -D_eta(N),
```

with `D_eta(N)/N` explicit and tending to zero as `eta` decreases.

### Normalization safeguard

A result of the form

```text
Delta_eta(N) >= -b(eta) * S(N) * N
```

is a valid theorem about this subproblem, but it cannot be charged directly against the existing
paper reserve `0.699*N`.  The singular factor is not uniformly bounded by one.  To make a closure
ledger, either:

* prove a compatible retained lower bound on the same `S(N)*N` scale; or
* convert the small-cofactor estimate to a uniform `N`-scale allowance without losing the gain.

Do not mix these normalizations.

### Phase 3 stopping condition

Return **UNRESOLVED** if the full-convolution gain is consumed by the retained projection, by
singular-series conversion, or by summing the `r`-ranges.  That outcome would still locate a
specific obstruction and would not authorize work on the full complement.

## Phase 4: map the exact complement

Only if Phases 0--3 pass, partition `Delta_remaining_eta` by factorization of `n`, not by one outer
divisor at a time.

At minimum, distinguish:

| Region | Required treatment |
|---|---|
| One large prime, cofactor `<=N^eta` | Removed by `Delta_eta` |
| One large prime, larger cofactor | Write the surviving grouped coefficient exactly |
| Two large prime factors, remaining cofactor `<=u` | Use the exact grouped formula, separating `r=1`, repeated primes, and `r>1` |
| Remaining truncated-divisor region | State the genuinely signed coefficient left for analysis |
| Region boundaries | Retain exact indicators or pay explicit errors |

For example, verify rather than assume the formulas for `n=p*q*r` with `p,q>u`.  Repeated large
primes and `r=1` have different coefficients and must be separate rows.

The output is a support map and an exact identity, not a claim that the balanced remainder is now
small.

## Optional Phase 5: one spectral block

Do not begin this phase until the small-cofactor calculation has passed and the balanced surviving
coefficient is explicitly known.

The 2026 Pascadi bilinear Kloosterman theorem supplies a genuine operator saving for certain sums of
square-root length.  It is not directly a theorem about this reflected-prime remainder.  A valid
application must first derive an identity

```text
B_grouped
  = sum_q c_q * sum_(m,n) alpha_(q,m) * beta_(q,n)
      * S(a_q*m,n;q)
    + E,
```

with the modulus `q`, ranges, coprimality conditions, smoothing, common-divisor terms, and error `E`
all explicit.  Then insert the exact theorem statement and compute whether its power saving survives
the coefficient norms and the sum over moduli.

The modulus in this transformation is not automatically the retained-arc denominator or `N`.
Merely citing a Kloosterman bound, or leaving an uncontrolled transform of `Lambda(N-n)`, is a
**FAIL**.

Primary reference:

```text
Alexandru Pascadi,
Non-Abelian Amplification and Bilinear Forms with Kloosterman Sums,
Geom. Funct. Anal. 36 (2026), 1174--1243,
https://doi.org/10.1007/s00039-026-00746-0
```

## Required verdict

### PASS

Supply:

* the exact disjoint support decomposition;
* an effective coefficient-mass bound;
* a complete fixed-center upper sieve for `C_eta`;
* a signed retained-projection calculation;
* a lower bound for `Delta_eta` with all constants and compatible normalization; and
* a numerical demonstration that the gain survives recombination for at least one explicit
  `eta`.

A PASS removes a proper subproblem and authorizes investigation of the exact complement.  It does
not by itself establish a new Goldbach route.

### UNRESOLVED

Identify the precise failed phase and the exact theorem still needed.  Do not replace that theorem
by the complete `Delta(N)>=-0.699*N` endpoint.

### FAIL

Give a contradiction, local obstruction, or quantitative ledger showing that no useful gain
survives even for this proper subproblem.

## Prohibited shortcuts

The following do not pass:

1. Separating the prime divisor `p` again after proving the same-`n` cancellation.
2. Using coefficient mass as though it were a correlation bound.
3. Replacing a uniform fixed-center statement by an average over `N`.
4. Treating `Lambda` as a prime indicator without a prime-power allowance.
5. Applying the coprime singular series when `(r,N)>1`.
6. Spending an `S(N)*N` error against an `N`-normalized reserve.
7. Bounding the retained projection without its sign and then hiding the loss in `O(N)`.
8. Citing Chen, Friedlander--Iwaniec, or Pascadi without deriving their exact application.
9. Starting a full-complement Lean or certificate project before this bounded paper test passes.

## Interpretation

The exact identity

```text
h_u(p*r) = -Lambda(r)
```

is a real structural cancellation: multiple large-divisor terms that looked individually large
collapse before analysis because they share the same integer and kernel value.  It narrows one
piece of the hard coefficient to a prime--prime-power family.

What remains unknown is whether that grouped family has a sufficiently small uniform fixed-center
correlation after its retained projection is restored.  This assignment is designed to answer
that one question without committing the project to another disguised Goldbach endpoint.
