# Route A factorable-dispersion audit

Date: 2026-10-28

## Verdict

**UNRESOLVED.  The factorable-dispersion reduction fails Phase A, and this Route A branch is now
frozen as a conditional reduction.**

The investigation does not disprove the complete complementary bound.  It proves something more
specific and strategically decisive: the exact Mobius coefficient cannot be replaced by a finite
sum of triply well-factorable weights plus independently small companion errors.  In particular,
the prime-modulus companion is not an `O(N)` error under the retained mask.

No further Lean formalization, finite certificate, or proof-completion stage is authorized by this
result.

## Factorability obstruction

If `lambda` is triply well-factorable of level `Z`, apply its defining factorization at

```text
Z1 = Z2 = Z3 = Z^(1/3).
```

Every modulus in its support is then a product of three integers at most `Z^(1/3)`.  Consequently,

```text
lambda(d) = 0 whenever P+(d) > Z^(1/3).
```

The analogous necessary condition for ordinary well-factorability is `P+(d)<=Z^(1/2)`.
These support restrictions survive finite linear combinations of admissible weights.

The raw interval coefficient

```text
mu(d) * 1_(D,2D](d)
```

is nonzero at prime `d` of size comparable to `sqrt N`.  Covering those primes by a triply
well-factorable sequence would require a level comparable to `N^(3/2)`, far beyond the applicable
prime-distribution theorem.  Exact decompositions by the number of large prime factors preserve
this support somewhere in their companion terms; they do not make it disappear.

The specialist also checked explicit smooth/rough and three-factor Mobius identities.  Their
pieces are convolutions, but they do not satisfy the universal factorability definition required
by the dispersion theorem.  Writing a coefficient as one convolution is not equivalent to being
well-factorable for every requested splitting of the level.

## Prime-companion obstruction

Define the positive coefficient

```text
P_N(n) = 1_[L,U](n)
         * sum_(p|n, p>u, p prime) log(n/p).
```

Because `mu(p)=-1`, the prime-`d` contribution to the complementary discrepancy is

```text
Delta_P(N) = -C_N(P_N,S_N) + J_M(P_N,S_N).
```

Put

```text
c = log(3) - 2/3,

kappa_100 = integral_(-100)^100
              (sin(pi*t)/(pi*t))^2 dt.
```

The specialist's paper calculation gives

```text
sum_(X<N<=2X, N even) Delta_P(N)
--------------------------------------------------
sum_(X<N<=2X, N even) N*log N

    -> -c*(1-kappa_100) < 0.
```

The retained principal arc captures the fraction `kappa_100` of the prime-companion main profile;
the omitted squared-sinc tail is strictly positive.  The supplied elementary lower bound gives

```text
c*(1-kappa_100) > 1/5000.
```

An independent arithmetic spot check confirms

```text
c = 0.43194562200144315,
c/(201.5*pi^2) = 0.00021719722923231783 > 1/5000.
```

It follows that at arbitrarily large even centers,

```text
Delta_P(N) < -(1/10000)*N*log N.
```

Therefore no fixed constant `C` can make

```text
Delta_P(N) >= -C*N
```

hold uniformly for all sufficiently large even `N`.

This does not obstruct the complete signed discrepancy.  It proves that a valid estimate must
permit some composite-`d` terms to compensate the isolated prime-`d` term.  Any ledger that
isolates the prime companion and charges it a fixed fraction of `N` is mathematically impossible.
This does not force compensation to cross the smooth/rough strata indexed by the number of large
prime factors; prime and composite terms may cancel within one stratum.

## Exact remaining surface

The complete coefficient can be decomposed exactly by the number of prime factors exceeding a
chosen smoothness threshold:

```text
Delta(N) = sum_(j=0)^5 (-1)^j * R_j(N).
```

This supplies useful structural information about where the cancellation must occur.  It does not
produce an independently controlled smaller theorem.  The required statement remains

```text
sum_(j=0)^5 (-1)^j * R_j(N) >= -0.69*N
```

for every admissible even `N`, which is exactly the Stage 2 discrepancy in smooth/rough notation.
Conditional on the provisional Stage 1 reserve, it would imply a quantitative binary Goldbach
result.

## Verification status

The report is a paper-level specialist argument, not a Lean theorem.  At first audit:

* the universal support consequence of triply well-factorable weights follows directly from the
  published definition;
* the cited large-residue range `153/256` agrees with the published theorem;
* the sign and scale of the prime companion are consistent with the exact Mobius coefficient and
  retained principal-arc kernel;
* the numerical squared-sinc-tail allowance is safe.

The full averaged asymptotic received an independent paper review with verdict **REVISE**.  The
headline theorem, leading constant, parity normalization, endpoint treatment, and factorability
support obstruction survived reconstruction.  The revision narrows the structural corollary as
described above.  The presentation-ready statement is:

```text
SupportingDocs/RouteAPrimeCompanionObstruction.md
```

The independent-review specification is:

```text
SupportingDocs/RouteAPrimeCompanionIndependentReviewAssignment.md
```

## Project consequence

The stopping rule in the feasibility assignment has been met:

1. the nonfactorable companion is not small;
2. its required cancellation with composite companions is unproved;
3. the recombined residual is not materially narrower than the original Goldbach-level
   fixed-center discrepancy.

Accordingly:

* freeze this Route A branch;
* retain Stage 1 as a provisional standalone major-arc result;
* retain the exact decompositions and obstruction as research outputs;
* do not resume the obsolete `X0` certificate for Route A closure;
* do not create another staged assignment that merely renames the same signed correlation.

Further work on this branch would be original research on a theorem preserving joint cancellation
between the prime-modulus term and suitable composite-modulus terms.  Those terms need not belong
to different smooth/rough strata.  The work should be described as original research, not as
integration, formalization, or completion of the existing route.

