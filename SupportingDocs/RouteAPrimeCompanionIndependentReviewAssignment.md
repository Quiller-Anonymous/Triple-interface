# Independent review assignment: Route A prime-companion obstruction

Date: 2026-10-28

## Outcome

The independent review returned **REVISE**.  The prime-companion obstruction, exact leading
constant, support proposition, and smooth/rough identities are valid.  The structural corollary
was too strong: compensation is required between the isolated prime-`d` term and composite-`d`
terms, but it need not cross different large-prime-factor strata.  The corrected presentation is:

```text
SupportingDocs/RouteAPrimeCompanionObstruction.md
```

## Purpose

Independently verify, correct, and present the paper-level claim that the isolated prime-modulus
part of the Route A hard coefficient cannot be assigned any uniform `O(N)` one-sided error under
the exact retained mask.

This review has two distinct objects:

1. an algebraic support obstruction for triply well-factorable weights;
2. an asymptotic theorem for the prime-`d` companion.

Do not infer the second merely from the first.  Audit both proofs separately.

The intended conclusion is **not** that the complete Route A discrepancy is false.  The intended
conclusion is that any successful estimate must preserve cancellation between prime-`d` and
composite-`d` contributions; a decomposition into factorable terms plus independently small
companions cannot close this route.

Do not begin Lean formalization during this review.

## Materials to review

Read:

```text
SupportingDocs/RouteAFactorableDispersionAudit.md
SupportingDocs/RouteAFactorableDispersionFeasibilityAssignment.md
SupportingDocs/RouteAComplementaryCrossStage2Audit.md
SupportingDocs/RouteAComplementaryCrossSpecialistAssignment.md
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
SupportingDocs/RouteAEnlargedMajorArcPaperProofPacket.md
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanIdentity.lean
Goldbach/Cert/MajorArcModules/RouteAFiniteWeightBilinearCircle.lean
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
```

The full specialist report beginning

```text
Verdict: UNRESOLVED -- the factorable-dispersion reduction does not pass Phase A
```

must accompany this assignment.  The audit document is a summary, not a substitute for checking
the report's derivation.

Relevant primary literature includes:

* Jared Duker Lichtman, *Primes in arithmetic progressions to large moduli, and Goldbach beyond
  the square-root barrier*, arXiv:2309.08522v1, especially Theorem 1.7 and equation (1.7).
* Alexandru Pascadi, *On the exponents of distribution of primes and smooth numbers*,
  arXiv:2505.00653v2, especially Definition 1.1 and the triply-well-factorable prime theorem.

Check the current versions and published status rather than relying only on the citations in the
specialist report.

## Fixed definitions

For every even integer `N` in the asymptotic range, put

```text
L = 1,000,001,
U = N-L,
u = floor(N^(1/3)),
e(x) = exp(2*pi*i*x).
```

Let

```text
S_N(n) = Lambda(n) * 1_[L,U](n).
```

The retained set is

```text
M = union over 1<=q<=100 and gcd(a,q)=1 of
      {alpha in R/Z : ||alpha-a/q|| <= 100/(q*N)}.
```

Its real even Fourier kernel is

```text
W_N(0) = (200/N) * sum_(q<=100) phi(q)/q,

W_N(j) = sum_(q<=100) c_q(j)
           * sin(200*pi*j/(q*N))/(pi*j),      j != 0.
```

Define

```text
E_N(t) = Lambda(N-t)
         - sum_(L<=b<=U) Lambda(N-b)*W_N(t-b).
```

The complete complementary discrepancy is

```text
Delta(N) =
  sum_(d>u, L<=d*m<=U) mu(d)*log(m)*E_N(d*m).
```

The prime-divisor coefficient is

```text
P_N(n) = 1_[L,U](n)
         * sum_(p|n, p>u, p prime) log(n/p).
```

Write

```text
C_N(P_N,S_N) = sum_(L<=n<=U) P_N(n)*Lambda(N-n),

J_M(P_N,S_N) =
  integral_M hat(P_N)(alpha)*hat(S_N)(alpha)*e(-N*alpha) d alpha.
```

Because `mu(p)=-1`, the exact prime-`d` companion is claimed to be

```text
Delta_P(N) = -C_N(P_N,S_N) + J_M(P_N,S_N).
```

This sign and identity must be checked directly from `Delta(N)` before reviewing any asymptotics.

## Claim A: universal factorability support obstruction

Review the following proposition.

> If `lambda` is triply well-factorable of level `Z`, then
> `lambda(d)=0` whenever the largest prime factor `P+(d)` exceeds `Z^(1/3)`.

The proposed proof applies the universal factorability definition to

```text
Z1 = Z2 = Z3 = Z^(1/3).
```

Every nonzero convolution term then writes `d=d1*d2*d3` with `di<=Z^(1/3)`, so no prime factor of
`d` can exceed `Z^(1/3)`.

Confirm:

1. that the cited theorem really uses factorability for every factorization of the level;
2. the treatment of nonintegral support endpoints;
3. whether harmless constants in the level alter the conclusion relevant to `d` comparable to
   `sqrt N`;
4. that the support obstruction survives arbitrary finite linear combinations of admissible
   weights at levels at most `Z`;
5. that a prime `d` comparable to `sqrt N` would require level at least comparable to `N^(3/2)`.

Also verify the analogous `P+(d)<=Z^(1/2)` necessary condition for ordinary well-factorability.

## Claim B: exact smooth/rough decomposition

The specialist sets

```text
theta = 611/1024,
Z = N^theta,
z = Z^(1/3) = N^(611/3072).
```

On a balanced interval `I=(D,2D]` with `D` comparable to `sqrt N`, define

```text
lambda_0(d) = 1_I(d)*mu(d)*1_(P+(d)<=z),

lambda_1(d) = 1_I(d)
              * sum_(s*p=d, p>z prime, P+(s)<=z) mu(s),

lambda_2(d) = 1_I(d)
              * sum_(s*p1*p2=d, z<p1<p2 prime, P+(s)<=z) mu(s).
```

Because `z^3=Z>2D`, the claimed exact identity is

```text
mu(d)*1_I(d) = lambda_0(d) - lambda_1(d) + lambda_2(d).
```

Check:

1. squarefree and nonsquarefree `d` separately;
2. uniqueness and multiplicity of the ordered large-prime factors;
3. the exponent comparison `z^3>2D` uniformly in the stated block;
4. all coefficient sup and `L2` bounds;
5. the examples showing that none of the three displayed sequences is automatically universally
   well-factorable;
6. the proposed three-factor Mobius identity and whether it merely transfers large prime factors
   into unrestricted companion variables.

For the global decomposition, check the assertion that `z^6>N` and therefore every squarefree
`d<=U` has at most five prime factors exceeding `z`.  Verify the exact formula

```text
Delta(N) = sum_(j=0)^5 (-1)^j * R_j(N)
```

including all support restrictions, multiplicities, and signs.

## Claim C: prime-companion asymptotic

Put

```text
c = log(3) - 2/3,

kappa_100 = integral_(-100)^100
              (sin(pi*t)/(pi*t))^2 dt.
```

The central proposed theorem is

```text
lim_(X->infinity)
  [sum_(X<N<=2X, N even) Delta_P(N)]
  / [sum_(X<N<=2X, N even) N*log N]

  = -c*(1-kappa_100) < 0.
```

The review must reconstruct this theorem, not merely check its heuristic scale.

### C1. Prime-divisor profile

Verify, uniformly for `t/N` in every fixed positive compact interval,

```text
sum_(N^(1/3)<p<=t) (1/p)*log(t/p)
  = (log(3)-2/3)*log N + o(log N).
```

State exactly which form of the prime number theorem and partial summation is used.  Check the
uniformity required later when `t` varies and provide a dominating bound near the integration
edges.

### C2. Principal retained arc

With

```text
V_0(beta) = integral_0^1 e(beta*t) dt,
```

verify uniformly for `|beta|<=100` that

```text
hat(P_N)(beta/N)/(N*log N) -> c*V_0(beta),

hat(S_N)(beta/N)/N -> V_0(beta).
```

Track the Fourier phase `e(-N*alpha)` and prove

```text
V_0(beta)^2*e(-beta)
  = (sin(pi*beta)/(pi*beta))^2.
```

This should yield

```text
J_(q=1)(P_N,S_N)
  = c*kappa_100*N*log N + o(N*log N).
```

Audit all sum-integral errors, the fixed cutoff `L`, and the balanced upper endpoint.

### C3. Nonprincipal retained arcs

For each `2<=q<=100`, verify the asserted uniform bound

```text
hat(P_N)(a/q+beta) = O_100(N)
```

on `|beta|<=100/(q*N)`.

The proof must account for:

* `p>u`, hence `gcd(p,q)=1`;
* rational exponential partial sums in `m`;
* the logarithmic `m` weight;
* the additional phase `e(beta*p*m)`;
* summation over `p`;
* all reduced numerators and all denominators `2..100`.

Then justify

```text
J_(q>=2)(P_N,S_N) = O(N) = o(N*log N).
```

An omitted factor of `log N` at this step would change the leading constant and must be treated as
a substantive error.

### C4. Average of the full convolution

Reconstruct

```text
sum_(X<N<=2X, N even) C_N(P_N,S_N)
  = (3*c/4)*X^2*log X + o(X^2*log X).
```

In particular, verify:

1. the replacement of the moving cutoff `N^(1/3)` by `X^(1/3)` and its total error;
2. why parity forces `m` odd when the reflected von Mangoldt variable is an odd prime;
3. the contribution of powers of `2` in the von Mangoldt weight;
4. the asymptotic

   ```text
   A_X(t) = (c/2)*t*log X + o(X*log X)
   ```

   with enough uniformity to integrate it;
5. both fixed support endpoints `L` and the moving balanced endpoint `N-L`;
6. the interchange of finite sums;
7. the denominator asymptotic

   ```text
   sum_(X<N<=2X, N even) N*log N
     ~ (3/4)*X^2*log X.
   ```

This is the most important independent-review step.

### C5. Explicit negativity and logical consequence

Verify the squared-sinc tail estimate

```text
1-kappa_100 >= 1/(201.5*pi^2).
```

Together with `c>0.43` and `pi^2<10`, this gives

```text
c*(1-kappa_100) > 1/5000.
```

Check the deduction from the averaged asymptotic to the existence of arbitrarily large even `N`
such that

```text
Delta_P(N) < -(1/10000)*N*log N.
```

Finally, prove explicitly that this contradicts every proposed uniform bound

```text
Delta_P(N) >= -C*N
```

for fixed `C` and all sufficiently large even `N`.

## Dependency and effectiveness audit

State separately:

* which claims require only the definition of triply well-factorable weights;
* which claims require the ordinary prime number theorem;
* whether any zero-free-region or ineffective result enters;
* whether the obstruction is merely asymptotic or has a computable threshold;
* whether Stage 1, Goldbach, or any project-specific analytic hypothesis is used.

The proposed obstruction should require neither Stage 1 nor Goldbach.  If that is false, identify
the dependency precisely.

An asymptotic proof with no explicit first counterexample is sufficient to disprove a uniform
`O(N)` companion allowance.  Do not claim an explicit numerical center unless one is actually
computed and checked.

## Presentation deliverable

If the claims survive review, return a standalone paper-style note with this structure:

1. definitions and Fourier normalization;
2. factorability support proposition;
3. exact extraction of the prime-`d` companion;
4. principal-arc asymptotic;
5. nonprincipal-arc error;
6. averaged full-convolution asymptotic;
7. prime-companion obstruction theorem;
8. corrected corollary requiring compensation from composite-modulus contributions;
9. explicit statement of what is **not** proved.

The recommended headline theorem is:

> For the exact retained mask with `P=Q=100`, the isolated prime-modulus contribution
> `Delta_P(N)` admits no uniform lower bound of the form `-C*N` for any fixed `C`.

The recommended structural corollary is:

> Any proof of the complete complementary bound must permit composite-modulus contributions to
> compensate the negative isolated prime-modulus contribution.  The exact prime companion cannot
> be assigned an independent uniform `O(N)` lower allowance.

The note must also say:

* the complete `Delta(N)>=-0.69*N` target has not been disproved;
* binary Goldbach has not been proved or disproved;
* the result closes one proposed reduction, not every possible use of dispersion or Triple
  Interface machinery.

## Required verdict

Return one of:

### PASS

Supply a corrected complete proof, exact dependencies, and a presentation-ready theorem and
corollary.

### REVISE

Identify every gap or incorrect constant, provide the corrected statement, and say whether the
strategic obstruction still follows.

### FAIL

Identify a false identity or asymptotic that invalidates the obstruction.  Give the corrected
calculation and explain whether the factorability branch should be reopened.

### UNRESOLVED

Identify the precise step that remains unproved and the narrowest theorem needed to settle it.
Do not endorse the project-level conclusion until that step is resolved.

## Project rule during review

This independent review does not reopen Route A.  The branch remains frozen unless the review
invalidates the obstruction and supplies a materially different, applicable theorem path.  A PASS
supports publication or formalization of the obstruction itself, not resumption of the old Route A
certificate or proof-completion program.

