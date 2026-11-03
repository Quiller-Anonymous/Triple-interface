# Prime-modulus companion obstruction under the fixed Route A mask

Date: 2026-10-28

## Status

Independent paper review returned **REVISE**:

* the headline prime-companion obstruction is valid;
* the factorability support proposition and smooth/rough identities are valid;
* the full-convolution average, parity normalization, retained-arc asymptotic, and explicit
  negative constant survive reconstruction;
* the structural corollary must be narrowed.

The result forces compensation between the isolated prime-`d` contribution and some
composite-`d` contributions.  It does **not** force that compensation to occur between different
smooth/rough strata indexed by the number of prime factors above a chosen threshold.  Prime and
composite divisors may cancel within the same stratum.

This is a paper theorem, not yet a Lean theorem.

## Definitions

Fix

```text
L = 1,000,001,
U = N-L,
u = floor(N^(1/3)),
e(t) = exp(2*pi*i*t),
S_N(n) = Lambda(n)*1_[L,U](n).
```

For the retained set

```text
M_N = union over q<=100 and gcd(a,q)=1 of
        {alpha in R/Z : ||alpha-a/q|| <= 100/(q*N)},
```

define `W_N(j)=integral_(M_N) e(j*alpha) d alpha`.  Thus

```text
W_N(0) = (200/N)*sum_(q<=100) phi(q)/q,

W_N(j) = sum_(q<=100) c_q(j)
           * sin(200*pi*j/(q*N))/(pi*j),       j != 0.
```

The positive prime-divisor coefficient is

```text
P_N(n) = 1_[L,U](n)
         * sum_(p|n, p>u, p prime) log(n/p).
```

Put

```text
C_N = sum_(n=L)^U P_N(n)*Lambda(N-n),

J_N = integral_(M_N)
        hat(P_N)(alpha)*hat(S_N)(alpha)*e(-N*alpha) d alpha.
```

The exact contribution from prime outer divisors `d=p>u` is

```text
Delta_P(N) = -C_N + J_N.
```

The sign is forced by `mu(p)=-1`; no positivity or Goldbach assumption enters this identity.

## Factorability proposition

If `lambda` is triply well-factorable of level `Z`, then

```text
lambda(d)=0 whenever P+(d)>Z^(1/3).
```

Apply the universal definition to `Z1=Z2=Z3=Z^(1/3)`.  Every nonzero convolution term has
`d=d1*d2*d3` with each `di<=Z^(1/3)`, so every prime factor of `d` is at most `Z^(1/3)`.

The analogous necessary support condition for ordinary well-factorability is
`P+(d)<=Z^(1/2)`.  Both conditions persist under finite linear combinations of admissible weights
at levels at most `Z`.

Consequently, a prime modulus `p` comparable to `sqrt N` can occur in a triply well-factorable
weight only at level at least comparable to `p^3`, hence `N^(3/2)`.  The applicable large-residue
theorem reaches exponent `153/256`, so it cannot cover these prime moduli directly.

This proposition uses only the definition of triply well-factorable weights.

## Main theorem

Let

```text
c = log(3)-2/3,

kappa_100 = integral_(-100)^100
              (sin(pi*t)/(pi*t))^2 d t,

D(X) = sum_(X<N<=2X, N even) N*log N.
```

Then

```text
sum_(X<N<=2X, N even) Delta_P(N)
  = -c*(1-kappa_100)*D(X) + O_L(X^2).
```

Equivalently,

```text
lim_(X->infinity)
  [sum_(X<N<=2X, N even) Delta_P(N)] / D(X)
  = -c*(1-kappa_100) < 0.
```

Since

```text
1-kappa_100 >= 1/(201.5*pi^2)
```

and `c>0.43`, one has `c*(1-kappa_100)>1/5000`.  It follows that arbitrarily large even centers
satisfy

```text
Delta_P(N) < -(1/10000)*N*log N.
```

Therefore, for no fixed constant `C` can

```text
Delta_P(N) >= -C*N
```

hold for every sufficiently large even `N`.  No particular numerical center is asserted.

## Proof map

### Prime-divisor profile

For `Y=N^(1/3)` and `Y<=t<=N`, partial summation with the ordinary prime number theorem gives

```text
F_Y(t) := sum_(Y<p<=t) (1/p)*log(t/p)

        = log(t)*log(log(t)/log(Y)) - log(t) + log(Y) + O(1).
```

For `t/N` in a fixed positive compact interval,

```text
F_(N^(1/3))(t) = c*log N + O(1),
```

and an integrable edge estimate gives

```text
integral_0^N |F_(N^(1/3))(t)-c*log N| d t = O(N).
```

### Principal retained arc

For bounded `beta`, sum-integral comparison yields

```text
hat(P_N)(beta/N)
  = c*N*log N*V_0(beta) + O_L(N),

hat(S_N)(beta/N)
  = N*V_0(beta) + O_L(N/log N),

V_0(beta) = integral_0^1 e(beta*t) d t.
```

The discretization error for `P_N` is only `O(N)` because

```text
sum_(p<=N) log(N/p) <= N.
```

Moreover,

```text
V_0(beta)^2*e(-beta)
  = (sin(pi*beta)/(pi*beta))^2.
```

After `alpha=beta/N`, the principal arc contributes

```text
J_(q=1) = c*kappa_100*N*log N + O_L(N).
```

### Nonprincipal retained arcs

For `2<=q<=100`, every prime `p>u` is coprime to `q`.  Rational exponential partial sums in `m`
are bounded by `q`.  Finite partial summation, including `|beta|<=100/(q*N)`, gives

```text
|hat(P_N)(a/q+beta)| <= (2q+200*pi)*N.
```

Since `|hat(S_N)|=O(N)` and the total nonprincipal retained-arc length is `O(1/N)`,

```text
J_(q>=2) = O(N).
```

Hence `J_N=c*kappa_100*N*log N+O_L(N)`.

### Average of the full convolution

When averaging over even `N` in `(X,2X]`, freezing the moving prime cutoff from `N^(1/3)` to
`X^(1/3)` costs `O(X^2)`.

For odd reflected prime powers, parity forces `m` to be odd.  Powers of `2`, the fixed lower cutoff,
and the balanced endpoint contribute `O_L(X^2)`.

Define

```text
A_X(t) = sum_(p>X^(1/3), m odd, p*m<=t) log m.
```

Elementary odd-logarithmic summation and the prime-divisor profile give, uniformly on
`X<=t<=2X`,

```text
A_X(t) = (c/2)*t*log X + O(X).
```

Summing first over the reflected von Mangoldt variable gives

```text
sum_(X<N<=2X, N even) C_N
  = integral_X^(2X) A_X(t) d t + O_L(X^2)
  = (3c/4)*X^2*log X + O_L(X^2).
```

Also `D(X)=(3/4)*X^2*log X+O(X^2)`.  Thus `sum C_N=c*D(X)+O_L(X^2)`, while summing the retained
estimate gives `sum J_N=c*kappa_100*D(X)+O_L(X^2)`.  The exact sign identity proves the theorem.

## Correct structural corollary

Write

```text
Delta(N) = Delta_P(N) + Delta_comp(N),
```

where `Delta_comp` contains all composite outer divisors.  If

```text
Delta(N) >= -C_0*N
```

eventually, then at arbitrarily large even centers from the theorem,

```text
Delta_comp(N)
  > (1/10000)*N*log N - C_0*N.
```

Therefore a successful proof must allow composite-modulus contributions to compensate the
negative isolated prime-modulus contribution.  A proof architecture that leaves the exact prime
companion as an independently `O(N)`-bounded error is impossible.

This does **not** imply that cancellation must occur between different values of the smooth/rough
index `j`.  The prime term and a composite term can lie in the same `j=1` stratum.  For example,
divisors `p` and `3p` of `3*p*r` contribute

```text
-log(3*r) + log(r) = -log 3
```

within that same stratum.

Accordingly, the result rules out factorable dispersion followed by an independently bounded
isolated prime companion.  It does not rule out every possible regrouping of factorable pieces and
jointly treated nonfactorable companions.

## Dependencies and limits

The theorem uses the factorability definition, finite Fourier algebra, `mu(p)=-1`, the ordinary
prime number theorem, partial summation, elementary rational exponential sums, and an elementary
squared-sinc tail estimate.  It does not use Stage 1, Goldbach, a project-specific analytic
hypothesis, or a dispersion theorem.

Explicit modulus-one PNT estimates make the errors effective, although no first numerical center
has been computed.

The result does not prove or disprove `Delta(N)>=-0.69*N`.  It neither proves nor disproves binary
Goldbach.  It closes one proposed reduction, not every possible use of Triple Interface or
dispersion machinery.

## Project consequence

The independent review validates the prime-companion obstruction and the decision to freeze this
Route A branch.  The correction affects only the overstrong cross-stratum presentation claim.

There is no authorized next Route A stage.  Any future attempt must provide a genuinely new joint
estimate for prime and composite modulus contributions; it cannot charge the prime term as an
independent `O(N)` companion.

The subsequent variable-principal-arc feasibility test confirmed this distinction.  Widening the
principal arc removes the isolated prime companion's negative `N*log(N)` average, but the complete
combined discrepancy changes by less than `0.000061*N`.  The isolated obstruction can therefore
move while the joint fixed-center frontier remains essentially unchanged.  See
`SupportingDocs/RouteCVariablePrincipalArcAudit.md`.

