# Route A enlarged-major-arc specialist assignment

Date: 2026-10-28

Mathematical base commit:

```text
22a16ab5822479d8ab1bcff9b3785652cf097544
```

Packet publication commit:

```text
f6e466ddfb9f7989097bef0fdc5136f89a6dff17
```

The full source packet is `SupportingDocs/RouteAEnlargedMajorArcPaperProofPacket.md`.  This document
is the narrower assignment to be given to an analytic number theorist.

## Question to decide

Can the balanced Vaughan decomposition retain all rational arcs with denominators `q <= 100` and
produce a rigorously positive signed reserve before the complementary hard term is estimated?

This is a bounded feasibility test, not a request for a proof of Goldbach.  A positive result would
authorize a second investigation of the complementary cross-correlation.  A negative result, or a
result that needs conjectural input, should stop this route in its current form.

## Fixed objects

For every even integer

```text
N >= exp(exp(100)),
```

put

```text
L = 1,000,001,
U = N - L,
u = floor(N^(1/3)),
e(x) = exp(2*pi*i*x).
```

Define the balanced prime, short Type-I, and hard coefficients by

```text
S_N(n) = Lambda(n) 1_[L,U](n),

A_u(n) = 1_[L,U](n)
         sum_{d*m=n, d<=u} mu(d) log(m),

h_u(n) = S_N(n) - A_u(n).
```

Use the Fourier convention

```text
hat f(alpha) = sum_n f(n)e(n*alpha),

C_N(f,g) = integral_[0,1]
             hat f(alpha) hat g(alpha)e(-N*alpha) d alpha.
```

Lean already checks the exact identities

```text
h_u(n) = 1_[L,U](n) sum_{d*m=n, d>u} mu(d)log(m),

C_N(S_N,S_N) = C_N(A_u,S_N) + C_N(h_u,S_N),

C_N(h_u,S_N) = J_M(h_u,S_N) + H_(M^c)(h_u,S_N)
```

for every measurable retained set `M`.  These identities may be treated as fixed algebra, but none
of the analytic estimates requested below may be assumed from them.

For `2 <= Q <= P` and `2*P*Q < N`, define

```text
M(P,Q) = union over q<=Q and (a,q)=1 of
         {alpha in R/Z : ||alpha-a/q|| <= P/(qN)}.
```

The pilot parameters are

```text
P = Q = 100.
```

## Known inputs and their status

Keep the following statuses separate.

1. A reviewed paper derivation gives the active Type-I main

   ```text
   M_A(N) > 0.9 N.
   ```

   It is not yet formalized in Lean.

2. A separate calculation gives the complete short Type-I error

   ```text
   E_I(N) < 5e-15 N.
   ```

   This value has not received the same independent review.  It may be used for a conditional
   feasibility total, but an unconditional verdict must either verify it or state it as a remaining
   input.

3. Lean proves the prime-power allowance

   ```text
   P_pp(N) <= (5/2)(sqrt(N)+1)log(N)^2.
   ```

4. The missing estimate in the old organization was a one-sided bound for the complementary hard
   correlation.  Do not attempt that estimate in this assignment.  First determine whether the
   enlarged major arcs create a positive reserve worth protecting.

## Task 1: prove or repair the Type-I rational-arc approximation

Let

```text
rho_q = mu(q)/phi(q),

V(beta) = integral_L^U e(beta*t) dt,

a_(q,u)(t) = sum_{d<=min(u,t), q|d}
               mu(d)/d * log(t/d),

A_(q,u)(beta) = integral_L^U a_(q,u)(t)e(beta*t) dt.
```

For every `q <= 100`, every reduced `a mod q`, and every

```text
|beta| <= 100/(qN),
```

prove the proposed estimate

```text
|hat A_u(a/q+beta) - A_(q,u)(beta)|
  <= 2*q*u*log(N)*(1+2*pi*N*|beta|).
```

If that exact constant is false or unjustified, replace it with an explicit proved bound and carry
the replacement through the reserve calculation.  Do not silently weaken the statement.

The proof should expose the following points:

* the precise treatment of the endpoints `L` and `U`;
* separation of resonant divisors `q|d` from nonresonant divisors;
* the rational exponential-sum bound used for nonresonant divisors;
* the finite partial-summation step, including its variation term;
* uniformity in the reduced numerator `a`;
* every floor or integral-versus-sum error.

Also prove the exact resonant profile.  If `q` is nonsquarefree, then

```text
a_(q,u)(t) = 0.
```

If `q` is squarefree, `q<=u`, and `t>=u`, then

```text
a_(q,u)(t)
  = mu(q)/q * (checkm_q(u/q) + log(t/u)m_q(u/q)),
```

where

```text
m_q(x)      = sum_{k<=x, (k,q)=1} mu(k)/k,
checkm_q(x) = sum_{k<=x, (k,q)=1} mu(k)/k * log(x/k).
```

The term `log(t/u)m_q(u/q)` must remain.  An asymptotic statement that merely sends `m_q` to zero
is not sufficient at the fixed explicit threshold.

## Task 2: prove or repair the prime rational-arc approximation

The available explicit progression input is

```text
|psi(t;q,b) - t/phi(q)| <= 0.011*t/log(t)
```

for `q<=100000`, `t>=1,000,000`, and `(b,q)=1`.  Check the exact hypotheses and endpoint convention
against the cited BMOR result before using it.

Set

```text
a0 = L-1,
G_q(t) = 0.011*phi(q)*t/log(t) + omega(q)log(t).
```

For every `q<=100` and reduced `a mod q`, prove or correct

```text
|sum_{n<=t} Lambda(n)e(a*n/q) - rho_q*t| <= G_q(t)
```

for all relevant `t`, and then prove or correct

```text
|hat S_N(a/q+beta) - rho_q V(beta)| <= E_S(q,beta),

E_S(q,beta)
  = G_q(U) + G_q(a0)
    + 2*pi*|beta| integral_a0^U G_q(t)dt
    + |rho_q|.
```

The proof must explicitly account for:

* summing the progression errors over the reduced residue classes;
* the Ramanujan sum that produces `rho_q`;
* prime powers whose base prime divides `q`;
* the transition from `[1,t]` to `[L,U]`;
* the difference between the discrete main term and `V(beta)`;
* all partial-summation boundary terms.

Again, replace an incorrect proposed constant by an explicit valid one and carry it forward.

## Task 3: evaluate the signed enlarged-major-arc reserve

On the `q`-arc define

```text
S_q^0(beta) = rho_q V(beta),
H_q^0(beta) = rho_q V(beta) - A_(q,u)(beta).
```

The signed model is

```text
J_model(N)
  = sum_{q<=100} c_q(N)
      integral_{-100/(qN)}^(100/(qN))
        H_q^0(beta)S_q^0(beta)e(-N*beta) d beta.
```

Use the approximation allowance

```text
E_major(N)
  = sum_{q<=100} phi(q)
      integral_{-100/(qN)}^(100/(qN))
        ( |H_q^0| E_S
          + |S_q^0|(E_S+E_A)
          + E_S(E_S+E_A) ) d beta,
```

or a rigorously proved sharper expression.

The quantity to lower-bound is

```text
R(N)
  = M_A(N) + Re J_model(N)
    - E_I(N) - E_major(N) - P_pp(N).
```

First evaluate `q=1,2,3,5`.  This smoke calculation must show:

* the exact sign and `N`-dependence through `c_q(N)`;
* the model contribution divided by `N`;
* the approximation allowance divided by `N`;
* whether the proposed errors are small enough to justify continuing.

Only if that smoke calculation is viable should the calculation be extended to every
`1<=q<=100`.

The final result must be uniform over all even `N>=exp(exp(100))`.  Preserve the signed arithmetic
dependence of `c_q(N)`.  Acceptable methods include an Euler-product argument, a finite partition
by relevant divisibility data, or another explicit uniform minimization.  Do not replace the
signed sum by the sum of absolute values unless the resulting reserve remains positive.

The current JSON checker stores one lower contribution per denominator.  That format is adequate
only if each row has a proved uniform lower bound.  If positivity instead relies on cancellation
between denominators in different divisibility classes of `N`, report the class structure and the
joint lower bounds first.  The checker will then be extended; do not destroy the mathematics to fit
the preliminary schema.

## Required deliverables

Return all of the following.

1. A proof or counterexample for the Type-I rational-arc estimate, with every constant explicit.
2. A proof or counterexample for the prime rational-arc estimate, with every constant explicit.
3. The signed `q=1,2,3,5` smoke table.
4. If the smoke table passes, a complete uniform calculation through `q=100`.
5. A final status chosen from:

   ```text
   PASS:
     R(N) >= r_* N for every admissible even N, with explicit r_*>0.

   FAIL:
     a proved uniform upper/lower calculation makes the reserve nonpositive.

   UNRESOLVED:
     identify the exact unproved inequality and the numerical margin it must achieve.
   ```

6. A dependency table distinguishing published theorems, elementary derivations, numerical
   interval calculations, and conjectural assumptions.
7. If the full stage passes, one proved row per `q` in a completed copy of
   `SupportingDocs/RouteAEnlargedMajorArcPilotTemplate.json`, or a proposed class-aware replacement
   if the preliminary schema is inadequate.

The ledger checker is then run as

```bash
python3 scripts/experiments/route_a_enlarged_major_arc_ledger.py \
  --input SupportingDocs/RouteAEnlargedMajorArcPilotCompleted.json \
  --check
```

`COMPLETE_POSITIVE` checks coverage and decimal arithmetic only.  It does not certify the analytic
proofs used to populate the rows.

## Stopping rules

Stop and report rather than repairing the route ad hoc if any of the following occurs:

1. The rigorously bounded reserve is nonpositive.
2. Positivity needs an unproved distributional hypothesis.
3. A fixed-center signed quantity is replaced by an average over centers or by a generic energy
   estimate.
4. Ramanujan signs or divisibility classes are discarded and the resulting absolute bound does not
   close.
5. The desired cancellation is inserted as an assumption.
6. The approximation errors are so large that reasonable improvements cannot recover a positive
   margin.

If the result is `PASS`, the next paper problem is the one-sided complementary cross estimate

```text
Re sum_{d>u, L<=d*m<=U} sum_{L<=b<=U}
     mu(d)log(m)Lambda(N-b)K_(100,100)(d*m-b)
  >= -D_minor(N),

D_minor(N) < R(N).
```

That second problem is outside the present assignment.
