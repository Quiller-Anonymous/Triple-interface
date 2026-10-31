# Route C feasibility assignment: growing principal arc

Date: 2026-10-28

## Outcome

**UNRESOLVED; candidate closed at Phase 3.**  The specialist established the exact widened kernel,
removed the isolated prime companion's negative `N*log(N)` average, and retained a provisional
paper reserve above `0.699*N` for `1 <= A <= 8`.  However, the complete widened discrepancy differs
from the original fixed-mask discrepancy by less than `0.000061*N`.  The residual is therefore
essentially the same fixed-center Mobius--prime correlation, not a materially narrower theorem.

Do not advance this assignment to Lean or certificate generation.  The complete outcome and its
standalone results are recorded in `SupportingDocs/RouteCVariablePrincipalArcAudit.md`.

## Decision to make

Determine whether replacing the fixed principal arc by a logarithmically growing one removes the
prime-companion obstruction while preserving a provable positive retained-main budget.

This is a paper-mathematics feasibility test.  It is not a continuation of fixed-mask Route A and
does not authorize Lean formalization, certificate generation, or a claim that Route C exists.

The candidate is viable only if it changes the analytic frontier.  Merely rewriting the remaining
fixed-center Goldbach correlation under a wider mask is an **UNRESOLVED** result, not a pass.

Read:

```text
SupportingDocs/RouteAPrimeCompanionObstruction.md
SupportingDocs/RouteAFactorableDispersionAudit.md
SupportingDocs/RouteAComplementaryCrossStage2Audit.md
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
SupportingDocs/RouteAEnlargedMajorArcPaperProofPacket.md
```

## Fixed arithmetic objects

For every even integer

```text
N >= exp(exp(100)),
```

put

```text
L = 1,000,001,
U = N-L,
u = floor(N^(1/3)),
e(t) = exp(2*pi*i*t).
```

Keep the exact balanced coefficients

```text
S_N(n) = Lambda(n)*1_[L,U](n),

A_u(n) = 1_[L,U](n)
         * sum_(d*m=n, d<=u) mu(d)*log(m),

h_u(n) = S_N(n)-A_u(n)
       = 1_[L,U](n)
         * sum_(d*m=n, d>u) mu(d)*log(m).
```

Do not replace `h_u` by a sieve majorant or separate its prime-modulus part as an independent
`O(N)` error.  The prime-companion theorem proves that the latter step is impossible for the fixed
mask.

## Candidate retained set

Let `A>0` be an explicit constant to be optimized, and put

```text
R_A(N) = A*log N.
```

Replace only the principal arc.  Define

```text
M_A(N) = {alpha in R/Z : ||alpha|| <= R_A(N)/N}

         union

         union over 2<=q<=100 and gcd(a,q)=1 of
           {alpha : ||alpha-a/q|| <= 100/(q*N)}.
```

The old `q=1` arc of radius `100/N` is replaced, not added a second time.  Keep every `q>=2` arc
unchanged in the first experiment.  Widening all arcs introduces additional losses and is a
different candidate.

Prove disjointness at the stated threshold.  Do not assume it from the fixed-mask calculation.

## Exact generalized kernel

The first task is to derive the exact kernel

```text
W_(A,N)(j) = integral_(M_A(N)) e(j*alpha) d alpha.
```

The expected formulas are

```text
W_(A,N)(0)
  = 2*R_A(N)/N
    + (200/N)*sum_(2<=q<=100) phi(q)/q,

W_(A,N)(j)
  = sin(2*pi*R_A(N)*j/N)/(pi*j)
    + sum_(2<=q<=100) c_q(j)
        * sin(200*pi*j/(q*N))/(pi*j),      j != 0.
```

Check the wrapped principal interval, signs, endpoint conventions, and reality/evenness.

Define the complementary discrepancy

```text
Delta_A(N)
  = integral_(M_A(N)^c)
      hat(h_u)(alpha)*hat(S_N)(alpha)*e(-N*alpha) d alpha.
```

Record its exact finite real-space form before estimating it.

## Phase 1: does the prime-companion obstruction recede?

Let

```text
P_N(n) = 1_[L,U](n)
         * sum_(p|n, p>u, p prime) log(n/p),

c = log(3)-2/3,

kappa_R = integral_(-R)^R
            (sin(pi*t)/(pi*t))^2 d t.
```

For the fixed mask, independent review proved that the isolated prime companion has average leading
term

```text
-c*(1-kappa_100)*N*log N.
```

For `R=R_A(N)`, investigate the proposed replacement

```text
-c*(1-kappa_(R_A(N)))*N*log N.
```

The elementary tail estimate

```text
1-kappa_R <= 2/(pi^2*R)
```

suggests a scale at most

```text
(2*c/(pi^2*A))*N.
```

This heuristic is not a proof because the fixed-width Fourier asymptotics were only established
uniformly for bounded local frequency.  Reconstruct them uniformly for

```text
|beta| <= A*log N.
```

Required output:

1. An exact prime-companion sign identity under `M_A(N)`.
2. A uniform principal-arc formula with every error term displayed.
3. A proof or disproof that the summed/average prime-companion contribution is `O_A(N)` per center
   at the leading scale.
4. An explicit constant, not just `O_A(1)`.
5. Confirmation that the unchanged `q>=2` arcs remain lower order under this calculation.

Track especially:

* the sum-integral error in `hat(P_N)(beta/N)` as `beta` grows;
* the PNT error in `hat(S_N)(beta/N)`;
* integration of products of main and error terms over a length `A*log N/N`;
* whether endpoint bounds remain integrable uniformly in `A`;
* whether an error of order `N*log N` reappears.

### Phase 1 stopping condition

Stop with **FAIL** if no fixed `A` gives a rigorous `O(N)` prime-companion allowance, or if the
constant needed to control it already exhausts the available retained-main reserve.

Passing Phase 1 only removes the known fixed-mask obstruction.  It does not control the complete
`Delta_A(N)`.

## Phase 2: recompute the retained-main budget

Rebuild the enlarged-major-arc paper ledger for `M_A(N)`.  The previous Stage 1 result for
`P=Q=100` cannot simply be reused because the `q=1` integration range has changed.

At minimum, compute:

```text
J_(M_A)(A_u,S_N)
```

with the exact Type-I and prime rational-arc models, and the corresponding retained hard/model
corrections needed by the full signed decomposition.

Required checks:

1. **Prime approximation.** Bound

   ```text
   hat(S_N)(beta)-V(beta)
   ```

   uniformly for `|beta|<=A*log N/N`, retaining the partial-summation term involving
   `|beta|*integral |psi(t)-t| d t`.

2. **Type-I approximation.** Recompute the `q=1` approximation to `hat(A_u)(beta)` over the same
   growing range.  Restore every factor of `A`, `log N`, and `u`.

3. **Signed model.** Evaluate the enlarged principal model without replacing an oscillatory
   integral by a supremum-times-width estimate unless that bound fits the final constant.

4. **Cross errors.** Integrate main/error and error/error products explicitly over the growing
   arc.

5. **Unchanged arcs.** State exactly which `q>=2` Stage 1 rows remain valid and why changing the
   principal arc does not alter them.

6. **Prime powers and endpoints.** Preserve the previous explicit allowances or recompute them if
   the new mask changes their treatment.

Produce a uniform lower bound

```text
R_major,A(N) >= r_A*N
```

with explicit `r_A>0`.  A ledger whose error is `O_A(N)` but has no numerical coefficient does not
pass.

### Phase 2 stopping condition

Stop with **FAIL** if the growing-arc PNT or Type-I errors consume the main term for every `A` that
passes Phase 1.

## Phase 3: demonstrate a genuinely narrower complement

Only after Phases 1 and 2 pass, analyze the complete joint discrepancy `Delta_A(N)`.

The task is not immediately to prove Goldbach.  It is to demonstrate that the new complement has
a theorem surface materially narrower than

```text
Delta_A(N) >= -d*N.
```

That bare inequality, when combined with the retained reserve, is again a Goldbach-level
restatement.

Required diagnostic:

1. Give the exact joint prime/composite decomposition under the new kernel.
2. Work one predicted worst balanced block with signs preserved.
3. Identify a published theorem that applies to the actual combined coefficients, or prove a new
   structural cancellation before invoking estimates.
4. Restore all norms, multiplicities, variable endpoints, dyadic ranges, and constants.
5. Produce a rigorous global forecast.

A pass requires either:

* a complete bound

  ```text
  Delta_A(N) >= -d_A*N
  ```

  with `r_A-d_A` positive after all other allowances; or

* a residual theorem that is demonstrably narrower than binary Goldbach and matched to an existing
  applicable result with enough numerical room.

### Phase 3 stopping condition

Return **UNRESOLVED** and stop if the residual is merely the original fixed-center signed
Mobius--prime correlation under a new kernel, if it requires assumed prime/composite cancellation,
or if only almost-all-center estimates apply.

## Parameter optimization

Do not select `A` by trial and then hide its tradeoff.  Derive a ledger of the form

```text
reserve(A)
  = retained_main(A)
    - principal_tail(A)
    - prime_approximation_error(A)
    - type_I_error(A)
    - other_allowances(A).
```

The principal tail is expected to decrease like `1/A`; some analytic approximation errors may
increase with `A`.  Give a provable interval of `A` with positive reserve, or prove that no such
interval follows from the available estimates.

Testing a short list such as `A=1,2,4,8` may be useful diagnostically, but the final conclusion must
come from inequalities valid throughout the chosen parameter range.

## Prohibited shortcuts

The following do not pass:

1. Reusing the fixed-width Stage 1 reserve without recomputing the widened `q=1` row.
2. Using the fixed-`beta` prime-companion asymptotic uniformly up to `A*log N` without proof.
3. Widening every rational arc silently.
4. Treating the isolated prime companion as an independent `O(N)` error without the Phase 1
   calculation.
5. Assuming favorable cancellation from composite divisors.
6. Replacing a uniform fixed-center target by an average over centers.
7. Returning a conditional record whose hypothesis is the desired complete complementary bound.
8. Starting Lean or a finite certificate before the paper ledger passes.

## Required verdict

### PASS

Supply:

* an explicit `A`;
* the generalized kernel and prime-companion theorem;
* a complete retained-main ledger with `r_A>0`;
* a complete complementary bound or a materially narrower theorem matched to a valid input;
* a final positive numerical margin.

### FAIL

Identify a mathematical obstruction or a rigorous ledger showing that no available `A` can pass
the first two phases.

### UNRESOLVED

State the precise remaining theorem.  Explain why it is narrower than the old fixed-mask
discrepancy.  If it is not narrower, say so and recommend abandoning this candidate.

## Consequence of the verdict

A PASS would justify naming this a Route C paper architecture and commissioning independent review.
It would still precede Lean formalization.

A FAIL or an UNRESOLVED result that reproduces the original fixed-center correlation ends this
Triple-Interface-based Goldbach endgame under the currently identified architectures.  The exact
identities and obstruction theorems would remain valid standalone results.

