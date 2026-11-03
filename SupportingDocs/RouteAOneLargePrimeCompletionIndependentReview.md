# Independent review: Route A one-large-prime completion audit

Date: 2026-10-29

## Verdict

**PASS for the audit's mathematics and its UNRESOLVED stopping decision.**

The independent review found no invalid identity, theorem application, or numerical inequality.  It
confirmed, without changing constants:

1. the normalized Stage 1 reconciliation on its inherited paper inputs;
2. the local-model coefficient `log(1/(1-eta))`;
3. the finite bounds `0.70*N<T_100(N)<5.911*N`;
4. positivity of the retained projection on `10^-8<=eta<=1/3`;
5. failure of the uniform factor-two envelope;
6. the sharpened finite-sieve fallback and safe exponent `17699/10^9`; and
7. sufficiency of the displayed missing theorem with buffer `0.707`.

This is a paper verification, not a Lean build.  It confirms that the branch has reached its stated
stopping rule; it does not prove that the missing fixed-center estimate is impossible.

## Normalized reserve

The active main and inherited Stage 1 allowances are distinct terms of the same exact decomposition.
Using `S(N)>=1` in the correct direction gives

```text
R_major(N)>0.708*S(N)*N.
```

The complete Type-I estimate and other inherited analytic bounds remain paper inputs.  The review
reconciles their normalization and placement; it does not formalize their underlying proofs.

## Complete-row structure

For `0<eta<=1/3`, the exact one-large-prime correlation is

```text
C_eta(N)
  = sum_(r<=N^eta) Lambda(r)
      sum_(u<p<=U/r, p prime) Lambda(N-r*p).
```

The coprime local model satisfies

```text
C_eta^0(N)/(S(N)*N)
  = log(1/(1-eta)) + explicit small error.
```

At the full-row endpoint, the coefficient is `log(3/2)`.  This evaluates the explicit local model,
not the actual prime-pair correlation.

## Retained projection

The exact rational-arc calculation gives

```text
J_eta(N)
  = log(1/(1-eta))*T_100(N) + e_eta(N),

0.70*N<T_100(N)<5.911*N.
```

The error is small enough to prove

```text
J_eta(N)>0
```

uniformly on the stated range.  The review independently checked the `q=1,2` contribution, the
negative-row charging sum, endpoint losses, nonsquarefree errors, and threshold comparison.

Because `S(N)` is unbounded along admissible even primorial centers while `T_100(N)<5.911*N`, the
finite retained mask cannot supply a uniform positive fraction of `S(N)*N`.  Therefore a uniform
factor-two full-correlation bound still costs

```text
2*log(3/2)=0.8109302162...>0.708.
```

This rejects that envelope, not the actual row.

## Sharpened fallback

The independent review confirms

```text
C_eta(N)
  < [40000*eta/(1-eta)+10^-30]*S(N)*N.
```

With the positive retained term, the safe explicit exponent is

```text
eta_*=17699/10^9=0.000017699,

Delta_(eta_*)(N)>-0.707972531*S(N)*N.
```

The zero-error boundary is slightly larger, but is not itself admissible after adding the positive
error.  Splitting the cofactor interval cannot improve the architecture because its leading costs
sum to `20000` over the complete range.

## Exact frontier

A sufficient row-compatible theorem is

```text
sum_(r<=u) Lambda(r)
  sum_(u<p<=U/r, p prime) Lambda(N-r*p)

  <= log(3/2)*T_100(N) + 0.707*S(N)*N.
```

The retained-model error then yields

```text
Delta_(1/3)(N)>-0.708*S(N)*N.
```

No theorem substitution checked in this investigation proves this fixed-center estimate.  The
explicit linear sieve leaves an uncontrolled application-specific progression remainder, and the
large-modulus dispersion theorem requires factorable weights not supplied by the raw cofactor
sequence.

## Final project decision

This branch is frozen as a conditional reduction:

1. preserve the independently reviewed `eta=10^-8` theorem;
2. preserve the normalized Stage 1 reconciliation, local-model evaluation, retained positivity, and
   exact missing theorem as paper results;
3. do not formalize or certificate-populate the `eta_*=0.000017699` fallback for Route A;
4. do not commission another microscopic exponent optimization; and
5. resume this branch only if a genuinely stronger fixed-center averaged prime-pair estimate applies
   to the displayed frontier.

