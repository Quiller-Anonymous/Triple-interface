# Route A one-large-prime completion audit

Date: 2026-10-29

## Status

**Independently reviewed paper-level UNRESOLVED.**  The complete one-large-prime row does not pass
the bounded feasibility test.  Gate 0 reconciles the normalized Stage 1 reserve, and the
deterministic full and retained models are favorable, but no verified fixed-center averaged
prime-pair estimate controls the difference between the actual convolution and its local model with
the required constant.

The fallback exponent improves substantially over the first small-cofactor theorem, but remains
below the assignment's stopping threshold:

```text
eta_*=17699/10^9=0.000017699<10^-4,

Delta_(eta_*)(N)>-0.707972531*S(N)*N.
```

Do not begin an incremental range-expansion, certificate, or Lean formalization program from this
outcome.  Independent review confirmed the mathematics, constants, and stopping decision without
correction; see `SupportingDocs/RouteAOneLargePrimeCompletionIndependentReview.md`.

## Gate 0: normalized reserve

The report verifies that the strengthened active main and the inherited Stage 1 allowances belong
to different terms of the same exact decomposition.  There is no duplicate principal contribution.
Using

```text
M_A(N)>0.91*S(N)*N,

major-model row sum       >= -0.200982*N,
complete Type-I error      < 5*10^-15*N,
major-model error          < 10^-37*N,
prime-power allowance      < 10^-130*N,
```

and `S(N)>=1`, the conversion has the sign

```text
-a*N >= -a*S(N)*N.
```

Consequently the paper ledger gives

```text
R_major(N)>0.708*S(N)*N.
```

This reconciles the stated paper estimates.  It does not formalize them in Lean.

## Exact complete row

For `0<eta<=1/3`, the full correlation is

```text
C_eta(N)
  = sum_(r<=N^eta) Lambda(r)
      sum_(u<p<=U/r, p prime) Lambda(N-r*p).
```

The endpoint `eta=1/3` is the complete one-large-prime row.  Splitting into the coprime-prime,
reflected-proper-prime-power, and common-factor cases leaves only the coprime prime-pair average as a
substantive unknown.  The other two cases have explicit negligible bounds.

## Full local model

For a coprime prime-power cofactor `r=lambda^k`, define

```text
C_eta^0(N)
  = S(N) * sum_(r=lambda^k<=N^eta, (r,N)=1)
      Lambda(r)*(lambda-1)/(lambda-2)
      * [Li(U/r)-Li(u)].
```

The report proves an effective evaluation of this explicit model:

```text
C_eta^0(N)/(S(N)*N)
  = log(1/(1-eta)) + explicit small error.
```

In particular,

```text
C_(1/3)^0(N)
  = [log(3/2)+explicit small error]*S(N)*N.
```

This is not an asymptotic theorem for the actual `C_eta`.  Writing

```text
E_pair(N,eta)=C_good(N)-C_eta^0(N)
```

isolates the missing arithmetic estimate.

## Retained model

The retained calculation preserves the exact quotient `q/(q,r)`, Ramanujan signs, common factors,
and fixed `P=Q=100` arc widths.  It reduces to

```text
J_eta(N)
  = log(1/(1-eta))*T_100(N) + e_eta(N),
```

where

```text
T_100(N)
  = sum_(q<=100) mu(q)^2*c_q(N)/phi(q)^2 * K_q(N)
```

and the report obtains the uniform finite bounds

```text
0.70*N<T_100(N)<5.911*N.
```

The explicit error is negligible at the frozen threshold, so

```text
J_eta(N)>0
```

for `10^-8<=eta<=1/3`.

The coupled deterministic model is therefore

```text
-C_eta^0(N)+J_eta^0(N)
  = -log(1/(1-eta))*[S(N)*N-T_100(N)]
    + explicit small error.
```

This is a new useful structural calculation.  It does not control `E_pair`.

## Why a factor-two upper sieve does not close the row

The singular factor is unbounded along suitable even primorial centers, while `T_100(N)<5.911*N`.
Thus

```text
inf_N T_100(N)/(S(N)*N)=0.
```

The positive retained model cannot supply a uniform positive fraction of the singular-series scale.
In the worst uniform case, a factor-two upper bound would cost

```text
2*log(3/2)=0.8109302162...>0.708.
```

Absent a uniformly helpful retained fraction, the multiplicative full-correlation factor must be
strictly below

```text
0.708/log(3/2)=1.7461428513....
```

This is a limitation of the proposed upper-bound architecture, not a proof that the actual
discrepancy is too negative.

## Published-theorem substitutions checked

The report examines two relevant theorem surfaces:

1. The explicit linear sieve supplies a main sieve function only after an application-specific
   progression remainder is bounded.  For the sequence here, that remainder has moving endpoints,
   residue `N*inverse(r) mod d`, weight `Lambda(r)`, and the reflected logarithmic weight.  No bound
   for this aggregate remainder was supplied.
2. The large-modulus dispersion theorem applies to triply well-factorable weights and allows a
   residue as large as the center.  The raw prime-power cofactor weights here were not shown to be
   triply well-factorable; prime cofactors near `N^(1/3)` are the immediate support problem.  No
   switching decomposition with controlled companion terms and explicit constants was derived.

The theorem search therefore produces no valid substitution with the required constant.  This is
not an impossibility theorem over all future sieve or dispersion arguments.

## Sharpened finite-sieve fallback

Summing the already reviewed finite Selberg bound before replacing local factors by coarse maxima
gives

```text
C_eta(N)
  <= [40000*eta/(1-eta)+10^-30]*S(N)*N.
```

Since the retained term is positive, this implies

```text
Delta_eta(N)
  > -[40000*eta/(1-eta)+10^-30]*S(N)*N.
```

The row-compatible threshold of this specific envelope is

```text
0.708/(40000+0.708)=0.0000176996867155...,
```

and the safe explicit choice is

```text
eta_*=17699/10^9.
```

Dividing the cofactor range into many intervals does not improve this architecture: the leading
costs add to

```text
40000*integral_0^(1/3) dt/(1-t)^2=20000.
```

There is no nonduplicative iteration mechanism hidden in the fallback.

## Exact missing theorem

A sufficient row-compatible statement is the following fixed-center inequality:

```text
sum_(r<=u) Lambda(r)
  sum_(u<p<=U/r, p prime) Lambda(N-r*p)

  <= log(3/2)*T_100(N) + 0.707*S(N)*N.
```

Together with the retained-model error, this would give

```text
Delta_(1/3)(N)>-0.708*S(N)*N.
```

Replacing `0.707` by `0.599` would give the strategically useful `0.600` row allowance.

This is narrower than the complete Mobius-prime discrepancy: it is a nonnegative prime-prime-power
correlation averaged over the cofactor.  No reviewed theorem currently proves it.

## Decision

Honor the stopping rule:

1. preserve the independently reviewed `eta=10^-8` theorem as a standalone result;
2. preserve the sharpened model, retained positivity, and exact missing theorem as research outputs;
3. do not formalize or certificate-populate the `eta_*=0.000017699` fallback for Route A;
4. do not commission another microscopic exponent optimization; and
5. leave Route A suspended unless a genuinely new fixed-center averaged prime-pair estimate addresses
   the displayed missing theorem.

