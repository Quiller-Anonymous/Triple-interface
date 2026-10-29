# Independent review assignment: one-large-prime completion audit

Date: 2026-10-29

## Outcome

**PASS for the audit's mathematics and its UNRESOLVED stopping decision.**  No constant or scope
correction was required.  The result is recorded in
`SupportingDocs/RouteAOneLargePrimeCompletionIndependentReview.md`.  This closes the bounded review
sequence; it does not authorize another microscopic range expansion or formalization program.

## Purpose

Review the provisional UNRESOLVED verdict in

```text
SupportingDocs/RouteAOneLargePrimeCompletionAudit.md
```

This is a verification task, not another attempt to solve the missing prime-pair theorem.  Report
**PASS**, **REVISE**, or **FAIL**, identifying the first invalid identity or inequality.

Read:

```text
SupportingDocs/RouteAOneLargePrimeCompletionFeasibilityAssignment.md
SupportingDocs/RouteAOneLargePrimeCompletionAudit.md
SupportingDocs/RouteASmallCofactorCancellationIndependentReview.md
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
SupportingDocs/RouteAEnlargedMajorArcStage1SpecialistReport.md
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanActiveMain.lean
```

## 1. Normalized Stage 1 reconciliation

Verify that the active main, hard retained model, Type-I error, major-model error, and prime-power
allowance are distinct terms of the same exact decomposition.  Check the sign conversion

```text
-a*N >= -a*S(N)*N
```

from `S(N)>=1`, and independently reproduce

```text
R_major(N)>0.708*S(N)*N.
```

State which ingredients remain paper-level.

## 2. Exact complete-row decomposition

Verify the identity

```text
C_eta(N)
  = sum_(r<=N^eta) Lambda(r)
      sum_(u<p<=U/r, p prime) Lambda(N-r*p)
```

and the disjoint separation into coprime-prime, reflected proper-prime-power, and common-factor
rows.  Check all floors, endpoints, uniqueness assertions, and the negligibility bounds for the last
two rows.

## 3. Local model

Reproduce the exact local factor and model

```text
S(N,r)=S(N)*(lambda-1)/(lambda-2),

C_eta^0(N)
  = S(N)*sum_(r=lambda^k<=N^eta, (r,N)=1)
      Lambda(r)*(lambda-1)/(lambda-2)
      * [Li(U/r)-Li(u)].
```

Verify, with explicit errors, that

```text
C_eta^0(N)/(S(N)*N)
  = log(1/(1-eta))+small error
```

and in particular the coefficient `log(3/2)` at `eta=1/3`.  Confirm that this evaluates only the
model and is not presented as an asymptotic for the actual convolution.

## 4. Retained model and positivity

Check the exact `q/(q,r)` reduction and derive

```text
J_eta(N)=log(1/(1-eta))*T_100(N)+e_eta(N).
```

Independently verify the finite arithmetic bounds

```text
0.70*N<T_100(N)<5.911*N
```

and all error estimates needed for `J_eta(N)>0` uniformly on `10^-8<=eta<=1/3`.

Check especially:

1. the `q=1,2` lower contribution;
2. the charging argument for negative squarefree rows;
3. the rational upward total `1.282878<1.283`;
4. endpoint losses in `K_q(N)`;
5. nonsquarefree actual errors; and
6. the threshold comparison between the positive main and `e_eta`.

## 5. Uniform factor-two diagnostic

Verify that `S(N)` is unbounded along admissible even centers and that `T_100(N)<5.911*N` implies

```text
inf_N T_100(N)/(S(N)*N)=0.
```

Then reproduce

```text
2*log(3/2)>0.708,

0.708/log(3/2)=1.7461428513....
```

Confirm that this defeats only the proposed uniform factor-two envelope, not the actual row.

## 6. Theorem-applicability audit

Check the report's use and non-use of:

1. the explicit linear sieve of Bordignon--Johnston--Starichkova; and
2. Lichtman's large-modulus theorem with triply well-factorable weights.

For the linear sieve, verify that its remainder term is not bounded merely by quoting the theorem.
For the dispersion theorem, verify the factorability and support obstruction for the raw cofactor
weights.  A **FAIL** here requires an exact theorem substitution that applies to the displayed
sequence with all hypotheses and constants, not a general claim that stronger sieve results exist.

Primary sources:

```text
https://arxiv.org/abs/2207.09452
https://arxiv.org/abs/2309.08522
```

## 7. Sharpened fallback arithmetic

Re-derive

```text
C_eta(N)
  <= [40000*eta/(1-eta)+10^-30]*S(N)*N
```

from the already reviewed finite sieve without the earlier coarse local-factor replacements.

Using outward arithmetic, verify

```text
eta_row=0.708/(40000+0.708)
       =0.0000176996867155...,

eta_*=17699/10^9,

40000*eta_*/(1-eta_*)
  =0.7079725304058...<0.708.
```

Also verify that interval subdivision adds to total leading cost `20000` over `0<=eta<=1/3` and
does not provide an iteration mechanism.

## 8. Missing-theorem sufficiency

Check that

```text
sum_(r<=u) Lambda(r)
  sum_(u<p<=U/r, p prime) Lambda(N-r*p)

  <= log(3/2)*T_100(N) + 0.707*S(N)*N
```

combined with the retained model and its explicit error is sufficient for

```text
Delta_(1/3)(N)>-0.708*S(N)*N.
```

Correct the `0.707` buffer if the displayed retained error requires a different outward constant.

## Required verdict

### PASS

Confirm separately:

1. the normalized Stage 1 reconciliation;
2. the local-model coefficient;
3. retained-model positivity;
4. the factor-two diagnostic;
5. the fallback exponent; and
6. the exact missing theorem.

Conclude only that the branch has reached its stopping rule.  Do not call the missing theorem
impossible.

### REVISE

Supply corrected constants or scope.  State whether the stopping decision changes.

### FAIL

Identify the first false structural claim, or provide a currently available theorem that actually
discharges the fixed-center average with the required constant.

## Prohibited shortcuts

The review does not pass if it:

1. treats the local model as the actual prime-pair correlation;
2. uses an average over centers for a fixed-center target;
3. discards the retained term before checking its sign;
4. assumes a finite retained mask captures a fixed fraction of an unbounded singular factor;
5. accepts a sieve theorem without its sequence remainder; or
6. restarts microscopic range expansion despite the stopping rule.

