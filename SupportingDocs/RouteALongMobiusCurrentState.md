# Long-Mobius / centered-divisor-graph current-state audit

Date: 2026-10-30

Repository commit: `d150106a204bb3ac4a523bdaa65256eb30526995`

## Executive verdict

There is no current long-Mobius or centered-divisor-graph audit in this repository.  The proposed
objects named `b_z`, `f_Y`, `I_Y`, `T_z(N)`, and `V_z(N)`, the proposed inequalities numbered
`(18)` through `(21)`, and a graph trace or spectral estimate for those objects do not occur in the
working tree or its Git history.  A scan of the retained plaintext project conversation archive
also found no earlier definition of them.

Accordingly, this packet does **not** reconstruct those definitions from conversation fragments.
There is presently no mathematically specified long-Mobius experiment to validate, no associated
code to run, and no four-point power-saving claim whose normalization can be checked.  If these
objects were developed elsewhere, that source document is required before the proposed mechanism
can receive a PASS, FAIL, or UNRESOLVED verdict.

The repository does contain a closely related but different exact coefficient surface:

```text
h_u(n) = sum_(d*m=n, d>u) mu(d) * log(m).
```

Lean proves that this is the combined hard coefficient left after removing the short Type-I term
from `Lambda`.  The repository also contains a reproducible structural audit of the old `X0`
Ramanujan certificate.  Those results, the latest fixed-center budget, and the relevant stopping
reports are inventoried below.  They must not be relabeled as the missing centered-divisor-graph
proposal.

## 1. Source and search audit

The following locations were searched for the names and phrases in the request:

```text
README.md
SupportingDocs/
Goldbach/
scripts/
SSU/
all Git revisions reachable from the repository
retained plaintext Codex session and archived-session messages
```

The search covered spelling variants of `long-Mobius`, `centered-divisor-graph`, `divisor graph`,
the five requested symbols, and `mathcal V_z`.  It returned no definition or proposal.  The only
near-name in the repository is the uppercase function `F_Y(t)` in
`RouteAPrimeCompanionObstruction.md`.  That function is an elementary prime-divisor profile and is
not the requested lowercase `f_Y`, graph observable, or long-Mobius experiment.

The equation numbers `(18)` through `(21)` are likewise absent from the relevant Route A reports.
Equation numbering therefore cannot be recovered reliably from the repository.

This is a negative provenance result, not a mathematical disproof.  It establishes that the
requested proposal is currently **unspecified** in the project record.

## 2. Exact Lean-checked coefficient surface that does exist

The exact finite Vaughan identity is proved in
`Goldbach/Cert/MajorArcModules/RouteABalancedVaughanIdentity.lean`.  With independent cutoffs `u`
and `v`, it states

```text
Lambda
  = Lambda_<=v
    + mu_<=u * log
    - mu_<=u * zeta * Lambda_<=v
    + mu_>u * zeta * Lambda_>v.
```

`Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean` then defines the combined hard
coefficient and proves

```text
vaughanHardArithmetic u v
  = Lambda - mu_<=u * log
  = mu_>u * log.
```

The pointwise theorem `vaughanHardArithmetic_apply` is exactly

```text
h_u(n)
  = sum_(d*m=n, d>u) mu(d) * log(m).
```

The same module proves that the combined coefficient is independent of the auxiliary cutoff `v`.
It also keeps the exact three-term internal split visible and proves the fixed-center recombination

```text
H(S,S) = H(mu_<=u * log, S) + H(h_u, S),
```

both for the full convolution and for complementary frequency masks.  These statements are
algebraic identities.  They do not assert cancellation in `H(h_u,S)`.

For the one-large-prime/small-cofactor subfamily, the paper audit proves the additional identity

```text
h_u(p*r) = -Lambda(r)
```

when `p>u` is prime and `1<=r<=u`.  This follows by combining all large divisors of the same
integer before taking absolute values.  Independent project review rederived this paper identity
and its finite-sieve application.  The specialized theorem has not been formalized in Lean.

These are the appropriate starting identities for any future long-Mobius graph construction.  A
new proposal must define its `b_z`, `f_Y`, interval, centering, and graph directly from this exact
coefficient, and then prove the equality between its graph statistic and the fixed-center
correlation it claims to control.

## 3. Trace-bound and graph-operator status

No centered-divisor graph is currently defined.  In particular, the repository provides none of
the following data:

```text
vertex set;
vertex measure or weights;
edge condition and multiplicity;
matrix entries;
centering projection;
operator normalization;
identity relating a trace or fourth moment to V_z(N);
diagonal contribution;
claimed spectral gap or power-saving exponent.
```

There is therefore no proposed trace-bound derivation to reproduce.  A statement that
"four-point correlations should exhibit a power saving" is, at present, an unrecorded heuristic.

The closest proved negative audit is
`SSU/Engines/TypeIIToeplitzGlobalNoSavingAudit.lean`.  It tests the global all-array
`Step34ProdSum` interface with the constant-one array at frequency zero and proves

```text
card(T) <= C * sqrt(H/X).
```

Thus the displayed square-root factor in that unrestricted interface does not itself beat the
trivial pointwise cardinality.  Any useful graph theorem must exploit a genuinely restricted
arithmetic coefficient family, an integrated estimate, or another structure absent from the
generic energy interface.

Before a proposed trace theorem is treated as evidence, it must pass two elementary tests:

1. Expand its diagonal and repeated-index contributions exactly and show that the claimed power
   saving is compatible with their nonnegative lower bound.
2. Restore the normalization that converts the trace estimate back to the one fixed center `N`.
   Averaging over centers, graph vertices, or truncation parameters cannot silently replace the
   required pointwise statement.

## 4. Reproducible experimental evidence

### 4.1 No long-Mobius experiment

There is no script, parameter file, output log, or retained payload for the requested `b_z` /
`f_Y` / `I_Y` / `T_z` / `V_z` proposal.  Hence there is no numerical evidence for signed
long-Mobius cancellation to report.

### 4.2 X0 Ramanujan certificate structure

The separate X0 audit is reproducible with

```text
python3 scripts/experiments/route_a_x0_certificate_structure_audit.py
```

using the exact rational payloads bundled with the review packet.  A fresh run at the commit above
reported:

```text
active modulus support                  3042
ordered pairs with a full block         49528
full-block zero records                 18870
full-block nonzero records              30658

periodic-main signed total              37602.761245367078709324
periodic-main absolute total            37602.782052311487596790
dyadic alias records                    2028
dyadic alias total                      37602.763328571457988040
dyadic share of absolute mass           99.999950207%
off-orbit signed total                  -0.002083204379278716
off-orbit absolute total                0.018723740029608750
dyadic orientation mismatches           0

odd cores 3,5,7 share                   96.537307169%
odd cores <=100 share                   99.969344030%
odd cores <=1000 share                  99.999805723%

active-boundary signed total            -25.284933542674991573
active-boundary absolute total          597.953421599744232634
absolute signed/variation ratio         4.228579122%
```

The non-dyadic payload has 27,657 records, 1,855 LCM fibers, and 1,489 dyadic odd-core orbits.  Its
mean-product, dyadic-weight, and LCM-total mismatch counts are all zero, and its exact totals match.

This is genuine structure: on even arguments, the modes `r` and `2r` are exact aliases for odd
`r`; quotienting by that relation makes the periodic-main Gram form almost diagonal; and modes
`3`, `5`, and `7` carry more than 96.52 percent of the full-period variance.  Lean formalizes the
uniform low-mode concentration in `Q0SigmaTruncLowModeConcentration.lean`.

It is not evidence for a long-Mobius four-point power saving.  It concerns the finite Ramanujan
truncation and explains why the X0 energy certificate compressed.

### 4.3 Fixed-center finite diagnostic

`scripts/experiments/route_a_retained_margin_feasibility.cpp` evaluates the exact finite
convolution and retained cutoff-two integral.  The retained audit records the following runs with
`L=1000001` and `u=floor(N^(1/3))`:

| `N` | complementary hard / `N` | retained hard / `N` | full hard / `N` |
| ---: | ---: | ---: | ---: |
| `2^21` | `+0.0118042` | `-0.0003035` | `+0.0115007` |
| `2^22` | `+0.1137834` | `-0.1031912` | `+0.0105922` |
| `2^23` | `+0.2312932` | `+0.0165746` | `+0.2478677` |

These values show favorable signs at three moderate centers only.  They are not a uniform theorem,
and no raw machine log beyond the source and report table is retained in the repository.  The
current macOS environment could not freshly compile the C++ source because its configured compiler
could not find the C++ standard-library headers; the packet records that reproduction limitation
rather than presenting the historical table as a fresh run.

## 5. Current fixed-center budget

The latest complete-row paper audit is
`SupportingDocs/RouteAOneLargePrimeCompletionAudit.md`, independently rederived within the project
in `RouteAOneLargePrimeCompletionIndependentReview.md`.  This is paper-level verification, not a
Lean theorem or external peer review.

On its inherited analytic inputs, the normalized ledger is

```text
active main                         >  0.91 * S(N) * N
major-model row sum                 >= -0.200982 * N
complete Type-I error               <  5e-15 * N
major-model error                   <  1e-37 * N
prime-power allowance               <  1e-130 * N
```

Using `S(N)>=1` in the correct direction gives the positive paper reserve

```text
R_major(N) > 0.708 * S(N) * N.
```

The complete one-large-prime row is

```text
C_eta(N)
  = sum_(r<=N^eta) Lambda(r)
      sum_(u<p<=U/r, p prime) Lambda(N-r*p),
```

with endpoint `eta=1/3`.  Its explicit local model has coefficient

```text
log(3/2) = 0.405465108108164...
```

and the retained model is

```text
J_eta(N) = log(1/(1-eta))*T_100(N) + e_eta(N),
0.70*N < T_100(N) < 5.911*N.
```

The exact currently missing sufficient theorem is

```text
sum_(r<=u) Lambda(r)
  sum_(u<p<=U/r, p prime) Lambda(N-r*p)

  <= log(3/2)*T_100(N) + 0.707*S(N)*N.
```

With the retained-model error this would give

```text
Delta_(1/3)(N) > -0.708*S(N)*N.
```

The factor-two sieve envelope costs

```text
2*log(3/2) = 0.810930216216329...,
```

which exceeds the reserve by

```text
0.102930216216329... * S(N)*N.
```

Equivalently, a multiplicative full-correlation factor must be strictly below

```text
0.708/log(3/2) = 1.746142851362513...,
```

an improvement of more than `0.253857148637487` over factor two.  Replacing `0.707` by `0.599` in
the sufficient theorem would give the strategically useful `0.600` row allowance.

The deterministic arithmetic in this section is reproduced by
`scripts/experiments/route_a_fixed_center_frontier_budget.py`.

The independently reviewed narrow small-cofactor theorem controls only `eta=10^-8`:

```text
Delta_(10^-8)(N) > -0.001609*S(N)*N.
```

After this allowance the ledger has `0.706391*S(N)*N` left.  The reviewed finite-sieve extension
reaches only `eta=17699/10^9`, below its stopping threshold, and does not close the full row.

## 6. Obstructions and stopping rules

The following results constrain any proposed long-Mobius theorem.

### Generic energy is insufficient

The Lean theorem in `TypeIIToeplitzGlobalNoSavingAudit.lean` proves that the unrestricted global
SSU interface pays the trivial cardinality at zero frequency.  A graph expansion cannot be counted
as progress unless its arithmetic restriction produces a quantitative saving after all coefficient
norms and shell sums are restored.

### Isolating the prime companion is impossible

The paper theorem in `RouteAPrimeCompanionObstruction.md` proves an averaged negative obstruction
for the isolated prime outer-divisor contribution under the fixed mask.  In particular, arbitrarily
large even centers satisfy

```text
Delta_P(N) < -(1/10000)*N*log N.
```

Thus this term cannot be bounded below by `-C*N` independently.  A successful argument must retain
cancellation with suitable composite-divisor terms.  The theorem does not say that cancellation
must cross the report's smooth/rough strata.

### Factorable dispersion does not cover the raw coefficient

`RouteAFactorableDispersionAudit.md` records that a triply well-factorable weight of level `Z`
vanishes when its modulus has a prime factor exceeding `Z^(1/3)`.  The raw Mobius interval contains
prime moduli near `sqrt(N)`, so a finite replacement by such weights leaves a large companion term.
The attempted reduction did not produce an independently smaller theorem.

### The one-large-prime completion remains Goldbach-level

The latest reviewed audit could not control the difference between the actual fixed-center
prime-pair convolution and its local model with the required constant.  Existing linear-sieve and
large-modulus-dispersion surfaces did not supply the displayed missing theorem.  This is the active
stopping rule: do not generate another certificate or optimize a microscopic exponent unless a new
fixed-center averaged prime-pair estimate beats the stated budget.

## 7. Falsification-first requirements for a supplied graph proposal

If an external long-Mobius document exists, the next review should require it to provide:

1. Exact definitions of all five requested objects, including endpoint conventions and whether
   `mu`, `Lambda`, and logarithmic weights are normalized or raw.
2. An exact equality from its statistic back to `h_u` and the reflected prime coefficient at one
   specified center.
3. The graph matrix, measure, centering projection, and trace normalization.
4. A complete diagonal calculation before any off-diagonal cancellation claim.
5. A theorem statement quantifying uniformly over every admissible even `N`, not merely an average
   over centers.
6. A restored ledger proving that the result supplies at least the saving stated in Section 5.
7. Code and raw output that separate signed sums from absolute sums and report every averaging or
   truncation parameter.

Until those items are supplied, the correct verdict on the centered-divisor-graph / long-Mobius
proposal is **UNSPECIFIED**, not PASS, FAIL, or UNRESOLVED.

