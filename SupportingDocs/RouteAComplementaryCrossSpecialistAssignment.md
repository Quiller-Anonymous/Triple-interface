# Route A Stage 2 complementary-cross specialist assignment

Date: 2026-10-28

Mathematical base commit:

```text
22a16ab5822479d8ab1bcff9b3785652cf097544
```

Stage 1 packet commit:

```text
f6e466ddfb9f7989097bef0fdc5136f89a6dff17
```

Read together with:

```text
SupportingDocs/RouteAEnlargedMajorArcPaperProofPacket.md
SupportingDocs/RouteAEnlargedMajorArcStage1SpecialistReport.md
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
SupportingDocs/RouteAHardResidualSSUApplicationAudit.md
Goldbach/Cert/MajorArcModules/RouteABalancedVaughanFixedCenter.lean
Goldbach/Cert/MajorArcModules/RouteAFiniteWeightBilinearCircle.lean
```

## Decision to make

Determine whether the exact complementary hard cross-correlation admits an unconditional,
fixed-center lower bound small enough to fit beneath the provisional Stage 1 reserve.

Stage 1 claims

```text
R_major(N) > 0.699 N
```

for every admissible even `N`.  The recommended Stage 2 target is therefore

```text
Re B(N) >= -0.69 N.
```

The formal minimum is any explicit bound `Re B(N) >= -d*N` with `d<0.699`.  The `0.69` target
leaves visible integration and formalization slack.  A stronger absolute bound `|B(N)|<=d*N` is
acceptable, but a one-sided argument may be substantially cheaper.

This is a bounded paper-mathematics feasibility study.  Do not begin Lean formalization and do not
manufacture a certificate unless the analytic estimate first survives this audit.

## Fixed notation

For every even integer

```text
N >= exp(exp(100)),
```

put

```text
L = 1,000,001,
U = N-L,
u = floor(N^(1/3)),
e(x) = exp(2*pi*i*x).
```

Define

```text
S_N(n) = Lambda(n) 1_[L,U](n),

A_u(n) = 1_[L,U](n)
         sum_{d*m=n, d<=u} mu(d)log(m),

h_u(n) = S_N(n)-A_u(n).
```

The checked large-divisor identity is

```text
h_u(n)
  = 1_[L,U](n)
    sum_{d*m=n, d>u} mu(d)log(m).
```

This combined hard coefficient is the primary object.  An auxiliary Vaughan cutoff may be
introduced inside a proof, but all resulting pieces must be recombined.  Bounding only an isolated
long Type-II component does not prove the required theorem.

## Exact retained set and complementary kernel

The retained set is

```text
M = union over 1<=q<=100 and (a,q)=1 of
    {alpha in R/Z : ||alpha-a/q|| <= 100/(qN)}.
```

Let

```text
K_N(j) = integral_[0,1] 1_(M^c)(alpha)e(j*alpha)d alpha.
```

The arcs are disjoint, and the kernel is real and even.  Its exact values are

```text
K_N(0)
  = 1 - (200/N) sum_{q<=100} phi(q)/q,

K_N(j)
  = -sum_{q<=100} c_q(j)
       * sin(200*pi*j/(qN))/(pi*j),       j != 0.
```

No asymptotic replacement of this kernel may be made without an explicit total error estimate.

Set `Srev_N(b)=S_N(N-b)=Lambda(N-b)1_[L,U](b)`.  The exact remaining term is

```text
B(N)
  = sum_{d>u, L<=d*m<=U} sum_{L<=b<=U}
      mu(d)log(m)Lambda(N-b)K_N(d*m-b).
```

Equivalently,

```text
B(N)
  = integral_(M^c)
      hat h_u(alpha) hat S_N(alpha)e(-N*alpha)d alpha.
```

All endpoints and all prime-power terms are already represented in these definitions.  Stage 1
has separately paid the prime-power disposal cost.

## Critical circularity warning

Expanding by shifts gives

```text
B(N) = sum_j K_N(j) C_N(j),

C_N(j) = sum_b h_u(b+j)Srev_N(b),
```

with the support restrictions understood.  The `j=0` term contains

```text
sum_n h_u(n)Lambda(N-n),
```

which is the full hard fixed-center convolution.  It is not known to be positive.  A proof may not
bound this term by assuming Goldbach, by assuming positivity of the full prime convolution, or by
using the desired complementary estimate itself.

Similarly, `K_N` is a positive-semidefinite Toeplitz kernel when paired quadratically with one
coefficient sequence, but `B(N)` is a rectangular cross form between `h_u` and `Srev_N`.
Positive semidefiniteness alone does not give the required sign.

## Phase A: bounded feasibility audit

Do not attempt a full proof before completing these four diagnostics.

### A1. Exact decomposition and normalization audit

Re-derive the displayed kernel and cross form from the Fourier convention.  Confirm:

* the sign of `K_N(j)`;
* the factor `200*pi/(qN)`;
* the wrapped principal arc;
* the reflection `Srev_N(b)=Lambda(N-b)`;
* the support ranges and endpoint conventions;
* that the resulting scalar is real.

Report any correction before estimating the form.

### A2. Known-theorem inventory

Identify the strongest published unconditional theorem that could apply to this exact form.  For
each candidate, state:

* its exact theorem statement and constants;
* whether it is pointwise in the center `N` or only averaged over centers;
* its coefficient hypotheses;
* its shift/frequency range;
* whether it exploits the Mobius and von Mangoldt structure or only coefficient energies;
* the bound obtained after restoring every logarithm, dyadic block, and overlap multiplicity.

Do not cite a theorem merely by family name (large sieve, dispersion, Bombieri--Vinogradov,
Type-II, or SSU).  Show the substitution into its hypotheses and the resulting numerical bound.

### A3. One fully restored dyadic block

Choose a block that is predicted to be among the worst after summation.  For example, restrict

```text
D<d<=2D,
M0<m<=2M0,
L<=d*m<=U,
```

and retain the complete reflected-prime variable.  Prove an actual estimate for

```text
B_(D,M0)(N)
  = sum_{D<d<=2D, d>u}
      sum_{M0<m<=2M0, L<=d*m<=U}
      sum_{L<=b<=U}
        mu(d)log(m)Lambda(N-b)K_N(d*m-b).
```

The worked block must display:

* all coefficient norms;
* product multiplicities;
* boundary losses;
* the number of dyadic blocks or shells needed globally;
* any smoothing and desmoothing losses;
* the exact fixed-center conclusion;
* the numerical saving over the trivial bound.

If the theorem applies only after separating `h_u` into several Vaughan pieces, show how the
companion pieces recombine and include all of their costs.

### A4. Global forecast

Before completing every block, sum a rigorously justified envelope over the entire dyadic range.
State the predicted final constant `d`.  Continue to Phase B only if the forecast gives

```text
d < 0.699,
```

preferably `d<=0.69`.

If the forecast is `N log N`, contains an unabsorbed positive power of `log N`, or exceeds the
reserve, stop and identify the precise missing theorem.

## Phase B: full paper theorem

If Phase A passes, prove the following theorem with explicit constants:

```text
For every even N>=exp(exp(100)),

Re sum_{d>floor(N^(1/3)), L<=d*m<=N-L}
     sum_{L<=b<=N-L}
       mu(d)log(m)Lambda(N-b)K_N(d*m-b)
  >= -d*N,

with d<0.699.
```

The proof must be uniform in every admissible even center; no exceptional centers are allowed.

Acceptable proof organizations include:

1. a direct one-sided estimate using the exact Ramanujan/sine kernel;
2. a dyadic dispersion or shifted-convolution argument for the actual cross coefficients;
3. a restricted cross-SSU theorem whose hypotheses are proved for these arithmetic coefficients;
4. an exact combination of major/minor or near/far shift estimates, provided no part is counted
   twice and every transition is explicit.

These are suggestions, not assumptions that such a theorem exists.

## Quantitative requirements

Every final proof must include a ledger containing at least:

| Component | Required output |
| --- | --- |
| Kernel diagonal/zero shift | Exact treatment, with no positivity assumption |
| Near nonzero shifts | Explicit one-sided or absolute allowance |
| Far shifts | Explicit allowance and theorem used |
| Dyadic hard blocks | Bound for each range and number of ranges |
| Prime coefficient | Exact norm or progression estimate |
| Mobius coefficient | Exact norm and any cancellation theorem |
| Smoothing/desmoothing | Explicit cost |
| Endpoints | Explicit cost |
| Total | `D_minor(N)/N <= d < 0.699` |

If a term is negligible because `log log N>=100`, state a monotone explicit inequality at the
threshold rather than writing `o(N)`.

## Prohibited shortcuts

The following do not satisfy the assignment:

1. A generic Cauchy--Schwarz or polarization estimate that yields only `O(N log N)`.
2. An estimate averaged over `N`, almost all `N`, or all but an exceptional set.
3. Replacing the fixed center by a nearby favorable center.
4. Assuming the cross-cancellation in a hypothesis, certificate record, or coefficient-flatness
   condition that has not itself been proved.
5. Proving a theorem for arbitrary coefficient arrays and counting a displayed square-root factor
   as a saving without restoring the actual array norms and tube counts.
6. Bounding only the isolated long Type-II term while omitting the companion terms.
7. Using positivity of the Goldbach convolution, the zero-shift hard convolution, or the desired
   conclusion.
8. Silently changing the retained set, arc width, threshold, or hard coefficient.

If changing one of those objects appears mathematically necessary, stop and propose the change as
a separate route with a complete new budget.

## Required response

Return a report with one of these verdicts.

### PASS

Supply:

* the complete theorem and proof;
* an explicit `d<0.699`;
* the restored component ledger;
* exact source dependencies;
* a short map from each paper lemma to the fixed objects above.

### FAIL

Supply either:

* a mathematical obstruction to the target; or
* a rigorous calculation showing that the strongest applicable unconditional estimate exceeds
  the reserve.

State whether the failure is caused by the zero shift, a particular dyadic region, coefficient
norms, endpoint losses, or lack of a fixed-center theorem.

### UNRESOLVED

State one precise missing theorem in a form that could be reviewed independently.  Include:

* its exact coefficient surface;
* its required numerical constant;
* why known theorems do not imply it;
* whether it would be a conventional strengthening or a genuinely new binary-Goldbach-level
  estimate.

Do not return a list of possible techniques without carrying at least one of them through the
worked-block calculation in Phase A.

## Consequence of a pass

If Stage 1 survives second review and this assignment proves `d<0.699`, then

```text
R_major(N) + Re B(N) > 0
```

at the paper level for every admissible even `N`.  The next work would be:

1. reconcile the positive weighted convolution with the exact prime-pair conclusion;
2. formalize the Stage 1 and Stage 2 analytic inputs in Lean;
3. connect the resulting theorem to the Route A wrapper;
4. audit the final theorem for project-specific assumptions.

Those consequences are not part of the present assignment.
