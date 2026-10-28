# Route A factorable-dispersion feasibility assignment

Date: 2026-10-28

## Purpose

Test the only concrete analytic opening left by the complementary-cross Stage 2 audit:

> Can the exact hard Mobius--prime correlation be decomposed into modulus weights covered by a
> fixed-center, large-modulus dispersion theorem, with every companion term controlled and a final
> one-sided allowance below `0.699*N`?

This is a bounded paper-mathematics investigation.  Do not write Lean, generate certificates, or
assume the desired cancellation.  The default expectation is **UNRESOLVED** unless a complete
theorem substitution is exhibited.

Read first:

```text
SupportingDocs/RouteAComplementaryCrossSpecialistAssignment.md
SupportingDocs/RouteAComplementaryCrossStage2Audit.md
SupportingDocs/RouteAEnlargedMajorArcStage1Audit.md
SupportingDocs/RouteAEnlargedMajorArcPaperProofPacket.md
```

## Fixed target

Retain all notation and normalizations from the Stage 2 assignment.  In particular,

```text
L = 1,000,001,
U = N-L,
u = floor(N^(1/3)),
N >= exp(exp(100)), N even,
```

and use the exact retained kernel `W_N` from the Stage 2 audit.  The quantity to bound is

```text
Delta(N) =
  sum_(d>u, L<=d*m<=U) mu(d)*log(m) * [
    Lambda(N-d*m)
    - sum_(L<=b<=U) Lambda(N-b)*W_N(d*m-b)
  ].
```

The required conclusion is

```text
Delta(N) >= -d0*N
```

for every admissible even `N`, with an explicit `d0<0.699` and preferably `d0<=0.69`.

Changing to an average over `N`, deleting the retained projection, or replacing the hard
coefficient by a sieve majorant is a different theorem and does not pass this assignment.

## Candidate mechanism

The Stage 2 report notes that modern fixed-residue dispersion estimates can reach beyond the
square-root barrier for triply well-factorable modulus weights.  They do not apply directly to

```text
lambda_D(d) = mu(d) * 1_(D,2D](d).
```

In particular, a triply supported convolution at level `D` vanishes at primes larger than the
component support, while `lambda_D(p)=-1` for primes in the interval.

The only admissible strategy is therefore an exact combinatorial decomposition, such as a
Vaughan-, Heath--Brown-, Buchstab-, or sieve-weight decomposition, that produces:

1. components satisfying the precise factorability hypotheses of a published theorem;
2. explicit companion components covering all omitted values, including prime `d`;
3. no appeal to the desired Goldbach correlation in controlling the companions.

The name of an identity is not enough.  Write every resulting coefficient and support range.

## Phase A: exact coefficient decomposition

Work first on a balanced block

```text
D<d<=2D,
M<m<=2M,
D,M comparable to sqrt N,
L<d*m<U.
```

Produce an exact finite identity for the block coefficient.  For each component state:

* its coefficient formula;
* support lengths;
* coefficient sup and `L2` norms;
* whether its modulus weight is well-factorable, triply well-factorable, or neither;
* whether factorability holds in the theorem's universal sense for every requested factorization;
* the treatment of prime and almost-prime values of `d`;
* all signs and multiplicities;
* all companion and boundary terms.

An identity whose remainder still contains

```text
mu(d) * 1_(D,2D](d)
```

on a set of mass large enough to reproduce the Stage 2 `N*log N` loss has failed this phase.

## Phase B: published-theorem substitution

For every component claimed to be controlled by dispersion, provide:

* the exact published theorem and version;
* the theorem's modulus level, residue range, smoothness, and factorability hypotheses;
* whether it is pointwise in the residue/center or permits exceptional centers;
* the substitution of `x`, the residue `N`, modulus level, interval endpoints, and all weights;
* the resulting exponent and every logarithmic factor;
* whether the implicit constant is effective;
* a computable threshold at which the result is below the allocated fraction of `N`.

The residue may grow with `N`; verify the theorem's stated uniformity rather than treating the
center as fixed.  Weighted `log(m)` and interval truncations must be restored by an explicit
partial-summation or smoothing argument.

If a reciprocal-phase estimate is used, derive the transformation from the exact reflected-prime
coefficient.  Do not replace `Lambda(N-d*m)` by a smooth weight without proving and budgeting that
step.

## Phase C: companions and global ledger

Sum the complete decomposition over all dyadic ranges.  The ledger must separately include:

| Component | Required accounting |
| --- | --- |
| Factorable progression discrepancies | Explicit total bound |
| Principal progression terms | Signed Mobius cancellation with proof |
| Prime-`d` and other nonfactorable companions | Explicit fixed-center bound |
| Retained-kernel correction | Exact bound, no double counting |
| Prime powers and noncoprime residues | Explicit allowance |
| Smoothing and desmoothing | Explicit allowance |
| Product boundaries and dyadic overlaps | Explicit allowance |
| Total | `Delta(N)/N >= -d0`, `d0<0.699` |

The final estimate must be uniform for every admissible even `N`.

## Hard stopping conditions

Return **FAIL** or **UNRESOLVED** immediately if any of the following occurs:

1. A nonfactorable companion remains at order `N`, `N*log N`, or larger without a proved favorable
   sign or cancellation theorem.
2. The cited theorem is only average over centers or allows exceptional even `N`.
3. The factorability hypothesis is asserted for the raw Mobius interval weight.
4. The proof controls an isolated Vaughan/Heath--Brown component but omits its companions.
5. The transformation to a Kloosterman or reciprocal phase leaves an uncontrolled prime
   transform.
6. The result is `o(N)` only with an ineffective or noncomputable threshold.
7. The final ledger does not beat `0.699*N`.

Do not respond to a stopping condition by enlarging a finite certificate.  The obstruction is
uniform and analytic.

## Required verdict

### PASS

Supply the exact decomposition, complete theorem substitutions, effective global ledger, and an
explicit `d0<0.699` for every admissible even `N`.

### FAIL

Identify the component that cannot satisfy the needed estimate and prove the resulting lower
limit on the available envelope or the mismatch with the cited theorem.

### UNRESOLVED

State one precise residual theorem, its exact coefficient surface, and why it is materially
narrower than the Stage 2 fixed-center discrepancy.  If the residual simply restates that
discrepancy or already implies quantitative binary Goldbach with no independently useful
structure, say so and stop.

## Project decision after this assignment

Passing this test would authorize a complete paper proof of the complementary bound, followed by
independent review and only then Lean formalization.  Failure or an unresolved Goldbach-level
remainder freezes this Route A branch as a conditional reduction and redirects effort to either a
different mathematical route or publication of the verified infrastructure and obstruction.

