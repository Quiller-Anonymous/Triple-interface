# Route A complementary-cross Stage 2 audit

Date: 2026-10-28

## Decision

The Stage 2 feasibility gate is **UNRESOLVED**.  Phase B is not authorized.

The specialist re-derived the exact complementary kernel, reflection, support, wrapped principal
arc, and sign conventions.  That part of the proposed enlarged-major-arc route survived the audit.
The specialist also obtained a genuine logarithmic improvement for a balanced dyadic block by
using a fixed-center prime-progression estimate and actual Mobius cancellation on the retained
arcs.  The improvement is nevertheless far too weak for the available Stage 1 reserve.

This is not a counterexample to the desired lower bound.  It is a demonstration that the reviewed
published estimates do not prove it on the present coefficient surface.

## Quantitative outcome

For a balanced block with `D` comparable to `sqrt N`, the specialist obtains

```text
|B_(D,D)(N)| <= D^2 * (24*log N + 4).
```

The direct elementary envelope for the same block is of order `D^2*(log N)^2`, so this is a real
factor-of-`log N` saving.  Since `D^2` is still a fixed fraction of `N`, however, the normalized
bound is of order `log N`, not a constant below `0.699`.

The resulting full-range envelope is

```text
B(N)/N >= -[
  6*log N*(1 + log N)
  + 10100*log^2(N/u)
  + 32*N^(-1/6)*log^2 N
].
```

Even if the retained contribution is granted the much stronger provisional allowance `0.201*N`,
the remaining estimate is still of order `N*(log N)^2`.  Endpoint refinements, prime-power
bookkeeping, and sharper Brun--Titchmarsh constants cannot remove this loss.

## Exact frontier

Let

```text
eta_N = (200/N) * sum_(q<=100) phi(q)/q,

W_N(0) = eta_N,

W_N(j) = sum_(q<=100) c_q(j)
           * sin(200*pi*j/(q*N))/(pi*j)       for j != 0.
```

The unresolved theorem is the fixed-center signed discrepancy

```text
sum_(d>u, L<=d*m<=U) mu(d)*log(m) * [
  Lambda(N-d*m)
  - sum_(L<=b<=U) Lambda(N-b)*W_N(d*m-b)
] >= -0.69*N.
```

The reviewed progression estimate controls prime values separately for each `d`, but taking
absolute values loses cancellation between those progression counts and `mu(d)`.  The available
ordinary Mobius bounds control the smooth retained model, not the nonsmooth weight
`Lambda(N-d*m)` at one prescribed center.

A proof of this inequality, combined with the provisional Stage 1 reserve, would already imply a
quantitative binary Goldbach result.  It should therefore be treated as a binary-Goldbach-level
analytic theorem, not as a missing routine bridge or a certificate population task.

## Candidate theorems checked in the specialist audit

The following do not presently close the exact form:

* Sharper Brun--Titchmarsh constants retain the fatal logarithm.
* Kloosterman-fraction estimates give genuine power savings for a reciprocal phase, but no
  justified transformation of the reflected prime coefficient to that phase was supplied.
* Large-modulus dispersion theorems apply to triply well-factorable modulus weights.  The raw
  weight `mu(d) * 1_(D,2D](d)` is not triply well-factorable; its nonzero values at large primes
  give an immediate support obstruction to such a representation.
* The strongest directly relevant prime-correlation results found are for almost all centers, not
  every fixed even center.
* The current SSU interface assumes the arithmetic fixed-array saving needed for this application;
  it does not prove that saving for the Mobius--prime coefficients.

## Project consequence

Do not:

1. start Phase B;
2. formalize the failed `N*(log N)^2` envelope as if it advanced closure;
3. commission another finite certificate for this obstruction;
4. describe Stage 1's positive reserve as an unconditional Route A closure result.

The enlarged-major-arc work remains useful as:

* a checked normalization and exact decomposition;
* a provisional positive retained-main result;
* a precise isolation of the fixed-center signed Mobius--prime obstruction;
* a reusable test surface for any genuinely new dispersion theorem.

Route A remains suspended as a proof-completion project.

## One bounded continuation

The specialist identified one nonvacuous opening: a more elaborate arithmetic decomposition might
replace part of the raw Mobius interval weight by triply well-factorable weights, at the cost of
companion terms.  This possibility has not been established.  It is the subject of

```text
SupportingDocs/RouteAFactorableDispersionFeasibilityAssignment.md
```

That assignment is a final bounded feasibility test, not authorization for a new Lean build.  If
the complete decomposition leaves a nonfactorable fixed-center remainder of linear or larger
scale, or only produces an almost-all-centers theorem, this branch stops.

