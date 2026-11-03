# Triple Interface: Final Route A Research Status

Date: 2026-10-31

Status: **ARCHIVED - ANALYTIC INPUT MISSING**

- Route A: analytically stalled
- Route B: retired
- Unconditional Goldbach closure: not established

This document supersedes Route A proof-completion plans that describe another certificate,
post-certificate bridge, or formal assembly step as the live blocker. The historical Q0 certificate
and its generated Lean modules remain useful computational artifacts, but they do not supply the
uniform fixed-center analytic theorem required by the Goldbach endpoint.

## Verified Structural Endpoint

Let

\[
  \mu_{\le D_0} = \mu\,\mathbf 1_{n\le D_0},
  \qquad
  \Lambda_{\le V_0} = \Lambda\,\mathbf 1_{n\le V_0},
\]

with complementary truncations defined similarly. The reflected Vaughan identity

\[
\Lambda = \Lambda_{\le V_0}
  + \mu_{\le D_0}*\log
  - \mu_{\le D_0}*\Lambda_{\le V_0}*1
  + \mu_{>D_0}*\Lambda_{>V_0}*1
\]

has been independently rechecked. It follows from `log = Lambda * 1` and `mu * 1 = epsilon`.
Restricting every term to the balanced window preserves the pointwise identity.

For

\[
F_{\mathrm{LP}}(n)=
\sum_{\substack{rp=n\\r\le u,\ p>u\text{ prime}}}\Lambda(r),
\]

and the four balanced Vaughan components `B0`, `B1`, `B2`, and `B3`, linearity gives the exact
projection-preserving decomposition

\[
C_{\mathrm{LP}}-J_{\mathrm{LP}}
=H_N(F_{\mathrm{LP}},B_0)
 +H_N(F_{\mathrm{LP}},B_1)
 -H_N(F_{\mathrm{LP}},B_2)
 +H_N(F_{\mathrm{LP}},B_3).
\]

No retained rational-arc projection term is discarded.

The semiprime parity check is also exact. If `n = q1*q2` for distinct primes
`q1,q2 > max(D0,V0)`, then on the balanced support

\[
B_0(n)=0,\qquad B_1(n)=\log n,\qquad B_2(n)=0,\qquad B_3(n)=-\log n.
\]

Thus Type II cancels the spurious Type-I contribution at a semiprime, while for a sufficiently
large prime the Type-II term vanishes and Type I supplies the von Mangoldt weight. This locates the
parity-sensitive information rather than proving the estimate that it needs.

These three verifications are independent paper-level algebraic checks. They are not new Lean
theorems and do not verify the missing analytic estimates.

## Precise Reopening Theorem

The missing term is the complete signed, fixed-center Type-II discrepancy

\[
H_N(F_{\mathrm{LP}},B_3)
=C_N(F_{\mathrm{LP}},B_3)-J_N(F_{\mathrm{LP}},B_3),
\]

where

\[
B_3(n)=\mathbf 1_{[L,U]}(n)
  (\mu_{>D_0}*\Lambda_{>V_0}*1)(n).
\]

Its convolution contains

\[
\sum_{\substack{
  r\le N^{1/3},\ p>N^{1/3}\text{ prime}\\
  d>D_0,\ m>V_0,\ k\ge1\\
  rp+dmk=N}}
\Lambda(r)\mu(d)\Lambda(m),
\]

with the original balanced support and endpoint restrictions. The balanced `k = 1` configuration is

\[
  rp+dm=N.
\]

Here `r` and `m` carry von Mangoldt weights, `p` carries a prime indicator, and `d` carries its
Moebius sign. Replacing the prime indicator by a von Mangoldt weight requires restoring the
corresponding logarithmic normalization.

Existing prime-distribution results plausibly address the Type-I progression pieces. They do not
establish this parity-sensitive, balanced Type-II correlation uniformly at each fixed even center.
A stronger level of distribution inserted into an ordinary upper sieve is not enough: the
dimension-one upper-sieve factor is approximately `2/theta`, and even the ideal `theta = 1` leaves
the factor-two cost above the present Route A allowance.

## Quantitative Requirement

The complete one-large-prime row would need

\[
C_{\mathrm{LP}}(N)-J_{\mathrm{LP}}(N)
  < 0.707\,\mathfrak S(N)N.
\]

The proposed prime-main benchmark is

\[
\log(3/2)\,\mathfrak S(N)N.
\]

The total conditional excess allowance is therefore

\[
0.707-\log(3/2)=0.3015348919\ldots
\]

in units of `mathfrak S(N)N`. This allowance covers all Type-I errors, the retained projection, prime powers,
endpoint corrections, and all Type-II companions combined. It must not be assigned to a selected
Type-II block before the Type-I main terms are evaluated.

## Why the Previous Completion Paths Stop

- The selected central long-Moebius matrix is exactly support-disjoint from the one-large-prime row
  responsible for the current deficit. Making its discrepancy zero does not repair that row.
- Direct Li-Liu switching estimates have the wrong sign for the required upper-bound improvement
  and do not cover most of the coefficient mass in the needed form.
- Lichtman's large-residue Type-II distribution theorem is a meaningful match for restricted
  progression terms, but transferring it through an ordinary upper sieve cannot beat the
  factor-two parity barrier.
- The reflected Vaughan decomposition preserves the full projection and exposes the correct
  parity-sensitive term, but no checked source supplies the required fixed-center estimate for it.
- Further finite certificates cannot prove this missing uniform analytic theorem.

## Standalone Results To Preserve

- Exact balanced large-divisor and Fourier decompositions.
- Same-integer small-cofactor cancellation `h_u(pr) = -Lambda(r)`.
- Exact support separation between the selected central block and the one-large-prime row.
- Exact short-Moebius and affine-solution parametrizations.
- Exact marked-reconstruction identities and their support obstruction.
- The periodic-main certificate and independently checked finite algebra.
- Numerical diagnostics, explicitly labelled as computational evidence only.
- Factorability, sieve-parity, generic-energy, fixed-center, and prime-companion obstruction reports.
- The final Vaughan identity, projection decomposition, and semiprime parity check.

Exploratory analytic savings retain their actual review status. They are not established theorems
unless separately proved and independently checked.

## Archival Policy

Route A is closed as a proof-completion campaign and marked **analytically stalled**. Route B
remains **retired**. The historical Q0 certificate is preserved as a computational artifact, not as
evidence of an unconditional Goldbach proof.

No further Lean generation, certificate campaign, post-certificate bridge build, or unrelated
analytic branch is part of the current proof-completion program. Route A may be reopened only after
an independently reviewed theorem controls the complete signed fixed-center Type-II contribution
with sufficient quantitative margin.
