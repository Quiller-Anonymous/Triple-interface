# Superseded Route A two-sided remainder specification

> **Retired on 2026-10-26.** This document records a historical proposal. The norm-and-budget
> target below is mathematically inconsistent with fixed-modulus PNT-in-progressions averages and
> must not be used as an active Route A specification. See
> `SupportingDocs/RouteAConsistencyAndSSUApplicationAudit.md`. The replacement bounded research
> surface is `SupportingDocs/RouteABalancedVaughanFixedCenterPlan.md`.

## Purpose

This document formerly proposed the next mathematical target after removal of the impossible
fixed-bank positive-mean route. It remains useful for identifying exact Lean objects and for
auditing why the proposal failed; it no longer specifies work to be completed.

## Checked reduction

For the balanced von Mangoldt weight on `[L,N-L]`, Lean now checks all of the following:

1. The exact-center convolution is a circle Fourier coefficient.
2. Removing higher prime powers costs at most
   `(5/2) * (sqrt N + 1) * log(N)^2`.
3. The seam-safe circle integral splits exactly into rational arcs through an arbitrary finite
   cutoff `Q` and an explicit remainder.
4. The published BMOR estimate integrates over those rational arcs with explicit error
   `balancedBMORIntegratedMajorError L N Q 1`.
5. The finite-cutoff model is exactly the real sum

   ```text
   sum_{1 <= q <= Q} muSq(q) * c_q(N) / phi(q)^2 * K_q(L,N),
   ```

   where `K_q(L,N) = balancedTruncatedGeometricKernelMass L N q 1` is nonnegative.
6. Conditional on `BalancedFiniteCutoffClosureCertificate`, a finite base proves `GoldbachRep N`
   for every even `N >= 4`. The implication is valid, but its two analytic fields cannot be
   simultaneously populated at cutoff two.

The axiom audit shows that items 1, 3, 5, and the closure plumbing use only Lean's standard logical
axioms. The major approximation and final closure inherit the already-declared analytic input
`ExplicitPNTinAP_BMOR.psi_bound`; no legacy certificate axiom is hidden in the chain.

## Rejected first cutoff proposal

The first serious target is `Q = 2`, not full `Q0`. For every even `N`, Lean proves

```text
balancedFiniteCutoffMain L N 2 1 = K_1(L,N) + K_2(L,N) >= 0.
```

Both arithmetic coefficients are exactly `+1`. Thus cutoff two removes all signed arithmetic
uncertainty from the main term. Any failure of the final lower bound is localized to the explicit
remainder or to an inadequate quantitative kernel lower bound.

With `L = 1,000,001`, the current nonrigorous ledger gives the following reserve after the checked
BMOR major-error formula and the checked prime-power allowance, but before a remainder allowance:

| `N` | reserve divided by `N` |
| ---: | ---: |
| 3,200,000 | 0.04575 |
| 3,400,000 | 0.11704 |
| 3,500,000 | 0.15065 |
| 4,000,000 | 0.29909 |
| 5,000,000 | 0.51698 |

These values use numerical quadrature and were feasibility evidence only. Subsequent
arithmetic-progression averaging shows that neither the two-sided target nor even the proposed
one-sided `Re remainder >= -N/10` target can hold beyond any threshold.

## Rejected missing theorem

The central object is

```text
balancedVonMangoldtAfterMajorUpToRemainder L N 2 1
```

and Lean has already identified it with

```text
balancedFiniteCutoffRemainderIntegral L N 2 1.
```

The historical candidate theorem was:

```text
theorem balanced_q2_remainder_le_tenth
    {N : Nat} (hN : 3_500_000 <= N) (hEven : Even N) :
    norm (balancedVonMangoldtAfterMajorUpToRemainder 1_000_001 N 2 1)
      <= (1 / 10 : Real) * N
```

No constant or threshold can make this two-sided norm target compatible with the associated strict
budget. The exact observable and center remain relevant, but a continuation would need a different,
one-sided arithmetic theorem.

The second missing quantitative theorem is the corresponding strict budget:

```text
balancedBMORIntegratedMajorError 1_000_001 N 2 1
  + remainderError N
  + (5/2) * (sqrt N + 1) * log(N)^2
  < balancedFiniteCutoffMain 1_000_001 N 2 1.
```

Lean retains these facts as `BalancedCutoffTwoRemainderTarget` and
`BalancedCutoffTwoBudgetTarget` for historical consistency auditing. The conditional wrapper
`goldbach_of_finiteBase_and_balancedCutoffTwoTargets` remains logically valid, but its hypotheses
are not an attainable Route A target.

## Mathematical difficulty

This remainder theorem is not routine bookkeeping. A sufficiently strong pointwise, uniform bound
for this binary-prime circle remainder is the core unresolved cancellation problem. Standard
Parseval or triangle-inequality estimates lose too much: they control an energy of order roughly
`N log N` rather than a scalar error strictly below the order-`N` main. The repository's old
Step-25 theorem only reduces a banked minor integral to a supplied exponential-sum cap, and its
certificate file postulates that cap. The Q0 SSU modules likewise do not instantiate a theorem for
the complete balanced von Mangoldt coefficients.

Accordingly, a proof of the displayed uniform remainder bound would be substantive new number
theory, not merely completion of a Lean wrapper. The formal development can expose, audit, and
combine such a theorem, but it must not silently rename a banked estimate or an average-result as
the needed pointwise statement.

## Historical proof program and stopping result

The useful parts of the proposed program survive only as requirements for a future one-sided
application: work with the complete balanced von Mangoldt sum, prove an exact Vaughan-like
identity, retain the phase `e(-N alpha)`, and restore every coefficient norm and constant. The
bounded SSU application audit found that the present Q0 interfaces do not supply the first exact
extraction step and that the global all-array SSU endpoint cannot itself beat the trivial
per-frequency bound. Under the adopted stopping rule, no further closure machinery should be built
until a restricted arithmetic application shows an explicit nontrivial saving.

Increasing to another fixed `Q` does not repair the same two-sided strategy: fixed-modulus
progression averages make the convolution-to-`N` ratio unbounded across suitable fixed moduli,
whereas a fixed-cutoff model remains `O_Q(N)`.

## Acceptance and rejection tests

A future replacement bridge is acceptable only if it:

- starts from the exact `balancedVonMangoldtAfterMajorUpToRemainder` object or proves an exact
  equality to the object it estimates;
- is uniform for every even `N` beyond an explicit threshold;
- retains the exact-center phase and the sign of helpful positive contributions;
- supplies a one-sided estimate whose fully restored constants give a strict positive final lower
  bound; and
- has an axiom audit listing only deliberately accepted analytic inputs.

Reject any proposal that:

- mentions `BG_Bank.wX` without an exact broad-coefficient transport theorem;
- proves only an average over centers or a density-one result;
- substitutes a positive nearby convolution for positivity at `N`;
- uses the completed `X0` certificate as a scale-uniform estimate; or
- hides the remainder estimate inside a new certificate structure or axiom;
- cites the global all-array SSU square-root factor without restoring its effective constant; or
- yields only the trivial bound after coefficient norms and shell sums are restored.

## Finite-base consequence

The present finite base reaches one million, whereas the BMOR adapter requires
`L - 1 >= 1,000,000` and the current diagnostic margin becomes useful only above roughly 3.2
million. Once the analytic threshold is fixed, either the finite base must be extended to it or a
separate intermediate-range argument must cover the gap. This is finite verification, not the
remaining analytic obstacle, and it should not begin until the remainder constant determines the
actual threshold.
