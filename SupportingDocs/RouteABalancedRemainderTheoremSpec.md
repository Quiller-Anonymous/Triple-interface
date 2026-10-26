# Corrected Route A remainder theorem specification

## Purpose

This document fixes the remaining mathematical target after removal of the impossible fixed-bank
positive-mean route. It is intentionally tied to the exact Lean objects. A theorem about the old
`BG_Bank.wX` coefficients, a window average, or the legacy Q0 certificate does not satisfy this
specification.

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
6. A finite base and `BalancedFiniteCutoffClosureCertificate` prove `GoldbachRep N` for every even
   `N >= 4`.

The axiom audit shows that items 1, 3, 5, and the closure plumbing use only Lean's standard logical
axioms. The major approximation and final closure inherit the already-declared analytic input
`ExplicitPNTinAP_BMOR.psi_bound`; no legacy certificate axiom is hidden in the chain.

## Canonical first cutoff

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

These values use numerical quadrature and are feasibility evidence only. They suggest testing a
remainder target of `N/10` from a threshold near 3.5 million, with a larger threshold available if
the provable constant is worse.

## Exact missing theorem

The central object is

```text
balancedVonMangoldtAfterMajorUpToRemainder L N 2 1
```

and Lean has already identified it with

```text
balancedFiniteCutoffRemainderIntegral L N 2 1.
```

A concrete candidate theorem is therefore:

```text
theorem balanced_q2_remainder_le_tenth
    {N : Nat} (hN : 3_500_000 <= N) (hEven : Even N) :
    norm (balancedVonMangoldtAfterMajorUpToRemainder 1_000_001 N 2 1)
      <= (1 / 10 : Real) * N
```

The constant and threshold may change. What must not change is the observable, the exact center, or
the uniform quantifier over even `N`.

The second missing quantitative theorem is the corresponding strict budget:

```text
balancedBMORIntegratedMajorError 1_000_001 N 2 1
  + remainderError N
  + (5/2) * (sqrt N + 1) * log(N)^2
  < balancedFiniteCutoffMain 1_000_001 N 2 1.
```

Lean exposes these facts as `BalancedCutoffTwoRemainderTarget` and
`BalancedCutoffTwoBudgetTarget`. Once they are proved and the finite base reaches the selected
threshold, `goldbach_of_finiteBase_and_balancedCutoffTwoTargets` finishes Route A without another
generated analytic certificate.

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

## Plausible proof program

1. Work directly with the balanced complete von Mangoldt exponential sum.
2. Use a genuine Vaughan or related identity whose equality to that sum is proved, not assumed.
3. Separate Type I and Type II ranges on the exact seam-safe complement of the `q <= 2` arcs.
4. Prove the needed bilinear cancellation with explicit constants and uniformity in `N`.
5. Integrate with the exact phase `e(-N alpha)` instead of replacing the scalar by a global
   unnormalized `L2` norm.
6. Re-run the ledger with the proved constant and choose the threshold only after the strict budget
   has positive certified margin.

The alternative is to increase `Q`, but that should be done only if the remainder theorem improves
more than the BMOR major error and signed-main reserve deteriorate. The corrected ledger currently
leaves `Q = 2` versus roughly `Q = 8..10` as an empirical tradeoff, not a settled choice.

## Acceptance and rejection tests

A proposed bridge is acceptable only if it:

- bounds the exact `balancedVonMangoldtAfterMajorUpToRemainder` object or proves an exact equality to
  the object it bounds;
- is uniform for every even `N` beyond an explicit threshold;
- retains the exact-center phase;
- supplies constants that pass the strict budget; and
- has an axiom audit listing only deliberately accepted analytic inputs.

Reject any proposal that:

- mentions `BG_Bank.wX` without an exact broad-coefficient transport theorem;
- proves only an average over centers or a density-one result;
- substitutes a positive nearby convolution for positivity at `N`;
- uses the completed `X0` certificate as a scale-uniform estimate; or
- hides the remainder estimate inside a new certificate structure or axiom.

## Finite-base consequence

The present finite base reaches one million, whereas the BMOR adapter requires
`L - 1 >= 1,000,000` and the current diagnostic margin becomes useful only above roughly 3.2
million. Once the analytic threshold is fixed, either the finite base must be extended to it or a
separate intermediate-range argument must cover the gap. This is finite verification, not the
remaining analytic obstacle, and it should not begin until the remainder constant determines the
actual threshold.
