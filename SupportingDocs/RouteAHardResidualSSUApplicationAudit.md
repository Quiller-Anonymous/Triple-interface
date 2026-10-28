# Route A hard-residual SSU application audit

Date: 2026-10-27

## Decision

The short Type-I and retained-arc feasibility checks now leave one quantitative gate:

```text
Re H_N(hard, Lambda; retained^c) >= -0.35 N,

hard = Lambda - mu_<=u * log,
u = floor(N^(1/3)).
```

The repository does not currently prove this estimate.  In particular, the standalone SSU
library does not yet contain a checked application from this arithmetic coefficient to a
fixed-center, one-sided bound.  Further Route A closure work should stop at this gate unless a
paper proof supplies that application with explicit constants.

## Independent specialist review

A subsequent independent paper review supports the two ancillary estimates needed by this
reduction, but does not supply the hard-residual theorem:

* it reconstructs the active-main argument with a conservative pointwise profile floor above
  `0.9102`, hence confirms the required aggregate bound `M_A > 0.9 N` without relying on the
  earlier `0.96866` intermediate value;
* it reconstructs the unmodulated hard-prefix bound `0.03 N`, improves the parity-prefix bound
  from `0.09 N` to `0.06 N`, and confirms the retained-arc allowance
  `0.4847091 N < 0.49 N` including the wrapped seam;
* it confirms that the active-main Euler product is the full Goldbach singular series, so the
  retired fixed-cutoff averaging obstruction does not transfer to this signed decomposition;
* it finds no published dispersion, spectral, or bilinear theorem whose hypotheses and
  fixed-center conclusion imply the remaining `0.35 N` estimate.

The review uses the uniform half-moment estimate

```text
sum_a |h_N(a)| sqrt(a) <= exp(12 sqrt(log N) + 8)
```

and splits the kernel at `u^(1/10)`.  This is a more conservative independently checkable route
than the sharper local budget in `RouteAActiveMainKernelAudit.md`.  Either route still requires
formalization before entering the Lean closure chain.

## Exact coefficient surface

`RouteABalancedVaughanFixedCenter.lean` now proves

```text
vaughanHardArithmetic u v = vonMangoldt - vaughanTypeIArithmetic u
```

and therefore proves that the combined hard coefficient is independent of the auxiliary cutoff
`v`.  The same module exposes its exact internal split

```text
hard
  = Lambda_<=v
    - mu_<=u * zeta * Lambda_<=v
    + mu_>u * zeta * Lambda_>v
```

on the balanced support and under the complementary frequency mask.  Thus `v` may be chosen to
organize a proof, but changing it cannot change the theorem that must ultimately be established.

The long Type-II coefficient has the checked nested divisor formula

```text
T_{u,v}(n)
  = sum_{x*k=n}
      (sum_{d | x, d>u} mu(d))
      * 1_{k>v} Lambda(k).
```

Equivalently, after writing `x=d*m`, its raw variables are

```text
sum_{d*m*k=n, d>u, k>v} mu(d) Lambda(k).
```

This is the correct coefficient to dyadically decompose.  No legacy Q0 Vaughan predicate is
needed to define it.

The specialist review identifies a simpler primary surface for the *combined* hard coefficient:

```text
hard(n) = sum_{d*m=n, d>u} mu(d) log(m).
```

`RouteABalancedVaughanFixedCenter.lean` now checks this as
`vaughanHardArithmetic_eq_muLarge_mul_log` and `vaughanHardArithmetic_apply`.  This identity
removes `v` entirely.  Estimating the isolated long Type-II component is insufficient unless its
two companion components are recombined with it.

## The exact cross-Toeplitz form

For a measurable retained set `R`, define its complementary Fourier kernel

```text
K_R(t) = integral_[0,1] 1_{R^c}(alpha) e(t alpha) d alpha.
```

If `S(b)` is the balanced von Mangoldt weight and `Srev(b') = S(N-b')`, then the long component of
the hard residual is exactly

```text
H_N(T_{u,v}, S; R^c)
  = sum_{d,m,k,b'}
      mu(d) Lambda(k) Srev(b') K_R(d*m*k - b'),
```

with all four variables restricted by the balanced support and by `d>u`, `k>v`.

This is a **cross** Toeplitz form: one side is a product coefficient and the other is the reflected
prime sequence.  It is not the quadratic form of one arbitrary coefficient array.  A polarization
argument can embed a cross form into quadratic forms, but an absolute-value energy bound obtained
that way pays the full energies of both sides and does not by itself give the required signed
fixed-center saving.

## What the proved SSU modules supply

The relevant repository facts are:

1. `SSU/Engines/BGTypeIIRankOne.lean` packages a dyadic rank-one array and proves deterministic
   product regrouping.  Its module documentation explicitly says that it contains no analytic
   bound.
2. `SSU/Engines/TypeIIToeplitz.lean` has both global and fixed-array Step 3/4 interfaces.  The
   fixed-array form is useful only after an actual arithmetic estimate constructs its witness.
3. The proved geometry and Montgomery--Vaughan constructors in the Type-II large-sieve tree bound
   coefficient energy.  Their theorem types do not use the Mobius signs in the extracted hard
   coefficient and do not mention the reflected prime factor or the fixed center `N`.
4. `SSU/Engines/TypeIIToeplitzGlobalNoSavingAudit.lean` proves that every global all-array
   `Step34ProdSum` witness must absorb at least the tube cardinality at frequency zero.  Its visible
   `sqrt(H/X)` factor therefore cannot be counted as a Goldbach saving without a restricted
   arithmetic theorem.
5. No module outside the balanced Vaughan development imports
   `RouteABalancedVaughanFixedCenter` and maps `balancedVaughanTypeIIWeight` or
   `balancedVaughanHardWeight` into an SSU coefficient family.
6. The legacy Q0 packet route cannot fill this gap: its Vaughan admissibility predicates are
   vacuous on the inspected surface, and its Goldbach packet ledger uses assumptions that do not
   identify the exact balanced hard coefficient.

These facts do not invalidate the standalone SSU contracts.  They show that their present
Goldbach application is missing the arithmetic theorem that would make the contracts useful here.

## Why generic energy control is insufficient

The target is one-sided and pointwise in the center.  A coefficient-blind Cauchy--Schwarz or
polarization estimate reduces it to global `l2` energies.  The prime factor alone has energy on
the scale `N log N`, while the hard coefficient is not known to have energy small enough to absorb
that logarithm.  More importantly, such a bound discards the oscillatory sign in
`K_R(d*m*k-b')`; that sign is precisely the information needed at a specified even center.

This is the binary-Goldbach difficulty in the present coordinates.  A standard large-sieve bound
for an arbitrary rank-one array may prove cancellation in an oscillatory sum, but it does not
automatically prove cancellation in the cross correlation with `Srev` after every dyadic block,
shell count, coefficient norm, and endpoint restriction has been restored.

## Finite diagnostic evidence

The independent FFT diagnostic

```text
scripts/experiments/route_a_retained_margin_feasibility.cpp
```

computes the exact finite convolution and the cutoff-two retained integral for moderate centers.
With the actual lower cutoff `L=1000001` and `u=floor(N^(1/3))`, powers of two give:

| `N` | `Re H(hard,S;R^c)/N` | `Re J(hard,S;R)/N` | full hard `/N` |
| ---: | ---: | ---: | ---: |
| `2^21` | `+0.0118042` | `-0.0003035` | `+0.0115007` |
| `2^22` | `+0.1137834` | `-0.1031912` | `+0.0105922` |
| `2^23` | `+0.2312932` | `+0.0165746` | `+0.2478677` |

All tested complementary hard values are positive and therefore satisfy the desired lower bound
at those finite centers.  This is useful evidence that the target is not numerically absurd.  It
is not evidence of a uniform theorem: the diagnostic does not cover the enormous analytic
threshold, and positivity at selected centers cannot replace the fixed-center estimate.

## The worked application a specialist must supply

A valid resumption theorem may use a broader retained major-arc set, but it must imply the existing
gate after exact recombination.  One acceptable paper-level target is:

```text
For every even N >= exp(exp 100), with u=floor(N^(1/3)),
there exist v and a measurable retained major-arc set R containing the q=1,2 arcs such that

  Re H_N(Lambda_<=v, S; R^c)
  + Re H_N(-mu_<=u*zeta*Lambda_<=v, S; R^c)
  + Re H_N(mu_>u*zeta*Lambda_>v, S; R^c)
  >= -0.35 N.
```

For the long term, the proof must state a restricted cross-form estimate for the actual dyadic
coefficients.  A useful block theorem would have the schematic form

```text
abs (sum_{d in D, m in M, k in K, b' in B}
       mu(d) Lambda(k) Srev(b') K_R(d*m*k-b'))
  <= Saving(D,M,K,B,N),
```

followed by an explicit shell summation whose total, together with the two short components, is at
most `0.35 N`.  Every coefficient norm and logarithmic factor must be present.  The theorem must
not take the desired cross-cancellation as an input record.

Equivalently, and preferably as the primary target, prove the combined form

```text
Re sum_{d>u, L<=d*m<=N-L} sum_{L<=b<=N-L}
     mu(d) log(m) Lambda(N-b) K_R(d*m-b)
  >= -0.35 N,
```

where for the wrapped `q=1,2` retained set

```text
K_R(0) = 1 - 3/N,
K_R(j) = -sin(2*pi*j/N)/(pi*j) - (-1)^j*sin(pi*j/N)/(pi*j)  (j != 0).
```

This theorem is consistent with the expected Hardy--Littlewood scale and with the finite
diagnostics, but no proof or contradictory averaging obstruction is presently known.

## Two plausible research directions

1. **Broaden the retained major arcs.**  Exact small denominators such as `q=3` have structured
   arithmetic contributions and should not be expected to disappear under a generic minor-arc
   estimate.  Retain all `q<=Q`, evaluate the hard major-arc cross term using progression
   information, and apply a Type-II estimate only on the genuine minor arcs.
2. **Prove a restricted cross-SSU theorem.**  Extend the rank-one/product machinery to the
   rectangular cross form above and exploit the actual Mobius and von Mangoldt coefficients, not
   only their energies.  The output must be a fixed-center scalar bound, not merely a packet norm.

The first direction is closer to conventional circle-method organization.  The second is the
possible genuinely new SSU contribution.  Neither result is presently in the repository.

## Stopping rule

Route A should be considered reopened only if a complete paper calculation produces a bound below
`0.35 N` on this exact coefficient surface.  If the strongest available theorem gives only a
generic energy bound, loses the fixed center, or requires the cross-cancellation as a hypothesis,
the balanced fixed-center route remains a useful reduction but not a path to an unconditional
Goldbach proof.
