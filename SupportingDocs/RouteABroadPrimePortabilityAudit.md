# Route A broad-convolution portability audit

## Purpose

The corrected Route A endpoint is the complete normalized prime-pair convolution at the exact
integer `N`. This audit records which parts of the previous fixed-bank/Q0 development can be used
for that endpoint. It is a dependency firewall: similarity of notation or proof shape is not an
acceptable bridge between observables.

## Decisive source distinction

The old analytic chain inserts the fixed arithmetic support before taking Fourier transforms or
forming the major/minor decomposition:

```text
MajorArcStep10RLSmoothIntegral.aTerm X n
  = BG_Bank.wX X n * BG_Bank.Lambda n.
```

`BG_Bank.wX X n` is supported on the fixed-width interval around `X/2`. Therefore
`RLambda_smooth`, its Q0 minor residual, the Type-I terms, and the generated zero/nonzero
certificates all concern the banked coefficient sequence. The complete convolution instead sums
the prime coefficient over every `2 <= n <= N - 2`. The two sequences are not definitionally equal,
and the fixed-bank obstruction proves that they cannot be universally interchangeable.

## Portability matrix

| Component | Status | Reason / required bridge |
| --- | --- | --- |
| Full-convolution positivity iff `GoldbachRep` | Reusable and complete | This is the corrected combinatorial endpoint. |
| Finite base up to `X0` | Reusable and complete | Independent of the large-number observable. |
| True Ramanujan/Euler-product singular series | Reusable | It supplies the genuine Hardy--Littlewood main model for even integers. Do not substitute the numeric lower-bound surrogate for the true constant. |
| Hardy--Littlewood main positivity | Reusable and complete | `RouteABroadPrimeMainError` proves positivity for even `N >= 2`. |
| Exact broad circle identity and major/minor split | Reusable/new and complete | It acts on the circle variable and is definitionally tied to the complete convolution. |
| Complete von Mangoldt Steps 2--5 | Reused on a balanced growing interval | `RouteABalancedBMORBridge` applies the existing BMOR theorem to `[L,N-L]` once `L-1 >= 10^6`, and derives the corresponding quadratic bound. This does not cover the low prefix of `[2,N-2]`; instead positivity of the restricted exact-center convolution is itself sufficient for Goldbach. |
| Old Step 19 prime-power disposal | Replaced | Its interval-cardinality estimate is order `N log N`. The new final-convolution argument has checked order `sqrt(N) log(N)^2`. |
| Exact von Mangoldt-to-prime transfer | Reusable/new and complete | The three contamination terms and the refined bound `(5/2)(sqrt(N)+1)log(N)^2` are checked without generated certificates. |
| Finite DFT and pointwise projector inequality | Exploratory only | Algebraically correct, but the tested global complement norm is far too large for the current pointwise budget. |
| Abstract SSU operator contracts | Reusable after new extraction | The operator theorems are generic, but a new packet/coefficient instance must be built from the broad sequence. |
| Old Q0 Fourier decomposition | Proof pattern only | Its `aTerm` already contains `wX`; it does not decompose the broad coefficients. |
| Old Q0 Type-I bounds | Not portable as estimates | Their masses and constants were proved for the fixed-width coefficient sequence. |
| Old Q0 zero-mode bound | Not portable as an estimate | It is an exact statement about the banked residual and its normalization. |
| Old Q0 nonzero/SSU bound | Not portable as an estimate | The concrete SSU instance is calibrated to banked packets. Only the generic SSU theorem can be reused. |
| `ProjectedTrueInput` and `ProjectedTrueFromCorrIntegral` | Not a broad endpoint | They repair the singular-series constant while still returning `R_bank`, `conv_ref`, or `conv_full`, all of which retain the arithmetic bank. |
| BG bridge, kernel tail, and bank positivity | Not portable | They are explicitly theorems about `BG_Bank.wX` and the banked convolution. |
| Completed legacy X0 certificate | Diagnostic/regression only | It checks a finite banked identity and can expose cancellation structure; it cannot prove a broad uniform estimate. |

## New checked integration boundary

The production broad route now has fourteen layers:

1. `RouteABroadPrimeConvolution.lean` defines the exact endpoint and proves positivity equivalent to
   a Goldbach representation.
2. `RouteABroadPrimeCircle.lean` proves that endpoint is exactly the relevant Fourier coefficient
   of the complete prime exponential sum.
3. `RouteABroadPrimeCircleProgram.lean` splits the circle variable and packages the only three
   analytic obligations: major approximation, minor norm, and strict positive budget.
4. `RouteAFiniteWeightCircle.lean` and `RouteAFiniteWeightCircleSplit.lean` factor the exact Fourier
   identity and major/minor split over an arbitrary finite real weight.
5. `RouteABroadPrimeVonMangoldt.lean`, `RouteABroadPrimePowerBound.lean`, and
   `RouteABroadPrimePowerCount.lean` transfer to the complete von Mangoldt sum and discharge the
   higher-prime-power correction uniformly.
6. `RouteABroadVonMangoldtClosure.lean` is the reduced complete-support endpoint: only a von
   Mangoldt major estimate, minor estimate, and their strict numerical budget remain.
7. `RouteABalancedBMORPrototype.lean` defines the symmetric growing support `[L,N-L]`, proves that
   positivity still gives an exact Goldbach representation at `N`, and inherits the checked
   prime-power allowance.
8. `RouteABalancedBMORBridge.lean` identifies the balanced circle sum with the existing real BMOR
   sum and proves the linear and quadratic pointwise major-arc approximation bounds.
9. `RouteABalancedQ0CircleSplit.lean` gives the exact finite-`Q0` major/minor split, extracts the
   major integral into reduced `(q,a)` arcs, and exposes a direct finite-base closure certificate.
   It is retained as an exact reference surface, not the production analytic split, because `[0,1]`
   cuts the principal arc at the circle seam.
10. `RouteABalancedQ0SeamSafeSplit.lean` moves the fundamental interval without changing the exact
    Fourier coefficient, keeps the full principal arc contiguous, and repeats the exact split and
    reduced-arc extraction.
11. `RouteABalancedFiniteCutoffCircle.lean` defines the exact low-denominator major contribution
    through an arbitrary `Q`, its exact algebraic remainder, and the direct finite-base closure
    certificate for that surface.
12. `RouteABalancedFiniteCutoffMajorApprox.lean` integrates the checked quadratic BMOR estimate over
    every reduced arc through `Q`, giving an explicit finite-cutoff major-model error.
13. `RouteABalancedFiniteCutoffModel.lean` proves that the model is exactly the real signed sum
    `sum_{q <= Q} muSq(q) * c_q(N) / phi(q)^2 * K_q(L,N)`, where every geometric kernel mass `K_q`
    is nonnegative. It also proves that the model integral has zero imaginary part.
14. `RouteABalancedFiniteCutoffRemainder.lean` identifies the algebraic remainder with an explicit
    complementary integral, and `RouteABalancedFiniteCutoffClosure.lean` packages the only two
    theorem-facing analytic obligations left: a norm bound for that remainder and a strict budget
    against the explicit finite-cutoff main.

The final theorem in layer 3 combines any solution of those obligations with the existing finite
base. This is a direct Route A closure theorem, not another proxy certificate.

The broad circle modules reprove the small orthogonality, circle-parameterization, and indicator
split facts they need from low-level Mathlib/Step 7 imports. They do not depend on the old banked
Step 9/16/17 chain.

## Remaining analytic work

1. Prove a balanced von Mangoldt norm bound for
   `balancedVonMangoldtAfterMajorUpToRemainder L N Q 1`. The exact complementary-integral identity
   is complete. The current Q0 SSU tower is not itself such a theorem: its concrete coefficients
   are banked, and its abstract layer uses uninstantiated oscillatory/overlap assumptions and a
   placeholder minor-arc set.
2. Select the cutoff jointly with that theorem. The corrected diagnostic does not pick one value:
   `Q = 2` gives the largest pre-remainder reserve, while roughly `Q = 8..10` captures more rational
   peaks. Full `Q0` accumulation is definitively unusable.
3. Resolve the threshold gap caused by the published BMOR range. With `L - 1 >= 10^6`, the balanced
   interval becomes useful only near `N > 2L`, beyond the current one-million finite base.
4. Prove, uniformly beyond that threshold, that the explicit finite-cutoff main exceeds the BMOR
   major error, the new remainder error, and `(5/2)(sqrt(N)+1)log(N)^2`. This is exactly the
   `BalancedFiniteCutoffClosureCertificate.strict_budget` field.

## Scale and edge cautions

The raw broad main has size approximately `sigma(N) N`; after dividing by `log(N)^2`, it has size
approximately `N / log(N)^2`. The exact circle program works at the raw scale, avoiding the global
output-block `l2` loss observed in the DFT experiment. Any proposed bound must nevertheless be
uniform at each even `N`, not merely on average over outputs.

## No-silent-substitution rules

- No theorem mentioning `BG_Bank.wX`, `R_bank`, `conv_ref`, or the repository's banked `conv_full`
  may discharge a broad-program field without a stated equality or norm comparison to the complete
  convolution.
- A positive window sum cannot replace positivity at the exact center.
- A majority-good-grid theorem cannot replace a pointwise theorem without a separate coverage or
  thickness result.
- A finite `X0` equality cannot replace a scale-uniform estimate.
- No bulk certificate should start until the broad numerical budget has positive margin.
- The balanced interval must grow with `N`; replacing it by another fixed-width bank would recreate
  the proved factorial obstruction.
- The exact remaining theorem and its acceptance tests are fixed in
  `SupportingDocs/RouteABalancedRemainderTheoremSpec.md`.
