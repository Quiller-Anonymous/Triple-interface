# Balanced Vaughan fixed-center program

Date: 2026-10-27

## Status

This is a bounded research program, not a declaration that Route A has reopened as a
proof-completion project. It replaces the failed two-sided finite-cutoff norm target with an exact
signed decomposition that preserves one copy of the balanced von Mangoldt sum.

The checked algebra now reaches the correct analytic frontier. It does not yet supply the
one-sided estimate needed for Goldbach.

## Checked algebraic surface

`RouteABalancedVaughanIdentity.lean` defines honest cutoffs of arithmetic functions and proves

```text
Lambda
  = Lambda_<=v
    + mu_<=u * log
    - mu_<=u * zeta * Lambda_<=v
    + mu_>u * zeta * Lambda_>v.
```

Here multiplication is Dirichlet convolution and `zeta` is the constant-one arithmetic function.
The proof uses Mathlib's checked identities `mu * zeta = 1` and `zeta * Lambda = log`; it adds no
analytic axiom.

`RouteAFiniteWeightBilinearCircle.lean` proves, for arbitrary finite real weights `f` and `g`,

```text
H_N(f,g; complement s)
  = C_N(f,g) - J_N(f,g; s),
```

where `C_N` is the exact additive convolution at the specified center, `J_N` is the integral over
the retained measurable frequency set, and `H_N` is the complementary masked integral. This is the
formal mask-removal identity. It neither smooths the mask nor averages over the center.

`RouteABalancedVaughanFixedCenter.lean` groups the exact Vaughan terms as

```text
A    = mu_<=u * log
hard = Lambda_<=v - mu_<=u * zeta * Lambda_<=v
                    + mu_>u * zeta * Lambda_>v
S    = A + hard.
```

After restriction to the balanced support, Lean proves both

```text
C_N(S,S) = C_N(A,S) + C_N(hard,S)
```

and, for every measurable retained set,

```text
H_N(S,S) = H_N(A,S) + H_N(hard,S).
```

This is the central organizational correction: do not expand both copies of `S` before applying
prime-distribution estimates.

The same module now checks both finite reindexings of the full Type-I correlation:

```text
C_N(A,S)
  = sum_{d <= u} mu(d)
      sum_{m: d*m in [L,N-L]} log(m) Lambda(N-d*m)
  = sum_{d <= u} mu(d)
      sum_{p in [L,N-L], p = N (mod d)} Lambda(p) log((N-p)/d).
```

The second equality is a genuine finite bijection, including the support endpoints; it is not an
informal change of variables. `BalancedVaughanTypeIProgressionEstimate` is now stated directly on
this checked residue sum, and the interface transfers it back to the convolution.

The module also names the canonical discrete coprime main

```text
sum_{d <= u, (d,N)=1} mu(d)/phi(d)
  * sum_{p in [L,N-L]} log((N-p)/d)
```

and defines `balancedVaughanTypeIProgressionError` as the exact difference from that main. This
residual is now partitioned exactly as

```text
progressionError = coprimeProgressionError + noncoprimeProgressionContribution.
```

The first term is the reduced-residue object for maximal Bombieri--Vinogradov and partial
summation. The second is a separate nonreduced-residue obligation, where only prime-power support
can contribute. Lean now checks this support statement: a nonzero von Mangoldt term in a
noncoprime progression is a prime power sharing a nontrivial factor with the modulus. The interface
proves that independent bounds for these two terms combine into the aggregate progression
estimate; neither may be silently discarded.

The existing interval summation-by-parts library is now connected to each named coprime-modulus
error. Lean checks both the exact identity and the bound by three explicit costs:

```text
|E_d(N-L)| |g_d(N-L)|
  + |E_d(L-1)| |g_d(L-1)|
  + sum_{L-1 <= n < N-L} |E_d(n)| |g_d(n+1)-g_d(n)|,
```

where `E_d(n) = psi(n; d, N) - n/phi(d)` and `g_d(n) = log((N-n)/d)`. Thus discrete partial
summation itself is no longer missing. The unresolved step is a quantitative, effective maximal
estimate for the sum of these costs over `d <= u`.

A later support audit found that this first comparison main is broader than the actual residue
sum: it includes terms with `d > N - p`, where no positive congruence solution can occur and where
the specialist's logarithmic conductor weight is not meant to apply.
`RouteABalancedVaughanActiveMain.lean` now repairs that mismatch without discarding the old
interface. Lean checks:

```text
old discrete main = active discrete main + inactive main tail,
prime residue sum = active main + active coprime error + noncoprime contribution,
old coprime error = active coprime error - inactive main tail.
```

It also proves partial summation with the exact modulus-dependent upper endpoint
`N - max L d` and a finite Fubini identity that sums first over `p` and then over precisely the
active moduli `d <= N - p`. This active pointwise formula is the correct surface for the proposed
primitive-conductor weight.

`RouteABalancedVaughanSignedConductor.lean` now records a narrower alternative. Lean checks the
exact sum of the partial-summation errors with the outer Mobius signs still present and proves that
any bound for this signed aggregate populates the existing coprime-progression interface. This
avoids making the unrestricted maximal Bombieri--Vinogradov norm the only possible Type-I input.
The first elementary signed-conductor gate is now complete. The modules
`RouteASignedMoebiusPartialSums.lean`, `RouteASignedMoebiusTotientKernel.lean`, and
`RouteASignedMoebiusEulerProduct.lean` prove in Lean

```text
|sum_{k <= X, (k,m)=1} mu(k) / phi(k)| <= 6 * m / phi(m).
```

The proof factors the coprime Mobius/totient weight as a signed convolution, proves its exact
prime-power values and multiplicativity, enlarges a finite prefix to the divisors of `X!`, and
bounds the resulting finite Euler product.

The next algebraic layer is also checked for the earlier uniform-endpoint signed error.
`RouteADirichletCharacterExpansion.lean` proves the exact finite character expansion of the
progression deviation and separates each induced character from its canonical primitive character
with an explicit correction term.
`RouteABalancedVaughanPrimitiveConductor.lean` partitions all character occurrences by canonical
primitive-character key, rewrites the actual signed Type-I partial-summation expression on that
partition, and proves that each fiber is

```text
primitive psi * signed fiber weight - induced-character correction.
```

Finally, `RouteABalancedVaughanConductorWeight.lean` proves the arithmetic estimate required for
the proposed fiber weight. It reindexes conductor lifts as `d = r*k`, applies the proved
constant-six prefix estimate through a checked finite Abel inequality, and obtains

```text
|W_r(t)| <= 6 * (r*N) / (phi(r*N) * phi(r))
  * max(0, log((N-t)/r)).
```

These modules add no project analytic axiom. The conductor-weight theorem has exactly the active
cutoff required by the corrected pointwise formula. `RouteABalancedVaughanActiveCharacterExpansion`
now joins the two surfaces: it character-expands and primitive-regroups the active pointwise
identity, proves fixed-level fiber uniqueness, identifies every complete fiber with the arithmetic
conductor-lift weight, and proves lift completeness for the principal conductor-one fiber. General
fiber completeness is reduced to the explicit algebraic statement
`PrimitiveCharacterChangeLevelStable`; Mathlib does not currently provide the needed conductor
stability theorem for `changeLevel`, so that statement remains open rather than assumed.

`RouteAInducedCharacterCorrection.lean` completes the other algebraic obligation. It proves an
explicit levelwise norm bound for the difference between an induced character sum and its
primitive character sum, sums that bound over every primitive fiber, and carries the correction
through the actual Type-I partial-summation formula. Lean now checks the exact decomposition

```text
signed coprime partial-summation error
  = primitive main partial summation
    - induced correction partial summation,
```

with an explicit finite norm majorant for the correction term. No conductor-lift completeness is
assumed in this bound.

`RouteAInducedCharacterCorrectionSharp.lean` proves the correction estimate required by the
specialist's active signed-conductor argument. Prime powers are grouped by their unique base prime;
their von Mangoldt mass is at most one `log X` per distinct prime divisor of the modulus. Lean
checks

```text
inducedCorrectionMass(X,q) <= (log q / log 2) * log X
```

and, after summing all level characters so that their cardinality cancels `phi(d)`,

```text
norm(activeInducedCorrection(L,N,u))
  <= u * log(u) * log(N)^2 / log(2).
```

The same module proves the exact global reduction

```text
active coprime error
  = primitive-character main - active induced correction - linear comparison.
```

Thus equations (14)--(15) of the specialist reduction are now represented on the repository's
exact active discrete surface.

`RouteABalancedVaughanConductorVariation.lean` proves the preceding bounded-variation input on the
same active surface.  When the cutoff drops from `X` to `X - 1`, the only possible departing
modulus is `d = X`, and its logarithmic weight is exactly `log(X/X) = 0`.  The persistent terms all
acquire one common logarithmic increment.  The signed prefix bound therefore telescopes to

```text
|W_r(a)| + |W_r(b)| + sum_{a <= t < b} |W_r(t) - W_r(t+1)|
  <= 2 c_r log N,

c_r = 6 rN / (phi(rN) phi(r)).
```

This is the specialist's equation (13) in exact finite form.  It uses no character estimate and
no project-specific axiom.

The remaining finite Stieltjes and conductor reindexing steps are now checked as well.
`RouteABalancedVaughanPrimitiveMeanValue.lean` turns a maximum bound for each ordinary cumulative
primitive-character `psi` sum into a bound for its weighted conductor sum.
`RouteABalancedVaughanPrimitiveReindexing.lean` proves the global finite Fubini identity that sums
the active primitive main by conductor. `RouteABalancedVaughanPrimitiveClosure.lean` separates the
centered conductor-one term from the nonprincipal conductors and proves the exact closure identity

```text
active coprime error
  = centered principal conductor-one sum
    + sum of nonprincipal primitive-conductor families
    - active induced-character correction.
```

Finally, `RouteABalancedVaughanPrimitiveAnalyticInterface.lean` exposes only ordinary cumulative
`psi` maximum bounds and their conventional weighted primitive-character mass. If that mass is at
most `B`, Lean proves the complete short Type-I correlation estimate with allowance

```text
principal allowance
  + (12 * N / phi(N) * log N) * B
  + u * log(u) * log(N)^2 / log(2)
  + noncoprime prime-power allowance.
```

This theorem reaches from the original finite bilinear convolution to the corrected active
discrete main. Its hypotheses still include `PrimitiveCharacterChangeLevelStable`, the principal
`psi` maximum, and the effective primitive-character mass bound. Those are visible theorem
arguments, not project axioms or generated certificates. Thus the formal short Type-I reduction is
complete, but the explicit analytic estimates and their numerical margin remain to be supplied.

The same module also splits the exact nonprincipal allowance at an arbitrary conductor cutoff
`R` and carries independent small- and large-conductor bounds through the original convolution.
This is the primary endpoint for the specialist argument: it preserves the extra conductor weight
used to obtain the large-conductor `1/R` saving. The all-conductor mean-value theorem above remains
a valid coarse corollary, but it is not substituted for this split in the feasibility calculation.

`RouteABalancedVaughanLargeConductor.lean` now proves that saving on the exact active surface. It
takes absolute values only over the lifts of one fixed primitive conductor, bounds their cost by
the finite prefix `sum_{k <= u/r} 1/phi(k)`, and shows that every conductor `r > R` contributes at
most

```text
(2 B log N / R) * (r / phi(r))
```

when the reciprocal-totient prefix through `u` is at most `B`. It then sums this bound against the
ordinary primitive-character maximum mass and carries the resulting small/large hybrid estimate
through the original Type-I convolution.

`RouteAReciprocalTotientPrefix.lean` discharges that remaining elementary prefix hypothesis. Lean
checks the exact positive-kernel identity

```text
sum_{k <= K} 1/phi(k)
  = sum_{d <= K} mu(d)^2/(d phi(d)) * harmonic(floor(K/d)),
```

compares the finite squarefree Euler product with the already-proved constant-six product, and
obtains

```text
sum_{k <= K} 1/phi(k) <= 6 * (1 + log K).
```

Consequently the final hybrid Type-I theorem no longer assumes a reciprocal-totient estimate. Its
large-conductor term is explicitly

```text
(12 * (1 + log u) * log N / R) * large-conductor primitive mean-value mass.
```

The axiom audit reports only Lean's standard logical axioms for this chain. The unresolved inputs
for this sharper complete-fiber chain are general conductor-lift stability, effective
small-conductor character estimates, and an effective large-conductor primitive mean-value bound.

The stability premise is no longer a mandatory gate. The modules
`RouteABalancedVaughanRepresentedFiberDirect.lean` and
`RouteABalancedVaughanRepresentedFiberClosure.lean` retain the actual subset of conductor lifts
represented by Mathlib's canonical primitive-character map rather than replacing it by every
multiple of the conductor. Lean proves the exact unconditional decomposition

```text
active coprime error
  = centered principal term
    + actual represented nonprincipal fibers
    - induced-character correction.
```

Direct endpoint and variation estimates give cost

```text
3 * (1 / phi(r)) * (sum_{k <= u/r} 1 / phi(k)) * log N
```

for each represented key. Consequently the original Type-I convolution is bounded without
`PrimitiveCharacterChangeLevelStable`. The all-conductor corollary has global factor
`18 * (1 + log u) * log N` times the conventional primitive-character mean-value mass. More
importantly, splitting at `R` preserves the large-conductor saving:

```text
(18 * (1 + log u) * log N / R)
  * large-conductor primitive mean-value mass.
```

The earlier globally quantified factor-12 theorem remains conditional on conductor stability at
every level, but it is not required for a valid Type-I reduction. The factor-18 represented route
has passed the axiom audit with only Lean's standard logical axioms.

`RouteABalancedVaughanLocalizedHybrid.lean` now combines the sharp and unconditional branches at
the theorem level. For represented conductors `r <= R`, it reuses the signed complete-fiber cost
two. For `r > R`, it uses the unconditional direct represented-fiber cost three. The global
`PrimitiveCharacterChangeLevelStable` premise is replaced by

```text
RepresentedConductorLiftCompleteUpTo L N u R,
```

which asks for represented active lifts only for nonprincipal keys through `R`, only on the prime
interval used by the balanced convolution, and only at moduli where the Mobius coefficient is
nonzero. Lean proves that missing zero-Mobius levels contribute exactly zero, so the weaker premise
still recovers the full signed conductor weight. `RouteADirichletCharacterConductorTransport.lean`
now proves the required supported stability: factor-through levels are closed under gcd at a
squarefree ambient level, so lifting a primitive character to a squarefree multiple preserves its
conductor and canonical primitive-character key. Since nonzero Mobius coefficients imply
squarefreeness, `PrimitiveCharacterSupportedChangeLevelStable` and then
`RepresentedConductorLiftCompleteUpTo` follow without assumptions. The resulting
large-conductor factor is

```text
18 * (1 + log u) * log N / R,
```

while the small-conductor allowance is exactly the original signed allowance. The numerical audit
in `scripts/experiments/route_a_signed_conductor_majorant.py --route localized --check` therefore
changes only the large-range coefficient from 12 to 18. At the specialist's test point
`log log N = 100`, that term is `8.688012977081e-193` and the total remains
`8.482782076783e-12`, dominated by the exceptional-character term. This verifies that localizing
the algebraic premise does not consume the proposed numerical margin; it does not verify the
external character estimates or the final retained-arc margin.

`RouteABalancedVaughanCanonicalPsiMax.lean` removes a final witness-packaging ambiguity. It defines
the principal and primitive `psi` maxima as finite suprema over the exact Type-I interval, proves
the pointwise maximal inequalities, constructs `PrimitivePsiMaxInput` canonically, and supplies a
localized Type-I corollary whose only analytic hypotheses are the small-conductor aggregate and
large-conductor mean-value inequalities for those explicit maxima.

`RouteABalancedVaughanNoncoprime.lean` separately closes the noncoprime progression interface by
bounding the finite von Mangoldt mass in those residue classes and inserting the resulting
explicit majorant into the existing coprime/noncoprime recombination theorem. This bound is coarse,
but it is proved and introduces no analytic axiom.

## The tractable Type-I term

For `u = floor(N^(1/3))`, expanding the full-circle term `C_N(A,S)` gives a prime-in-progressions
sum with outer modulus `d <= u` and residue `N mod d`. A maximal Bombieri--Vinogradov theorem is
uniform in the reduced residue and averages over `d`, so fixing the additive center does not by
itself prevent this application.

The expected paper theorem is

```text
C_N(A,S) = M_A(N) + O_K(N / log(N)^K),
```

after partial summation, with the non-coprime residue classes handled by prime powers dividing
`gcd(d,N)`. The retained `q=1,2` arcs should similarly satisfy

```text
J_N(A,S) = J_A(N) + O_{K,L}(N / log(N)^K).
```

Together with the checked mask identity this gives

```text
H_N(A,S) = M_A(N) - J_A(N) + O_{K,L}(N / log(N)^K).
```

This is a genuine fixed-center signed estimate for an actual term. It is not currently a Lean
theorem. The exact partial-summation derivation is now checked, but the repository does not yet
contain the required maximal Bombieri--Vinogradov estimate or effective constants.

The existing `ExplicitPNTinAP_BMOR.psi_bound` is not a substitute for this missing input. It is a
pointwise explicit estimate restricted to `q <= 100000`. The intended cutoff `u = floor(N^(1/3))`
is unbounded, while the specialist deduction uses an average over all `d <= u`. The BMOR theorem
can control a fixed initial modulus range, but applying it alone would leave a growing outer tail.

`RouteABalancedVaughanTypeIInterface.lean` records exactly the outputs such a proof must supply and
checks their recombination. It introduces structures as explicit hypotheses, not axioms.

## Signed-conductor proposal

A specialist proposal dated 2026-10-27 observes that the actual Type-I error retains

```text
sum_{d <= N^(1/3), (d,N)=1} mu(d) * error_d,
```

whereas the maximal-Bombieri--Vinogradov route takes absolute values before exploiting `mu(d)`.
After character expansion, grouping induced characters by primitive conductor should produce a
conductor weight whose modulus sum is controlled by the elementary target

```text
|sum_{k <= X, (k,m)=1} mu(k) / phi(k)| <= 6 * m / phi(m).
```

The proposal combines this cancellation with explicit primitive-character mean values and
explicit exceptional-zero estimates. Its deliberately conservative paper calculation claims an
`O(10^-9 N)` bound only above `N >= exp(exp 100)`. That threshold is far too high for the existing
finite base, but the calculation would establish an effective `o(N)` treatment of this isolated
short Type-I term if every reduction and constant is verified.

`scripts/experiments/route_a_signed_conductor_majorant.py` independently evaluates the six-term
majorant from that calculation in logarithmic coordinates. At `log log N = 100` it obtains
`8.482782076783e-12`, with the exceptional-character term dominant, and therefore confirms that
the displayed numerical majorant is below `10^-9`. This is a reproducible numerical audit, not a
Lean proof of the cited character estimates. It also confirms that the large-conductor saving must
retain its separate conductor weight; the coarser all-conductor mean-value corollary in the Lean
interface is sound but is not by itself strong enough to reproduce the specialist's `1/R` gain.

This is now the primary Type-I research path, subject to five checks:

1. prove the Mobius/totient partial-sum lemma in Lean (complete: theorem
   `RouteASignedMoebiusEulerProduct.signedMoebiusTotientSixBound`);
2. prove the exact character expansion and primitive-conductor regrouping, including induced
   character and conductor conditions (complete unconditionally on the active surface using the
   actual represented fibers; the sharper complete-fiber formula remains conditional on the
   isolated `PrimitiveCharacterChangeLevelStable` theorem);
3. prove the stated induced-character and noncoprime prime-power corrections (complete, including
   the sharp active allowance `u log(u) log(N)^2 / log 2`);
4. prove the conductor-weight endpoint and variation estimate (complete with factor two for a
   complete fiber and factor three for an actual represented subset);
5. supply the effective primitive-character mean-value estimate and rederive its numerical
   majorant against the repository's discrete main term (the exact interface consuming such an
   estimate and producing the full short Type-I convolution bound is complete).

The fifth point matters because the specialist wrote a continuous integral main, while the
checked repository identity uses an exact active discrete sum. A sum-versus-integral correction
must be proved explicitly; it may not be treated as merely an endpoint convention. The inactive
tail in the older comparison main is now separately named and cannot be silently absorbed into
that correction.

The stronger maximal-Bombieri--Vinogradov interface remains available as an alternative sufficient
route, but failure to populate it is no longer by itself a stopping condition.

## Effectivity requirement

An asymptotic `O_K` statement with an unspecified or ineffective constant is insufficient for the
project's finite-base architecture. Before the Type-I result can support an end-to-end theorem, it
must provide either:

- explicit constants and a computable threshold; or
- a separately proved effective version strong enough to meet the numerical budget.

This requirement must be tested before commissioning another finite computation.

## The hard residual

After the Type-I term is removed, the exact unresolved object is

```text
H_N(hard,S),
```

not the full complementary energy and not six unrelated absolute values. The long part includes
the Type-II coefficient

```text
mu_>u * zeta * Lambda_>v.
```

Known results show that neither a reflected additive convolution nor a growing specified center is
categorically inaccessible. However, the available shifted-divisor and Kloosterman-fraction
theorems do not automatically accept the actual truncated Mobius--von-Mangoldt weights. Expanding
the second arithmetic factor produces nonsmooth correlated weights, and a divisor-size majorant
does not transfer a cancellation estimate.

The theorem still needed is one-sided. In the present interface it has the form

```text
H_N(hard,S).re >= -hardAllowance(N),
```

with a margin that survives the Type-I errors, retained-arc model, major approximation, and
higher-prime-power allowance. `balancedMaskedCorrelation_lower_bound` checks the exact
recombination:

```text
M_A - J_A - fullError - retainedError - hardAllowance
  <= H_N(S,S).re.
```

## Work order and stopping rule

1. Prove the elementary Mobius/totient partial-sum bound used by the signed-conductor proposal.
   **Complete.**
2. Formalize the exact primitive-conductor regrouping of the checked signed partial-summation sum,
   retaining every induced-character correction. **Complete unconditionally on the active
   discrete surface by summing the actual represented primitive-character fibers. The principal
   centered term, represented nonprincipal fibers, sharp induced correction, and full
   convolution-to-active-main bound have all been recombined in Lean. A globally quantified
   complete-fiber variant remains conditional on conductor stability at every level. The localized
   hybrid needs stability only on the nonzero-Mobius support of represented small-conductor
   fibers; the squarefree conductor-transport theorem proves it. The hybrid uses the unconditional
   represented estimate above `R`, and its final Type-I endpoint has no algebraic completeness
   premise.**
3. Verify the published explicit character estimates, their range hypotheses, and the resulting
   aggregate constants against the discrete repository formula. **The all-conductor factor
   `12 * N / phi(N) * log N` and the sharper split large-conductor factor
   `12 * (1 + log u) * log N / R` are checked. The reciprocal-totient input to the latter is now
   proved on the conditional complete-fiber branch. The unconditional represented-fiber branch
   has split large-conductor factor `18 * (1 + log u) * log N / R`. The preferred localized branch
   retains the signed small-conductor allowance and pays factor 18 only above `R`; its numerical
   majorant passes the existing specialist test. Its supported small-fiber completeness is now
   proved, and its maximal-input record now has a canonical finite-supremum realization. Populating
   the resulting principal, small-conductor, and large-conductor quantities with verified effective
   estimates remains open.** Keep maximal BV as an independent sufficient fallback, not a
   mandatory gate.
4. Prove the elementary noncoprime prime-power bound and combine it with the signed coprime bound
   through the checked error-partition theorem. **Complete, with a coarse explicit finite bound.**
5. Analyze the retained `q=1,2` arcs and compute the resulting signed margin before doing any
   further Type-II formalization.
6. Convert `H_N(hard,S)` to the exact input form of one candidate dispersion, spectral, or
   Kloosterman theorem, including all coefficient norms and smoothness/factorability conditions.

Stop if either of the following occurs:

- the effective Type-I constants do not leave a usable margin; or
- no established theorem accepts the actual hard coefficients and yields a fixed-center one-sided
  saving after recombination.

Passing the Type-I stage is useful mathematics, but it does not by itself reopen Route A. Passing
the hard-residual stage with explicit constants would justify doing so.
