# Balanced Vaughan fixed-center program

Date: 2026-10-26

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

1. State the precise effective Bombieri--Vinogradov input required by the checked prime-residue
   formula, including its computable constant, threshold, and maximal partial-sum form.
2. Prove that the effective maximal theorem controls the named coprime progression error, without
   replacing it by a pointwise fixed-range theorem.
3. Bound the checked partial-summation endpoint/variation expression and the separate noncoprime
   prime-power term, then combine them through the checked error-partition theorem.
4. Analyze the retained `q=1,2` arcs and obtain the explicit Type-I masked main expression.
5. Compute the resulting signed margin before doing any further Type-II formalization.
6. Convert `H_N(hard,S)` to the exact input form of one candidate dispersion, spectral, or
   Kloosterman theorem, including all coefficient norms and smoothness/factorability conditions.

Stop if either of the following occurs:

- the effective Type-I constants do not leave a usable margin; or
- no established theorem accepts the actual hard coefficients and yields a fixed-center one-sided
  saving after recombination.

Passing the Type-I stage is useful mathematics, but it does not by itself reopen Route A. Passing
the hard-residual stage with explicit constants would justify doing so.
