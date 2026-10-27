# Route A active-main kernel audit

## Result

The active discrete Type-I main has a viable uniform positive lower bound at the frozen analytic
threshold.  This is a paper-mathematics feasibility result, not yet a Lean theorem:

```text
L = 1,000,001
N >= exp(exp 100), N even
u = floor(N^(1/3))

balancedVaughanTypeIActiveDiscreteCoprimeMain L N u >= 0.9 N.
```

The constant `0.9` is intentionally loose.  The checked budget gives more than `0.95` for each
profile in the long part of the interval, while the omitted short part is astronomically small
relative to `N`.

This result removes one paper-level obstruction identified in `RouteARetainedMarginAudit.md`.
It does **not** close Route A: retained-arc matching and the one-sided hard residual remain.

## Exact repository surface

The active main is now rewritten in Lean as a sum of one-variable profiles:

```text
activeDiscreteCoprimeMain_eq_sum_logProfile

M_A(L,N,u)
  = sum_{p in [L,N-L]}
      sum_{d <= min(u,N-p), (d,N)=1}
        mu(d)/phi(d) * log((N-p)/d).
```

The theorem is in
`Goldbach/Cert/MajorArcModules/RouteABalancedVaughanActiveMain.lean`.  It compiles under the
project toolchain.  Thus the analytic profile below is exactly the profile used by the checked
Type-I decomposition; it is not a surrogate continuous main.

## Kernel reduction

Put

```text
c_N(d) = 1_(d,N)=1 mu(d)/phi(d),
a(d)   = mu(d)/d.
```

The repository already proves the Dirichlet-convolution identity

```text
c_N = a * h_N,
```

where `h_N` is `signedMoebiusTotientKernel N`.  Its prime-power values are

```text
h_N(p^j) =  1/p^j                  if p divides N,
h_N(p^j) = -1/(p^j (p-1))         if p does not divide N,
```

for `j >= 1`.  The repository also proves

```text
sum_{d <= X} |h_N(d)| <= 6 N/phi(N).
```

For real `x >= 1`, define the ordinary Mobius sums

```text
m(x)      = sum_{n <= x} mu(n)/n,
checkm(x) = sum_{n <= x} mu(n)/n * log(x/n).
```

Finite hyperbola reindexing gives

```text
A_N(U) = sum_{d <= U} c_N(d)
       = sum_{r <= U} h_N(r) m(U/r),

G_N(U) = sum_{d <= U} c_N(d) log(U/d)
       = sum_{r <= U} h_N(r) checkm(U/r).
```

For `k >= u`, the profile in the active main is exactly

```text
G_N(u) + A_N(u) log(k/u).
```

The infinite kernel sum is the Goldbach singular series:

```text
H_N = sum_{r >= 1} h_N(r)
    = 2 C2 * product_{p|N, p>2} (p-1)/(p-2).
```

For even `N`, write `P_N=N/phi(N)`.  The Euler factors also give

```text
P_N/H_N
  = C2^(-1) * product_{p|N, p>2} (1 - 1/(p-1)^2)
  <= C2^(-1).
```

Using the elementary numerical floor `C2 > 0.66`, this yields `H_N >= 1.32` and
`P_N/H_N < 1/0.66`.

## Explicit Mobius inputs

Ramaré's 2015 explicit estimates give

```text
|m(x)| <= 1/(69 log x)                  for x >= 96,955,
|checkm(x) - 1| <= 1/(389 log x)        for x >= 3,155.
```

The same source supplies the global fallback bounds `|m(x)| <= 1` and
`|checkm(x)-1| <= 1`.  These are used only on the kernel tail.

Reference: Olivier Ramaré, *Explicit estimates on several summatory functions involving the
Möbius function*, Mathematics of Computation 84 (2015), 1359-1387.

## Kernel tail

Split the kernel at

```text
D = floor(u^(1/100)).
```

For `d <= D`, one has `u/d >= u^(99/100)`, so the sharp Mobius estimates apply.  For the tail,
Rankin's device with exponent `1/2` gives

```text
sum_{d>D} |h_N(d)|
  <= D^(-1/2) sum_d |h_N(d)| sqrt(d).
```

The local factors imply the elementary moment estimate

```text
sum_d |h_N(d)| sqrt(d)
  <= exp(8 + 7 sqrt(1 + log(N)/log(2))).
```

Indeed, the off-conductor Euler product has logarithm below `8`; at conductor primes use
`-log(1-p^(-1/2)) <= (2+sqrt(2))p^(-1/2)`, order the distinct prime divisors increasingly, and use
`omega(N) <= log(N)/log(2)`.

At `log N >= exp(100)`, the resulting tail is smaller than `exp(-300)`.  This is an extremely
loose bound; its logarithm at the threshold is below `-4.48e40`.

## Budget

The preceding bounds yield

```text
|A_N(u)|
  <= 6 P_N / (69 * (99/100) log u) + tail,

|G_N(u) - H_N|
  <= 6 P_N / (389 * (99/100) log u) + 2 tail.
```

Since `u=floor(N^(1/3))`,

```text
log(N/u) / log u <= 2.01
```

throughout the frozen range.  Therefore the loss from the harmonic term is at most

```text
(402/2277 + negligible) P_N < 0.1766 P_N,
```

and the smoothing loss is negligible at this threshold.  Relative to `H_N`, the total checked
loss is below `0.267`.  Consequently every profile with `k >= u` is greater than `0.95`.

For `k < u`, the repository's reciprocal-totient prefix bound gives the crude absolute estimate

```text
|profile_N,u(k)| <= 6 (1 + log u) log u.
```

There are at most `u` such indices, so their total possible negative contribution is

```text
6 u (1 + log u) log u = o(N).
```

At `N >= exp(exp 100)`, that ratio and the fixed endpoint loss from `L` are both below
`exp(-300)`.  The safe aggregate conclusion is `M_A >= 0.9 N`.

The arithmetic is reproduced by

```text
python3 scripts/experiments/route_a_active_main_kernel_budget.py --check
```

The script works entirely with logarithms and checks every deliberately rounded inequality.

## Formalization obligations

The next Lean work for this component is finite and well specified:

1. Prove the logarithmically weighted hyperbola identity for `c_N = a * h_N`.
2. Add theorem interfaces for Ramaré's two explicit inequalities.  These are published analytic
   inputs and should remain visibly named until formalized from lower-level prime estimates.
3. Prove the infinite kernel Euler product and the `1/2`-moment tail estimate.
4. Combine those facts with `activeDiscreteCoprimeMain_eq_sum_logProfile` to obtain the explicit
   `0.9 N` lower theorem.

This component should not be expanded into generated certificates.  Its proof is structural and
uniform.

## Remaining Route A gate

The retained difference

```text
J(S,S) - J(A,S),
```

on the same seam-safe `q=1,2` arcs now also has a viable paper bound.  The direct hard-residual
estimate in `RouteARetainedHardAudit.md` gives `|J(S-A,S)| < 0.49 N`, preserving more than
`0.40 N` of the active-main margin before the complementary hard term.  The remaining substantive
Route A gate is therefore the one-sided complementary estimate recorded there.
