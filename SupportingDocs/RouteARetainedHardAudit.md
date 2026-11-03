# Route A retained hard-residual audit

## Result

The retained `q=1,2` comparison can be bounded without estimating two large retained integrals
separately.  Write

```text
S = balanced von Mangoldt weight,
A = short Type-I weight,
hard = S - A,
J = retained q=1,2 integral.
```

Then

```text
J(S,S) - J(A,S) = J(hard,S).
```

At

```text
L = 1,000,001,
N >= exp(exp 100), N even,
u = floor(N^(1/3)),
```

the paper estimates below give the safe bound

```text
|J(hard,S)| < 0.49 N.
```

Together with the active-main audit and revised complete Type-I allowance,

```text
M_A >= 0.9 N,
Type-I full error < 5e-15 N,
```

this leaves

```text
M_A - Type-I error + J(hard,S) > 0.40 N.
```

Thus the remaining complementary hard-residual theorem need only establish, with room for the
prime-power contamination and rounding terms,

```text
H(hard,S).re >= -c_hard N
```

for some explicit `c_hard < 0.40`.  A safer commissioning target is `c_hard <= 0.35`.

This is still a paper feasibility derivation.  Its two elementary summatory lemmas and the
seam adapter have not yet been formalized in Lean.

## Lean recombination surface

`RouteABalancedVaughanTypeIInterface.lean` now contains

```text
BalancedVaughanRetainedHardResidualLowerBound
balancedFullCorrelation_lower_bound_of_retainedHard
```

The theorem combines:

1. the full Type-I progression estimate;
2. a direct lower bound for `J(hard,S)`;
3. a direct lower bound for `H(hard,S)`.

It does not require separate approximations to `J(S,S)` and `J(A,S)`.  Lean compiles this exact
algebraic recombination.

## Principal prefix

Let

```text
A_u(n) = sum_{d|n, d<=u} mu(d) log(n/d),
T_u(x) = sum_{n<=x} A_u(n).
```

For `x >= u`, changing the order of summation gives

```text
T_u(x) = sum_{d<=u} mu(d) log(floor(x/d)!).
```

The elementary integral comparison for `log(M!)` yields

```text
T_u(x)
  = x [checkm(u) + m(u)(log(x/u)-1)] + R_u(x),
|R_u(x)| <= u(1 + 2 log x),
```

where

```text
m(u)      = sum_{d<=u} mu(d)/d,
checkm(u) = sum_{d<=u} mu(d)/d log(u/d).
```

Ramaré's explicit estimates give

```text
|m(u)| <= 1/(69 log u),
|checkm(u)-1| <= 1/(389 log u).
```

Since `log(N/u)/log u <= 2.01`, the main relative error is below

```text
1/(389 log u) + (log(N/u)+1)/(69 log u)
  = 0.028986... + negligible.
```

The factorial remainder, the range `x<u`, and the fixed lower endpoint `L` are all below
`exp(-300)N` at the frozen threshold.  Johnston--Yang's explicit PNT error is smaller still.
Consequently the unmodulated hard prefix satisfies the safe uniform bound

```text
max_t |sum_{L<=n<=t} (Lambda(n)-A_u(n))| <= 0.03 N.
```

## Parity prefix

For the `q=2` arc, modulate by `(-1)^n`.  The von Mangoldt side obeys

```text
sum_{n<=x} (-1)^n Lambda(n) = -psi(x) + O(log x),
```

because only powers of `2` contribute to the correction.

For the Type-I side, write

```text
O_u(x) = sum_{n<=x, n odd} A_u(n).
```

The odd logarithmic factorial satisfies

```text
sum_{m<=y, m odd} log m = (y/2)(log y-1) + O(1+log y).
```

The odd Mobius sums are exact power-of-two convolutions of the ordinary sums:

```text
m_odd(x)      = sum_{2^j<=x} 2^(-j) m(x/2^j),
checkm_odd(x) = sum_{2^j<=x} 2^(-j) checkm(x/2^j).
```

Split at `2^j <= u^(1/100)`.  On the main range, `u/2^j >= u^(99/100)` and the weights sum to at
most `2`; the remaining geometric tail is below `exp(-300)`.  Hence

```text
|O_u(x)-x|/N < 0.03
```

uniformly on the relevant prefixes.  Since

```text
sum (-1)^n A_u(n) = T_u(x) - 2 O_u(x),
```

the parity-modulated hard prefix has the safe bound

```text
max_t |sum_{L<=n<=t} (-1)^n (Lambda(n)-A_u(n))| <= 0.09 N.
```

## Integration on the retained arcs

Finite Abel summation turns a prefix bound `E` into

```text
|sum h(n)e(n beta)| <= E(1 + 2 pi N |beta|).
```

Integrating this expression, rather than replacing it by its endpoint maximum, gives

```text
integral_{|beta|<=1/N}       (1+2 pi N|beta|) dbeta
  = 2(1+pi)/N,

integral_{|beta|<=1/(2N)}    (1+2 pi N|beta|) dbeta
  = (1+pi/2)/N.
```

The other exponential sum is bounded by `psi(N) <= 1.01 N`.  Therefore

```text
|J(hard,S)|/N
  <= 1.01 [2(1+pi)(0.03) + (1+pi/2)(0.09)]
  < 0.49.
```

The rounded computation is reproduced by

```text
python3 scripts/experiments/route_a_retained_hard_budget.py --check
```

## Formalization obligations

Before using `0.49 N` in the final chain:

1. Prove the logarithmic-factorial comparison and the exact summatory formula for `A_u`.
2. Prove the odd-logarithmic-factorial comparison and the two power-of-two convolution identities.
3. Introduce the wrapped `[0,1]` retained set containing both halves of the principal arc and the
   full parity arc, and prove its equality to the seam-safe translated integral.
4. Formalize finite Abel summation on those two arcs and insert the explicit PNT/Mobius inputs.

These are structural lemmas, not generated certificates.

## Decision rule for the hard residual

The next mathematical assignment is now unambiguous:

```text
Prove H(hard,S).re >= -0.35 N
```

on the complement of the wrapped `q=1,2` arcs, for the exact Vaughan hard coefficient in the
repository.  A valid proof may use restricted-family Type-II/SSU information, but it must expose a
real saving for this coefficient family.  If the best demonstrable estimate is `0.40 N` or larger,
or if it assumes the desired cancellation, this fixed-center decomposition does not close Route A
and should stop there.
