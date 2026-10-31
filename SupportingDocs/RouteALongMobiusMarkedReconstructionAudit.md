# Long-Mobius marked-reconstruction audit

Date: 2026-10-30

Status: **SOURCE-ONLY TRANSFER FAILS GATE B; LOW-FACTOR MEAN SQUARE UNRESOLVED**

## Executive verdict

The supplied factorial-marking argument answers the reconstruction question sharply.

* The unmarked coefficient has an exact binomial expansion in damped factorial marks.
* The total formal coefficient mass is only polylogarithmic for the proposed reciprocal-prime
  mass.
* Positive-order marks vanish identically when an endpoint has no usable auxiliary-prime factor.
* The uncovered support is too large to discard by absolute values at the proposed unit
  normalization.  On admissible power-of-two centers, an explicit both-zero subset already has
  weighted absolute mass exceeding the nominal fixed-center reserve.

Therefore the existing positive-order marked theorem does not reconstruct the selected unmarked
long-Mobius block.  This is a failure of the source-only application, not a disproof of the
unmarked slope-averaged theorem.  The numerical diagnostic remains compatible with strong signed
cancellation inside the omitted low-factor remainder.

The only narrow continuation justified by the present evidence is a bounded feasibility study of
that remainder.  It would be a new arithmetic theorem, not bookkeeping around the existing marked
source.

## 1. Exact factorial reconstruction

Let the disjoint auxiliary-prime groups be `P_j`, and put

```text
V_j = sum_{p in P_j} 1/p,
k_j(n) = # {p in P_j : p divides n},
k(n) = sum_j k_j(n).
```

For `0<q<1`, `theta=1-q`, and a multi-index `tau`, define

```text
W_tau(n) = q^(k(n)-|tau|) * product_j (k_j(n))_(tau_j) / V_j^(tau_j),
c_tau    = product_j (theta*V_j)^(tau_j) / tau_j!.
```

The binomial theorem gives the pointwise finite identity

```text
sum_{tau >= 0} c_tau W_tau(n) = 1.
```

Indeed, after multiplying coefficients,

```text
c_tau W_tau(n)
  = q^(k(n)-|tau|) product_j binom(k_j(n),tau_j) theta^(tau_j),
```

and summing gives `product_j (q+theta)^(k_j(n))=1`.

For the exact fiber correlation this yields

```text
C_alpha
  = sum_{tau,upsilon >= 0}
      c_tau c_upsilon C_alpha^(tau,upsilon).
```

No coefficient support is omitted in this identity.  Its total coefficient mass is

```text
sum_tau c_tau = exp(theta * sum_j V_j).
```

This is a fixed power of `log N` when the total reciprocal-prime mass is `O(log log N)`.

## 2. Exact support obstruction

If `k(n)=0`, then

```text
W_0(n)=1,
W_tau(n)=0 for every |tau|>0.
```

Thus no linear combination of positive-order marks can recover the coefficient on the
zero-usable-prime stratum.  Recoloring or repartitioning the same auxiliary pool cannot change
this: an integer with no prime from the pool has no mark in any partition.

Including the zero-order term repairs the algebra but not the analysis.  On the zero-mark
component, the conditioned raw reflection has norm one.  The currently quoted source theorem does
not provide the required signed raw-plus-comparison estimate for this component.

## 3. Exact low-factor remainder

Pooling the usable primes, write

```text
k = omega_P(n),
V = sum_{p in P} 1/p,
W_j(n) = q^(k-j) (k)_j / V^j.
```

For `K>=1`, Newton interpolation gives explicit coefficients

```text
a_(j,K) = V^j/j! * sum_{i=K}^j (-1)^(j-i) binom(j,i) q^(j-i)
```

such that

```text
1_{k>=K} = sum_{j=K}^k a_(j,K) W_j(n).
```

Consequently the exact fiber decomposition is

```text
C_alpha
  = sum_{j,l>=K} a_(j,K) a_(l,K) C_alpha^(j,l)
    + R_(alpha,K),
```

where

```text
R_(alpha,K)
  = sum_{t in I_alpha} b_z(d_t)b_z(a_t)
      1_{min(omega_P(d_t),omega_P(a_t)) < K}.
```

The coefficient bound

```text
sum_{j>=K} |a_(j,K)| <= exp((1+q)V)
```

is again polylogarithmic under the intended reciprocal-mass choice.  The obstruction is therefore
not a formally enormous reconstruction coefficient.  It is the signed remainder `R_(alpha,K)`.

## 4. Absolute disposal is impossible

Take the maximal usable pool on a good fiber to be

```text
P_alpha^* = {p : z < p <= H and p does not divide r*s*A},
H = exp((log N)^(2/5)).
```

The supplied paper argument proves, for coprime long fibers,

```text
# {t : sigma_z(d_t)sigma_z(a_t)=1 and
       omega_(P_alpha^*)(d_t)=omega_(P_alpha^*)(a_t)=0}
  >= M_alpha / (100*(log N)^(7/4)).
```

The proof uses an explicit upper bound for the reciprocal-prime mass, adjacent Bonferroni
truncations, Chinese-remainder counting, and explicit removal of small square divisors.  The
constants are extremely conservative at `log N >= exp(100)`.  This result is paper-level and has
not been formalized in Lean.

For `N=2^j`, restrict to odd coprime slopes

```text
0.70*Y <= m,b <= 0.71*Y.
```

There are at least `Y^2/100000` such ordered pairs, every associated fiber has
`M_alpha>=Y/100`, and the diagnostic bump gives `w_alpha>=(log N)^2/25`.  Therefore the both-zero
subset has weighted absolute mass at least

```text
N*(log N)^(1/4) / 25000000000.
```

At the frozen threshold this exceeds `2*N`, while the available major reserve on powers of two is
less than `1.416*N`.  Hence no absolute-value estimate can dispose of this omitted support.

This reserve comparison concerns the proposed diagnostic block and its explicit bump at unit
normalization.  The exact identity mapping that block into the Vaughan hard remainder has not yet
been supplied.  The lower bound therefore rules out absolute disposal inside the proposed
application; it is not by itself a contradiction in the final Goldbach ledger with every transfer
coefficient restored.

The lower bound also says nothing about the sign of the omitted correlation.  It proves that a
signed theorem is indispensable if this block is to be used at the proposed scale.

## 5. Reproducible finite low-factor diagnostic

The experiment

```text
scripts/experiments/route_a_long_mobius_fibers.py
```

now accepts

```text
--auxiliary-upper H
```

and reports two exact finite restrictions for the chosen surrogate pool:

```text
low_union: at least one endpoint has no usable pool prime;
both_zero: both endpoints have no usable pool prime.
```

For example:

```bash
python3 scripts/experiments/route_a_long_mobius_fibers.py \
  7077888 16777216 --square-cutoff 7 --auxiliary-upper 97
```

produces:

| `N` | total `T/N` | low-union `T/N` | both-zero `T/N` | low-union absolute / `N` | both-zero absolute / `N` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 7077888 | 0.000155029 | 0.000094457 | 0.000038718 | 0.001393681 | 0.000541644 |
| 16777216 | 0.000166302 | 0.000163398 | 0.000086300 | 0.001712993 | 0.000623577 |

With the wider surrogate pool `7<p<=997`, the low-union mean square still accounts for roughly
63--71 percent of the complete active mean square in the tested centers from `7077888` through
`500000000`; the both-zero part accounts for roughly 17--22 percent.  Its rescaled quantity

```text
N^(1/3) * V_low / S0
```

remains between about `1.01` and `1.79` in those tests, again compatible with diagonal-scale
cancellation.

These are deliberately labelled surrogate results.  At feasible centers the prescribed
`z=ceil(log(N)^20)` leaves the exact auxiliary pool empty, so the exact finite experiment cannot
test the asymptotic mark construction.

## 6. What remains mathematically possible

### Option 1: direct low-factor slope mean square

Define `R_(alpha,1)` exactly as above and seek

```text
sum_alpha |R_(alpha,1)|^2 / M_alpha
  << N^(2/3) * (log N)^C,
```

or the corresponding weight-adapted estimate.  The low-factor indicator has real sieve structure:
each endpoint has no prime divisor in a specified medium-prime interval.  A credible proof would
need to expand that sieve condition while retaining the Möbius signs and then exploit averaging
over the slopes.  Taking absolute values loses the ledger immediately.

This theorem is narrower than the complete unmarked mean-square theorem but is not supplied by the
existing marked source.  It is original paper mathematics.

### Option 2: extend the signed operator to zero-order sectors

Construct comparison kernels for the zero-order and mixed zero/positive-order components, preserve
their actual centers, and prove a signed residual estimate.  Merely adding the zero-order raw
operator fails because its norm is one.

### Option 3: enlarge the usable-prime range

A much larger auxiliary pool would shrink the no-mark support, but the existing reflected graph
theorem is stated only for its restricted prime ranges and fixed mark parameters.  Extending the
pool requires a new uniform graph theorem and does not by itself control mixed low-order endpoints.

## 7. Decision and stopping rule

Stop treating the existing positive-order marked theorem as a route to the full coefficient.  It
has failed the reconstruction gate.

The broader long-Mobius branch earns one bounded next investigation: determine whether the direct
low-factor slope mean square in Option 1 is compatible with an available sieve/dispersion theorem.
Stop the branch if that reduction:

1. takes absolute values over the low-factor support;
2. returns only the trivial `O(N polylog N)` mean square;
3. assumes cancellation of `R_(alpha,1)`;
4. loses the fixed center;
5. or cannot restore the current fixed-center ledger constants.

No marked saving should be entered into the Goldbach ledger at the present stage.
