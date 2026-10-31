# Fixed-center slope-averaged long-Mobius diagnostic

Date: 2026-10-30

Status: **NUMERICALLY COMPATIBLE; ANALYTICALLY UNRESOLVED**

## Executive verdict

The supplied fixed-center formulation repairs two defects in the earlier long-Mobius discussion:

1. it uses each affine fiber's exact cardinality rather than replacing it by an asymptotic density;
2. it asks for a mean square over slopes at one fixed center, rather than an unavailable uniform
   estimate for every individual progression.

The basic fiber identities and the two Cauchy--Schwarz reductions below are exact.  The normalization
does **not** make the raw reflection operator contractive: every nonempty unit-amplitude conditioned
reflection sector has norm one.  Any saving must therefore come from the complete signed
raw-plus-comparison residual, with mark transitions, endpoint norms, and comparison-fiber centers
left visible.

The first reproducible coefficient experiment is encouraging.  Across 30 even centers from
`884736` through `1000000000`, the exact coefficient mode satisfies

```text
0.9387 < N^(1/3) * V / S0 < 3.2280.
```

This is compatible with the diagonal/random-sign scale `V/S0 ~ N^(-1/3)`.  The largest observed
absolute signed contribution was `0.000333965*N`; the largest honest active-fiber weight-adapted
Cauchy bound was `0.001131899*N`.  These are finite experiments with an exploratory smooth weight,
not a theorem, not a marked-operator test, and not a Route A ledger entry.

The next justified task is a paper theorem, not a Lean certificate: construct the exact signed
marked application identity and prove a slope-averaged bound for that exact residual.  If the source
marking cannot be reconstructed back to the unmarked coefficient without assuming the desired
cancellation, this branch stops.

## 1. Exact coefficient and fibers

Put

```text
D = N^(2/3),   Y = N^(1/3),   ell = log N,
I_D = (D/2, 3D/4],   I_Y = (Y/2, 3Y/4].
```

For the exploratory coefficient use

```text
b_z(n) = lambda(n) * 1_{p^2 does not divide n for every prime p <= z},
z = ceil(ell^20).
```

For a fixed slope pair `alpha=(m,b)` write

```text
g = gcd(m,b),   r = m/g,   s = b/g,   A = N/g.
```

There are no solutions unless `g | N`.  Otherwise choose one solution of

```text
r*d0 + s*a0 = A
```

and parameterize all solutions by

```text
d_t = d0 + s*t,   a_t = a0 - r*t.
```

The exact fiber and its cardinality are

```text
I_alpha = {t in Z : d_t in I_D and a_t in I_D},
M_alpha = # I_alpha.
```

No replacement of `M_alpha` by `A/(r*s)` is made at boundary fibers.  Define

```text
C_alpha = sum_{t in I_alpha} b_z(d_t) b_z(a_t),
kappa_alpha = C_alpha / M_alpha
```

for nonempty fibers.  On normalized counting measure on `I_alpha`, `kappa_alpha` is exactly the
inner product of the two endpoint coefficient vectors.

For slope weights `w_alpha=f_Y(m)f_Y(b)`, set

```text
S0 = sum_alpha M_alpha,
W2 = sum_alpha |w_alpha|^2 M_alpha,
V  = sum_alpha M_alpha |kappa_alpha|^2,
Vw = sum_alpha |w_alpha|^2 M_alpha |kappa_alpha|^2,
T  = sum_alpha w_alpha M_alpha kappa_alpha.
```

Two exact inequalities are then available:

```text
|T|^2 <= W2 * V,
|T|^2 <= S0 * Vw.
```

These are bookkeeping reductions only.  The missing mathematics is a nontrivial upper bound for
`V` or `Vw` on the actual arithmetic coefficient.

## 2. The useful quantitative theorem shape

The elementary fiber count from the supplied review gives, at the project threshold,

```text
S0 <= 5*N*ell.
```

Since the exploratory logarithmic slope weight satisfies `|w_alpha| <= ell^2`, it also gives

```text
W2 <= 5*N*ell^5.
```

Consequently either of the following would be more than sufficient for a small fixed-center error:

```text
V  << N^(2/3) * ell^C,
Vw << N^(2/3) * ell^C
```

for any explicit fixed exponent `C`, once the theorem is connected to the actual hard remainder.
For example, the weight-adapted inequality would give

```text
|T|/N << N^(-1/6) * ell^((C+1)/2),
```

which is negligible at `N >= exp(exp 100)`.

A weaker logarithmic theorem can also suffice, but its exact constant cannot be chosen until the
application identity restores every coefficient and the fixed-center ledger identifies the precise
allowance for this block.  It is therefore premature to advertise a target epsilon detached from
the decomposition.

Expanding `V` exposes the actual four-point problem:

```text
V = sum_alpha (1/M_alpha)
      sum_{t,u in I_alpha}
        b_z(d_t)b_z(a_t)b_z(d_u)b_z(a_u).
```

The diagonal `t=u` naturally has the `N^(2/3)` scale.  The theorem must show that the off-diagonal
four-point correlations do not rebuild an order-`N` contribution after the slope sum.

## 3. Operator requirements and falsification tests

Changing from counting measure to normalized counting measure fixes the arithmetic scale of the
endpoint vectors, but it does not change an operator norm between equal finite spaces.

For a fixed raw edge-product sector, conditioned reflection identifies one source coordinate with
one target coordinate.  The unit-amplitude matrix is therefore an identity or permutation matrix:

```text
||R_j|| = 1.
```

With diagonal amplitude `a_j(t)`, its norm is exactly `max_t |a_j(t)|`.  A numerical experiment on
the raw reflection matrix cannot produce the missing saving.

The application must instead prove an identity of the form

```text
kappa_alpha_mark = <U_alpha, B_alpha V_alpha> + e_alpha,
```

where `B_alpha` is the **combined signed raw-plus-comparison residual**.  Define

```text
Xi = sum_alpha |w_alpha|^2 M_alpha
       ||U_alpha||^2 ||V_alpha||^2 ||B_alpha||^2,
E  = sum_alpha |w_alpha| M_alpha |e_alpha|.
```

Then the exact application estimate is

```text
|T_mark| <= sqrt(S0 * Xi) + E.
```

The following details are mandatory:

1. mark lists remain part of the state space;
2. endpoint masses and reconstruction coefficients remain explicit;
3. a comparison term created by a free-label product `D_C` lives at center `A*D_C`, not silently
   on the original fiber;
4. the transfer maps between comparison fibers and the original expression are stated exactly;
5. sector orthogonality controls the maximum sector norm on each fiber, not the maximum of the
   sector-averaged norms.

In particular, separate estimates for sectors `j` generally yield a sum of squared sector
allowances.  Different sectors may be hot on different slope fibers.  A valid theorem must control

```text
sum_alpha |w_alpha|^2 M_alpha max_j ||B_{alpha,j}||^2
```

directly, or provide a summable family of sector allowances.

## 4. Provisional exceptional-stratum budget

The supplied paper review gives the following elementary decomposition for the unmarked coefficient
`|b_z| <= 1` and `|w_alpha| <= ell^2`.

Choose

```text
M0 = Y/ell^K,
G = R = exp(40*sqrt(ell)).
```

Then the claimed bounds are

```text
|T_short|       <= N*ell^(2-K),
|T_{g>G}|       <= 3*N*ell^2*exp(-8*sqrt(ell)),
|T_largeCommon| <= 12*N*ell^3*exp(-8*sqrt(ell)).
```

For `K=20` and `ell >= exp(100)`, their sum is less than

```text
2*N*ell^(-18).
```

On the surviving fibers,

```text
r/gcd(r,A), s/gcd(s,A) > Y/(2*G*R).
```

Thus an edge-product cutoff `Q < Y/(2*G*R)` excludes the small reduced-slope failure mode.

These estimates are currently **paper-level and provisional**.  They have not been formalized in
Lean.  Their marked analogue must restore the supremum sizes of the marked endpoint weights before
choosing `K`; the unmarked `K=20` allowance cannot simply be copied.

The estimates deliberately do not discard all noncoprime fibers.  That is necessary: the finite
experiment below shows that small-common-factor fibers can carry most of the signed contribution.

## 5. Reproducible finite experiment

The diagnostic is

```text
scripts/experiments/route_a_long_mobius_fibers.py
```

Example exact-coefficient invocation:

```bash
python3 scripts/experiments/route_a_long_mobius_fibers.py \
  884736 2097152 4096000 7077888 16777216
```

The complete 30-center audit set was

```text
884736 2097152 4096000 5000000 6000002 7077888 10000000 11239424
12345678 15000000 16777216 32000000 64000000 100000000 250000000
500000000 1000000000 50000002 75000004 125000006 175000008 225000010
300000012 375000014 450000016 550000018 650000020 750000022 850000024
950000026
```

At all computationally practical centers in this audit, the prescribed `z=ceil(log(N)^20)` exceeds
every relevant square-prime base.  Hence the exact coefficient mode is simply `b_z=mu` on the
tested long interval.  It does **not** instantiate the source's auxiliary marked states.

The option

```text
--square-cutoff 7
```

creates a labelled surrogate coefficient experiment with nonempty large-prime structure.  It is not
evidence at the frozen parameters and is not mixed into the table below.

The smooth slope weight used here is explicitly

```text
f_Y(m) = bump(m/Y) * log(m),
bump(x) = exp(1 - 1/(1-((x-0.70)/0.04)^2))
```

on `|x-0.70|<0.04`, and zero otherwise.  This is an admissible exploratory weight, not a claim that
all project weights have been reduced to this bump.

### Selected exact-mode results

| `N` | `T/N` | active weight-adapted CS / `N` | `N^(1/3) V/S0` | coprime `T/N` | noncoprime `T/N` |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 884736 | -0.000106224 | 0.000723231 | 1.22659 | 0.000024275 | -0.000130499 |
| 2097152 | 0.000333964 | 0.000887702 | 2.10014 | 0.000047928 | 0.000286037 |
| 5000000 | -0.000090334 | 0.001131899 | 0.93871 | -0.000008305 | -0.000082029 |
| 7077888 | 0.000164961 | 0.000965694 | 1.24559 | 0.000007168 | 0.000157793 |
| 16777216 | 0.000154150 | 0.000895852 | 2.43269 | 0.000070425 | 0.000083725 |
| 100000000 | 0.000019510 | 0.000845995 | 1.52286 | 0.000026140 | -0.000006629 |
| 250000000 | -0.000031677 | 0.000849860 | 1.55870 | -0.000019885 | -0.000011792 |
| 500000000 | -0.000002961 | 0.000779881 | 1.51877 | 0.000008228 | -0.000011189 |
| 1000000000 | 0.000013574 | 0.000744740 | 1.56735 | 0.000005891 | 0.000007683 |

An additional 13-center holdout sample between `50000002` and `950000026` gave

```text
1.53775 <= N^(1/3) V/S0 <= 3.22799,
2.14e-7 <= |T|/N <= 3.63e-5,
0.000678 <= active weight-adapted CS/N <= 0.001003.
```

Across all 30 tested centers, the full observed range was

```text
0.93870 <= N^(1/3) V/S0 <= 3.22799,
|T|/N <= 0.000333965,
active weight-adapted CS/N <= 0.001131899.
```

### What the experiment does and does not say

The stable rescaling by `N^(1/3)` is a concrete signal that the unmarked mean square may live near
its diagonal scale rather than its trivial order-`N` scale.  That is the first useful target for a
four-point theorem.

It does not show:

1. uniformity for every even center;
2. an asymptotic bound;
3. the signed marked residual estimate;
4. reconstruction of the unmarked coefficient from source marks;
5. compatibility with the final fixed-center budget after all other hard terms are restored.

The coprime/noncoprime columns also show why a coprime-only theorem is not enough.  At several
centers the noncoprime part is the dominant part of `T`; the good domain must retain controlled
small common factors.

## 6. Development gates

The branch should proceed only through the following gates.

### Gate A: exact marked application identity

Write the source's actual marked endpoint weights, state spaces, raw term, every comparison term,
and their centers.  Prove the exact identity back to the selected fixed-center coefficient block.
No operator estimate is relevant until this identity exists.

### Gate B: unmarking or reconstruction

Give an exact finite identity or a quantitatively controlled approximation that recovers the
unmarked `b_z` block.  The source mark weight vanishes on a non-negligible part of the unmarked
support, so division by that weight is not available.  If the complement's cancellation has to be
assumed, stop: that would merely rename the missing theorem.

### Gate C: slope-averaged signed residual estimate

Prove a bound for `Xi`, including the per-fiber sector maximum or a summable sector decomposition.
The raw norm-one reflection test must remain as a regression test.  Rational-grid energy may be
used for comparison terms only; it does not establish the raw signed theorem.

### Gate D: exceptional strata and reconstruction errors

Restore marked amplitudes in the short-fiber, large-gcd, and large-common-factor bounds.  Add the
comparison and reconstruction errors explicitly.

### Gate E: fixed-center ledger

Map the resulting `T` to the exact Vaughan hard remainder and calculate the final constant.  A
small graph norm or a favorable finite experiment is not progress unless the restored theorem
beats the current factor-two deficit in the actual ledger.

## 7. Stopping rule

Stop this branch if any of the following occurs:

1. the exact source marking cannot be reconstructed to the unmarked coefficient;
2. the combined operator estimate becomes only the norm-one raw reflection estimate after endpoint
   masses are restored;
3. sector averaging assumes away fiber-dependent hot spots;
4. comparison terms are moved from center `A*D_C` to `A` without an exact transfer;
5. the final bound is no better than the current factor-two envelope;
6. the required cancellation is inserted as an input hypothesis.

Until Gates A--E pass, the correct mathematical status is **UNRESOLVED WITH A CONCRETE NUMERICAL
SIGNAL**, not a repaired Route A proof.
