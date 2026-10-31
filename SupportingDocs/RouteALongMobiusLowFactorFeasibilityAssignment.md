# Specialist assignment: low-factor long-Mobius slope mean square

Date: 2026-10-30

## Requested verdict

Determine whether the zero-usable-prime / low-usable-factor remainder left by the exact marked
reconstruction admits a genuinely nontrivial fixed-center slope-averaged mean-square estimate.

Return one of:

```text
PASS        an explicit theorem with all normalizations and a proved quantitative saving;
FAIL        a diagonal, support, or lower-bound obstruction rules out the required estimate;
UNRESOLVED  the target is compatible with known constraints but requires a new theorem.
```

This is a bounded feasibility study.  Do not extend the existing positive-order marked theorem by
analogy, do not average over the center, and do not formalize in Lean before the paper theorem and
its constants pass review.

## 1. Fixed-center setup

Let

```text
N >= exp(exp 100), N even,
D = N^(2/3), Y = N^(1/3), ell = log N,
I_D = (D/2,3D/4], I_Y = (Y/2,3Y/4].
```

Use

```text
b_z(n) = lambda(n) sigma_z(n),
sigma_z(n) = 1_{p^2 does not divide n for every prime p <= z},
z = ceil(ell^20),
H = exp(ell^(2/5)).
```

For each slope pair `alpha=(m,b)` with `m,b in I_Y`, put

```text
g = gcd(m,b), r=m/g, s=b/g, A=N/g.
```

Discard the fiber when `g` does not divide `N`.  Otherwise parameterize its exact solutions by

```text
r*d_t + s*a_t = A,
d_t = d0+s*t, a_t=a0-r*t,
I_alpha = {t : d_t,a_t in I_D}, M_alpha=#I_alpha.
```

Use the maximal available auxiliary-prime pool

```text
P_alpha = {p prime : z < p <= H and p does not divide r*s*A}.
```

Define the zero-usable-prime indicator

```text
L_alpha(n) = 1_{no p in P_alpha divides n}.
```

For the `K=1` marked reconstruction, the exact low-factor residual is

```text
R_alpha
  = sum_{t in I_alpha} b_z(d_t)b_z(a_t)
      1_{L_alpha(d_t)=1 or L_alpha(a_t)=1}

  = sum_t b_z(d_t)b_z(a_t)
      (L_alpha(d_t)+L_alpha(a_t)-L_alpha(d_t)L_alpha(a_t)).
```

No average over `N` is permitted.

## 2. The target to test

First test the unweighted mean square

```text
V_low(N) = sum_alpha |R_alpha|^2/M_alpha.
```

The strategically useful target is

```text
V_low(N) <= C * N^(2/3) * ell^B
```

for explicit absolute `C,B`.  Any fixed exponent `B` is numerically adequate at the frozen
threshold, subject to the exact application and ledger restoration described below.

For the diagnostic weight

```text
w_alpha=f_Y(m)f_Y(b), |w_alpha|<=ell^2,
```

also test

```text
V_low,w(N) = sum_alpha |w_alpha|^2 |R_alpha|^2/M_alpha
            <= C_w * N^(2/3) * ell^B_w.
```

Since the exact fiber count gives `S0=sum M_alpha<=5*N*ell`, the latter would imply

```text
|sum_alpha w_alpha R_alpha|/N
  <= sqrt(5*C_w) * N^(-1/6) * ell^((B_w+1)/2).
```

An `O(N polylog N)` bound for either mean square is not a pass.  It is the trivial scale and does
not establish the required cancellation.

## 3. Mandatory diagonal calculation

Expand

```text
V_low
  = sum_alpha (1/M_alpha)
      sum_{t,u in I_alpha} c_alpha(t)c_alpha(u),
```

where

```text
c_alpha(t)=b_z(d_t)b_z(a_t)
  1_{L_alpha(d_t)=1 or L_alpha(a_t)=1}.
```

Separate `t=u` before applying any estimate.  Report its exact or explicit upper scale and verify
that it is compatible with the proposed `N^(2/3) polylog(N)` target.

Do not call the diagonal a lower bound for the complete mean square: the off-diagonal terms in the
expanded square may be negative.  Its purpose is to calibrate the natural scale and detect an
impossible claimed power saving.

## 4. Exact off-diagonal object

Write `u=t+h`.  The four coefficient arguments are

```text
d, d+s*h, a, a-r*h.
```

The off-diagonal problem is therefore an average over admissible slopes of

```text
b_z(d)b_z(d+s*h)b_z(a)b_z(a-r*h)
```

with the corresponding low-factor indicators and the exact equation `r*d+s*a=A`.

The review must state precisely which variable is averaged by each proposed theorem.  A theorem
for an average over centers, arbitrary coefficient arrays, fixed shifts, or unrestricted intervals
does not automatically apply to this growing-slope, fixed-center family.

## 5. Sieve expansion requirements

The indicator has the exact formal expansion

```text
L_alpha(n) = sum_{q | n, q | product(P_alpha)} mu(q).
```

Any truncation, beta-sieve weight, or Selberg majorant used in its place must specify:

1. its level and dependence on `alpha`;
2. the sign of every replacement inequality after the square is expanded;
3. the coefficient norm introduced by the replacement;
4. the treatment of primes removed because they divide `r*s*A`;
5. the total remainder after summing slopes and shifts.

An upper-bound sieve for the absolute support is not enough by itself.  The existing audit proves
that the support's absolute weighted mass exceeds the nominal Goldbach reserve on admissible
power-of-two centers at the proposed diagnostic normalization.  The eventual Vaughan-remainder
identity must still restore the actual transfer coefficient before this is called a ledger
comparison.

## 6. Required stress tests

The proposed proof must pass all of these tests.

### Constant-one test

Replace `b_z` by `1`.  The argument should expose that no Möbius cancellation remains and should
not falsely return the desired saving.

### Zero-shift test

The `h=0` contribution must agree with the separately calculated diagonal.

### Degenerate-form test

Identify shifts and slopes for which two of

```text
d, d+s*h, a, a-r*h
```

coincide or acquire a substantial common factor.  Bound those strata explicitly rather than
placing them into a generic four-point theorem.

### Small-common-factor test

Do not assume `gcd(r*s,A)=1` for the complete application.  The finite diagnostic shows that
controlled noncoprime fibers can carry most of the signed total at some centers.  A coprime theorem
must be accompanied by an honest bound or separate theorem for the remaining fibers.

### Fixed-center test

No averaging over `N` may be used to replace the theorem required at the specified center.

## 7. Numerical evidence to reproduce, not assume

The current diagnostic is

```text
scripts/experiments/route_a_long_mobius_fibers.py
```

For the explicitly surrogate pool `7<p<=997`, four tested centers from `7077888` through
`500000000` gave:

```text
0.63 <= V_low/V_total <= 0.71,
1.01 <= N^(1/3)*V_low/S0 <= 1.79.
```

The both-zero component contributed roughly `17%` to `22%` of the total mean square.  These values
are compatible with diagonal-scale cancellation inside the omitted support.  They are not evidence
for a uniform theorem, because the practical cutoff is a surrogate and the tested centers are
small.

Reproduce the definitions before using these numbers.  Distinguish signed sums, absolute support
mass, unweighted mean square, and weight-adapted mean square.

## 8. Relation to the marked source

The exact factorial reconstruction and its coefficient bounds may be used.  The existing
positive-order marked theorem may be used only for mark orders and prime ranges it actually covers.

It does not control `R_alpha`.  Do not:

* divide by a mark weight that vanishes;
* infer signed cancellation from low support density;
* relabel comparison fibers at center `A*D_C` as fibers at center `A`;
* extend fixed mark-order estimates to orders growing with `N` without proof;
* or count a norm-one zero-order raw reflection as a saving.

## 9. Ledger obligation

Passing the mean-square test would not by itself close Route A.  The final report must state the
exact identity connecting the selected long-Mobius block to the Vaughan hard remainder and restore:

```text
marked terms,
low-factor residual,
comparison terms at their real centers,
exceptional strata,
reconstruction coefficients,
and every logarithmic slope weight.
```

Only then should the resulting constant be compared with the current factor-two deficit.  Until
that identity exists, describe a successful low-factor theorem as a new analytic input, not as a
closed Goldbach ledger.

## 10. Stopping rule

Return **FAIL** or **UNRESOLVED** and stop this branch if the best justified reduction:

1. takes absolute values over `R_alpha`;
2. yields only `O(N polylog N)` for `V_low`;
3. invokes a four-point cancellation theorem whose hypotheses do not cover the growing affine
   forms;
4. averages over the center;
5. assumes the desired low-factor cancellation;
6. or loses the required saving after coefficient norms and slope summation are restored.

The assignment passes only if it identifies a genuine theorem-level advantage over the complete
unmarked problem and quantifies that advantage at the fixed center.
