# Stage 4 Fixed-Target Four-Point Atlas

Date: 2026-11-03

Status: **initial computational evidence; no asymptotic estimate proved**

## Purpose

This experiment implements the fixed-target primitive Type-III/Type-III
correlation isolated in *Stage 4 - Investigation 12: diagonal extraction and
the genuine four-point obstruction*.  Its purpose is to locate arithmetic
structure that could guide a proof of

\[
  \mathscr G_{R,R'}(N)
  \ll \frac{X^2}{X^{1/4}(\log X)^3},
\]

uniformly in each populated box and each even `N` in `[X,2X]`.  The stronger
research target replaces `(log X)^3` by `(log X)^5` and asks for a uniform
little-o estimate.

This is new Stage 4 research.  It is not the archived Route A certificate or
its former bridge problem.

## Reconciliation With The Stage 4 Roster

The Stage 4 manuscript defines

\[
  \gamma_j(n)=
  \sum_{am=n,\ a>U}
    \mu(a)\beta_V(m)\vartheta(a/A_j)\omega(am/X),
  \qquad A_j=2^j.
\]

In the primitive prime-cofactor sector,

\[
  m=rp,\qquad p>V\text{ prime},\qquad r<V,
  \qquad \beta_V(m)=\log p.
\]

Thus Investigation 12's abstract weights are the block-specific functions

\[
  \mathsf W_m(a)=\vartheta(a/A_j)\omega(am/X),
  \qquad
  \mathsf W'_n(b)=\vartheta(b/A_k)\omega(nb/X).
\]

The script analyzes all `j,k` satisfying

\[
  X^{3/4}/2\le 2^j,2^k<2X^{3/4},
\]

and partitions the unique short cofactors `r,r'` into sharp dyadic boxes.
It retains `(m,n)=1`, excludes the proper-prime-power sector, and uses
`U=V=floor(X^(1/6))` computed by exact integer arithmetic.

## Frozen Smooth Model

The manuscripts leave the admissible smooth functions unfixed.  For a
reproducible experiment, this audit chooses one explicit admissible model.

Let

\[
 s(u)=\frac{e^{-1/u}}{e^{-1/u}+e^{-1/(1-u)}}\quad(0<u<1),
\]

extended by zero and one at the respective ends.  Let `chi(t)` equal one for
`t <= 1`, equal `1-s(t-1)` for `1<t<2`, and equal zero for `t >= 2`.  Set

\[
  \vartheta(t)=\chi(t)-\chi(2t).
\]

Then `vartheta` is nonnegative, supported in `(1/2,2)`, and

\[
  \sum_{j\in\mathbb Z}\vartheta(2^{-j}t)=1\qquad(t>0).
\]

The product cutoff is

\[
  \omega(t)=
  \begin{cases}
  \exp\!\left(4-\dfrac1{(t-1/4)(5/4-t)}\right),&1/4<t<5/4,\\
  0,&\text{otherwise}.
  \end{cases}
\]

The implementation's partition-of-unity test had maximum detected error zero
on its logarithmic validation grid.  Results apply to this frozen model only;
smooth-cutoff robustness remains to be tested.

## Exact Fast Collision Decomposition

For fixed `m`, group the weighted representation records by `n`.  A record
has endpoints `{a,b}` and signed weight

\[
 v=w_n\mu(a)\mu(b)\mathsf W_m(a)\mathsf W'_n(b).
\]

Write `T_n` for the sum of record weights, `E_{n,x}` for the sum over records
containing endpoint `x`, and `P_{n,{x,y}}` for the sum over records having the
unordered endpoint pair `{x,y}`.  After excluding records with `a=b`, exact
inclusion-exclusion gives

\[
\begin{aligned}
 G_m={}&\left(\left(\sum_nT_n\right)^2-\sum_nT_n^2\right)\\
 &-\sum_x\left(\left(\sum_nE_{n,x}\right)^2-\sum_nE_{n,x}^2\right)\\
 &+\sum_{\{x,y\}}\left(\left(\sum_nP_{n,\{x,y\}}\right)^2
                    -\sum_nP_{n,\{x,y\}}^2\right).
\end{aligned}
\]

This computes the four-distinct term without quadratic enumeration of all
record pairs.  Replacing every `v` by `abs(v)` computes its absolute envelope.

At `X=4096`, the optimized result was checked independently by direct ordered
pair enumeration.  The maximum discrepancy was `8.88e-16`.  The checks
`M=D+C+G` and `W_R M-|S|^2 >= 0` also passed.

## Initial Results

The random-target runs use deterministic seed `20261103`.  The table reports
the worst populated box for each target, followed by distribution summaries
over the sampled targets.

| `X` | targets | median `max G/T3` | 90th percentile | worst `max G/T3` | worst `max G/T5` | worst absolute envelope `/T3` |
|---:|---:|---:|---:|---:|---:|---:|
| 262,144 | 101 | 0.000270 | 0.002336 | 0.011202 | 1.743727 | 3.303858 |
| 1,000,000 | 101 | 0.000247 | 0.001620 | 0.004640 | 0.885628 | 4.574321 |
| 4,000,000 | 51 | 0.000097 | 0.000559 | 0.000966 | 0.223262 | 6.178399 |

Here

\[
 T_3=\frac{X^2}{X^{1/4}(\log X)^3},\qquad
 T_5=\frac{X^2}{X^{1/4}(\log X)^5}.
\]

The important observation is not merely that `G` is small.  The absolute
envelope grows relative to `T3`, while the signed residual decreases across
these sampled scales.  The experiment is therefore detecting cancellation,
not only sparse support or a shrinking unsigned sum.

For `X=10^6`, the median ratio of the block-summed signed residual to the
block-summed absolute envelope was `2.20e-4`; its sampled maximum was
`1.24e-3`.  Restricting attention to blocks carrying at least one percent of
the target's largest envelope, the median worst ratio was `0.00479`.

These finite values do not establish a uniform constant, a power saving, or a
little-o theorem.  In particular, the `T5` maximum exceeds one at the smallest
sampled scale.

## First Structural Localization

The positive upper tail is not spread evenly across cofactor boxes.

- At `X=10^6`, the top positive box had `R'=1` for 84 of 101 targets.
- Among the 20 targets with largest positive normalized residual, 18 had
  `R'=1`.
- The single largest sampled value occurred in `(j,k,R,R')=(15,14,1,1)`.
- Coarse target features such as the 2-adic valuation, number of prime
  factors, divisor count, and number of prime factors at most 19 had only weak
  sample correlations with the logarithm of the residual (absolute Pearson
  correlations below `0.15`).

Thus the next promising surface is the orientation in which the second
prime-cofactor is itself prime (`r'=1`), especially the adjacent block pair
`(j,k)=(15,14)` at `X=10^6`.  Some of this asymmetry may come from applying
Cauchy-Schwarz in the first cofactor variable, so the swapped orientation must
also be compared before proposing a theorem.

## Reproduction

Run the small brute-force validation:

```bash
python3 scripts/experiments/exp_stage4_fixed_target_four_point_atlas.py \
  --x 4096 --target-count 3 --target-mode random --brute-limit 2000 \
  --output /tmp/stage4-four-point-small.json
```

Run the `X0` atlas:

```bash
python3 scripts/experiments/exp_stage4_fixed_target_four_point_atlas.py \
  --x 1000000 --target-count 101 --target-mode random \
  --target-seed 20261103 --brute-limit 0 \
  --output /tmp/stage4-four-point-X0.json
```

## Next Bounded Investigation

1. Split the `R'=1` contribution by `(m,n1,n2)` geometry, especially
   `gcd(n1,n2)`, relative shift, and the two affine slopes.
2. Compare the Cauchy orientation with the transposed orientation to separate
   intrinsic arithmetic concentration from a second-moment artifact.
3. Repeat with at least two materially different admissible smooth partitions.
4. Increase the scale and target sample while tracking the upper tail of
   `G/T3` and `G/T5`, not only averages.
5. Stop if cancellation disappears under smooth-cutoff changes, occurs only
   after summing boxes or targets, or is driven by a vanishing absolute
   envelope.

Only after those tests should a paper theorem be formulated.  Even a bound for
this primitive central sector would still need to be reconciled with proper
prime powers, overlap terms, the remaining Type-II/III ranges, and the full
Stage 4 PSB ledger.
