# Structural audit of the X0 certificate

## Verdict

The X0 certificate contains a real and reusable arithmetic structure. It is not a
large collection of unrelated finite checks. On even inputs, the moduli `r` and
`2*r` define the same Ramanujan observable for odd `r`. After quotienting by this
alias, the periodic-main correlation matrix is almost diagonal, and its energy is
overwhelmingly concentrated in the odd cores `3`, `5`, and `7`.

This does **not** repair Route A. It explains the truncation-energy certificate,
not the missing positive prime-companion estimate. The proper outcome is to retain
this as a standalone structural result and stop treating the X0 build as a route
to the failed positivity target.

The exact audit is reproduced by:

```sh
python3 scripts/experiments/route_a_x0_certificate_structure_audit.py
```

The script reads the locally retained exact payloads under `.cache/`; it does not
rebuild any generated Lean certificate.

The formal concentration theorem and its axiom report are reproduced by:

```sh
lake build +Goldbach.Cert.MajorArcModules.Q0SigmaTruncLowModeConcentration:olean
lake env lean scripts/experiments/route_a_x0_certificate_structure_audit.lean
```

The theorem uses the same finite `native_decide` packet as the existing scalar
bounds. Its reported axioms are `propext`, `Classical.choice`,
`Lean.ofReduceBool`, `Lean.trustCompiler`, and `Quot.sound`; it introduces no
project-specific axiom or `sorry`.

## 1. The quotient mode space

For odd squarefree `r`, the even-input identities collapse the two moduli `r` and
`2*r`. The repository now states this uniformly as

```text
sigma_trunc_Q0 (2*n)
  = sum_r oddWeightRat(r) * ramanujanR r n,
```

where the coefficient has multiplicity two when `2*r <= Q0`. See
`Q0SigmaTruncEvenDivisor.sigma_trunc_Q0_even_eq_oddWeightRat` and
`Q0SigmaTruncScalarBounds.evenMultiplicity`.

Thus the effective modes are odd squarefree cores, not all moduli separately.
Equivalently, the original feature map factors through the relation

```text
q ~ 2*q  (q odd).
```

This is an exact arithmetic identity for every even argument. It is not fitted to
`X0`.

## 2. What the X0 periodic-main data shows

The active support has 3,042 moduli. Of the ordered pairs, 49,528 have at least one
complete period block in the `X0` window. Among those, 18,870 periodic-main records
are zero and 30,658 are nonzero. The restriction to full blocks is important: the
remaining millions of pairs should not be described as arithmetic zeros.

The 30,658 nonzero records split as follows:

| class | records | signed total | absolute total |
|---|---:|---:|---:|
| dyadic aliases `(r,2r)` and `(2r,r)` | 2,028 | 37602.763328571458 | 37602.763328571458 |
| all other records | 28,630 | -0.002083204379 | 0.018723740030 |
| all records | 30,658 | 37602.761245367079 | 37602.782052311488 |

The dyadic alias records contain **99.999950207%** of periodic-main absolute mass.
Every such record is positive, and all 1,014 orientation pairs have exactly equal
values. The signed off-orbit correction is about `5.54e-8` of the dyadic total.

The correct matrix interpretation is therefore:

1. Before quotienting, every odd core produces a duplicated `2 x 2` Gram block.
2. After quotienting, the periodic-main matrix is essentially diagonal.
3. The small off-orbit part is a finite-window mean-defect correction, not a second
   energy-bearing population.

## 3. Low-mode concentration

Inside the dyadic total, the first modes dominate:

| odd core | periodic-main contribution | share of dyadic absolute mass |
|---:|---:|---:|
| 3 | 31237.500000000000 | 83.072352229% |
| 5 | 3906.250624750075 | 10.388200970% |
| 7 | 1156.944513833353 | 3.076753971% |
| 15 | 486.328368066826 | 1.293331460% |
| 11 | 249.700015974410 | 0.664046985% |

The cumulative shares are:

| odd-core cutoff | share |
|---:|---:|
| `r <= 7` | 96.537307169% |
| `r <= 25` | 99.601199793% |
| `r <= 100` | 99.969344030% |
| `r <= 1000` | 99.999805723% |

This concentration is not peculiar to the `X0` endpoint decomposition. The exact
full-period variance is

```text
sum_{r > 1, r odd squarefree} t_r^2 / phi(r)^3,
```

and the `r = 3,5,7` terms total

```text
1/2 + 1/16 + 1/54 = 251/432.
```

Since the checked total variance is below `0.601924`, these three modes account
for more than `96.52%` of the full-period variance, uniformly rather than only at
`X0`. This is formalized in
`Q0SigmaTruncLowModeConcentration.lowModeVarianceRat_gt_9652_permyriad`.

## 4. Periodic main and boundary are two pieces of one Gram entry

For a dyadic alias pair, the two centered observables are identical on the even
window. Their complete covariance must therefore equal the diagonal energy. The
certificate obscures this by splitting the covariance into periodic-main blocks
and a boundary remainder. The first three modes reconstruct exactly:

| core | periodic main, both orientations | boundary, both orientations | result |
|---:|---:|---:|---:|
| 3 | 31237.500000000000 | 18.750000000000 | `2 * 15628.125` |
| 5 | 3906.250624750075 | 3.123750374900 | `2 * 1954.687187562487...` |
| 7 | 1156.944513833353 | 0.115601921274 | `2 * 578.530057877313...` |

The audit checks these identities as exact rationals. This shows that the boundary
is not new spectral mass; it is the endpoint remainder needed to reconstruct the
same duplicated Gram block.

The whole active boundary is nevertheless cancellation-heavy:

```text
signed total   = -25.284933542674991573...
absolute total = 597.953421599744232634...
ratio          = 4.228579122%
```

Multiplier families preserve many dyadic aliases locally, but the complete
boundary is not low-rank or positive. It should be treated as a signed divisibility
discrepancy, not as a source of a Goldbach lower bound.

## 5. The off-orbit correction also factorizes

The existing non-dyadic LCM payload contains 27,657 ordered records after removing
row five. Every record agrees exactly with a product of two one-variable window
weights and an LCM-fiber scalar. Its audit reports:

```text
mean_product_mismatch_count = 0
dyadic_weight_mismatch_count = 0
lcm_total_mismatch_count = 0
exact_totals_match = true
```

There are 1,855 LCM fibers and 1,489 dyadic odd-core orbits. This is not a single
rank-one matrix because the scalar varies with the LCM, but it is an
LCM-weighted product kernel rather than arbitrary pair data.

## 6. What has and has not been learned

The substantive structural statement is:

> The fixed Ramanujan truncation on even integers has an effective odd-core mode
> basis. Its full-period Gram form is diagonal in that basis, more than 96.52% of
> its variance lies in three modes, and the finite-window deviations are an
> LCM-fibered mean defect plus a signed endpoint discrepancy.

This explains why the X0 certificate closed, why most generated pair files were
mathematically redundant, and why the later uniform proof could replace the huge
certificate with divisor moments and a small number of cancellations.

It is not a theorem that primes have the required positive companion, a new lower
sieve, or a repair of the one-large-prime row. It supplies no answer to the
factor-two sieve obstruction and no route around the fixed-bank counterexample.
Accordingly, it is interesting structure in the truncation model, but not evidence
that Route A remains a viable Goldbach proof-completion project.
