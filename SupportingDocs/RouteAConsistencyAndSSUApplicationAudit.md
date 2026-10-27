# Route A consistency and SSU application audit

Date: 2026-10-26

## Decision

Suspend Route A as a proof-completion project on its current theorem surfaces. Do not generate a
new remainder certificate, extend the finite base, or add another conditional closure record until
a concrete arithmetic application demonstrates a strict quantitative advantage over the trivial
bound.

The large `Q0MinorZeroModeNormalizedAverageX0Cert` build may be completed as a finite diagnostic
and regression artifact. It is not a dependency of a valid uniform Route A closure theorem.

This decision has three independent causes:

1. The fixed-width prime bank has arbitrarily large empty supports, so it cannot support the old
   universal positive-mean target.
2. The finite-cutoff two-sided norm-and-budget certificate forces an eventual upper bound on the
   full balanced von Mangoldt convolution that conflicts with fixed-modulus arithmetic-progression
   averages.
3. The inspected Q0/SSU chain does not contain the exact arithmetic extraction needed to apply a
   proved SSU theorem to the balanced remainder. A separate exact Vaughan extraction has now been
   built, but its hard Type-II residual does not match any proved repository SSU application, and
   the global all-array interface has no intrinsic pointwise saving.

These conclusions do not invalidate the checked exact identities and major-arc estimates listed
below. They do invalidate the claim that Route A merely awaits completion of the present
certificates.

## Preserved results

The following machinery remains mathematically and formally useful:

- the complete prime and von Mangoldt convolution definitions;
- exact Fourier coefficient and circle-split identities;
- balanced interval support and the seam-safe fundamental interval;
- the finite-cutoff arithmetic-geometric major model;
- the BMOR-based major-arc approximation, subject to its declared analytic input;
- the exact higher-prime-power transfer and its explicit allowance;
- the exact finite Vaughan identity and fixed-center bilinear mask identity;
- the exact signed split into a short Type-I--prime correlation and one hard residual;
- the finite `X0` certificate as a diagnostic of the pinned observable;
- the standalone SSU library contracts on the coefficient families named in their theorem types.

None of these results by itself proves a positive lower bound for every specified even center.

## Retired proof targets

### Fixed-bank positive mean

The fixed bank can be empty at arbitrarily large scales. Its universal positive-mean target is
false. A completed finite-scale certificate cannot repair that quantifier failure.

### Two-sided finite-cutoff remainder closure

`BalancedFiniteCutoffClosureCertificate` requires both

```text
norm remainder <= remainderError
majorError + remainderError + primePowerAllowance < finiteCutoffMain.
```

The Lean theorem

```text
RouteABalancedFiniteCutoffObstruction.convolution_lt_two_main_sub_power
```

checks that those fields force

```text
balancedVonMangoldtPairConvolution
  < 2 * balancedFiniteCutoffMain - primePowerAllowance.
```

For cutoff two, the elementary Parseval estimate gives `finiteCutoffMain <= 2N`, so the old
certificate would imply `convolution < 4N` eventually. Fixed-modulus PNT-in-progressions averaging
for `N = 0 mod 210` gives limiting average ratio

```text
210 / phi(210) = 35 / 8 > 4.
```

Therefore the two fields cannot be populated simultaneously. Increasing the threshold does not
help. Increasing to another fixed cutoff also does not repair the same two-sided strategy: fixed
even primorial classes make the average convolution-to-`N` ratio unbounded, while a fixed-cutoff
model remains `O_Q(N)`.

The Lean module

```text
Goldbach/Cert/MajorArcModules/RouteABalancedFiniteCutoffObstruction.lean
```

formalizes the order-theoretic implication and the contradiction from two explicit propositions:
the cutoff-two model cap and the arithmetic-progression witness. The repository does not yet
formalize the full fixed-modulus PNT averaging lemma, so those two arithmetic propositions remain
inputs to the final Lean contradiction theorem. This limitation is intentional and recorded rather
than hidden behind a new axiom.

### Universal Q0 calibration

The former `ssu_minor_energy_calibration` asserted fixed calibration caps for every tuple satisfying
monotone upper-bound conditions. Enlarging a valid witness preserves those upper bounds but can
make the fixed caps false.

`Q0MinorCalibrationUniversalContradiction.lean` proves in Lean that the former universal
proposition contradicts the existing `q0MinorDyadicGramDecayPoly_exists` axiom. The universal axiom
has been removed. The compatibility module now accepts calibration for one chosen witness as an
explicit hypothesis.

The active pinned provider does not use that compatibility module. It obtains its cap-16 bound from
`Q0MinorSSUFromCert.nonzeroModeEnergyBound` and the checked conversion in
`Q0MinorEnergyFromLedgerCert`.

## Dependency audit

The axiom audit in `scripts/experiments/route_a_consistency_audit.lean` separates the surviving
surfaces:

| Surface | Dependency status |
| --- | --- |
| Exact balanced remainder integral identity | Core logical axioms only |
| Bad upper-bound consequence of the retired closure record | Inherits the declared BMOR input used by the closure adapter |
| No-cutoff-two theorem | Same, plus explicit cap and progression hypotheses |
| Universal-calibration contradiction | Core axioms plus `q0MinorDyadicGramDecayPoly_exists` |
| Global `Step34ProdSum` no-saving theorem | Core logical axioms only |
| Exact finite Vaughan identity | Core logical axioms and Mathlib arithmetic-function identities only |
| Bilinear fixed-center mask identity | Core logical axioms only |
| Exact `H(S,S) = H(A,S) + H(hard,S)` split | Core logical axioms only |
| Type-I and hard-residual recombination interface | Core logical axioms only; analytic estimates remain explicit hypotheses |
| `vaughanLambda_suppliesF3Energy` | Formally proved, but content-free because its target predicate is `True` |
| `globalSSU_of_vaughan` | Depends on abstract packet/sequence axioms and `overlapSummationLedger_of_vaughan` |
| `rawFullPacketLedger_1_1` | Depends on `rawMinorPacketEnergy_canon` through the legacy raw-ledger route |

The exact convolution, circle, major-model, and prime-power results should remain available. Results
that depend on the retired closure assumptions or legacy packet-energy/calibration assumptions must
not be presented as progress toward an unconditional Goldbach endpoint.

## Bounded SSU application test

### Selected arithmetic term

The test selected the exact cutoff-two complementary Fourier coefficient

```text
balancedVonMangoldtAfterMajorUpToRemainder L N 2 1.
```

Lean already proves that this equals

```text
balancedFiniteCutoffRemainderIntegral L N 2 1.
```

This is a legitimate Route A term: it belongs to an exact decomposition of the full balanced von
Mangoldt convolution and retains the specified center through the phase `e(-N alpha)`.

### Required application chain

A successful worked application would need all of the following:

1. An exact Vaughan, Heath-Brown, or comparable identity for the balanced coefficients in this
   remainder integral.
2. Explicit Type I, Type II, and residual terms, with supports and endpoint corrections proved.
3. An exact map from one Type II term to the coefficient array of a proved restricted-family SSU
   theorem.
4. Proofs of every support, tube, scale, phase, and coefficient-energy hypothesis.
5. Restoration of all coefficient norms, dyadic-shell counts, packet constants, and normalization
   factors.
6. Recombination at the original Fourier coefficient for the fixed integer `N`.
7. A numerical comparison showing a strict improvement over the corresponding trivial bound.

### Corrected extraction result

The application no longer stops at step 1. The following modules now supply an independent,
non-placeholder extraction:

- `RouteABalancedVaughanIdentity.lean` proves the exact arithmetic-function identity

  ```text
  Lambda = Lambda_<=v + mu_<=u * log
    - mu_<=u * zeta * Lambda_<=v
    + mu_>u * zeta * Lambda_>v.
  ```

- `RouteAFiniteWeightBilinearCircle.lean` proves the fixed-center bilinear circle identity and
  exact set/complement mask removal for arbitrary finite real weights.
- `RouteABalancedVaughanFixedCenter.lean` keeps the second von Mangoldt factor intact and proves

  ```text
  H(S,S) = H(A,S) + H(hard,S),
  ```

  where `A = mu_<=u * log` and `hard` is the exact signed combination of the other three Vaughan
  terms. It also proves the exact prime-residue formula

  ```text
  C_N(A,S) = sum_{d <= u} mu(d)
    sum_{p in [L,N-L], p = N (mod d)} Lambda(p) log((N-p)/d).
  ```

  The finite change of variables and all support endpoints are checked in Lean.
- `RouteABalancedVaughanTypeIInterface.lean` checks how a full Type-I progression estimate and a
  retained-arc estimate combine, states the required maximal Bombieri--Vinogradov selector
  interface, and leaves the hard residual as an explicit one-sided input. The progression error is
  also split exactly into a reduced-residue coprime term and a noncoprime contribution, with a
  checked theorem recombining independent bounds for the two pieces. A support theorem verifies
  that every nonzero von Mangoldt term in the latter piece is a prime power noncoprime to its
  modulus.

These theorems do not depend on the legacy Q0 Vaughan scaffold.

### What the legacy Q0 source provides

The legacy packet chain still does not advance the new extraction through a proved SSU estimate:

- `Q0VaughanDecomposition.lean` explicitly states that it does not prove the full analytic Vaughan
  identity.
- `SmoothDyadicCutoff` is currently `True`.
- `isVaughanTypeIIBlockFamily` is currently `True`.
- `vaughanLambda_suppliesF3Energy` constructs a singleton block with `W = 0`; it does not identify
  any sum with `Lambda` or with the balanced remainder.
- `packetTransform` and `sequenceMass` are axioms on this interface.
- `globalSSU_of_vaughan` depends on the axiom `overlapSummationLedger_of_vaughan`.
- `rawFullPacketLedger_1_1` is an alias for the axiom-backed
  `rawLedger_canon_one_one_axiom`.
- `rawFullPacketLedger_1_1_of_globalSSU` does not use its `hSSU` argument.

There is consequently still no honest map from the extracted hard term to the legacy packet
objects. Filling that gap with a record field would assume the desired Type-II application rather
than demonstrate it.

### Positive fixed-center Type-I application

The specialist review identifies a genuine application of maximal Bombieri--Vinogradov to the
short Type-I--prime term. The averaging is over moduli `d <= N^(1/3)`, while the residue
`N mod d` may remain fixed because the theorem is maximal over reduced residues. Partial summation
should give

```text
C_N(A,S) = M_A(N) + O_K(N / log(N)^K),
```

and separate `q=1,2` arc analysis should give the corresponding retained-arc expression. This
would control the signed combination `H(A,S)` without passing through full complementary energy.

The exact finite progression formula is now formalized. The analytic estimate is not. In
particular, the repository's explicit BMOR input only covers each modulus `d <= 100000`; it cannot
replace an average over the unbounded range `d <= N^(1/3)`. The repository still needs an effective
maximal Bombieri--Vinogradov theorem, noncoprime prime-power control, explicit constants, and a
computable threshold before this term can be joined to a finite base. The exact interval
partial-summation identity and its endpoint/variation bound are now checked against the new
per-modulus error. Therefore this is a credible partial theorem, not a completed Route A estimate.

### Global-interface control test

`SSU/Engines/TypeIIToeplitzGlobalNoSavingAudit.lean` proves that every global
`Step34ProdSum X H T` witness on a nonempty tube satisfies

```text
T.card <= C * sqrt(H / X).
```

The proof chooses frequency zero and the constant-one coefficient array. Thus the displayed
`sqrt(H/X)` factor in the all-array theorem cannot itself beat the trivial per-frequency bound; its
constant must absorb at least the tube cardinality. A useful Goldbach application must use a
genuinely restricted arithmetic family, an integrated estimate, or additional structure not
present in the global interface alone.

### Result and stopping rule

The extraction and mask-removal stages now pass, and one substantial Type-I subfamily has a
credible conventional fixed-center estimate. The application still fails at the hard residual:
the long-modulus/Type-II coefficient has not been converted to the input of an applicable theorem,
and no one-sided saving has been demonstrated after recombination. This preserves the agreed
stopping condition:

> Develop the effective Type-I estimate as a bounded test, but stop before further closure
> machinery unless the actual hard residual can be matched to a theorem that produces a visible
> one-sided saving.

No additional Route A certificate is justified by the present interfaces.

## The theorem needed to resume

The next candidate must be a genuine arithmetic theorem, not a new wrapper. The algebraic
decomposition in item 1 is now checked. The remaining work must provide:

1. an effective Bombieri--Vinogradov/partial-summation theorem for the extracted Type-I--prime
   correlation, including its retained `q=1,2` arc model;
2. a restricted-family SSU, dispersion, spectral, or Kloosterman estimate for the actual extracted
   hard coefficients;
3. explicit coefficient norms, factorability/smoothness checks, and shell-summation estimates;
4. a one-sided bound for the hard Fourier coefficient, since the two-sided fixed-cutoff
   target is impossible; and
5. constants that pass the full major-error and prime-power budget.

A specialist should first decide whether such a pointwise, fixed-center theorem is plausible and
genuinely stronger than standard large-sieve/energy estimates. If the best available application
still yields only the trivial bound or assumes its own cancellation, Route A should remain
suspended.

## Operational consequence

- Do not commission another generated closure certificate.
- Do not extend the finite base for this route.
- Do not select a new empirical constant and call it a theorem target.
- Keep the current large certificate only as a finite diagnostic/regression artifact.
- Preserve and maintain the independent exact identities and major-arc infrastructure.
- Follow `SupportingDocs/RouteABalancedVaughanFixedCenterPlan.md` for the bounded Type-I test.
- Reopen Route A only after the hard-residual application test passes with explicit constants.
