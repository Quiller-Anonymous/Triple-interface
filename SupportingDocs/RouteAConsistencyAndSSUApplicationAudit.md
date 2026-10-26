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
   proved SSU theorem to the balanced remainder. Its global all-array interface also has no
   intrinsic pointwise saving.

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

### What the current source provides

The chain stops at step 1:

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

There is consequently no honest term to which coefficient norms and SSU constants can yet be
restored. Filling that gap with a record field would assume the desired application rather than
demonstrate it.

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

The worked application fails before a quantitative SSU estimate can be applied. It would require
the missing cancellation/application link as an assumption. This triggers the agreed stopping
condition:

> Stop extending the Goldbach closure machinery until a concrete arithmetic application produces
> a visible nontrivial saving.

No additional Route A certificate is justified by the present interfaces.

## The theorem needed to resume

The next candidate must be a genuine arithmetic theorem, not a new wrapper. At minimum it must
provide:

1. an exact phase-preserving decomposition of the balanced von Mangoldt remainder into explicit
   Type I, Type II, and controlled residual terms;
2. a restricted-family SSU or other bilinear estimate for the actual extracted Type II arrays;
3. explicit coefficient-energy and shell-summation estimates;
4. a one-sided bound for the resulting Fourier coefficient, since the two-sided fixed-cutoff
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
- Reopen Route A only after the worked arithmetic application test passes.
