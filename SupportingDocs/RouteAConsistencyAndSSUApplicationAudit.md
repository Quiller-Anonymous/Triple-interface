# Route A consistency and SSU application audit

Date: 2026-10-27

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
| Signed Mobius/totient six-bound | Finite arithmetic-function identities and a finite Euler-product estimate only; no project analytic axiom |
| Exact character expansion and primitive-character fiber partition | Core logical axioms only; induced-character correction remains explicit |
| Logarithmic conductor-weight bound | Finite Abel summation plus the signed Mobius/totient six-bound; no project analytic axiom |
| Direct large-conductor `1/R` reduction | Exact absolute lift sum, finite Stieltjes control, and an explicit reciprocal-totient prefix input; core logical axioms only |
| Reciprocal-totient prefix `<= 6(1+log K)` | Exact finite hyperbola identity, positive squarefree Euler product, and Mathlib's harmonic bound; no project analytic axiom |
| Explicit small/large hybrid Type-I endpoint | Reciprocal-totient input discharged; conductor stability and character estimates remain theorem arguments |
| Represented-fiber Type-I endpoint | Exact sum over the primitive keys actually represented by `primitiveCharacter`; removes conductor stability, with factor-three endpoint cost and factor `18(1+log u) log N/R` on the large range; character estimates remain theorem arguments |
| Squarefree conductor transport | A primitive character lifted to a squarefree multiple keeps its conductor and canonical primitive-character key; core logical axioms only |
| Localized signed/direct Type-I endpoint | Signed factor-two cost through `R`, unconditional represented factor-three cost above `R`; nonzero Mobius support supplies squarefreeness, so the restricted small-fiber completeness condition is proved; character estimates remain theorem arguments |
| Canonical finite `psi` maxima | Exact finite suprema construct `PrimitivePsiMaxInput` and feed the localized endpoint; the aggregate character estimates remain theorem arguments |
| Noncoprime Type-I progression bound | Explicit finite von Mangoldt-mass bound; core logical axioms only |
| Induced-character correction through partial summation | Exact decomposition plus an explicit finite norm majorant; core logical axioms only |
| Active-main correction and pointwise active-modulus reindexing | Exact finite identities; core logical axioms only |
| Active primitive-character reduction and sharp induced correction | Exact active primitive-main-minus-corrections identity; correction bounded by `u log(u) log(N)^2 / log 2`; core logical axioms only |
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

The first specialist review identified maximal Bombieri--Vinogradov as a sufficient input for the
short Type-I--prime term. A later review found a narrower candidate route: retain the outer Mobius
signs and group the progression errors by primitive conductor before taking absolute values. The
averaging remains over moduli `d <= N^(1/3)` at the fixed residue `N mod d`. Either route should
ultimately give

```text
C_N(A,S) = M_A(N) + O_K(N / log(N)^K),
```

and separate `q=1,2` arc analysis should give the corresponding retained-arc expression. This
would control the signed combination `H(A,S)` without passing through full complementary energy.

The exact finite progression formula is now formalized. A support audit also found and repaired an
interface mismatch: the earlier comparison main summed logarithms in the inactive region
`d > N - p`, although the residue sum has no such terms. Lean now checks an exact active-main
decomposition, modulus-dependent partial summation with endpoint `N - max L d`, and a pointwise
Fubini formula over precisely the active moduli. The old main and error are retained with an
explicit inactive-tail identity. The repository's explicit BMOR input only covers each modulus
`d <= 100000`; it cannot
replace an average over the unbounded range `d <= N^(1/3)`. No published unrestricted explicit
maximal theorem has yet been found in the exact required form. The signed-conductor proposal avoids
that stronger norm at the algebraic level: Lean now checks the constant-six Mobius/totient prefix
bound, exact active character expansion, canonical primitive-character partition, logarithmic
conductor-lift majorant, fixed-level fiber uniqueness, and the exact global
primitive-main-minus-corrections identity. The active induced correction is bounded sharply by
`u log(u) log(N)^2 / log 2`, matching the specialist's elementary correction allowance. The
conductor weight now also has its exact one-step cutoff identity and the telescoping estimate
`|W(a)| + |W(b)| + Var(W) <= 2 c_r log N`; in particular, the moving active cutoff creates no
uncontrolled boundary term. The noncoprime progression contribution has a proved coarse explicit
bound, and principal conductor-one lift completeness is checked.

The finite Stieltjes and global conductor-reindexing layer is now complete. Lean separates the
centered conductor-one family, reindexes every nonprincipal family, and proves that an ordinary
maximum bound for each cumulative primitive-character `psi` sum yields the complete short Type-I
estimate

```text
|Type-I prime convolution - active discrete main|
  <= principal allowance
     + (12 * N / phi(N) * log N) * primitive mean-value mass
     + induced-character allowance
     + noncoprime allowance.
```

This complete-fiber endpoint has no project analytic axiom. Its still-unproved inputs are explicit
theorem arguments: general conductor stability for `changeLevel`, a principal `psi` maximum, and
an effective bound for the conventional weighted primitive-character mass.

A subsequent direct represented-fiber construction removes the conductor-stability argument from
the valid proof path. Instead of asserting that every multiple of a primitive conductor occurs, it
sums only the primitive keys and lifts actually represented by the canonical Mathlib map. Lean
checks the exact principal-plus-represented-minus-induced decomposition, finite Stieltjes control,
and the original Type-I convolution endpoint. The direct endpoint/variation cost has constant
three rather than two. Its conventional all-conductor factor is
`18 * (1 + log u) * log N`, and its split large-conductor factor is
`18 * (1 + log u) * log N / R`. Thus conductor stability is optional sharpening, not a blocking
assumption. Effective principal, small-conductor, and large-conductor character bounds remain
genuine analytic obligations.

The localized hybrid is now the strongest theorem surface that avoids assuming global conductor
stability. `RouteABalancedVaughanLocalizedHybrid.lean` uses the complete signed fiber estimate only
for represented keys of conductor at most `R`, where its finite completeness predicate ignores
every modulus with zero Mobius coefficient. Above `R`, the hybrid switches to the unconditional
direct represented-fiber estimate. Thus the small range keeps cost two, while only the large-range
coefficient changes from 12 to 18.

The restricted completeness condition is no longer an assumption. In
`RouteADirichletCharacterConductorTransport.lean`, Lean proves that factor-through levels are
closed under gcd when the ambient level is squarefree. It follows that changing the level of a
primitive character to a squarefree multiple preserves both its conductor and its canonical
primitive-character key. Since `moebius d != 0` implies `Squarefree d`, this proves
`PrimitiveCharacterSupportedChangeLevelStable` and then
`RepresentedConductorLiftCompleteUpTo L N u R` for all parameters. The final localized theorem
`abs_typeIPrimeConvolution_sub_activeMain_le_localizedHybridMeanValueAllowance_unconditional`
carries the split through the principal, induced-character, noncoprime, and original-convolution
recombination layers without a conductor-stability or completeness premise. Its axiom audit reports
only Lean's standard logical axioms.

`RouteABalancedVaughanCanonicalPsiMax.lean` additionally replaces the abstract maximal-input
witness by exact finite suprema over `Finset.Icc (L - 1) (N - L)`. The canonical record and its
localized endpoint are proved with only Lean's standard logical axioms. This does not prove a
numerical character estimate; it makes the remaining small- and large-conductor hypotheses refer
to concrete repository expressions rather than an arbitrary witness record.

The numerical script now audits both routes. At `log log N = 100`, the localized route changes the
large term from `5.792008651388e-193` to `8.688012977081e-193`, while the total remains
`8.482782076783e-12`. This is evidence that the local algebraic repair preserves the proposed
constant budget. It is not evidence that the external small- and large-character estimates, their
range hypotheses, or the retained main/arc margin have been proved.

Because the specialist estimate treats exceptional/small conductors separately from the
large-conductor mean-value range, Lean also checks an exact split at every cutoff `R` and a final
convolution theorem taking independent bounds for the two ranges. This avoids losing the
large-conductor weight in the coarser all-conductor corollary.

The direct large-conductor branch has now been carried through rather than left as a schematic
split. For `r > R`, Lean proves that the exact active conductor cost is bounded by

```text
(2 B log N / R) * (r / phi(r)),
```

and sums it against the large-conductor primitive-character mass. A separate finite arithmetic
module proves the required input

```text
sum_{k <= u} 1/phi(k) <= 6 * (1 + log u)
```

from an exact Dirichlet-hyperbola identity and a constant-six squarefree Euler-product comparison.
The resulting original-convolution theorem therefore has explicit large term

```text
(12 * (1 + log u) * log N / R) * large-conductor primitive mean-value mass
```

without assuming the reciprocal-totient estimate. This is a genuine `1/R` saving and is not the
coarse all-conductor mass bound in different notation. The unconditional represented-fiber route
has the corresponding factor `18 * (1 + log u) * log N / R`. The globally quantified factor-12
complete-fiber theorem still asks for stability at every level, but the localized theorem now uses
proved squarefree support to retain its signed small-conductor branch and needs no such premise.
Effective small/large primitive-character estimates remain explicit hypotheses.

Lean also checks the exact Mobius-signed partial-summation aggregate and its adapter to the existing
coprime-progression interface. The specialist's continuous integral main is not identical to the
repository's exact active discrete main, so any sum-versus-integral correction must also remain
explicit. The inactive tail from the older comparison main is separately exposed and may not be
folded silently into that correction.
Therefore this is a credible partial theorem, not a completed Route A estimate.

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

The later hard-residual audit sharpens this conclusion.  Lean proves that the hard coefficient is
`Lambda - mu_<=u * log`, independent of the auxiliary cutoff `v`, and extracts the three Vaughan
components under the exact complementary mask.  Its long component is a cross-Toeplitz form
between the product coefficient `mu(d) Lambda(k)` and the reflected prime sequence.  The proved
rank-one SSU modules do not presently map that cross form to a fixed-center one-sided estimate.
See `SupportingDocs/RouteAHardResidualSSUApplicationAudit.md`.

## The theorem needed to resume

The next candidate must be a genuine arithmetic theorem, not a new wrapper. The algebraic
decomposition in item 1 is now checked. The remaining work must provide:

1. an effective signed-conductor/partial-summation theorem, or the stronger maximal
   Bombieri--Vinogradov theorem, for the extracted Type-I--prime correlation, including its
   retained `q=1,2` arc model;
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
