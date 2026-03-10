# SSU status (rolling)

Last updated: 2026-03-08

Estimated “status bar” (**M1–M6 flagship roadmap tranche**): 100%

Estimated “status bar” (**TeX-strength**, full end-to-end SSU as in TeX): 100%

Internal micro-bar (Type–II large sieve stage): ~100%

Secondary bar (**plumbing + weak fallbacks**, end-to-end objects exist but with crude CS/geometry surrogates standing in for real large-sieve input): ~100%

## Platinum completion state

- ✅ **Project-complete at platinum level** for the frozen SSU blueprint and canonical flagship APIs.
- ✅ Canonical extracted/default routes are non-fallback and proof-driven on the promoted paths.
- ✅ Remaining work, if any, is optional sharpening (better constants or stronger families), not required
  to use SSU as a completed library contract surface.

## Goldbach ep-1 integration note

- ✅ Downstream `Q0` pinned-route seam is now narrowed: Step-1/Step-2 are derived from the
  project-neutral dyadic polynomial-decay boundary
  `q0MinorDyadicGramDecayPoly_exists` in
  `Goldbach/Cert/MajorArcModules/Q0MinorInterzoneDyadicConventionalAxioms.lean`.
- ✅ Remaining project-pinned `ep-1` seam is calibration-only (Crow cap inequalities), exposed as
  `ssu_minor_energy_calibration` in
  `Goldbach/Cert/MajorArcModules/Q0MinorEnergyLedgerEngineAxiom.lean`.
- ✅ Mathematician-facing handoff theorem/module added:
  `Goldbach/Cert/MajorArcModules/Q0MinorCalibrationHandoff.lean`.

## Major status (flagship)

M6 stabilization + proof audit:
- ✅ Constants/assumptions audit pass completed against the frozen TeX-facing pipeline shape
  (Step-2 Toeplitz extraction, Step-3/4 promoted extracted route, selector-first flagship API).
- ✅ Flagship build/test pass completed cleanly (warnings only):
  - `lake build SSU.Instances.Basic SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.FejerBankedTypeIIToeplitzBridge SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis SSU.Instances.FejerBankedTypeIIToeplitzStep34Proof`
  - `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis SSU.Instances.FejerBankedTypeIIToeplitzStep34Proof`
- ✅ Canonical API/deprecation docs refreshed (`SSU/README.md`): selector-first canonical
  endpoints documented; legacy reduction/fallback names marked compatibility-only.
- ✅ Audit conclusion: canonical flagship surfaces are proof-driven and build-clean; remaining
  “TeX-strength” delta is analytic sharpening work (stronger large-sieve families and constants),
  not unresolved reduction plumbing or unchecked assumptions.

Step-3 status (split):
- ✅ Engine/use-site proved: non-fallback `Step3LargeSieveOuterUFor` route exists for the extracted
  Type–II signal shape (BG rank-one/modEq pathway in
  `FejerBankedTypeIIBridgeTeXBGRankOne`).
- ✅ Removed the last MV-by-residue placeholder assumptions from the flagship extracted
  general-slope Step-3/Step-4 chain:
  `SSU/Engines/LargeSieve/MVByResidueHypothesis.lean` now builds
  `step3MV_byResidue` / `step4MV_byResidue` from proved deterministic constructors
  (`Step3MontgomeryVaughanByResidue.of_general_geometry`,
  `Step4MontgomeryVaughanByResidue.of_box_geometry`) instead of axioms; the flagship
  call site in `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean` is rewired to pass
  explicit positivity/scale hypotheses.
- ✅ Added sharpened one-add-log residue MV constructors and bridge wiring:
  `step3MV_byResidue_oneAddLog_ref` / `step4MV_byResidue_oneAddLog_ref`
  are now proved constructors in `SSU/Engines/LargeSieve/MVByResidueHypothesis.lean`
  (using the common-domain `hZeq`/`hEqOn` witness package),
  and the extracted bridge now exposes
  `TubeFormInputFor.of_sumFiber_ref_on_zSet_oneAddLog_uniformMV`
  to route non-box Step-3/Step-4 through the by-residue MV chain without dropping to
  deterministic-by-residue envelopes when uniform witness hypotheses are available.
- ✅ Call-site migration pass for the new uniformMV route:
  no existing downstream constructors/callers currently supplied the stronger uniform-in-`F`
  witness package; added canonical public endpoint
  `tubeFormInputForOfSumFiberRefOnZSetOneAddLogUniformMV` in `SSU/Instances/Basic.lean`
  for immediate use wherever those stronger hypotheses are available.
- ✅ Added matching higher-bridge uniformMV endpoints in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  `toUniformInputStep3Step4_of_sumFiber_ref_on_zSet_oneAddLog_uniformMV`,
  `toHypothesisStep34ForUniform_of_sumFiber_ref_on_zSet_oneAddLog_uniformMV`,
  `gramHypothesis_of_sumFiber_ref_on_zSet_oneAddLog_uniformMV`,
  `contract_of_sumFiber_ref_on_zSet_oneAddLog_uniformMV`.
- ✅ Product-side extracted class strengthened on canonical public routes: added a non-box
  tube-window use-site family (`InputFor.tubeWindowOneAddLog`) with geometry-derived fiber bound
  (`≤ 2 * (2U + 1)` from BG tube geometry), and exported it as the preferred public endpoint in
  `SSU.Instances.Flagship.Extracted` (`tubeWindowOneAddLogInputFor`,
  `normInnerPacketOpUnnormalizedLeTubeWindowOneAddLog`).
- ✅ Added residue-structured non-box extracted family on the same product-side route:
  `InputFor.tubeWindowResidueOneAddLog` / `ofTubeWindowResidueProdFiberCardBound`, with level set
  derived internally as `Icc (-U) U` filtered by a shear congruence class (no user-supplied
  `levels` finset), plus public wrappers
  `tubeWindowResidueOneAddLogInputFor` /
  `normInnerPacketOpUnnormalizedLeTubeWindowResidueOneAddLog`.
- ✅ M2 kickoff completed on a genuine extracted non-rank-one family: for the extracted box-signal
  route in `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`, we now construct explicit
  use-site `Step3LargeSieveOuterUFor` and `Step4LargeSieveOuterVFor` witnesses and combine them
  via `Step34LargeSieveTeXFor.of_step3_step4` before producing the theorem-side
  `Step34ProdSumFor` package.
- ✅ Extended the same Step-3/Step-4-for + combiner pattern to the extracted non-box
  tube-window/residue-structured TeX route (`TubeFormInputFor`):
  `sumFiberRefOnZSetOneAddLogStep3For`,
  `sumFiberRefOnZSetOneAddLogStep4For`,
  and `sumFiberRefOnZSetOneAddLogStep34TeXFor` are now explicit constructors, and
  `of_sumFiber_ref_on_zSet_oneAddLog` is wired through that composed chain.
- ✅ M2 completed on a genuine extracted non-rank-one non-box family:
  - proved explicit non-fallback `Step3LargeSieveOuterUFor` and
  `Step4LargeSieveOuterVFor` constructors on the extracted centered-unit tube-window family;
  - combined them into theorem-producing `Step34ProdSumFor`
  (`tubeWindowCenteredUnitOneAddLogStep34For`);
  - exposed public constructor/theorem endpoints in `SSU.Instances.Flagship.Extracted` via
  `tubeWindowCenteredUnitOneAddLogInputFor` and
  `normInnerPacketOpUnnormalizedLeTubeWindowCenteredUnitOneAddLog`.
- ✅ M3 production promotion (centered-unit extracted family) is now packaged as a first-class
  constructor:
  - `centeredUnitStep34For_of_step34TeXFor` provides the proved small-`ξ`/large-`ξ` split and
    integration route from use-site `Step34LargeSieveTeXFor` to uniform/global
    `Step34ProdSumFor`;
  - `tubeWindowCenteredUnitOneAddLog_ofStep34TeXFor` is the corresponding extracted `InputFor`
    constructor;
  - canonical default route `tubeWindowOneAddLogDefault` promotes to this branch when centered-unit
    compatibility hypotheses hold.
- ✅ Production M3 route now also drives the extracted box-family constructor:
  `boxGeometryOneAddLogStep34For` is no longer a separate duplicated split proof; it now
  constructs centered-unit tube-window hypotheses and routes through
  `centeredUnitStep34For_of_step34TeXFor`, so the same proved small-`ξ`/large-`ξ` integration
  path removes the `X / |ξ|` dependence on this extracted family as well.
- ✅ M4 completed on selector-first flagship surfaces:
  - extracted TT*-native selector/fallback endpoints are now compatibility aliases to the same
    non-fallback canonical route (`ToeplitzInputFor.toTTStarInputFor`);
  - higher `uniform`/`gramHypothesis`/`contract` selector wrappers on the flagship rank-one bridge
    now delegate directly to canonical default non-fallback endpoints (route argument retained for
    API compatibility only);
  - higher-level default aliases were migrated to call canonical default endpoints directly
    (instead of selector + default-route indirection), so fallback routes are compatibility aliases
    and are no longer internally selected on canonical paths.
- ✅ Final bridge-layer assumption discharge (remaining legacy reduction assembly where proofs now
  exist):
  - in `FejerBankedTypeIIBridgeTeXBGRankOne`, `ofBGGeometryReduction_autoTubeForm` is now
    proof-driven (delegates through `ofBGGeometryCoeffReduction_autoTubeForm` with
    `inner_eq_coeff`/`energy_le_coeff` derived from the supplied reduction witness) rather than
    assembling a raw `GeometryInput` record directly;
  - the rank-one companion `ofBGGeometryReduction_rankOne_autoTubeForm_from_hF` now inherits that
    same proof-driven path.
  - targeted bridge pass completed: `hypothesisStep34ForUniform_ofBGGeometry` now routes through
    `GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction` (deriving coefficient-form
    `inner_eq_coeff`/`energy_le_coeff` from the supplied reduction + `hF` witness), so this
    compatibility constructor no longer assembles the legacy reduction path internally.
- ✅ M5 bridge-layer cleanup pass completed on the BG rank-one higher bridge:
  - added proof-driven constructors
    `hypothesisStep34ForUniform_ofBGGeometryReductionData`,
    `gramHypothesis_ofBGGeometryReductionData`,
    `contract_ofBGGeometryReductionData` in
    `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`;
  - rewired legacy reduction-witness constructors
    `hypothesisStep34ForUniform_ofBGGeometry`,
    `gramHypothesis_ofBGGeometry`,
    `contract_ofBGGeometry` to delegate to those proof-driven constructors by deriving
    `Cenergy`/`inner_eq_coeff`/`energy_le_coeff` from the supplied reduction witness.
- ✅ Legacy bridge theorem cleanup completed:
  `norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLog` and
  `norm_inner_packetOpUnnormalized_le_tubeWindowCenteredUnitOneAddLog` are now explicitly
  compatibility-only (docstring) and deprecated in favor of
  `norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault`.
- ✅ Extended this proved Step-3/Step-4-for + `Step34ProdSumFor` pattern to the canonical broader
  non-box default route:
  `InputFor.tubeWindowOneAddLogDefault` now auto-promotes to the centered-unit proved chain when
  compatible (`a=0,s=0,q=1` and scale side-conditions), else uses the broader non-box
  product-fiber one-add-log route; `SSU.Instances.Flagship.Extracted.tubeWindowOneAddLogInputFor`
  now points to this promoted default.
- ✅ Strengthened that promotion to a genuinely non-centered non-box family on the canonical
  product-side route:
  added `tubeWindowShiftedUnitOneAddLog` (unit slope with arbitrary offset `s`) by a proved
  geometry lift `tubeFinset P 0 1 s ⊆ tubeFinset P' 0 1 0` with `P'.U = P.U + |s|`, and updated
  `tubeWindowOneAddLogDefault` to use this non-fallback path whenever `a=0,q=1` (no `s=0`
  requirement). This removes product-fiber fallback dependence on the full shifted-unit family.
- ✅ Added a proved non-fallback Step-3/Step-4→Step34 constructor for genuinely non-centered,
  non-box extracted families on the TeX tube-form route:
  `Extracted.TubeFormInputFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry` in
  `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean` now constructs `Step34LargeSieveTeXFor`
  from the BG rank-one/modEq geometry theorem family (`a/q` arbitrary under BG assumptions),
  avoiding product-fiber fallback structure on this extracted route.
- ✅ Added the corresponding **product-side** non-fallback Step-3/Step-4→Step34 route for
  non-unit slope (`a/q` general, centered window `s=0`) on the extracted family:
  `Extracted.InputFor.tubeWindowGeneralSlopeOneAddLog` now builds `Step34ProdSumFor` by combining
  `Step34LargeSieveTeXFor.of_box_geometry` with proved deterministic product↔shear phase-twist
  identities (`prodSum_eq_typeIISum_prodPhaseTwist`, `tubeEnergy_prodPhaseTwist_eq`), and is
  exported on flagship basic API as
  `tubeWindowGeneralSlopeOneAddLogInputFor` /
  `normInnerPacketOpUnnormalizedLeTubeWindowGeneralSlopeOneAddLog`.
- ✅ Promoted that route into canonical default selectors where hypotheses are available:
  `InputFor.tubeWindowOneAddLogDefault` and
  `InputFor.tubeWindowResidueSetOneAddLogDefault` now branch as
  centered-unit (shifted) non-fallback → shifted-window general-slope non-fallback
  (no coprime or `q ≤ D` gate; scale-equality + positivity side conditions) → product-fiber fallback.
- ✅ Removed the remaining auxiliary scale-product gate (`1 ≤ X*H`) from both canonical defaults:
  this condition is now proved internally from the existing small-band hypothesis
  `(1/H)/X < 1/2` and positivity (`X>0`, `H>0`) via
  `InputFor.one_le_mul_of_small_band`, so these routes no longer fall back solely because
  `1 ≤ X*H` was not supplied as an explicit compatibility witness.
- ✅ Added packet-scale-agnostic non-fallback constructors
  `InputFor.tubeWindowOneAddLogScaleAgnostic` and
  `InputFor.tubeWindowResidueSetOneAddLogScaleAgnostic`; canonical defaults are now aliases to
  these routes, and on true scale mismatch / missing positivity side-conditions they route to the
  non-box product-side constructors (`tubeWindowOneAddLog` / `tubeWindowResidueSetOneAddLog`)
  instead of the trivial extracted fallback.
- ✅ Scale-decoupled non-fallback Step-3/Step-4 constructor upgrade:
  the general-slope extracted non-fallback chain now uses `TubeData` with packet scales
  (`td.X := Dpacket.X`, `td.H := Dpacket.H`) directly, so promotion no longer requires explicit
  scale-compatibility equalities `Dpacket.X = P.X` / `Dpacket.H = P.H`.
  Canonical scale-agnostic defaults now use deterministic `(D,U)` inflation (`withUnitDU`) and
  no longer gate non-fallback promotion on an explicit `1 ≤ P.D` assumption.
- ✅ Closed the `q > D` non-fallback gap on the general-slope Step-3 path:
  exported universal `zSet` bound `card_zSet ≤ D/q + 2` and added broad-geometry
  Montgomery–Vaughan Step-3 + Step34 constructors (`of_general_box_geometry`), then rewired
  extracted general-slope one-add-log constructors/default selectors to use this route.
- ✅ Closed the non-coprime fallback gap on the extracted product-side general-slope route:
  added deterministic gcd-reduction constructors
  `tubeWindowGeneralSlopeOneAddLogNoCoprime` /
  `tubeWindowShiftedGeneralSlopeOneAddLogNoCoprime` that reduce `(a,q)` to coprime
  `(a/g,q/g)` on geometry, and rewired the canonical defaults to prefer this non-fallback path.
- ✅ Completed deterministic geometry lift for shifted general slope:
  `tubeFinset_subset_shiftedShearCentered` now proves
  `tubeFinset P a q s ⊆ tubeFinset P' a q 0` with `P'.U = P.U + |s|`, and this is wired into
  `InputFor.tubeWindowShiftedGeneralSlopeOneAddLog` on the extracted product-side route.
- ✅ Added flagship-facing shifted general-slope wrappers in `SSU.Instances.Basic`:
  `tubeWindowShiftedGeneralSlopeOneAddLogInputFor` and
  `normInnerPacketOpUnnormalizedLeTubeWindowShiftedGeneralSlopeOneAddLog`.
- ✅ Completed scale-agnostic migration on route-specific general-slope public wrappers in
  `SSU.Instances.Basic`:
  - added canonical default endpoints
    `tubeWindowGeneralSlopeOneAddLogDefaultInputFor` /
    `tubeWindowShiftedGeneralSlopeOneAddLogDefaultInputFor` and matching theorem endpoints
    `normInnerPacketOpUnnormalizedLeTubeWindowGeneralSlopeOneAddLogDefault` /
    `...Shifted...Default`;
  - rewired legacy compatibility-signature wrappers
    `tubeWindowGeneralSlopeOneAddLogInputFor`,
    `tubeWindowShiftedGeneralSlopeOneAddLogInputFor`, and their theorem companions to delegate
    directly to those scale-agnostic defaults (legacy `hcop`, `q ≤ D`, and explicit scale-equality
    arguments are now compatibility-only on that surface).
- ✅ Applied the same centered-unit promotion pattern to residue-structured extracted families:
  added `InputFor.tubeWindowResidueSetOneAddLogDefault` and
  `InputFor.tubeWindowResidueOneAddLogDefault` in
  `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`, so residue routes now choose the proved
  non-fallback centered-unit Step-3/Step-4 chain whenever compatible and otherwise fall back to
  the residue-union product-fiber route.
  `SSU.Instances.Flagship.Extracted.tubeWindowResidueSetOneAddLogInputFor` and
  `...tubeWindowResidueOneAddLogInputFor` now target these default constructors.
- ✅ Follow-up broad-class route cleanup:
  `InputFor.tubeWindowResidueOneAddLog` now mirrors the scale-agnostic routing policy directly
  (promote to non-fallback shifted general-slope chain when compatible, otherwise residue-set
  product-fiber compatibility path), instead of always forcing residue-set product-fiber.
- ✅ Higher-level call-site naming cleanup:
  `SSU.Instances.Flagship.Extracted.tubeWindowOneAddLogInputFor` /
  `...tubeWindowResidueSetOneAddLogInputFor` and theorem companions now call canonical endpoints
  (`tubeWindowOneAddLog`, `tubeWindowResidueSetOneAddLog`) directly, not route-specific
  `...ScaleAgnostic` names.
- ✅ Follow-up canonical-route cleanup in the extracted bridge layer:
  `tubeWindowGeneralSlopeOneAddLogDefault` /
  `tubeWindowShiftedGeneralSlopeOneAddLogDefault` and
  `norm_inner_packetOpUnnormalized_le_tubeWindowOneAddLogDefault` now call
  `InputFor.tubeWindowOneAddLog` directly (rather than route-specific
  `...ScaleAgnostic` internals), and legacy `...ProdFiber` compatibility constructors now
  delegate to canonical `tubeWindowOneAddLog` / `tubeWindowResidueSetOneAddLog` endpoints.
- ✅ Removed remaining product-fiber dependence behind legacy broad-family constructor names:
  `InputFor.tubeWindowOneAddLogProdFiber` and
  `InputFor.tubeWindowResidueSetOneAddLogProdFiber` are now compatibility-signature wrappers over
  the proved non-fallback scale-agnostic Step-3/Step-4 routes
  (`tubeWindowOneAddLogScaleAgnostic`,
  `tubeWindowResidueSetOneAddLogScaleAgnostic`), rather than assembling product-fiber bounds.
- ✅ Follow-up caller migration/deprecation pass:
  - repository scan shows no remaining internal call sites naming
    `...tubeWindowOneAddLogProdFiber` / `...tubeWindowResidueSetOneAddLogProdFiber`;
  - both names are now explicitly deprecated in-code and documented as compatibility-only in
    `SSU/README.md`.
- ✅ Strengthened residue-window product-fiber control with a modulus-explicit cardinality envelope:
  `residueWindowCardBound` now derives the level-count from `Int.Ioc_filter_modEq_card`
  (with the `m = 0` singleton fallback), and
  `ofTubeWindowResidueProdFiberCardBound` now uses this bound directly instead of carrying only
  `levels.card`.
- ✅ Broadened the product-side extracted residue class from a single congruence class to finite
  residue unions:
  `ofTubeWindowResidueSetProdFiberCardBound` /
  `tubeWindowResidueSetOneAddLog` now support assumptions of the form
  `∃ r ∈ residueReps, shear ≡ r [ZMOD m]`, with modulus-explicit bound
  `∑ r∈residueReps, residueWindowCardBound U m r`.
- ✅ `hF`-plumbing improved: new coefficient-form constructors can now discharge `hF`
  definitionally once inner/energy reduction identities are supplied in rank-one coefficient form.
- ✅ Flagship-instance extraction discharge complete for the non-fallback route: concrete
  auto-Step-2 flagship wrappers now prove extraction-side constancy internally (no external
  `hF0`/`hαconst`/`hβconst` family on the canonical flagship surface).

1) ✅ Discharge extraction-side constancy inputs used by the proved Step-3/Step-4 routes.
- Completed on the canonical flagship path via concrete auto-Step-2 wrappers.

2) ✅ Finish the non-toy extraction bridge to Toeplitz form for the frozen Fejér-banked packets.
- Completed: the production `inner_eq_toeplitzForm` path is now packaged for the main instance.
- Progress: the non-toy frozen-packet Step-2 extraction is now packaged as a canonical
  pair-dependent Toeplitz-form interface (`PairHypothesis.ofFrozenPackets` in
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.lean`), and the extracted
  higher bridge routes through that package. The honest extracted TeX-facing bridge is now
  **Toeplitz-first**: `Extracted.ToeplitzInput` packages a `ToeplitzPairHypothesis` together with
  `Step34ProdSum`, and `Extracted.Input.toTTStarInput` is derived through this Toeplitz package
  rather than starting from a legacy reduction witness. The remaining gap is the *legacy
  operator-global* reduction surface (`ReductionToTubeForm` for arbitrary `f`), not the honest
  extracted signal.
- New extension: there is now also a **general extracted-signal** higher bridge (global in the
  coefficient input `f : H0`) that uses the proved extraction theorem and non-fallback Step 3–4
  directly, with no supplied reduction witness on that surface.
- New non-extracted extension: there is now a **reduction-free operator-global Toeplitz surface**
  (`ToeplitzOperatorInput` in `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`) that splits
  the old `ReductionToTubeFormProd` seam into:
  - a TT*-native Toeplitz identity (`ToeplitzPairHypothesis` with the honest global signal),
  - and a separate tube-energy comparison.
  This gives a new canonical non-extracted TeX-facing bridge object without a bundled
  `reductionTorus` field, although the legacy `Hypothesis` / `HypothesisFor` compatibility
  records still remain.

3) ✅ Discharge flagship instance assumptions (especially `tubeForm_eq` + reduction plumbing) by proof.
- Completed on the flagship canonical path: selector/default flagship constructors route through
  proof-driven `autoStep2` and `...fromReductionData` assembly, so `tubeForm_eq` and raw
  `ReductionToTubeForm` plumbing are no longer required on application-facing flagship endpoints.
- Legacy `...fromReductionLegacy`/compatibility wrappers are retained intentionally for API
  compatibility, but they are no longer canonical.

4) ✅ Close the SSU heart for the flagship packet family and expose the final contract.
- Completed and exposed on canonical surfaces:
  - reduction-free operator-global: `Flagship.HeartOperatorGlobal.gramHypothesis` /
    `Flagship.HeartOperatorGlobal.contract`;
  - proof-driven auto-Step-2 reduction-data route:
    `Flagship.Heart.gramHypothesis` / `Flagship.Heart.contract`.

The flagship heart-closure milestone is complete. Remaining work is now primarily analytic
strengthening (replacing surrogate/global one-add-log routes with sharper non-fallback families).

## Secondary-bar closure substeps (closed)

1) ✅ Selector migration at use sites completed.
- Selector-path APIs are canonical (`...flagship_select_ofIndexWitness...`), with route-specific
  wrappers kept as compatibility shims.

2) ✅ Endpoint surface normalized.
- Full parity is present across `uniform` / `gram` / `contract` for each route tier
  (`from_hF`, extracted-constancy, `autoTubeForm`) on default and fallback routes.

3) ✅ Direct hypothesis seams eliminated on selector surfaces.
- Geometry-input and auto-Step-2 selector paths are the canonical route; raw
  `tubeForm_eq`-style seams are no longer exposed on the flagship selector surface.

4) ✅ Validation lock completed.
- Bridge/importer build checks pass after migration batches, and status now tracks major
  remaining work outside secondary-bar plumbing.

## Broad roadmap (finish line)

A) **Flagship extraction discharge**
- Prove the flagship extracted coefficients satisfy the required `hF`/constancy/modEq hypotheses.
- Remove the last application-facing placeholder assumptions from flagship constructor endpoints.

B) **Production Toeplitz extraction**
- Complete the non-toy `inner_eq_toeplitzForm` path for the frozen Fejér-banked packet family.
- Wire it as the canonical Step-2 reduction path used by flagship contracts.

C) **Flagship TeX Step 3/4 closure**
- Keep the non-fallback Step-3/Step-4 route as default for the extracted Type–II signal.
- Ensure fallback-only routes are optional compatibility paths, not required in flagship usage.

D) **SSU-heart integration**
- Route the proved extraction + Step-3/4 chain into final `GramHypothesis` and ledger contract.
- Expose one stable, minimal flagship API for Goldbach/Twin/Alt-Zeta consumption.

E) **Hard-analysis replacement pass**
- Replace any remaining weak/geometry surrogates with full TeX-strength large-sieve/Type-II proofs.
- Recheck constants and assumptions once the analytic replacement is complete.

## Current step breakdown (Step 2: production Toeplitz extraction)

1. Freeze the canonical extracted Type–II coefficient map for the flagship packet family.
2. Prove the non-toy `inner_eq_toeplitzForm` bridge for that extracted map.
3. Refactor the higher flagship surface to a TT*-native pair-dependent interface and route callers
   through it (remove placeholder reduction seams on the honest extracted-signal path).
4. Validate with
   `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
5. Shift to Step 3 discharge (`tubeForm_eq` + reduction plumbing fully proved).

Latest microstep:
- Extended non-box extracted TeX family assembly to match the same explicit Step-3/Step-4-for
  pattern used on the extracted box family:
  - added `sumFiberRefOnZSetOneAddLogStep3For`,
    `sumFiberRefOnZSetOneAddLogStep4For`,
    `sumFiberRefOnZSetOneAddLogStep34TeXFor` in
    `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`;
  - rewired `Extracted.TubeFormInputFor.of_sumFiber_ref_on_zSet_oneAddLog` to construct
    `step34TeXFor` via this explicit Step-3/Step-4 combiner path.
- Validation:
  `lake build SSU.Instances.FejerBankedTypeIIToeplitzBridge SSU.Instances.Basic`.
- Migrated single-residue wrapper/caller surfaces onto the residue-union route where hypotheses
  match:
  - `SSU/Instances/Basic.lean`: `tubeWindowResidueOneAddLogInputFor` and
    `normInnerPacketOpUnnormalizedLeTubeWindowResidueOneAddLog` are now compatibility wrappers
    over `...ResidueSet...` with singleton `residueReps = {r}`; ordering was fixed so these
    wrappers elaborate.
  - `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`:
    `InputFor.tubeWindowResidueOneAddLog` and
    `norm_inner_packetOpUnnormalized_le_tubeWindowResidueOneAddLog` now route through the
    residue-set constructor/theorem path (singleton residue set), keeping one canonical route.
- Validation:
  `lake build SSU.Instances.Basic SSU.Instances.FejerBankedTypeIIToeplitzBridge`.
- Completed a focused higher-level migration pass in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  legacy-named default/fallback wrappers in the `...autoTubeForm_fromReduction` family now call
  `...autoTubeForm_fromReductionData` selector endpoints directly (`.nonFallback`,
  `.step3FallbackStep4`, `.step4FallbackStep3`) wherever signatures matched.
- Validation:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Reworked the flagship reduction wrappers in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` so internal composition is now
  data-first/proof-driven:
  - added `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_autoTubeForm_fromReductionDataCore`;
  - rewired both `...fromReduction` and `...fromReductionData` constructors to delegate to this
    core data route.
  This removes internal raw reduction assembly from the flagship constructor composition path.
- Validation:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Added proof-driven rank-one selector constructors that internalize reduction assembly in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_autoTubeForm_fromReductionData`
  - `gramHypothesis_flagship_select_ofIndexWitness_autoTubeForm_fromReductionData`
  - `contract_flagship_select_ofIndexWitness_autoTubeForm_fromReductionData`
  These derive the `ReductionToTubeForm` witness from explicit
  `Cenergy + inner_eq_coeff + energy_le_coeff` data via
  `SSU.Instances.FejerBankedTypeIIBridgeTeX.reduction_of_data`, instead of requiring callers to
  pre-assemble a reduction record.
- Validation:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added full default/fallback wrapper families for this proof-driven route in the same file
  (`...flagship_default...fromReductionData`, including Step3FallbackStep4 and
  Step4FallbackStep3 variants), and exported selector/default aliases in
  `SSU/Instances/Basic.lean`:
  - `...select_ofIndexWitness_autoTubeForm_fromReductionData`
  - `...ofIndexWitness_autoTubeForm_fromReductionData`
  - fallback companions for both one-sided route tags.
- Validation:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Migrated higher-level canonical aliases in `SSU/Instances/Basic.lean` so
  `...autoTubeForm_fromReduction` now routes to the proof-driven
  `...autoTubeForm_fromReductionData` endpoints (default and fallback),
  while `...fromReductionLegacy` remains available as compatibility.
- Validation:
  `lake build SSU.Instances.Basic`.
- Added proof-driven Step-2 discharge endpoints:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`, added
    `tubeForm_eq_of_step2ToTubeForm` plus
    `gramHypothesis_of_box_geometry_autoStep2` and
    `contract_of_box_geometry_autoStep2`;
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBoxFallback.lean`, added
    `..._autoStep2` variants across the fallback bridge wrappers
    (`hypothesisMVKhat`, `hypothesisKhat`, `hypothesis`, uniform/gram/contract paths), each
    deriving `tubeForm_eq` from a supplied `Step2ToTubeForm`.
- Validation:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX
  SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback SSU.Instances.Basic`.
- Added a reduction-free **non-extracted** TeX-facing bridge surface in
  `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`:
  - `ToeplitzOperatorInput` packages the operator-global TT* identity as a
    `ToeplitzPairHypothesis` on torus `L²`, together with a separate `energy_le` field, instead
    of a single bundled `ReductionToTubeFormProd`;
  - `ToeplitzOperatorInput.norm_inner_packetOpUnnormalized_le` gives the honest operator-global
    torus packet Gram bound directly from the Toeplitz-first Step-2/Step-3–4 route;
  - `ToeplitzOperatorInput.gramHypothesisTorusUnnormalized` turns that into a torus-side
    `GramHypothesis` for the unnormalized packet family, with no reduction object involved.
- Re-exported this surface in `SSU/Instances/Basic.lean` as
  `SSU.Instances.Flagship.ToeplitzOperatorInput`.
- This still does **not** remove the legacy `reductionTorus` seam from the full core-facing
  `Hypothesis` / `HypothesisFor` records.
- The stable reduction-free non-extracted surface currently stops at the torus-side TT* bound:
  - `ToeplitzOperatorInput.norm_inner_packetOpUnnormalized_le`
  - public aliases `SSU.Instances.Flagship.toeplitzOperatorNormInnerPacketOpUnnormalizedLe`
    and `SSU.Instances.Flagship.OperatorGlobal.Input / normInnerPacketOpUnnormalizedLe`
- The attempted direct core-facing Gram/contract promotion through `ToeplitzOperatorInput` hit a
  Lean elaboration bottleneck and was rolled back, so the core-facing non-extracted path still runs
  through the legacy reduction-based records for now.
- Stopped treating the legacy reduction-based surface as primary in the remaining TeX-facing
  selector layer for the honest extracted path:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added
    `toeplitzInput_flagship_select_ofIndexWitness_extracted`, and rewired
    `ttStarInput_flagship_select_ofIndexWitness_extracted` plus its packet-Gram theorem to take
    `Extracted.ToeplitzInput` directly (the TT* layer is now obtained from the Toeplitz-first
    package, not passed in as the first-class input);
  - in `SSU/Instances/Basic.lean`, added public Toeplitz-first selector aliases
    `SSU.Instances.Flagship.Extracted.toeplitzInputSelect` / `toeplitzInput` and fallback
    companions.
- This makes the remaining TeX-facing extracted selector surface explicitly consume the honest
  `ToeplitzPairHypothesis`-based package before entering the TT* wrapper layer.
- Re-centered the remaining TeX-facing extracted higher bridge layers around the honest
  Toeplitz-form package instead of treating reduction-based surfaces as primary:
  - in `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`, added
    `Extracted.TTStarInput.ofToeplitzPairHypothesis` and the new record
    `Extracted.ToeplitzInput`, which packages
    `ToeplitzPairHypothesis + Step34ProdSum` and derives the TT*-native bridge object from that
    pair;
  - added `Extracted.Input.toToeplitzInput`, and rewired
    `Extracted.Input.toTTStarInput` to route through `toToeplitzInput.toTTStarInput`;
  - re-exported the new canonical public alias in `SSU/Instances/Basic.lean` as
    `SSU.Instances.Flagship.Extracted.ToeplitzInput`.
- This means the honest extracted path is now explicitly
  `ToeplitzPairHypothesis → ToeplitzInput → TTStarInput`, while the old reduction-based
  operator-global surfaces remain compatibility layers only.
- Validation: `SSU.Instances.FejerBankedTypeIIToeplitzBridge` builds cleanly; no `error:` entries
  were produced in the combined bridge/basic build log.
- Extended the fixed-rank-one `...from_hF` layer with **promotion endpoints** so the old
  one-sided fallback-shaped BG one-add-log families are no longer the strongest route there:
  - in `GeometryInputConstStep3Step4`, added
    `ofGeometryInputBGConstOnUIndexOneAddLogStep3FallbackStep4OfModEq_promote_from_hF` and
    `ofGeometryInputBGConstOnVIndexOneAddLogStep4FallbackStep3OfModEq_promote_from_hF`,
    both of which route directly to the full non-fallback
    `ofGeometryInputBGConstOnIndexOneAddLogOfModEq_from_hF` path when both residue-index witness
    families are available.
  - in the one-record fixed-rank-one layer, added matching promoted
    `hypothesis/gram/contract ..._promote_from_hF` endpoints for both U-side and V-side
    fallback-shaped families; these now delegate straight to the full non-fallback
    `...BGConstOnIndex_oneAddLog_ofModEq_from_hF` flagship path.
- This makes the old one-sided `...step3_fallback_step4...from_hF` /
  `...step4_fallback_step3...from_hF` families explicit compatibility surfaces rather than the
  strongest available route once both witness sets are present.
- Tightened one remaining helper family by removing redundant route-by-route fallback branching in
  `gramHypothesis_flagship_select_ofIndexWitness_from_hF` and
  `contract_flagship_select_ofIndexWitness_from_hF`; both now derive directly from the already
  collapsed non-fallback selector theorem
  `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_from_hF`.
- Validation: incremental build log for
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne` shows no `error:` entries.
- Strengthened the remaining mathematically fallback-shaped **modEq helper families** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` by adding promotion wrappers that
  accept both residue-index witness families and route directly to the full non-fallback
  const-on-index path:
  - `GeometryInput.*_step3_fallback_step4_ofModEq_promote` upgrades the U-side fallback-shaped
    BG helpers to the two-sided non-fallback route once `v`-side witnesses are available.
  - `GeometryInput.*_step4_fallback_step3_ofModEq_promote` does the symmetric V-side upgrade.
  - matching `GeometryInputConst` one-record promotion wrappers now expose the same stronger path
    at the constant-input insertion layer.
- This does not prove a new large-sieve estimate, but it removes another class of
  fallback-only *mathematical* helper surfaces by making their honest two-sided route explicit
  wherever both witness families are present.
- Validation: no `error:` entries in an incremental
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne` pass.
- Removed the last fallback-backed proof production from the **selector-first BG higher bridge**
  where both residue-index witnesses are already available.
  In `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`,
  `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_from_hF` and
  `hypothesisStep34ForUniform_flagship_select_ofIndexWitness` now collapse all selector routes
  (`nonFallback`, `step3FallbackStep4`, `step4FallbackStep3`) onto the proved non-fallback
  production path internally. The route argument remains only for API compatibility.
- This means the selector-first BG higher bridge no longer assembles fallback Step-3/Step-4
  packages on those flagship surfaces; fallback route names are now compatibility wrappers around
  the same non-fallback proof object whenever the stronger witness set is already present.
- Validation passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Retired the remaining *canonical* public references to the reduction-based
  `uniform/gram/contract` selector family in `SSU/Instances/Basic.lean` by demoting them to
  explicit legacy aliases:
  - added `...autoTubeForm_fromReductionLegacy` selector/default/fallback surfaces,
  - kept the old `...autoTubeForm_fromReduction` names only as compatibility aliases.
  This makes the reduction-based family visibly non-canonical at the public re-export layer.
- Extended the TT*-native extracted selector surface so fallback-route consumers no longer need to
  touch the legacy reduction-based family:
  - added
    `norm_inner_packetOpUnnormalized_le_flagship_default_step3_fallback_step4_ofIndexWitness_extracted`
    and
    `norm_inner_packetOpUnnormalized_le_flagship_default_step4_fallback_step3_ofIndexWitness_extracted`
    in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`,
  - re-exported them in `SSU/Instances/Basic.lean` as
    `SSU.Instances.Flagship.Extracted.normInnerPacketOpUnnormalizedLeStep3FallbackStep4`
    and
    `SSU.Instances.Flagship.Extracted.normInnerPacketOpUnnormalizedLeStep4FallbackStep3`.
  Both currently route to the same proved non-fallback extracted TT* chain.
- Validation passes:
  `lake build SSU.Instances.Basic`.
- Added TT*-native selector-first higher-wrapper endpoints in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `ttStarInput_flagship_select_ofIndexWitness_extracted`,
  - `norm_inner_packetOpUnnormalized_le_flagship_select_ofIndexWitness_extracted`,
  plus default/fallback aliases.
  These are selector-surface companions to the older
  `..._autoTubeForm_fromReduction` family, but they route through the honest extracted TT* bridge
  (`Extracted.Input.toTTStarInput`) instead of presenting the reduction-based family as canonical.
- Re-exported the new higher-layer TT*-native selector endpoints from `SSU/Instances/Basic.lean`
  under `SSU.Instances.Flagship.Extracted`:
  - `inputSelect`, `input`,
  - `normInnerPacketOpUnnormalizedLeSelect`, `normInnerPacketOpUnnormalizedLe`,
  together with route-compatible fallback aliases.
- Validation passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Added a TT*-native pair-dependent extracted-signal bridge surface in
  `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`:
  - `Extracted.TTStarInput`,
  - `Extracted.TTStarInput.step34For`,
  - `Extracted.TTStarInput.inner_eq_toeplitzFormTeXC_onJ`,
  - `Extracted.TTStarInput.norm_inner_packetOpUnnormalized_le`,
  - `Extracted.Input.toTTStarInput`,
  and kept
  - `Extracted.Input`,
  - `Extracted.Input.step34For`,
  - `Extracted.Input.norm_inner_packetOpUnnormalized_le`,
  - `Extracted.Input.norm_inner_packetOpUnnormalized_le_onJ`.
  This makes the canonical higher extracted route explicit in the honest TT* form: a signal
  `signal f i j : L²(𝕋)` depending on the packet pair, together with the theorem
  `inner = (1/X) * toeplitzFormTeXC` on `J × J`.
- Added the generic Step 3–4 wrapper theorem
  `FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.norm_inner_packetOpUnnormalized_le_of_toeplitz`,
  so the non-fallback Step 3–4 chain now runs from an abstract TT* Toeplitz identity instead of
  only the hard-coded canonical `fTT`.
- Re-exported the TT*-native record from `SSU/Instances/Basic.lean` as
  `SSU.Instances.Flagship.Extracted.TTStarInput`, and switched
  `SSU.Instances.Flagship.Extracted.Input` to the TT*-native surface. The constructor record is
  retained as `SSU.Instances.Flagship.Extracted.LegacyInput`.
- The canonical constructor `Extracted.Input.toTTStarInput` uses the production theorem from
  `FejerBankedTypeIIToeplitzTorusPackets.General` together with
  `FejerBankedTypeIIToeplitzTorusPackets.General.inner_packetOpUnnormalized_eq_toeplitzFormTeXC_onJ`,
  so the extracted-signal route now has **no supplied `ReductionToTubeFormProd` witness** and no
  need to force the pair-dependent `fTT(f,i,j)` into a single-operator abstraction.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIToeplitzBridge SSU.Instances.Basic`.
- Important boundary: the original `Hypothesis` / `HypothesisFor` records in the higher bridge
  still retain `reductionTorus` on the fully operator-global surface, because their abstraction is
  stronger than the current production theorem supports. The extracted torus TT* input is
  pair-dependent (`fTT(f,i,j)`), so the new proved route removes the seam on the honest
  extracted-signal flagship surface rather than by pretending we already have an operator-global
  `ReductionToTubeFormProd`.
- Connected the higher Toeplitz bridge layer to the now-canonical production extraction on the
  honest fixed-signal flagship route.
  Concretely, `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean` now contains
  `RankOne.FixedSignalInput`, which packages:
  - the canonical extracted box-data array,
  - the production Step-2 weighted-band / Toeplitzized TT* hypotheses,
  - the non-fallback Step 3–4 specialization for that extracted array, and
  - the resulting higher-layer packet Gram bound
    `FixedSignalInput.norm_inner_packetOpUnnormalized_le`.
  This removes any application-supplied reduction witness from the *fixed-signal* flagship use-site
  API while staying mathematically honest about the fact that the current production extraction is
  not yet a global `ReductionToTubeForm`.
- Re-exported that fixed-signal higher bridge route from `SSU/Instances/Basic.lean` under
  `SSU.Instances.Flagship.FixedSignalRankOne`, so the strongest fully proved flagship path is now
  reachable from the public instance surface.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIToeplitzBridge SSU.Instances.Basic`.
- Rewired the canonical rank-one production extraction in
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean` so the weighted-band TT*
  hypothesis is now the primitive endpoint, and the Toeplitz-form TT* hypothesis is derived from it
  via the deterministic fixed-signal ξ-band → Toeplitz conversion (`inner_eq_toeplitzFormTeXC`).
- This means the newly packaged fixed-signal Step-2 Toeplitzization theorem is now part of the
  actual flagship rank-one extraction path, rather than just an unused side interface.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne`.
- Added a fixed-signal deterministic Step-2 Toeplitzization bridge:
  - `SSU/Instances/FejerBankedTypeIIToeplitzTTStarHypothesis.lean` now includes
    `HypothesisFor.inner_eq_toeplitzFormTeXC`, the fixed-signal analogue of the global
    weighted-band TT* → Toeplitz-form theorem.
  - `SSU/Instances/FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.lean` now includes
    `SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis.HypothesisFor.toToeplitzHypothesis`,
    so a fixed-signal weighted-band TT* witness upgrades directly to the fixed-signal Toeplitz
    hypothesis interface.
  - This closes a real Step-2 proof gap in the extracted-signal setting: fixed-signal callers can
    now reuse the deterministic ξ-band → Toeplitz conversion instead of reproving it locally.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIToeplitzTTStarHypothesis SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne`.
- Extended the reduction-based auto-Step-2 flagship surface to full default/fallback parity.
  Concretely:
  - `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` now includes canonical
    default-route wrappers and both fallback-route wrappers for
    `..._ofIndexWitness_autoTubeForm_fromReduction` across `uniform` / `gram` / `contract`,
    matching the older `from_hF`, extracted-constancy, and `autoTubeForm` families.
  - `SSU/Instances/Basic.lean` now re-exports the same reduction-based family on both fallback
    routes via
    `..._step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReduction` and
    `..._step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReduction`.
  - This closes the remaining surface mismatch in the reduction-based Step-2 API layer, so every
    flagship route tier now has uniform default/fallback coverage in `SSU.Instances.Flagship`.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Added a new reduction-based auto-Step-2 flagship surface in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInput.ofBGGeometryReduction_autoTubeForm`,
  - `GeometryInput.ofBGGeometryReduction_rankOne_autoTubeForm_from_hF`,
  - selector endpoints
    `..._select_ofIndexWitness_autoTubeForm_fromReduction`
    for `uniform` / `gram` / `contract`.
  This removes the raw `inner_eq_coeff` / `energy_le_coeff` family from one additional flagship
  Step-2 call surface when a packaged `ReductionToTubeForm` is already available.
- Re-exported those reduction-based selector endpoints through `SSU.Instances.Flagship` in
  `SSU/Instances/Basic.lean` via
  `..._ofIndexWitness_autoTubeForm_fromReduction` and the matching route-selectors.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Documented the canonical flagship API surface in `SSU/README.md` so downstream use is centered on
  `SSU.Instances.Basic` / `SSU.Instances.Flagship` selector-first endpoints.
- Marked the secondary bar as closed (`~100%`) after completing selector-surface normalization and
  fallback parity in `SSU.Instances.Flagship`.
- Updated status tracking to switch active work from Step 1 extraction-side discharge to
  Step 2 production Toeplitz extraction (`inner_eq_toeplitzForm` path).
- Extended `SSU/Instances/Basic.lean` with explicit fallback-route re-exports for all three
  index-witness wrapper tiers (`from_hF`, extracted-constancy, `autoTubeForm`) across
  `uniform` / `gram` / `contract`, via:
  - `step3FallbackStep4Route`,
  - `step4FallbackStep3Route`,
  and corresponding `..._step3FallbackStep4_...` / `..._step4FallbackStep3_...` aliases.
- Build check passes:
  `lake build SSU.Instances.Basic`.
- Extended `SSU/Instances/Basic.lean` with canonical route-selector re-exports in
  `SSU.Instances.Flagship` for all three index-witness wrapper tiers:
  - `..._select_ofIndexWitness_from_hF`,
  - `..._select_ofIndexWitness`,
  - `..._select_ofIndexWitness_autoTubeForm`,
  each with `uniform` / `gram` / `contract` parity.
- Rewired existing default-route aliases in `SSU/Instances/Basic.lean` to call those selector
  re-exports at `defaultRoute`, so downstream default usage and explicit-route usage now share one
  surface path.
- Build checks pass:
  `lake build SSU.Instances.Basic SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a selector-first default-route API layer in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `flagshipSelectorDefaultRoute : FlagshipIndexRoute := .nonFallback`,
  - canonical selector-default aliases for all three wrapper tiers (`from_hF`,
    extracted-constancy, `autoTubeForm`) across `hypothesisStep34ForUniform` /
    `gramHypothesis` / `contract`.
- Extended `SSU/Instances/Basic.lean` with `SSU.Instances.Flagship` aliases that re-export these
  selector-first default endpoints as the recommended downstream surface.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Selector call-site migration completed for flagship index-witness surfaces in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - rewired all selector `gramHypothesis`/`contract` endpoints
    (`..._select_ofIndexWitness...`, `..._select_ofIndexWitness_from_hF...`,
    `..._select_ofIndexWitness_autoTubeForm...`)
    to consume route-specific hypothesis endpoints directly in each route branch.
  - net effect: selector wrappers now consistently flow through hypothesis packaging before
    projecting to Gram/contract, reducing duplicated route-level call plumbing.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`,
  `lake build SSU.Instances.Basic`.
- Added fallback selector/default compatibility lemmas in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` for both fallback families
  (step3-fallback-step4 and step4-fallback-step3), covering all three wrapper tiers:
  `from_hF`, extracted-constancy, and `autoTubeForm`, across
  `hypothesisStep34ForUniform` / `gramHypothesis` / `contract`.
  This mirrors the existing non-fallback compatibility shim and completes default-vs-legacy
  simp coverage across all flagship routes.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Extended the same “default implementation + thin compatibility alias” pattern to both fallback
  families in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - renamed fallback implementation bodies to canonical
    `...flagship_default_step3_fallback_step4...` and
    `...flagship_default_step4_fallback_step3...` definitions,
  - restored legacy fallback names as thin `abbrev` compatibility aliases.
- Retargeted selector fallback branches to canonical default fallback definitions (not legacy
  compatibility names), completing the selector/default split consistently across all three routes.
- Retargeted all non-fallback branches in selector endpoints to call canonical default endpoints
  directly (instead of legacy non-fallback wrappers) in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_from_hF`,
  - `hypothesisStep34ForUniform_flagship_select_ofIndexWitness`,
  - `gramHypothesis_flagship_select_ofIndexWitness`,
  - `contract_flagship_select_ofIndexWitness`,
  - `gramHypothesis_flagship_select_ofIndexWitness_from_hF`,
  - `contract_flagship_select_ofIndexWitness_from_hF`,
  - `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_autoTubeForm`,
  - `gramHypothesis_flagship_select_ofIndexWitness_autoTubeForm`,
  - `contract_flagship_select_ofIndexWitness_autoTubeForm`.
  This completes the “legacy wrappers as thin aliases” direction for the non-fallback path while
  leaving fallback routes intact as compatibility branches.
- Converted legacy non-fallback index-witness wrapper families into thin aliases over canonical
  default endpoints in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_ofIndexWitness_from_hF`,
  - `hypothesisStep34ForUniform_flagship_ofIndexWitness`,
  - `gramHypothesis_flagship_ofIndexWitness_from_hF`,
  - `gramHypothesis_flagship_ofIndexWitness`,
  - `contract_flagship_ofIndexWitness_from_hF`,
  - `contract_flagship_ofIndexWitness`,
  - `hypothesisStep34ForUniform_flagship_ofIndexWitness_autoTubeForm`,
  - `gramHypothesis_flagship_ofIndexWitness_autoTubeForm`,
  - `contract_flagship_ofIndexWitness_autoTubeForm`.
  Their former bodies now live in corresponding `..._flagship_default_...` definitions.
- Added selector/default compatibility lemmas in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` tying canonical default aliases to
  legacy non-fallback wrappers (uniform/Gram/contract at `from_hF`, extracted-constancy, and
  auto-Step-2 tiers):
  - `..._default_ofIndexWitness_from_hF_eq_legacy`,
  - `..._default_ofIndexWitness_eq_legacy`,
  - `..._default_ofIndexWitness_autoTubeForm_eq_legacy`.
  This gives a proof-level shim that call-site migration can rely on without changing behavior.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`,
  `lake build SSU.Instances.Basic`.
- Added canonical non-fallback selector aliases in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_default_ofIndexWitness_from_hF`,
  - `gramHypothesis_flagship_default_ofIndexWitness_from_hF`,
  - `contract_flagship_default_ofIndexWitness_from_hF`,
  - `hypothesisStep34ForUniform_flagship_default_ofIndexWitness`,
  - `gramHypothesis_flagship_default_ofIndexWitness`,
  - `contract_flagship_default_ofIndexWitness`,
  - `hypothesisStep34ForUniform_flagship_default_ofIndexWitness_autoTubeForm`,
  - `gramHypothesis_flagship_default_ofIndexWitness_autoTubeForm`,
  - `contract_flagship_default_ofIndexWitness_autoTubeForm`.
  These make selector routing the canonical non-fallback surface while preserving existing
  route-specific wrappers for compatibility.
- Added selector-path flagship endpoints at the **geometry-input** layer in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_from_hF`,
  - `gramHypothesis_flagship_select_ofIndexWitness_from_hF`,
  - `contract_flagship_select_ofIndexWitness_from_hF`,
  - `hypothesisStep34ForUniform_flagship_select_ofIndexWitness`,
  - `gramHypothesis_flagship_select_ofIndexWitness`,
  - `contract_flagship_select_ofIndexWitness`.
  These route by `FlagshipIndexRoute` across non-fallback and both fallback families while
  staying on geometry-input APIs; this gives a canonical selector surface where Step-2 tube-form
  plumbing is already discharged via `GeometryInput.reduction`/`hF0` instead of raw
  `tubeForm_eq` assumptions.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Completed the three pending flagship-surface plumbing items:
  1) `SSU/Instances/Basic.lean` now re-exports the flagship/fallback index-witness API module
     (`FejerBankedTypeIIBridgeTeXBGRankOne`);
  2) added a canonical route selector in
     `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
     `FlagshipIndexRoute` with selector endpoints
     `hypothesisStep34ForUniform_flagship_select_ofIndexWitness_autoTubeForm`,
     `gramHypothesis_flagship_select_ofIndexWitness_autoTubeForm`,
     `contract_flagship_select_ofIndexWitness_autoTubeForm`;
  3) selector endpoints are routed through the auto-Step-2 flagship wrappers, so this top-level
     surface no longer asks for direct `tubeForm_eq` / `reduction` hypotheses.
- Build checks pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne SSU.Instances.Basic`.
- Extended canonical **index-witness flagship simplification** to both fallback families in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - Step-3-proved/Step-4-fallback flagship index-witness wrappers
    (`...flagship_step3_fallback_step4_ofIndexWitness...`) added for
    uniform/Gram/contract, including `from_hF` and `autoTubeForm` variants.
  - Step-4-proved/Step-3-fallback flagship index-witness wrappers
    (`...flagship_step4_fallback_step3_ofIndexWitness...`) added for
    uniform/Gram/contract, including `from_hF` and `autoTubeForm` variants.
  - Net effect: canonical flagship surfaces are now uniform across non-fallback and fallback
    families at the index-witness level.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a new canonical flagship endpoint family for the non-fallback route that uses
  **index witnesses** (rather than class witnesses) in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_ofIndexWitness_from_hF`,
  - `gramHypothesis_flagship_ofIndexWitness_from_hF`,
  - `contract_flagship_ofIndexWitness_from_hF`,
  - `hypothesisStep34ForUniform_flagship_ofIndexWitness`,
  - `gramHypothesis_flagship_ofIndexWitness`,
  - `contract_flagship_ofIndexWitness`,
  - `hypothesisStep34ForUniform_flagship_ofIndexWitness_autoTubeForm`,
  - `gramHypothesis_flagship_ofIndexWitness_autoTubeForm`,
  - `contract_flagship_ofIndexWitness_autoTubeForm`.
  These wrappers remove the class-witness requirement from canonical flagship call-sites while
  preserving the same non-fallback Step-3/Step-4 bridge route.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Completed the internal micro-bar target by adding concrete auto-Step-2 flagship wrappers that
  discharge extraction-side constancy by proof in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_ofClassWitness_autoTubeForm`,
  - `gramHypothesis_flagship_ofClassWitness_autoTubeForm`,
  - `contract_flagship_ofClassWitness_autoTubeForm`.
  These instantiate `g := GeometryInput.ofBGGeometryCoeffReduction_rankOne_autoTubeForm ...` and
  derive required extracted constancy using:
  `GeometryInput.hαconst_ofBGGeometryCoeffReduction_rankOne_autoTubeForm`,
  `GeometryInput.hβconst_ofBGGeometryCoeffReduction_rankOne_autoTubeForm`.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Eliminated the remaining flagship `hF0` family from the canonical API surface by adding
  proof-based flagship wrappers in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_ofClassWitness`,
  - `gramHypothesis_flagship_ofClassWitness`,
  - `contract_flagship_ofClassWitness`.
  These route through the existing rank-one modEq class-witness proof path using extracted
  constancy (`hαconst`/`hβconst`) instead of taking a direct `hF0` witness.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Revalidated flagship bridge build after the current wrapper pass:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne` (passes; warnings only).
- Added canonical flagship alias endpoints in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_flagship_ofClassWitness_from_hF`,
  - `gramHypothesis_flagship_ofClassWitness_from_hF`,
  - `contract_flagship_ofClassWitness_from_hF`.
  These pin a single non-fallback “rank-one + modEq + class-witness + fixed-`hF`” route as the
  default top-level interface for downstream usage.
- Removed explicit class-constancy assumptions from the flagship `from_hF` class-witness fallback
  endpoint families in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - rank-one U-side (`...BGConstOnUIndex...ofClassWitness_from_hF`, uniform/Gram/contract),
  - rank-one V-side (`...BGConstOnVIndex...ofClassWitness_from_hF`, uniform/Gram/contract),
  - constant-input insertion aliases for both U/V families.
  These now derive class constancy directly from modEq + class-witness membership as geometry
  lemmas inside the wrappers, instead of requiring external `hβconst_class` / `hαconst_class`
  hypotheses at call sites.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added new **one-record insertion constructors** for the BG const-on-index modEq class-witness
  route in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInputConstStep3Step4.ofBGConstOnIndexOneAddLogOfModEqOfClassWitness`,
  - `GeometryInputConstStep3Step4.ofGeometryInputBGConstOnIndexOneAddLogOfModEqOfClassWitness_from_hF`.
  These derive index references (`mRefU`, `mRefV`) from class witnesses
  (`uRef ∈ uClass(r)`, `vRef ∈ vClass(r)`) and route through the existing modEq insertion
  constructor, so class-witness call-sites can now land directly at the insertion layer.
- Added top-level insertion aliases and rewired endpoints to consume them:
  - `inputStep3Step4_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_from_hF`,
  - `inputStep3Step4_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_from_hF`.
  The corresponding `hypothesisStep34ForUniform` / `gramHypothesis` / `contract` wrappers for both
  families now route through these insertion records (`.toHypothesisStep34ForUniform`,
  `.gramHypothesis`, `.contract`) instead of bypassing the insertion tier.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added missing modEq-derived fallback insertion constructors in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInputConstStep3Step4.ofBGConstOnUIndexOneAddLogStep3FallbackStep4OfModEq`,
  - `GeometryInputConstStep3Step4.ofBGConstOnVIndexOneAddLogStep4FallbackStep3OfModEq`,
  - plus `...ofGeometryInput...OfModEq_from_hF` companions for both U/V fallback routes.
  Then rewired the six constant-input fallback `...ofModEq_from_hF` endpoint wrappers to consume
  these direct insertion constructors (`.toHypothesisStep34ForUniform` / `.gramHypothesis` /
  `.contract`), restoring direct insertion-layer routing with modEq auto-derivation.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Fixed and stabilized the new constant-input fallback `from_hF` wrappers in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` (U-index Step-3 fallback + V-index
  Step-4 fallback families): these now route via
  `GeometryInputConst.ofGeometryInput_from_hF` into the existing constant-input `...ofModEq`
  endpoints, eliminating the intermediate arity mismatch introduced by direct insertion-record
  calls.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added four new `GeometryInputConstStep3Step4` constructors in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` that build BG const-on-index
  Step-3/Step-4 insertion records directly from a fixed rank-one witness `hF0`
  (via `GeometryInputConst.ofGeometryInput_from_hF`):
  - `ofGeometryInputBGConstOnIndexOneAddLogOfModEq_from_hF`,
  - `ofGeometryInputBGConstOnIndexOneAddLog_from_hF`,
  - `ofGeometryInputBGConstOnUIndexOneAddLogStep3FallbackStep4_from_hF`,
  - `ofGeometryInputBGConstOnVIndexOneAddLogStep4FallbackStep3_from_hF`.
  This removes another extraction-constancy seam (`hαconst_extr` / `hβconst_extr`) at the
  insertion-record layer on both non-fallback and fallback BG const-on-index routes.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Tightened the constant-input `from_hF` routing in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` so
  `inputStep3Step4_ofBGGeometry_input_const_coeffReduction_rankOne_step3step4_tight_ofModEq_from_hF`
  now calls the tight insertion endpoint (`...step3step4_tight_ofModEq`) directly.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added missing tight-constant wrappers for the **constant-input coeff-reduction (modEq)**
  insertion tier in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - inside `GeometryInputConst`:
    `toInputStep3Step4_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq`,
    `toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq`,
    `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq`,
    `contract_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq`;
  - top-level insertion aliases:
    `inputStep3Step4_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_tight_ofModEq`,
    `hypothesisStep34ForUniform_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_tight_ofModEq`,
    `gramHypothesis_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_tight_ofModEq`,
    `contract_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_tight_ofModEq`.
  This closes the remaining naming/parity gap between supplied-Step-3/4 and tight-constant
  insertion endpoints on the constant-input coeff-reduction path.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added missing constant-input insertion-layer tight `from_hF` wrappers for the direct non-fallback
  rank-one/modEq coefficient-reduction route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `inputStep3Step4_ofBGGeometry_input_const_coeffReduction_rankOne_step3step4_tight_ofModEq_from_hF`,
  - `hypothesisStep34ForUniform_ofBGGeometry_input_const_coeffReduction_rankOne_step3step4_tight_ofModEq_from_hF`,
  - `gramHypothesis_ofBGGeometry_input_const_coeffReduction_rankOne_step3step4_tight_ofModEq_from_hF`,
  - `contract_ofBGGeometry_input_const_coeffReduction_rankOne_step3step4_tight_ofModEq_from_hF`.
  These route through `GeometryInputConst.ofGeometryInput_from_hF` and the
  `...const_input_coeffReduction_rankOne_step3step4_tight_ofModEq` insertion endpoint.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added missing tight-constant `from_hF` endpoint wrappers for the direct non-fallback
  rank-one/modEq coefficient-reduction route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq_from_hF`,
  - `gramHypothesis_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq_from_hF`,
  - `contract_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq_from_hF`.
  These route through the existing
  `geometryInputStep3Step4_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq_from_hF`
  constructor, so tight Step-3/Step-4 call-sites can now consume a single fixed-rank-one `hF`
  witness instead of separate coefficient-reduction identities.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a reusable extraction helper in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hF_eq_rankOne_of_extractedConst`.
  This theorem packages the repeated derivation
  `g.reduction.F = RankOneShear.coeff ... α0 β0` from extracted coefficient constancy
  (`hαconst`/`hβconst`).
- Rewired the three constant-input coeff-reduction auto routes to use that helper:
  - `hypothesisStep34ForUniform_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq`,
  - `gramHypothesis_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq`,
  - `contract_ofBGGeometry_input_const_coeffReduction_rankOne_ofModEq`.
  Net effect: less duplicated extraction-side plumbing, and one canonical proof path for the
  fixed-rank-one `hF` identity in this insertion layer.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added the missing **auto-Step-2 + class-witness companions** for the non-modEq
  BG const-on-index rank-one route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness_autoTubeForm`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness_autoTubeForm`,
  - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness_autoTubeForm`.
  These wrappers take `Step2ToTubeForm` (`h2`, `hKhat`) and derive `tubeForm_eq` internally via
  `GeometryInputConst.tubeForm_eq_of_step2ToTubeForm`, removing one more manual Step-2 seam on
  flagship class-witness paths.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added the missing **auto-Step-2 + class-witness companions** for the BG const-on-index
  rank-one modEq route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_autoTubeForm`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_autoTubeForm`,
  - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_autoTubeForm`.
  These wrappers consume `Step2ToTubeForm` (`h2`, `hKhat`) and derive `tubeForm_eq` via
  `GeometryInputConst.tubeForm_eq_of_step2ToTubeForm`, giving class-witness parity with the new
  auto non-class-witness endpoints.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added new auto-Step-2 endpoint family for the BG const-on-index (modEq) route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_autoTubeForm`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_autoTubeForm`,
  - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq_autoTubeForm`.
  These consume a packaged `Step2ToTubeForm` witness (`h2`, `hKhat`) and discharge
  `tubeForm_eq` automatically via `GeometryInputConst.tubeForm_eq_of_step2ToTubeForm`, removing
  one more manual Step-2 hypothesis from this flagship endpoint family.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added extraction-side constancy lemmas for the **auto Step-2 rank-one constructor** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hαconst_ofBGGeometryCoeffReduction_rankOne_autoTubeForm`,
  - `hβconst_ofBGGeometryCoeffReduction_rankOne_autoTubeForm`.
  These prove (definitionally) that extracted `α`/`β` for
  `GeometryInput.ofBGGeometryCoeffReduction_rankOne_autoTubeForm` are independent of `(f,i,j)`
  and equal to the fixed rank-one input coefficients (`I0.α`, `I0.β`), closing a remaining
  extraction-side constancy gap on the auto Step-2 pathway.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added missing **combined-index const-input class-witness wrappers** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `...input_const_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`
    (uniform/Gram/contract, non-`from_hF`),
  - routes use `GeometryInputConst.ofGeometryInput` and forward directly to
    `...const_input_BGConstOnIndex...ofClassWitness`.
  This closes another API-parity gap between const-input and rank-one wrappers and removes a
  remaining call-site need to manually introduce index-reference maps when class witnesses are
  available.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added missing **combined-index rank-one class-witness wrappers** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` for both direct and `from_hF` routes:
  - `...input_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`
    (uniform/Gram/contract),
  - `...input_rankOne_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_from_hF`
    (uniform/Gram/contract).
  These derive `mRefU`/`mRefV` from `uRef`/`vRef` via `uIndex`/`vIndex` plus
  `Finset.mem_image.mpr`, then route to the existing combined-index rank-one endpoints.
  Net effect: combined-index rank-one APIs now have class-witness parity with the U/V fallback
  families and no longer require manual index-reference plumbing at call sites.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added `ofModEq_ofClassWitness_from_hF` wrappers for the **U/V fallback rank-one routes** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `...BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq_ofClassWitness_from_hF`
    (rank-one + constant-input insertion layers; uniform/Gram/contract),
  - `...BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq_ofClassWitness_from_hF`
    (rank-one + constant-input insertion layers; uniform/Gram/contract).
  These derive index representatives from class witnesses (`uRef/huRef`, `vRef/hvRef`) and then
  route through existing modEq `from_hF` endpoints, so class-witness call-sites no longer need
  separate class-constancy assumptions.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added constant-input insertion-layer aliases for the BG class-witness fallback routes in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `...input_const_BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofClassWitness_from_hF`
    (uniform/Gram/contract),
  - `...input_const_BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofClassWitness_from_hF`
    (uniform/Gram/contract).
  These consume `(hβmod, hαmod, hF0)` and route through the existing rank-one class-witness
  fallback constructors, so the constant-input insertion tier now has the same `from_hF`
  class-witness entrypoints as the modEq tier.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added `from_hF` wrappers for the **BG class-witness fallback routes** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `...BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofClassWitness_from_hF`
    (uniform/Gram/contract),
  - `...BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofClassWitness_from_hF`
    (uniform/Gram/contract).
  These wrappers consume `(hβmod, hαmod, hF0)` and discharge coefficient-reduction identities
  from `g.reduction` definitionally, then route through the existing coefficient-form class-witness
  constructors.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added `from_hF` wrappers for the **BG const-on-index fallback routes** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, so these endpoint families no longer
  require extracted `hαconst`/`hβconst` assumptions when a fixed rank-one witness is already
  available:
  - `...BGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq_from_hF` (uniform/Gram/contract),
  - `...BGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq_from_hF` (uniform/Gram/contract).
  These route through `GeometryInputConst.ofGeometryInput_from_hF` using `(hβmod, hαmod, hF0)`.
  Net effect: more of the fallback insertion layer now consumes the same `hF`-first plumbing used
  by the non-fallback rank-one/modEq APIs.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a new fixed-rank-one conversion helper in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInputConst.ofGeometryInput_from_hF`.
  This builds `GeometryInputConst` directly from a packaged `GeometryInput` plus a single
  rank-one coefficient witness
  `hF0 : reduction.F = RankOneShear.coeff ... I0.α I0.β`, avoiding separate extracted
  `hαconst`/`hβconst` assumptions.
- Added new geometry-input endpoint families that consume the same `hF0` witness directly for the
  BG const-on-index one-add-log modEq routes:
  - `hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_from_hF`,
  - `gramHypothesis_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_from_hF`,
  - `contract_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_from_hF`,
  - `hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_from_hF`,
  - `gramHypothesis_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_from_hF`,
  - `contract_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness_from_hF`.
  These route through the new conversion helper and remove duplicated constancy plumbing at this
  insertion layer.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added one-record convenience wrappers for the constant-input coefficient-reduction path in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInputConst.toInputStep3Step4_ofBGGeometryCoeffReduction_rankOne_ofModEq`,
  - top-level wrappers
    `inputStep3Step4_ofBGGeometry_const_input_coeffReduction_rankOne_ofModEq` and
    `inputStep3Step4_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_ofModEq`.
  Also rewired auto and supplied endpoint wrappers to consume these one-record builders directly.
  This further consolidates routing through `GeometryInputConstStep3Step4` and removes duplicated
  endpoint plumbing.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added explicit one-record autoTubeForm entrypoints in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `inputStep3Step4_ofBGGeometryCoeffReduction_rankOne_ofModEq_autoTubeForm`,
  - `inputStep3Step4_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq_autoTubeForm`.
  Rewired the corresponding auto hypothesis/Gram/contract endpoints to consume these one-record
  builders directly (`.toHypothesisStep34ForUniform` / `.gramHypothesis` / `.contract`), so the
  Step-2 auto path now has a single insertion point shared across endpoint tiers.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Rewired the two flagship **Step-2 autoTubeForm** endpoint families to route through the new
  one-record insertion constructors in `GeometryInputConstStep3Step4`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq_autoTubeForm`,
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq_autoTubeForm`.
  This removes duplicated direct plumbing in those auto routes and makes them consume the same
  one-record insertion layer now used elsewhere.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a new **one-record Step-2 auto constructor layer** for constant-input non-fallback
  insertion records in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInputConstStep3Step4.ofBGGeometryCoeffReduction_rankOne_ofModEq_autoTubeForm`,
  - `GeometryInputConstStep3Step4.ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq_autoTubeForm`.
  These constructors consume a packaged `Step2ToTubeForm` witness (`h2` + `hKhat`) and route to:
  - auto BG modEq one-add-log Step-3/Step-4 insertion (`ofBGModEqOneAddLog`), or
  - supplied tight Step-3/Step-4 insertion (`step3`, `step4`) with `C3 := step3.C`, `C4 := step4.C`.
  Net effect: Step-2 auto tube-form wiring now lands directly in `GeometryInputConstStep3Step4`
  (the one-record non-fallback insertion point), not only hypothesis/Gram/contract endpoints.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added **Step-2-based auto tube-form constructor family** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` to reduce manual
  `tubeForm_eq` plumbing:
  - `GeometryInput.tubeForm_eq_of_step2ToTubeForm`,
  - `GeometryInput.ofBGGeometryCoeffReduction_autoTubeForm`,
  - `GeometryInput.ofBGGeometryCoeffReduction_rankOne_autoTubeForm`,
  - `GeometryInputConst.tubeForm_eq_of_step2ToTubeForm`,
  - `GeometryInputConst.ofBGGeometryCoeffReduction_autoTubeForm`,
  - `GeometryInputConst.ofBGGeometryCoeffReduction_rankOne_autoTubeForm`.
  These endpoints take a packaged `Step2ToTubeForm` witness (plus `hKhat` identification) and
  derive the required `tubeForm_eq` field automatically before routing into existing BG
  coefficient-reduction constructors.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a new **tight-constant non-fallback API tier** (for supplied Step-3/Step-4 bounds) in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - geometry-input direct coeff-reduction insertions:
    - `geometryInputStep3Step4_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq`,
    - `hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq`,
    - `gramHypothesis_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq`,
    - `contract_ofBGGeometry_input_rankOne_coeffReduction_step3step4_tight_ofModEq`;
  - top-level coefficient-reduction endpoints:
    - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq`,
    - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq`,
    - `contract_ofBGGeometryCoeffReduction_rankOne_step3step4_tight_ofModEq`.
  These constructors set `C3 := step3.C`, `C4 := step4.C` internally (with `hC3/hC4 := le_rfl`),
  so non-fallback use-sites no longer need to pass envelope constants manually.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a dedicated **one-record insertion constructor** for the constant-input, supplied
  non-fallback Step-3/Step-4 rank-one coeff-reduction route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInputConst.toInputStep3Step4_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq`.
  It packages `step3`/`step4` directly into `GeometryInputConstStep3Step4`, with per-`(f,i,j)`
  `step3For`/`step4For` built by rewriting via `g.hF`.
- Rewired the matching `GeometryInputConst` endpoints to consume that insertion record:
  - `toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq`,
  - `contract_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq`.
  This removes duplicated coefficient-reduction plumbing in those endpoint definitions.
- Build check passes:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a **rank-one convenience constructor** for BG geometry inputs with constant coefficients
  (no explicit `hαconst`/`hβconst` plumbing) in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInput.ofBGGeometryCoeffReduction_rankOne`.
  This packages the rank-one `BGTypeIIRankOne.Input` directly into the coefficient-reduction
  geometry input, using modEq constancy hypotheses for `α`/`β` only.
- Added a **fixed-signal TT\* Toeplitz hypothesis interface** and packaged the rank-one box-data
  torus packet identity into it:
  - new `HypothesisFor` in
    `SSU/Instances/FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.lean`,
  - new constructor
    `ttStarToeplitzHypothesisFor_rankOne_boxData` in
    `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean`.
  This gives a clean use-site wrapper for the rank-one extracted signal
  `fTT` in Toeplitz form (with `I.boxData`).
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne`.
- Added a **box-data weighted-integral `onJ` wrapper** for the rank-one torus packets in
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean`:
  - `inner_packetOpUnnormalized_eq_weightedIntegral_rankOne_boxData_onJ`.
  This matches the earlier box-data integral identity but fits heart-facing `i,j ∈ J` APIs.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne`.
- Added **box-data Toeplitz TT\*** endpoints for the rank-one torus packets in
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean`:
  - `inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne_boxData`,
  - `inner_packetOpUnnormalized_eq_toeplitzFormTeXC_rankOne_boxData_onJ`.
  These rewrite the weighted-integral identity directly into
  `toeplitzFormTeXC` with `I.boxData` (no manual `prodSumRealByProd` re-expansion at call sites).
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne`.
- Added a **non-fallback constant-input coeff-reduction route** (supplied Step-3/Step-4, modEq)
  in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - new `GeometryInputConst` endpoints:
    - `toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq`,
    - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq`,
    - `contract_ofBGGeometryCoeffReduction_rankOne_step3step4_ofModEq`;
  - new top-level one-record wrappers:
    - `hypothesisStep34ForUniform_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_ofModEq`,
    - `gramHypothesis_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_ofModEq`,
    - `contract_ofBGGeometry_const_input_coeffReduction_rankOne_step3step4_ofModEq`.
  These consume `step3`/`step4` directly for the fixed rank-one coeff array
  `RankOneShear.coeff td g.α0 g.β0` and discharge `inner_eq_coeff`/`energy_le_coeff`
  from `g.reduction` + `g.hF`, removing duplicated call-site plumbing on the
  non-fallback path.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a new **direct rank-one coeff-reduction one-record layer** for `GeometryInput` in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` that removes extracted-constancy
  assumptions (`hαconst`/`hβconst`) from these routes:
  - auto one-add-log modEq endpoints:
    - `hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_coeffReduction_direct_ofModEq`,
    - `gramHypothesis_ofBGGeometry_input_rankOne_coeffReduction_direct_ofModEq`,
    - `contract_ofBGGeometry_input_rankOne_coeffReduction_direct_ofModEq`;
  - supplied non-fallback Step-3/Step-4 endpoints:
    - `hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_coeffReduction_step3step4_direct_ofModEq`,
    - `gramHypothesis_ofBGGeometry_input_rankOne_coeffReduction_step3step4_direct_ofModEq`,
    - `contract_ofBGGeometry_input_rankOne_coeffReduction_step3step4_direct_ofModEq`.
  These route via the existing coefficient-form `GeometryInput` APIs and accept direct
  rank-one/modEq + `inner_eq_coeff`/`energy_le_coeff` hypotheses instead of extracted coefficient
  constancy across `(f,i,j)`.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a **class-witness completion layer** for the constant-input BG const-on-index route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - new constant-input constructors:
    - `GeometryInputConst.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofClassWitness`,
    - `GeometryInputConst.toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`;
  - new constant-input endpoints (uniform/Gram/contract) for both class-constancy and
    modEq-derived variants:
    - `...toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofClassWitness`,
    - `...gramHypothesis_ofBGConstOnIndex_oneAddLog_ofClassWitness`,
    - `...contract_ofBGConstOnIndex_oneAddLog_ofClassWitness`,
    - `...toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`,
    - `...gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`,
    - `...contract_ofBGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`;
  - new top-level one-record wrappers for the same class-witness paths:
    - `hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofClassWitness`,
    - `gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofClassWitness`,
    - `contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofClassWitness`,
    - `hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`,
    - `gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`,
    - `contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq_ofClassWitness`.
  These remove direct `(mRefU, hmRefU, mRefV, hmRefV)` plumbing at call sites and keep the
  constant-input flagship path aligned with the existing coefficient-reduction class-witness API.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added **one-record consumption endpoints** that wire the new auto rank-one/modEq
  coeff-reduction route into the constant-input flagship-plumbing layer in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `GeometryInputConst.toHypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq`,
  - `GeometryInputConst.gramHypothesis_ofBGGeometryCoeffReduction_rankOne_ofModEq`,
  - `GeometryInputConst.contract_ofBGGeometryCoeffReduction_rankOne_ofModEq`,
  - plus top-level wrappers
    `hypothesisStep34ForUniform_ofBGGeometry_const_input_coeffReduction_rankOne_ofModEq`,
    `gramHypothesis_ofBGGeometry_const_input_coeffReduction_rankOne_ofModEq`,
    `contract_ofBGGeometry_const_input_coeffReduction_rankOne_ofModEq`.
  These discharge `inner_eq_coeff`/`energy_le_coeff` from `g.reduction` via `g.hF` and remove
  explicit step3/step4 and residue-reference plumbing at this insertion layer.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added direct **auto Step-3/Step-4 one-add-log wrappers** for rank-one coeff-reduction + modEq in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_ofModEq`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_ofModEq`,
  - `contract_ofBGGeometryCoeffReduction_rankOne_ofModEq`.
  These route through `GeometryInput.hypothesisStep34ForUniform_ofBGGeometryCoeffReduction` and
  remove manual use-site `step3/step4` arguments for this endpoint family.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a new **non-fallback Step-3/Step-4 coefficient-reduction insertion route** in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_step3step4`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_step3step4`,
  - `contract_ofBGGeometryCoeffReduction_step3step4`.
  These endpoints take the real extracted coefficient-form inputs (`α,β`, `inner_eq_coeff`,
  `energy_le_coeff`) plus supplied use-site Step-3 and Step-4 bounds, then route directly to the
  TeX Step-5 packaging/Gram/contract without using fallback Step-3/Step-4 constructors.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Discharged the symmetric **V-side extraction-constancy obligation** at the geometry-input layer
  by adding modEq-derived endpoints (no explicit `hαconst` assumption) in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `toUniformInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq`,
  - `toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq`,
  - `gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq`,
  - `contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3_ofModEq`.
  These derive the required V-index constancy directly from `g.hαmod_sig` plus residue-partition
  geometry (`vFromIndex`/`vResidue` modEq lemmas), completing U/V parity at this geometry-input
  insertion layer.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Discharged the first **U-side extraction-constancy obligation** at the geometry-input layer by
  adding modEq-derived endpoints (no explicit `hβconst` assumption) in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq`,
  - `toHypothesisStep34ForUniform_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq`,
  - `gramHypothesis_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq`,
  - `contract_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4_ofModEq`.
  These derive the required U-index constancy directly from `g.hβmod_sig` plus residue-partition
  geometry (`uFromIndex`/`uResidue` modEq lemmas), matching the existing full-index modEq pattern.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added **fallback-side `ofModEq` parity** (plus class-witness discharge) for coefficient-reduction
  BG one-add-log routes in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - new `..._step3_fallback_step4_ofModEq` and `..._step4_fallback_step3_ofModEq` endpoint
    families (hypothesis/Gram/contract);
  - new matching `..._ofModEq_ofClassWitness` wrappers for both fallback directions
    (hypothesis/Gram/contract), deriving index references from geometric class witnesses;
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added fallback-side coefficient-reduction endpoint parity with class-witness discharge in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - new one-shot endpoints for Step-3-proved/Step-4-fallback and Step-4-proved/Step-3-fallback:
    - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`,
    - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`,
    - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnUIndex_oneAddLog_step3_fallback_step4`,
    - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`,
    - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`,
    - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnVIndex_oneAddLog_step4_fallback_step3`;
  - added matching class-witness/class-constancy wrappers that derive index references internally:
    - `...step3_fallback_step4_ofClassWitness` (hypothesis/Gram/contract),
    - `...step4_fallback_step3_ofClassWitness` (hypothesis/Gram/contract);
  - these wrappers use `uFromIndex`/`vFromIndex` class-membership lemmas to discharge
    index-reference constancy from geometric class witnesses.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added a new **class-witness + class-constancy** API tier for the non-modEq coefficient-reduction
  BG-const-on-index one-add-log route in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness`,
  - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofClassWitness`.
  These wrappers:
  - accept geometric witnesses `uRef ∈ uClass(r)` / `vRef ∈ vClass(r)` and class-level constancy
    hypotheses on `β`/`α`,
  - derive reference indices `mRefU := uIndex(uRef)`, `mRefV := vIndex(vRef)` and the required
    index-reference constancy lemmas internally via `uFromIndex`/`vFromIndex` class-membership
    lemmas from `TypeIIResiduePartition`,
  - route directly into the existing non-modEq one-add-log insertion chain.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added and compile-stabilized the **non-modEq** coefficient-reduction rank-one
  BG-const-on-index one-add-log endpoint family in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog`,
  - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog`,
  - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog`.
  Fixes included:
  - corrected named-argument routing to
    `hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog`
    (`hβconst` / `hαconst`);
  - rewired Gram/contract wrappers through explicit constant-input endpoint constructors,
    avoiding dependent projection mismatches from local `let` bindings.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added direct one-shot **coefficient-reduction + fixed rank-one input** endpoints that remove the
  extraction-side constancy obligations (`hαconst`/`hβconst`) from this route:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added:
    - `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq`,
    - `gramHypothesis_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq`,
    - `contract_ofBGGeometryCoeffReduction_rankOne_BGConstOnIndex_oneAddLog_ofModEq`;
  - these build `GeometryInputConst` directly via
    `GeometryInputConst.ofBGGeometryCoeffReduction` with `I0.α/I0.β`, then route through the
    existing modEq-derived const-on-index insertion chain;
  - net effect: for the fixed-rank-one flagship path, callers no longer need to separately prove
    or pass extracted-coefficient constancy across `(f,i,j)`;
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Added rank-one-input endpoints for the modEq-derived const-on-index route:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added one-record wrappers that
    consume a fixed `BGTypeIIRankOne.Input` (instead of separate `(α0,β0)` functions):
    - `hypothesisStep34ForUniform_ofBGGeometry_input_rankOne_BGConstOnIndex_oneAddLog_ofModEq`,
    - `gramHypothesis_ofBGGeometry_input_rankOne_BGConstOnIndex_oneAddLog_ofModEq`,
    - `contract_ofBGGeometry_input_rankOne_BGConstOnIndex_oneAddLog_ofModEq`;
  - net effect: flagship callers with extracted rank-one coefficients now pass directly through the
    modEq-derived const-on-index endpoint family with less plumbing.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Coefficient-form one-shot endpoint wrappers (`hypothesis`/`Gram`/`contract`) compile-stabilized:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, fixed the new
    `GeometryInput.ofBGGeometryCoeffReduction` endpoint wrappers to avoid premature
    dot-notation projection on not-yet-defined `GeometryInput` methods at that source location;
  - wrappers now route through `UniformInput.ofBGGeometry` +
    `UniformInputStep3Step4.ofBGModEqOneAddLog` directly, and then expose:
    `hypothesisStep34ForUniform_ofBGGeometryCoeffReduction`,
    `gramHypothesis_ofBGGeometryCoeffReduction`,
    `contract_ofBGGeometryCoeffReduction`;
  - net effect: the new coefficient-form constructor + one-shot endpoint API is now build-stable.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big flagship plumbing discharge batch completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added
    coefficient-form convenience constructors that build reduction records directly with
    `F_{i,j,f} = RankOneShear.coeff ...` and discharge `hF` by `rfl`:
    - `GeometryInput.ofBGGeometryCoeffReduction`,
    - `GeometryInputConst.ofBGGeometryCoeffReduction`;
  - net effect: flagship callers no longer need to separately provide `hF` when their
    reduction hypotheses are already stated in rank-one coefficient form;
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Batch 3/3 (geometry-input const-extraction endpoint completion) completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added
    `GeometryInputConstStep3Step4` constructors:
    - `ofGeometryInputBGConstOnIndexOneAddLog`,
    - `ofGeometryInputBGConstOnUIndexOneAddLogStep3FallbackStep4`,
    - `ofGeometryInputBGConstOnVIndexOneAddLogStep4FallbackStep3`;
  - added matching top-level one-record endpoint families (hypothesis/Gram/contract)
    for geometry-input + extracted-constness on all three routes:
    - non-fallback const-on-index one-add-log,
    - U-side one-add-log (Step-3 proved, Step-4 fallback),
    - V-side one-add-log (Step-4 proved, Step-3 fallback);
  - net effect: callers starting from `GeometryInput` + extracted coefficient constancy
    can now reach Step34 insertion, Gram hypotheses, and final contracts without manual
    conversion to `GeometryInputConst`;
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Batch 2/3 (geometry-input const-extraction modEq route wiring) completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added a new constructor on
    `GeometryInputConstStep3Step4`:
    - `ofGeometryInputBGConstOnIndexOneAddLogOfModEq`
      (takes `GeometryInput` + extracted-coefficient constancy proofs for `α,β`,
      then routes through the existing constant-input modEq-derived BG one-add-log insertion path);
  - added matching top-level one-record endpoints from `GeometryInput` with const extraction:
    - `hypothesisStep34ForUniform_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq`,
    - `gramHypothesis_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq`,
    - `contract_ofBGGeometry_input_const_BGConstOnIndex_oneAddLog_ofModEq`;
  - net effect: the “real extracted constant coefficients” path now has a direct API from
    geometry-input records to Step-3/Step-4 insertion, Gram, and final contract, without manual
    hand-conversion to `GeometryInputConst` at call sites.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Batch 1/3 (extraction-to-const-input closure) completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added two new
    constructors under `GeometryInputConst`:
    - `ofBGGeometry` (convenience constructor for constant extracted coefficients),
    - `ofGeometryInput` (derives a constant-coefficient package from a `GeometryInput`
      plus constancy proofs for extracted `α, β` across `(f,i,j)`).
  - key effect: `hF` closure is now packaged as reusable plumbing; once extraction
    constancy is proved, the constant-input bridge can be built without duplicating
    manual `RankOneShear.coeff` rewrite boilerplate.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big Step-4-first (non-fallback) insertion-path parity batch completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, completed the missing
    constant-input and one-record wrapper parity for the new V-side one-add-log route
    (Step 4 proved, Step 3 fallback):
    - added constant-input insertion endpoint
      `toInputStep3Step4_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3`,
    - added constant-input hypothesis/Gram/contract endpoints
      `toHypothesisStep34ForUniform_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3`,
      `gramHypothesis_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3`,
      `contract_ofBGConstOnVIndex_oneAddLog_step4_fallback_step3`,
    - added top-level one-record wrappers
      `hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3`,
      `gramHypothesis_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3`,
      `contract_ofBGGeometry_const_input_BGConstOnVIndex_oneAddLog_step4_fallback_step3`.
  - net effect: U-side and V-side one-add-log hybrid routes are now symmetric through
    geometry-input + constant-input API layers, including one-record endpoints through contract.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big Step-3-first (non-fallback) insertion-path batch completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added a new U-side one-add-log
    route that proves Step 3 from `sumFiberUZ` geometry/equality hypotheses and keeps Step 4 on the
    existing fallback:
    - `toUniformInputStep3Step4_of_sumFiberUZ_ref_on_zSet_oneAddLog_step3_fallback_step4`,
    - matching geometry-input endpoints to hypothesis/Gram/contract.
  - added BG-specialized U-only constancy route:
    - `toUniformInputStep3Step4_ofBGConstOnUIndex_oneAddLog_step3_fallback_step4`,
    - matching geometry-input one-record wrappers
      `..._ofBGGeometry_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4`.
  - extended constant-input plumbing end-to-end for the same Step-3-first route:
    - insertion constructor `GeometryInputConstStep3Step4.ofBGConstOnUIndexOneAddLogStep3FallbackStep4`,
    - `toInput...`, `toHypothesis...`, `gramHypothesis...`, `contract...`,
    - top-level one-record wrappers
      `..._ofBGGeometry_const_input_BGConstOnUIndex_oneAddLog_step3_fallback_step4`.
  - net effect: there is now a full packaged path where Step 3 is genuinely proved from U-side
    geometry/equalities while Step 4 can remain fallback, at both geometry-input and constant-input
    API layers.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big geometry-input Step-4-fallback MV parity batch completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added the missing one-record
    geometry-input wrappers for “MV Step 4 + fallback Step 3”:
    - `hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughanStep4_fallback_step3`,
    - `hypothesisStep34ForUniform_ofBGGeometry_input_montgomeryVaughanByResidueStep4_fallback_step3`,
    - `gramHypothesis_ofBGGeometry_input_montgomeryVaughanStep4_fallback_step3`,
    - `gramHypothesis_ofBGGeometry_input_montgomeryVaughanByResidueStep4_fallback_step3`,
    - `contract_ofBGGeometry_input_montgomeryVaughanStep4_fallback_step3`,
    - `contract_ofBGGeometry_input_montgomeryVaughanByResidueStep4_fallback_step3`.
  - net effect: geometry-input one-record API is now aligned with constant-input parity for both
    fallback directions and both MV variants (global + per-residue) through hypothesis/Gram/contract.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big constant-input Step-4-fallback parity batch completed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added full constant-input API
    parity for “supplied/MV Step 4 + fallback Step 3”:
    - `GeometryInputConst` endpoints:
      `toInputStep3Step4_ofStep4WithFallbackStep3`,
      `toInputStep3Step4_ofMontgomeryVaughanStep4FallbackStep3`,
      `toInputStep3Step4_ofMontgomeryVaughanByResidueStep4FallbackStep3`,
      and matching hypothesis/Gram/contract endpoints;
    - one-record wrappers:
      `hypothesisStep34ForUniform_ofBGGeometry_const_input_step4_fallback_step3`,
      `gramHypothesis_ofBGGeometry_const_input_step4_fallback_step3`,
      `contract_ofBGGeometry_const_input_step4_fallback_step3`,
      plus MV/by-residue Step4-fallback variants.
  - net effect: constant-input wiring now matches geometry-input wiring for both fallback directions
    (Step3→fallback Step4 and Step4→fallback Step3), including MV and supplied-step insertion routes.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big hybrid API expansion: MV Step 3 + fallback Step 4 now wired end-to-end.
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added new hybrid constructor
    routes that keep Step 4 on the BG one-add-log fallback while sourcing Step 3 from MV:
    - geometry-input level:
      `toUniformInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4`,
      `toUniformInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4`,
      plus corresponding `toHypothesis...`, `gramHypothesis...`, `contract...` endpoints;
    - insertion-record level:
      `GeometryInputStep3Step4.ofMontgomeryVaughanStep3FallbackStep4`,
      `GeometryInputStep3Step4.ofMontgomeryVaughanByResidueStep3FallbackStep4`;
    - constant-input insertion record + endpoint chain:
      `GeometryInputConstStep3Step4.ofMontgomeryVaughanStep3FallbackStep4`,
      `GeometryInputConstStep3Step4.ofMontgomeryVaughanByResidueStep3FallbackStep4`,
      `toInputStep3Step4_ofMontgomeryVaughanStep3FallbackStep4`,
      `toInputStep3Step4_ofMontgomeryVaughanByResidueStep3FallbackStep4`,
      and matching hypothesis/Gram/contract endpoints;
    - top-level one-record wrappers for both geometry-input and constant-input variants.
  - net effect: we now have a fully packaged “proved Step 3 route, fallback Step 4 route” API
    parallel to the existing fully non-fallback and fully supplied-step3 families.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Hybrid Step-3 supplied + fallback Step-4 API batch finalized and build-fixed:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, completed the endpoint chain for
    “supplied Step-3 (`step3For`) + fallback Step 4” at both geometry-input and constant-input
    layers, through to one-record `HypothesisStep34ForUniform`, `GramHypothesis`, and contracts;
  - fixed two projection/parser blockers in the new one-record wrappers by normalizing to explicit
    `let`-bound record projections;
  - net effect: this hybrid route is now stable and callable end-to-end from one-record inputs.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big const-input modEq-derived endpoint parity batch:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, extended the
    BG const-on-index one-add-log **modEq-derived** route across the constant-input layer:
    - added insertion constructor
      `GeometryInputConstStep3Step4.ofBGConstOnIndexOneAddLogOfModEq`;
    - added `GeometryInputConst` endpoints:
      `toInputStep3Step4_ofBGConstOnIndex_oneAddLog_ofModEq`,
      `toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog_ofModEq`,
      `gramHypothesis_ofBGConstOnIndex_oneAddLog_ofModEq`,
      `contract_ofBGConstOnIndex_oneAddLog_ofModEq`;
    - added one-record top-level wrappers:
      `hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq`,
      `gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq`,
      `contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog_ofModEq`.
  - net effect: the modEq-derived const-on-index path is now API-complete at both geometry-input
    and constant-input one-record levels, up through final SSU contracts.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big modEq-derived BG const-on-index endpoint stabilization + wrapper expansion:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, fixed the new
    `..._ofModEq` route to use the correct residue primitives
    (`SSU.Engines.TypeII.LargeSieve.vResidue` / `uResidue`);
  - added one-record geometry-input wrappers for the modEq-derived const-on-index path:
    - `hypothesisStep34ForUniform_ofBGGeometry_input_BGConstOnIndex_oneAddLog_ofModEq`,
    - `gramHypothesis_ofBGGeometry_input_BGConstOnIndex_oneAddLog_ofModEq`,
    - `contract_ofBGGeometry_input_BGConstOnIndex_oneAddLog_ofModEq`;
  - net effect: callers can now use the modEq assumptions directly at the one-record geometry
    API layer, with no manual unpacking and no identifier breakage in the endpoint chain.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big constant-input BG const-on-index non-fallback API expansion:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added a new constructor on the
    one-record insertion type:
    - `GeometryInputConstStep3Step4.ofBGConstOnIndexOneAddLog`;
  - added matching constant-input endpoint chain in `GeometryInputConst`:
    - `toInputStep3Step4_ofBGConstOnIndex_oneAddLog`,
    - `toHypothesisStep34ForUniform_ofBGConstOnIndex_oneAddLog`,
    - `gramHypothesis_ofBGConstOnIndex_oneAddLog`,
    - `contract_ofBGConstOnIndex_oneAddLog`;
  - added one-record top-level wrappers:
    - `hypothesisStep34ForUniform_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog`,
    - `gramHypothesis_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog`,
    - `contract_ofBGGeometry_const_input_BGConstOnIndex_oneAddLog`;
  - net effect: BG geometry + residue-index constancy hypotheses on fixed extracted coefficients
    (`α₀`,`β₀`) now flow directly through the constant non-fallback insertion path to uniform
    Step-5 packages, Gram hypotheses, and final contracts.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Major Step-3/Step-4 torus packet wrapper stabilization:
  - in `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.lean`, completed the full
    proof of `norm_inner_packetOpUnnormalized_le` with no placeholder assumptions by:
    - proving scalar norm factorization cleanly (`1/X` extraction),
    - replacing brittle pointwise simplification with direct `rw`/`calc` steps for
      `‖S * star S‖ = ‖S‖^2`,
    - rewriting Step-5 integration via restricted-measure `integral_mono_of_nonneg`,
      explicit `Khat_integrableOn`, and `integral_mul_const`,
    - discharging kernel moment on the exact band domain by explicit band=`Icc` normalization,
    - proving `tubeEnergy` nonnegativity locally as geometry-free finite-sum positivity,
    - adding a local heartbeat override on the theorem to avoid elaboration timeout in this
      large expression.
  - net effect: the previously failing Step-3/Step-4 bound wrapper now compiles end-to-end and
    directly bridges the Toeplitzized packet Gram to the Step34 product-sum hypothesis.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound`,
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne
      SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsStep34Bound
      SSU.Instances.FejerBankedPlatinum`.
- Added rank-one torus packet TT* identities in weighted-band form:
  - in `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean`, added
    `inner_packetOpUnnormalized_eq_weightedIntegral_rankOne` and
    `inner_packetOpUnnormalized_eq_weightedIntegral_rankOne_onJ`, giving the exact TeX-style
    weighted-band integral (with `signalRealByProd`) for the rank-one torus packet Gram entry.
  - fixed `FejerBankedTypeIIToeplitzTorusRankOneTTStar.lean` to use the current
    `BGTypeIIRankOne.Input` signal names and the explicit `H0 := SSU.Torus.L2` box-data packaging.
  - net effect: the rank-one torus TT* bridge now exposes both Toeplitz-form and weighted-integral
    statements, aligned with the `TTStarHypothesis` interfaces for downstream use-site wiring.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIToeplitzTorusPacketsRankOne`.
- Big non-fallback Toeplitz bridge wiring chunk (use-site Step-3/Step-4 route now transported
  through normalization + Fourier-core conjugation):
  - in `SSU/Engines/TypeIIToeplitz.lean`, added:
    - `Step34ProdSumFor.prodSum_mul_const`,
    - `Step34ProdSumFor.mul_const`,
    - `Step34ProdSumFor.mul_const_C`;
  - in `SSU/Instances/TorusDyadicShellToeplitzReduction.lean`, added transport simp lemmas:
    - `reductionUnnormalizedToNormalized_F`,
    - `reductionToCore_F`,
    - `reductionToCore_reductionUnnormalizedToNormalized_F`;
  - in `SSU/Instances/FejerBankedTypeIIToeplitzBridge.lean`:
    - completed `HypothesisFor.gramHypothesis` wiring via `gramHypothesis_of_step2KernelRep_for_uniform`
      using transported/scaled use-site bounds (`step34For`) rather than the global Step34 fallback;
    - now explicitly scales extracted arrays by `normFactor` in the normalized packet path and then
      transfers to `Global.Signal` through `l2ZToTorus`.
  - net effect: the Toeplitz flagship bridge now has a **working use-site non-fallback insertion
    path** compatible with normalized torus packets and the SSU core ambient.
  - Build checks pass:
    `lake build SSU.Engines.TypeIIToeplitz`,
    `lake build SSU.Instances.TorusDyadicShellToeplitzReduction`,
    `lake build SSU.Instances.FejerBankedTypeIIToeplitzBridge`.
- Big non-fallback Step-3/Step-4 constructor batch from geometry-friendly fiber equalities:
  - in `SSU/Engines/TypeIILargeSieveTeXFor.lean`, added residue-class one-add-log constructors
    that do **not** assume rank-one/modEq, only per-residue common-domain equalities:
    - `Step3FiberLargeSieveByResidueFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog`,
    - `Step4FiberLargeSieveByResidueFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog`;
  - added outer wrappers:
    - `Step3LargeSieveOuterUFor.of_sumFiberUZ_uFromIndex_eq_ref_on_zSet_oneAddLog`,
    - `Step4LargeSieveOuterVFor.of_sumFiberVZ_vFromIndex_eq_ref_on_zSetV_oneAddLog`;
  - added combined Step-5 constructor:
    - `Step34LargeSieveTeXFor.of_sumFiber_ref_on_zSet_oneAddLog`;
  - net effect: Step-3/Step-4/Step-5 use-site plumbing now has a direct non-fallback route from
    deterministic residue-class geometry/extraction equalities (`hZeq` + `hEqOn`) without going
    through the rank-one/modEq specialization.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big bridge-plumbing unblock in the TeX toy endpoint:
  - in `SSU/Instances/FejerBankedPlatinumTypeIIToeplitzToy.lean`, replaced the
    `ReductionInputTeXTrivial` proof packaging (which had two blocked coercion/equality goals)
    with a direct call to
    `FejerBankedTypeIIToeplitzBridge.mk_trivialStep34`;
  - this removes the fragile intermediate `hData`/`hK` obligations at the toy wrapper level while
    preserving the same mathematical object (`reductionTorus` from the TeX toy reduction);
  - net effect: the previously failing toy bridge module now builds again end-to-end.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIToeplitzBridge
      SSU.Instances.FejerBankedPlatinumTypeIIToeplitzToyTeX
      SSU.Instances.FejerBankedPlatinumTypeIIToeplitzToy`.
- Geometry-first Step-3/Step-4/Step-5 constructor batch for BG rank-one/modEq:
  - in `SSU/Engines/TypeIILargeSieveTeXFor.lean`, added
    `Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry`,
    `Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry`, and
    `Step34LargeSieveTeXFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry`;
  - these constructors now derive positivity/division side conditions from geometric natural
    hypotheses (`D ≥ 1`, `U ≥ 1`, `q ≤ D`, `X > 0`, `H > 1`) instead of requiring the derived
    real-side assumptions directly;
  - rewired `GeometryInput.step3For` / `GeometryInput.step4For` in
    `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean` to use the new geometry-first
    constructors;
  - fixed `GeometryInputStep3Step4` packaging to build its hypothesis path through
    `UniformInputStep3Step4` directly, avoiding forward-reference fragility;
  - build check passes:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big API completion swing on MV endpoints for BG geometry records:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added direct
    `GeometryInput` endpoints for global/per-residue MV hypotheses:
    - `toUniformInputStep3Step4_ofMontgomeryVaughan`,
    - `toUniformInputStep3Step4_ofMontgomeryVaughanByResidue`,
    - `toHypothesisStep34ForUniform_ofMontgomeryVaughan`,
    - `toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidue`,
    - `gramHypothesis_ofMontgomeryVaughan`,
    - `gramHypothesis_ofMontgomeryVaughanByResidue`,
    - `contract_ofMontgomeryVaughan`,
    - `contract_ofMontgomeryVaughanByResidue`;
  - added matching constant-input endpoints on `GeometryInputConst`:
    - `toInputStep3Step4_ofMontgomeryVaughan`,
    - `toInputStep3Step4_ofMontgomeryVaughanByResidue`,
    - `toHypothesisStep34ForUniform_ofMontgomeryVaughan`,
    - `toHypothesisStep34ForUniform_ofMontgomeryVaughanByResidue`,
    - `gramHypothesis_ofMontgomeryVaughan`,
    - `gramHypothesis_ofMontgomeryVaughanByResidue`,
    - `contract_ofMontgomeryVaughan`,
    - `contract_ofMontgomeryVaughanByResidue`;
  - net effect: callers can now go from one-record geometry inputs + MV assumptions straight to
    Step-3/Step-4 insertion objects, uniform Step-5 hypotheses, Gram hypotheses, and final
    contracts without manually unpacking `UniformInput`/`UniformInputStep3Step4`.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big MV insertion-point integration for BG rank-one bridge:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added non-fallback constructors
    on `UniformInputStep3Step4`:
    - `ofMontgomeryVaughan`,
    - `ofMontgomeryVaughanByResidue`;
  - these route global/per-residue MV hypotheses through
    `step3FiberLargeSieve_of_montgomeryVaughan` / `step4FiberLargeSieve_of_montgomeryVaughan`,
    then `step3OuterU_of_fiberLargeSieve` / `step4OuterV_of_fiberLargeSieve`, and finally into
    use-site `Step3LargeSieveOuterUFor` / `Step4LargeSieveOuterVFor` envelopes;
  - in `GeometryInputConstStep3Step4`, added matching constructors:
    - `ofMontgomeryVaughan`,
    - `ofMontgomeryVaughanByResidue`;
  - net effect: we now have a direct, proved-API path from MV-level inputs into the constant
    rank-one non-fallback Step-3/Step-4 insertion record, ready for real Step-3/Step-4 proofs.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Ambitious non-fallback packaging step (constant rank-one insertion point):
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added
    `GeometryInputConstStep3Step4`, a one-record non-fallback interface carrying:
    - `base : GeometryInputConst`,
    - supplied use-site `step3For` / `step4For`,
    - envelope constants `C3`, `C4` and bounds;
  - added endpoint methods:
    - `GeometryInputConstStep3Step4.toHypothesisStep34ForUniform`,
    - `GeometryInputConstStep3Step4.gramHypothesis`,
    - `GeometryInputConstStep3Step4.contract`;
  - added compatibility lift:
    `GeometryInputConstStep3Step4.ofBGModEqOneAddLog`;
  - added one-record top-level endpoints:
    `gramHypothesis_ofBGGeometry_const_input_step3step4`,
    `contract_ofBGGeometry_const_input_step3step4`;
  - net effect: we now have a production one-record insertion point for replacing fallback
    Step-3/Step-4 with proved use-site bounds in the constant extracted rank-one path.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big non-fallback constant-input insertion-point expansion (BG rank-one bridge):
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added direct constant-coefficient
    Step-3/Step-4 endpoints:
    - `hypothesisStep34ForUniform_ofBGGeometry_const_step3step4`,
    - `gramHypothesis_ofBGGeometry_const_step3step4`,
    - `contract_ofBGGeometry_const_step3step4`;
  - these expose the decoupled non-fallback path (`step3For`, `step4For`, `C3`, `C4`) for
    `GeometryInputConst`, so the first real extracted rank-one signal can now be wired without
    reintroducing `(f,i,j)`-indexed coefficient boilerplate.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big bridge-API simplification for constant rank-one extraction data:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added
    `BGRankOne.GeometryInputConst`, a one-record route for BG geometry + reduction plumbing when
    extracted rank-one coefficients are constant in `(f,i,j)` (`α0`, `β0`);
  - added adapters/endpoints:
    - `GeometryInputConst.toGeometryInput`,
    - `GeometryInputConst.toUniformInput`,
    - `GeometryInputConst.toUniformInputStep3Step4`,
    - `GeometryInputConst.toHypothesisStep34ForUniform`,
    - `GeometryInputConst.gramHypothesis`,
    - `GeometryInputConst.contract`;
  - added direct constructors:
    `hypothesisStep34ForUniform_ofBGGeometry_const`,
    `gramHypothesis_ofBGGeometry_const`,
    `contract_ofBGGeometry_const`;
  - net effect: the first non-toy rank-one pipeline no longer needs repeated
    `hβmod_sig`/`hαmod_sig` boilerplate over `(f,i,j)`, reducing call-site friction for the
    upcoming TeX-strength Step-3/Step-4 insertions.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big bridge-proof consolidation (non-fallback Step-3/Step-4 → Step-5 path):
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added a shared deterministic
    comparison lemma for `Step34LargeSieveTeXFor.of_step3_step4` constants:
    `step34_of_step3_step4_C_le_C34_from_C3C4` (and module-level aux variant);
  - rewired all three duplicated Step-5 envelope proofs to use that one lemma:
    - `UniformInput.step34For_C_le_C34_from_C3C4`,
    - `UniformInputStep3Step4.step34For_C_le_C34_from_C3C4`,
    - the local `C34_le` proof inside
      `hypothesisStep34ForUniform_ofBGGeometry_step3step4`;
  - net effect: one canonical proof path for the `sqrt(C3*C4)` envelope, less duplicate algebra,
    and lower risk of drift between fallback/non-fallback bridge variants.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big non-fallback insertion-point batch (Step-3/Step-4 supplied route):
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added
    `UniformInputStep3Step4`, a decoupled bridge input that accepts user-supplied use-site
    `step3For'` / `step4For'` objects plus envelope bounds (`C3`,`C4`);
  - added the full derived chain on this new input:
    `step34For`, `C34_from_C3C4`, `toHypothesisStep34ForUniform`, `gramHypothesis`, `contract`;
  - added compatibility lift
    `UniformInputStep3Step4.ofBGModEqOneAddLog` so the current BG one-add-log route plugs into the
    new abstraction immediately;
  - rewired `GeometryInput` adapters (`toHypothesisStep34ForUniform`, `step3For`, `step4For`,
    `gramHypothesis`, `contract`) through this decoupled Step-3/Step-4 path.
  - This cleanly separates “bridge plumbing” from “how Step-3/Step-4 are proved,” which is the
    main prerequisite for replacing fallback routes with TeX-strength proofs.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Significant Step-3/Step-4 → Step-5 rewiring in the BG rank-one flagship bridge:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`,
    `UniformInput.step34For` now is built by
    `Step34LargeSieveTeXFor.of_step3_step4 (step3For) (step4For)` (instead of calling the
    monolithic BG Step-5 constructor directly);
  - added explicit deterministic Step-5 envelope derived from Step-3/Step-4 envelopes:
    `UniformInput.C34_from_C3C4`, `C34_from_C3C4_nonneg`,
    `step34For_C_le_C34_from_C3C4`;
  - `toHypothesisStep34ForUniform` now consumes this new Step-3/Step-4-derived `C34` envelope;
  - net effect: the use-site Step-5 wiring now explicitly flows through proved Step-3 and
    Step-4 endpoints with bridge-level constant control.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Significant Step-3/Step-4 constant-envelope discharge for the BG rank-one/modEq route:
  - in `SSU/Engines/TypeIILargeSieveTeXFor.lean`, added deterministic coefficient-independence
    theorems and canonical envelope constants for both use-site interfaces:
    - `Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog_C_eq`,
      `Step3LargeSieveOuterUFor.bgRankOneModEqOneAddLogC`,
      `Step3LargeSieveOuterUFor.of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC`;
    - `Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog_C_eq`,
      `Step4LargeSieveOuterVFor.bgRankOneModEqOneAddLogC`,
      `Step4LargeSieveOuterVFor.of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC`;
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, exposed these envelopes at the
    flagship bridge level via `UniformInput.C3`, `UniformInput.C4`,
    `UniformInput.step3For_C_le_C3`, and `UniformInput.step4For_C_le_C4`;
  - this materially tightens Step-3/Step-4 use-site plumbing and makes constant control explicit
    before the final non-fallback outer-`u`/outer-`v` closure.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big consolidation: moved direct box-geometry Gram/contract constructors into the core TeX bridge
  module and rewired fallback entrypoints to use them:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`, added
    `gramHypothesis_of_box_geometry` and `contract_of_box_geometry`, which directly consume
    `gramHypothesis_of_reduction_step2ToTubeForm_box_geometry` (Step-2 + balanced-ξ + reduction +
    geometry assumptions);
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBoxFallback.lean`,
    `gramHypothesis_uniform` and `contract_uniform` now call those core constructors instead of
    duplicating local Step-2/balanced-ξ plumbing;
  - this makes both core and fallback bridge layers share one canonical direct geometry path into
    the SSU heart-facing contract.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX
      SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback`.
- Rewired the flagship fallback Fejér bridge entrypoint to the new direct box-geometry Gram path:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBoxFallback.lean`,
    `gramHypothesis_uniform` now calls
    `gramHypothesis_of_reduction_step2ToTubeForm_box_geometry` directly (via explicit Step-2 +
    balanced-ξ construction), instead of routing through extra wrapper packaging;
  - `contract_uniform` now contracts from that direct Gram result;
  - this completes end-to-end consumption of the new Step-3/4 geometry fallback wiring at the
    fallback instance entrypoint.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback`.
- Big Step-3/4 proof-wiring batch for use-site TT*:
  - in `SSU/Engines/TypeIILargeSieveTeXFor.lean`, added proved fallback constructors
    `Step3LargeSieveOuterUFor.of_box_geometry`,
    `Step4LargeSieveOuterVFor.of_box_geometry`, and
    `Step34LargeSieveTeXFor.of_box_geometry`;
  - these are pure-geometry/progression-cardinality routes (no MV hypothesis objects required at
    call sites) and produce use-site Step-3/4/5 objects directly for fixed extracted arrays `F`;
  - in `SSU/Engines/TypeIITTStarWrappersTeXFor.lean`, added
    `gramHypothesis_of_reduction_step2ToTubeForm_box_geometry`, so the SSU heart-facing Gram
    contract can now be built from reduction + Step-2 + balanced-ξ + geometry assumptions only;
  - Build check passes:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Engines.TypeIITTStarWrappersTeXFor`.
- Substantial BG bridge API expansion in
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - added `BGRankOne.GeometryInput`, a single-record input for the full BG rank-one/modEq route
    (geometry assumptions + tube-form/reduction plumbing + extracted `α/β` + modEq + rank-one
    identification);
  - added bundled endpoint methods:
    - `GeometryInput.toUniformInput`
    - `GeometryInput.toHypothesisStep34ForUniform`
    - `GeometryInput.gramHypothesis`
    - `GeometryInput.contract`;
  - this gives an actual one-object end-to-end path from BG geometry data to the SSU heart-facing
    outputs, reducing high-arity call-site plumbing and making future caller migration practical.
  - Build check passes:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big integration step: exposed direct geometry-to-endpoint constructors for the BG rank-one
  bridge route in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
  - added `hypothesisStep34ForUniform_ofBGGeometry`,
    `gramHypothesis_ofBGGeometry`, and `contract_ofBGGeometry`;
  - these let callers build the full uniform Step-5 bundle / Gram hypothesis / final contract
    directly from geometric assumptions, without manually constructing `UniformInput` first;
  - this operationalizes the new `Regime.ofBGGeometry` path into one-call end-to-end endpoints.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne
      SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Big geometry discharge step for BG rank-one bridge packaging:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, added
    `BGRankOne.Regime.ofBGGeometry`, which proves most `Regime` fields from geometric/natural
    hypotheses (box slope inequalities, positivity/size, `q ≤ D`, and the two `XH` band bounds)
    instead of requiring all fields to be supplied one-by-one;
  - added `BGRankOne.UniformInput.ofBGGeometry` convenience constructor, so callers can build the
    full BG rank-one bridge input from these geometric assumptions directly while reusing the same
    downstream `step34For`/`gramHypothesis`/`contract` pipeline;
  - this is the first concrete “prove geometry, don’t assume every bridge field” step in the
    BG rank-one route, and it reduces manual assumption wiring at call sites.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne
      SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Big bridge API consolidation for the BG rank-one route:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, introduced
    `BGRankOne.Regime`, bundling the repeated BG geometry/numeric assumptions used by the
    one-add-log Step-5 constructors (`ha0/hlower/hupper`, positivity bounds, and both `hXH_*`
    band-compatibility hypotheses);
  - refactored `BGRankOne.UniformInput` to take one field `R : Regime ...` instead of carrying
    these assumptions as many independent fields;
  - rewired all downstream constructor calls (`C34`, `C34_nonneg`, `step34For`, and
    `toHypothesisStep34ForUniform`) to consume `h.R.*`, with no behavioral change to resulting
    `gramHypothesis` / `contract`;
  - this is a plumbing-only refactor, but it materially reduces boilerplate and makes the next
    geometry-discharge step (proving regime facts once, reusing everywhere) cleaner.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne
      SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Big bridge API consolidation: added a shared global-Step34→uniform bridge constructor and
  rewired all major Fejér entrypoints to use it:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`, added
    `HypothesisStep34ForUniform.of_globalStep34`;
  - `Hypothesis.toHypothesisStep34ForUniform`,
    `HypothesisMV.toHypothesisStep34ForUniform`, and
    `HypothesisKhat.toHypothesisStep34ForUniform` now route through that single constructor;
  - this removes duplicated `C34/C34_nonneg/C34_le` assembly code and makes the uniform Step-5
    path consistent across legacy/MV/Khat bridge routes.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX
      SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne
      SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback`.
- Big bridge/engine consolidation: promoted the BG one-add-log Step-5 constant envelope to a
  reusable engine API and rewired the BG rank-one uniform bridge to consume it:
  - in `SSU/Engines/TypeIILargeSieveTeXFor.lean`, added:
    - `Step34LargeSieveTeXFor.bgRankOneModEqOneAddLogC`,
    - `Step34LargeSieveTeXFor.bgRankOneModEqOneAddLogC_nonneg`,
    - `Step34LargeSieveTeXFor.of_bgTubeRankOne_modEq_oneAddLog_C_le_bgRankOneModEqOneAddLogC`;
  - these package the previously local “`C` does not depend on coefficients” fact as an engine
    theorem usable across bridge modules;
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`, `UniformInput.C34`,
    `C34_nonneg`, and `C34_le` now use the canonical engine-level envelope instead of duplicating
    local zero-coefficient instantiations/equality proofs.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne`.
- Big bridge batch: removed the manual uniform-Step-5 envelope hypothesis from the BG rank-one
  bridge package by proving deterministic `C`-invariance of the BG one-add-log Step-5 constructor:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBGRankOne.lean`:
    - removed `C34`, `C34_nonneg`, and `C34_le` as input fields from
      `BGRankOne.UniformInput`;
    - added `step34_bg_C_eq` (the constructor `C` is independent of rank-one coefficient choices
      and modEq witnesses);
    - added derived `UniformInput.C34` (canonical zero-coefficient instantiation),
      `UniformInput.C34_nonneg`, and automatic `C34_le` discharge in
      `toHypothesisStep34ForUniform`;
    - kept `step34For`, `gramHypothesis`, and `contract` APIs unchanged for callers.
  - This turns one previously user-supplied SSU-bridge hypothesis into a proved deterministic
    lemma in the BG route.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne
      SSU.Instances.FejerBankedTypeIIBridgeTeX
      SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback`.
- Mega batch: expanded fallback bridge packaging so all three Step-5 consumption styles are now
  available from one geometry-only constructor path:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeXBoxFallback.lean`, added:
    - `hypothesisKhat` (global-Step-5 Khat package),
    - `hypothesis` (legacy global-Step-5 package),
    - `hypothesisStep34ForUniform` (uniform use-site Step-5 package),
    - `gramHypothesis_uniform`,
    - `contract_uniform`;
  - this makes the box-geometry fallback usable without manual re-wrapping at call sites, and
    supports both legacy and uniform TT* bridge routes from the same input data.
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`, added `contract_uniform` helpers for
    `Hypothesis`, `HypothesisMV`, and `HypothesisMVByResidue` so callers can opt into the uniform
    route directly even where default `contract` remains compatibility-preserving.
  - Build checks pass:
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX
      SSU.Instances.FejerBankedTypeIIBridgeTeXBoxFallback`.
- Big bridge batch on uniform Step-5 wiring in
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`:
  - added global-Step5 → uniform-use-site adapters for `Hypothesis`
    (`toHypothesisStep34ForUniform`, `gramHypothesis_uniform`, `contract_uniform`);
  - added explicit `contract_uniform` helpers for `HypothesisMV` and `HypothesisMVByResidue`;
  - added `HypothesisKhat.toHypothesisStep34ForUniform` and
    `HypothesisKhat.gramHypothesis_uniform`, and switched `HypothesisKhat.contract` to use the
    uniform route by default;
  - retained legacy `gramHypothesis` definitions for compatibility while exposing the uniform route
    everywhere in this bridge module.
  - Build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Switched the `MVKhat` default contract path to the new uniform use-site Step-5 route:
  - `HypothesisMVKhat.contract` now contracts from `gramHypothesis_uniform`
    (instead of routing through the legacy `toHypothesisMV.contract`);
  - `HypothesisMVKhatByResidue.contract` now also contracts from
    `gramHypothesis_uniform`;
  - this makes the new Step34-for-uniform plumbing the default for the `MVKhat` entry points.
  - Build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Completed a larger bridge batch in `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`:
  - fixed the ordering regression around `HypothesisStep34ForUniform` by moving MV/MVByResidue
    conversion defs (`toHypothesisStep34ForUniform`, `gramHypothesis_uniform`) to a post-structure
    section where the type is in scope;
  - added matching uniform-bridge adapters for
    `HypothesisMVKhat` and `HypothesisMVKhatByResidue`, so all MV-family entry points now expose
    the same use-site Step-5 → Gram route;
  - build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Wired the new uniform use-site Step 5 → Gram path into the Fejér bridge layer:
  - added `HypothesisStep34ForUniform` in
    `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`;
  - this variant takes:
    - `step34For : ∀ f i j, Step34LargeSieveTeXFor td (reduction.F f i j)`,
    - a uniform envelope `C34` with `C34_le : (step34For f i j).C ≤ C34`;
  - and produces `gramHypothesis`/`contract` via
    `gramHypothesis_of_reduction_step2ToTubeForm_step34TeXFor_uniform`.
  - Build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Added a new reduction-level Gram builder that consumes **use-site** Step 5 bounds with a
  uniform constant envelope (instead of requiring global Step 3/4 objects):
  - new def in `SSU/Engines/TypeIITTStarWrappersTeXFor.lean`:
    `gramHypothesis_of_reduction_step2ToTubeForm_step34TeXFor_uniform`;
  - inputs are:
    - `h34For : ∀ f i j, Step34LargeSieveTeXFor td (R.F f i j)`,
    - a uniform bound `hC34 : (h34For f i j).C ≤ C34`;
  - output is a full `SSU.Interzone.GramHypothesis` (constant decay profile), with all positivity
    side conditions proved deterministically from `hU`, `hD`, `hH0`, `hX0`, `hbal`, and
    `R.Cenergy_nonneg`.
  - This closes a missing wiring path from “proved Step34 on extracted arrays” to the SSU heart.
  - Build check passes: `lake build SSU.Engines.TypeIITTStarWrappersTeXFor`.
- Added a direct identity-shear Type-II variant of the new rank-one energy-form bound:
  - new theorem in `SSU/Engines/BGTypeIIRankOneToyMV.lean`:
    `Input.norm_typeIISum_sq_le_one_add_log_box_rankOne_geom_tubeEnergy`;
  - this rewrites the product-phase estimate into the canonical Type-II sum form
    (`typeIISum (a:=0) (q:=1)`) using the deterministic identity
    `prodSum_eq_typeIISum_box`, so TeX-facing wrappers can consume it without an extra manual
    conversion step.
  - Build check passes: `lake build SSU.Engines.BGTypeIIRankOneToyMV`.
- Added a TeX-facing energy rewrite for the rank-one toy MV box bound:
  - new theorem in `SSU/Engines/BGTypeIIRankOneToyMV.lean`:
    `Input.norm_prodSum_sq_le_one_add_log_box_rankOne_geom_tubeEnergy`;
  - this upgrades the existing geometry-specialized one-add-log estimate from a product of 1D
    energies to the literal Type-II energy `tubeEnergy P.box (I.F P W)`, which is the form needed
    by downstream Toeplitz/TT* wrappers;
  - implementation is deterministic: rewrite `tubeEnergy` as a swapped shear-box sum, use
    `RankOneShearBox.sum_norm_sq_on_box_eq_boxEnergy` and `RankOneShear.boxEnergy_eq`, then
    substitute into the already-proved bound.
  - Build check passes: `lake build SSU.Engines.BGTypeIIRankOneToyMV`.
- Repaired and stabilized `SSU/Engines/TypeIILargeSieveTeXFor.lean` after the const-on-index
  constructor expansion:
  - fixed wrong namespace references for class→index rewrites
    (`sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet`,
    `sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet`);
  - simplified two nonneg/multiplicative subproofs that were triggering heartbeat blowups in the
    Step 3/4 one-add-log const-on-index constructors;
  - scoped heartbeat budget for the heavy constructor blocks so the file elaborates deterministically;
  - build check passes again:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor`.
- Small cleanup in `SSU/Engines/TypeIILargeSieveTeXFor.lean`:
  - added a private reverse band helper
    `mem_Icc_of_abs_le_one_div : |ξ| ≤ 1/H → ξ ∈ Icc (-(1/H)) (1/H)`,
  - used it in the two BG one-add-log residue constructors
    (`Step3FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog` and
    `Step4FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog`)
    to remove duplicated local `abs_le.mp` conversions.
  - Build check passes: `lake build SSU.Engines.TypeIILargeSieveTeXFor`.
- Extended interval-geometry wrappers to the **global** TeX interfaces and consumed them in the
  global TT* wrapper:
  - `SSU/Engines/TypeIILargeSieveTeX.lean` now provides
    `Step3LargeSieveOuterU.bound_outerGeom`,
    `Step4LargeSieveOuterV.bound_outerGeom`, and
    `Step34LargeSieveTeX.bound_outerGeom` (from `ξ ∈ Icc (-(1/H)) (1/H)`).
  - `SSU/Engines/TypeIITTStarWrappersTeX.lean` now uses
    `Step34LargeSieveTeX.bound_outerGeom` directly inside
    `norm_tubeForm_le_of_step2ToTubeForm_step34TeX`, replacing local manual abs-band conversion.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeX
      SSU.Engines.TypeIITTStarWrappersTeX
      SSU.Engines.TypeIITTStarWrappersTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Threaded interval-geometry use into the TT* use-site proof core:
  - in `SSU/Engines/TypeIITTStarWrappersTeXFor.lean`, the main TT* proof
    `norm_tubeForm_le_of_step2ToTubeForm_step34TeXFor` now uses
    `Step34LargeSieveTeXFor.bound_outerGeom` directly on `ξ ∈ Icc (-(1/H)) (1/H)`
    instead of manually deriving and threading a separate `|ξ| ≤ 1/H` local hypothesis.
  - this confirms the new `outerGeom` plumbing is consumed at the TT* integration layer.
  - Build checks pass:
    `lake build SSU.Engines.TypeIITTStarWrappersTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Wired interval-geometry (`ξ ∈ Icc (-(1/H)) (1/H)`) use-site wrappers through
  `SSU/Engines/TypeIILargeSieveTeXFor.lean`:
  - added `bound_outerGeom` wrappers for:
    - `Step34LargeSieveTeXFor`
    - `Step3LargeSieveOuterUFor`
    - `Step3FiberLargeSieveByResidueFor`
    - `Step3FiberLargeSieveFor`
    - `Step4LargeSieveOuterVFor`
    - `Step4FiberLargeSieveByResidueFor`
    - `Step4FiberLargeSieveFor`
  - these remove manual `|ξ| ≤ 1/H` plumbing at TeX use-sites by deriving the band bound
    deterministically from interval membership.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Engines.TypeIITTStarWrappersTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Added interval-geometry wrappers for the **non-one-add-log** BG residue-class witness/class
  rank-one modEq bounds:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean` now includes
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass_outerGeom`,
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass_outerGeom`,
    `step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass_outerGeom`,
    and
    `step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass_outerGeom`.
  - These remove explicit `|ξ| ≤ 1/H` threading in the base modEq witness/class APIs by accepting
    `ξ ∈ Icc (-(1/H)) (1/H)` and deriving the band bound deterministically.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve
      SSU.Engines.TypeIILargeSieveTeXFor`.
- Added interval-geometry wrappers for BG residue-class witness one-add-log interfaces:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean` now has:
    - `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass_outerGeom`
    - `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass_outerGeom`
    - `step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass_outerGeom`
    - `step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass_outerGeom`
  - These eliminate explicit `|ξ| ≤ 1/H` hypotheses in the “of_mem_*” APIs by accepting
    `ξ ∈ Icc (-(1/H)) (1/H)` and deriving ξ-band bounds deterministically.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve
      SSU.Engines.TypeIILargeSieveTeXFor`.
- Added BG one-add-log interval-geometry wrappers for rank-one/modEq residue-index bounds:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean` now has
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_outerGeom`
    and
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_outerGeom`.
  - These wrappers remove explicit `|ξ| ≤ 1/H` inputs at this BG rank-one layer by accepting
    `ξ ∈ Icc (-(1/H)) (1/H)` and deriving the ξ-band bound deterministically.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve
      SSU.Engines.TypeIILargeSieveTeXFor`.
- Propagated interval-geometry one-add-log wrappers into residue-class fiber bounds:
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean` now has
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_constCoeff_uIndexSet_one_add_log_outerGeom`
    and
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_constCoeff_vIndexSet_one_add_log_outerGeom`.
  - These remove explicit `|ξ| ≤ 1/H` hypotheses at the residue-class one-add-log layer by taking
    `ξ ∈ Icc (-(1/H)) (1/H)` and deriving the band bound deterministically.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.TypeIIFiberLargeSieveFromFiniteLargeSieve
      SSU.Engines.LargeSieve.BGTubeFiberLargeSieve`.
- Added interval-geometry wrappers for residue-index one-add-log MV constants:
  - `SSU/Engines/LargeSieve/TypeIIResidueIndexLargeSieve.lean` now has
    `uIndexSet_finiteLargeSieve_C_le_one_add_log_outerGeom` and
    `vIndexSet_finiteLargeSieve_C_le_one_add_log_outerGeom`.
  - Both wrappers derive `|ξ| ≤ 1/H` from `ξ ∈ Icc (-(1/H)) (1/H)`, so callers no longer need to
    thread the band bound separately in residue-index one-add-log pathways.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.TypeIIResidueIndexLargeSieve
      SSU.Engines.BGTypeIIRankOneToyMV`.
- Consumed the new interval-geometry rank-one wrapper in the BG toy bridge:
  - `SSU/Engines/BGTypeIIRankOneToyMV.lean` now proves
    `norm_prodSum_sq_le_one_add_log_box_rankOne_geom` by routing through
    `RankOneProductToy.norm_typeIISum_sq_le_one_add_log_Icc_outerGeom`
    (instead of re-proving a local `hDist` bound).
  - This keeps the “derive diameter from interval geometry” pattern consistent across the toy
    and generic rank-one paths.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.TypeIIRankOneProductToyTeX
      SSU.Engines.BGTypeIIRankOneToyMV`.
- Added a geometry-specialized outer-interval MV wrapper for the rank-one toy Type-II bridge:
  - `SSU/Engines/LargeSieve/TypeIIRankOneProductToyTeX.lean` now has
    `norm_typeIISum_sq_le_one_add_log_Icc_outerGeom`, which removes explicit `R`/`hDist` for
    outer index sets of the form `U = Icc A B` by proving
    `distZ ≤ Int.toNat (B - A)` deterministically.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.TypeIIRankOneProductToyTeX
      SSU.Engines.BGTypeIIRankOneToyMV`.
- Added an interval-geometry specialization of the generic rank-one decomposition bridge:
  - `SSU/Engines/LargeSieve/TypeIIRankOneLargeSieveBridgeTeX.lean` now has
    `typeIISum_norm_sq_le_of_rankOneDecomp_one_add_log_Icc`, which removes explicit
    `R`/`hDist` inputs for `J = Icc A B` by deriving `distZ ≤ Int.toNat (B - A)` deterministically.
  - Build check passes:
    `lake build SSU.Engines.LargeSieve.TypeIIRankOneLargeSieveBridgeTeX`.
- Removed explicit `hDist` assumptions from the rank-one Step 3/4 MV application interfaces by
  proving deterministic `distZ` diameter bounds from geometry:
  - added `..._geom` variants in
    `SSU/Engines/LargeSieve/TypeIIStep3RankOneApplyMVTeX.lean` and
    `SSU/Engines/LargeSieve/TypeIIStep4RankOneApplyMVTeX.lean` that derive `R` from
    `uSet`/`vSet` via `TypeIIIndexBounds`;
  - added matching fiber-bridge wrappers
    `norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBox_geom` and
    `norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBoxV_geom` in
    `SSU/Engines/LargeSieve/TypeIIRankOneFiberBridgeTeX.lean`.
  - Build checks pass:
    `lake build SSU.Engines.LargeSieve.TypeIIStep3RankOneApplyMVTeX
      SSU.Engines.LargeSieve.TypeIIStep4RankOneApplyMVTeX
      SSU.Engines.LargeSieve.TypeIIRankOneFiberBridgeTeX`,
    and downstream:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor
      SSU.Engines.TypeIITTStarWrappersTeXFor
      SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Removed one remaining toy large-sieve distance hypothesis by proving it from interval geometry:
  - added `Input.norm_prodSum_sq_le_one_add_log_box_rankOne_geom` in
    `SSU/Engines/BGTypeIIRankOneToyMV.lean` (same bound as the prior toy theorem, but with
    deterministic `nRange = Icc (N+1) (2N)` diameter in place of an external `hDist` assumption).
  - Build check passes: `lake build SSU.Engines.BGTypeIIRankOneToyMV`.
- Extended the residue-class Fejér TeX bridge with use-site Step 3/4/5 packaging:
  - in `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`, `HypothesisMVByResidue` now has
    `step3For`, `step4For`, and `step34For` (all specialized to extracted arrays
    `reduction.F f i j`);
  - added `HypothesisMVByResidue.norm_inner_le_step34For`, parallel to the MV-path packaged bound.
  - Build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Added BG rank-one one-add-log constructors to the fixed-`F` TeX large-sieve interfaces in
  `SSU/Engines/TypeIILargeSieveTeXFor.lean`:
  - `Step4FiberLargeSieveByResidueFor.of_bgTubeRankOne_modEq_oneAddLog` (new Step 4 side,
    matching the existing Step 3 constructor);
  - `Step34LargeSieveTeXFor.of_bgTubeRankOne_modEq_oneAddLog` (new combined constructor wiring
    BG one-add-log Step 3/4 residue bounds directly to a Step 5-style fixed-`F` object).
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor` and
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Removed explicit class-witness plumbing from the new one-add-log class-energy wrappers in
  `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean`:
  - added
    `step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy`
    and
    `step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_energy`
    (no `u0 ∈ uClass` / `v0 ∈ vClass` input needed).
  - these split on class nonemptiness: if nonempty, reuse the `_of_mem_*` theorem; if empty,
    both sides simplify to `0`.
  - Build check passes: `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve`.
- Closed the class-energy wrapper build blocker in
  `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean` by replacing two fragile
  `Int.toNat_of_nonneg` rewrites with `Int.le_toNat`-based proofs for the
  `1 ≤ Int.toNat (...)` side conditions in one-add-log Step 3/4 constants.
  This completes the new witness→class-energy wrappers end-to-end.
  - Build check passes: `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve`.
- Repaired and completed the new fixed-`F` residue/fiber Step 3/4 interfaces in
  `SSU/Engines/TypeIILargeSieveTeXFor.lean`:
  - fixed namespace scoping in the new blocks (`uSet`/`vSet`, `uResidue`/`vResidue`);
  - completed `Step3FiberLargeSieveFor.of_byResidue` and
    `Step4FiberLargeSieveFor.of_byResidue` by routing fiber-energy closure through the proved
    geometric identities
    `sum_u_z_norm_fiberUZ_sum_sq_eq_tubeEnergy` and
    `sum_v_z_norm_fiberVZ_sum_sq_eq_tubeEnergy`;
  - deterministic Cauchy reductions now compile end-to-end for the fixed-`F` Step 3/4 path.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor` and
    `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Kept the Khat-by-residue path residue-native through the bridge conversion layer:
  - `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean` now adds
    `HypothesisMVKhatByResidue.hH`,
    `HypothesisMVKhatByResidue.balancedXi`, and
    `HypothesisMVKhatByResidue.toHypothesisMVByResidue`.
  - `HypothesisMVKhatByResidue.gramHypothesis` now routes via
    `toHypothesisMVByResidue.gramHypothesis` (residue-native path), with
    `contract` still built directly from that Gram hypothesis.
  - Build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Extended the Khat + residue-class bridge namespace with a direct Gram/contract path:
  - `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean` now defines
    `HypothesisMVKhatByResidue.gramHypothesis`.
  - `HypothesisMVKhatByResidue.contract` now routes through
    `FB.contract_of_gramHypothesis` (parallel to the MV-by-residue path), instead of only via the
    intermediate conversion object.
  - Build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Added a residue-class-native Fejér bridge hypothesis layer:
  - `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean` now defines
    `HypothesisMVByResidue` with Step 3/4 inputs as
    `Step3MontgomeryVaughanByResidue` / `Step4MontgomeryVaughanByResidue`.
  - Added `HypothesisMVByResidue.toHypothesisMV`, which deterministically collapses residue-class
    hypotheses to global MV via `Step3MontgomeryVaughan.of_byResidue` /
    `Step4MontgomeryVaughan.of_byResidue`, then reuses existing end-to-end TT*/contract wiring.
  - Added `HypothesisMVByResidue.contract`.
  - Added the analogous Khat-only entrypoint:
    `HypothesisMVKhatByResidue` in
    `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean`,
    plus
    `HypothesisMVKhatByResidue.toHypothesisMVKhat` and
    `HypothesisMVKhatByResidue.contract`.
  - Build check passes: `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Wired residue-class-native MV interfaces through the TeX use-site and TT* layers:
  - `SSU/Engines/TypeIILargeSieveTeXFor.lean` now has
    `Step3LargeSieveOuterUFor.of_montgomeryVaughan_byResidue`,
    `Step4LargeSieveOuterVFor.of_montgomeryVaughan_byResidue`,
    and `Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue`.
  - `SSU/Engines/TypeIITTStarWrappersTeXFor.lean` now has residue-class-native TT* wrappers:
    `norm_tubeForm_le_of_step2ToTubeForm_step3MVByResidue_step4MVByResidue`,
    `norm_inner_le_of_reduction_step2ToTubeForm_step3MVByResidue_step4MVByResidue`,
    and
    `gramHypothesis_of_reduction_step2ToTubeForm_step3MVByResidue_step4MVByResidue`.
  - This lets downstream callers stay in `Step3/4MontgomeryVaughanByResidue` form end-to-end,
    only collapsing to global MV internally via deterministic `of_byResidue` adapters.
  - Build checks pass:
    `lake build SSU.Engines.TypeIILargeSieveTeXFor SSU.Engines.TypeIITTStarWrappersTeXFor SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Added one-add-log residue-class (`uClass`/`vClass`) wrappers for BG rank-one/modEq Step 3/4:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean` now includes
    `step3_sum_uClass_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass`
    and
    `step4_sum_vClass_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass`.
  - These are the class-sum counterparts of the existing one-add-log `_of_mem_uClass/_of_mem_vClass`
    index-sum wrappers; they reindex with
    `sum_uClass_norm_innerSumUZ_sq_eq_sum_uIndexSet` /
    `sum_vClass_norm_innerSumVZ_sq_eq_sum_vIndexSet`, then apply the existing from-index bounds.
  - Build check passes: `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve`.
- Added residue-witness wrappers for the **non-one-add-log** BG rank-one/modEq Step 3/4 bounds:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean` now includes
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_uClass`
    and
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_of_mem_vClass`.
  - These expose the same inequalities as the `m0`-based lemmas but take `u0 ∈ uClass r` /
    `v0 ∈ vClass r` directly, matching the residue-class-first TeX presentation and reducing
    caller-side index bookkeeping.
  - Build check passes: `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve`.
- Added residue-witness convenience wrappers for BG rank-one one-add-log Step 3/4 bounds:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean` now includes
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_uClass`
    and
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log_of_mem_vClass`.
  - These wrappers let callers provide `u0 ∈ uClass r` / `v0 ∈ vClass r` directly (no explicit
    index witness `m0`), then internally construct `m0 := uIndex r u0` / `vIndex r v0` and rewrite
    back via `uFromIndex_uIndex_of_mem_uClass` / `vFromIndex_vIndex_of_mem_vClass`.
  - Build check passes: `lake build SSU.Engines.LargeSieve.BGTubeFiberLargeSieve`.
- Refactored the new MV→Gram constructor to avoid heartbeat-heavy constant synthesis:
  - `SSU/Engines/TypeIITTStarWrappersTeXFor.lean` now builds
    `gramHypothesis_of_reduction_step2ToTubeForm_step3MV_step4MV` by routing
    `Step3/4MontgomeryVaughan → fiber → outer → gramHypothesis_of_step2ToTubeForm_step3_step4_teX`
    (global TeX path), instead of constructing a per-signal constant envelope.
  - Added the required import of `SSU/Engines/TypeIITTStarWrappersTeX.lean` and updated the
    MV bridge callsite to pass `hX : 0 < X`.
  - Result: both targets build cleanly:
    `lake build SSU.Engines.TypeIITTStarWrappersTeXFor SSU.Instances.FejerBankedTypeIIBridgeTeX`.
- Added extracted-array Step 5 packaging in the Fejér MV bridge:
  - `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean` now defines
    `HypothesisMV.step34For (f i j) : Step34LargeSieveTeXFor td (reduction.F f i j)`.
  - Added theorem `HypothesisMV.norm_inner_le_step34For`, so downstream code can consume the TT*
    bound via a named `Step34LargeSieveTeXFor` object for the actual extracted signal.
- Wired the new one-shot reduction-level MV wrapper into the Fejér TeX bridge layer:
  - `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean` now imports
    `SSU/Engines/TypeIITTStarWrappersTeXFor`.
  - Added `HypothesisMV.step2` and
    `HypothesisMV.norm_inner_le_step3MV_step4MV` (single-entrypoint use-site Gram bound for
    fixed `(f,i,j)`).
- Added one-shot **reduction-level** TeX TT* wrappers that consume Step 3/4 use-site hypotheses
  directly for the extracted array `R.F f i j` (so callers no longer need to build an explicit
  intermediate `Step34LargeSieveTeXFor` object by hand):
  - `SSU/Engines/TypeIITTStarWrappersTeXFor.lean`:
    `norm_inner_le_of_reduction_step2ToTubeForm_step3_step4TeXFor`
    and
    `norm_inner_le_of_reduction_step2ToTubeForm_step3MV_step4MV`.
  This completes the TT* wiring path
  `reduction + Step3/4(use-site or MV) + balanced-ξ → Gram bound`.
- Added BG rank-one/modEq **one-add-log** wrappers (residue-index Step 3/4 form), so the
  geometric/modulo plumbing now yields explicit polylog constants directly:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean`:
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log`,
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq_one_add_log`.
- Added TeX use-site constructors that route Montgomery–Vaughan hypotheses directly into the
  per-signal Step 3/4/5 interfaces (so downstream wrappers no longer need const-coeff-only entry points):
  - `SSU/Engines/TypeIILargeSieveTeXFor.lean`:
    `Step3LargeSieveOuterUFor.of_montgomeryVaughan`,
    `Step4LargeSieveOuterVFor.of_montgomeryVaughan`,
    `Step34LargeSieveTeXFor.of_step3MV_step4MV`.
- Added the matching TT* convenience wrapper:
  - `SSU/Engines/TypeIITTStarWrappersTeXFor.lean`:
    `norm_tubeForm_le_of_step2ToTubeForm_step3MV_step4MV`.
- Added modulo-invariance wrappers that remove the explicit progression-constancy assumptions in
  the BG residue-index rank-one wrappers:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean`:
    `beta_const_on_uFromIndex_of_modEq`,
    `alpha_const_on_vFromIndex_of_modEq`,
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime_of_modEq`,
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime_of_modEq`.
  These now consume a single modulo-invariance hypothesis (`[ZMOD q]`) on `β`/`α`, with the
  progression constancy proved deterministically from residue geometry.
- Added BG-regime **rank-one MV specializations** that consume the new extraction helpers and
  remove explicit `hEqOn` obligations in the residue-index finite-large-sieve wrappers:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean`:
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_rankOneShear_of_regime`
    (Step 3, assuming class-constancy of `β` on `uIndexSet`),
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_rankOneShear_of_regime`
    (Step 4, assuming class-constancy of `α` on `vIndexSet`).
  This turns the prior “domain equality + `hEqOn`” interface into ready-to-use rank-one lemmas.
- Added BG-regime **rank-one extraction helpers** that turn the remaining `hEqOn` assumptions into
  proved geometric/algebraic statements under explicit progression-constancy hypotheses:
  - `SSU/Engines/LargeSieve/BGTubeFiberLargeSieve.lean`:
    `sum_fiberUZ_uFromIndex_eq_ref_on_zSet_of_rankOneShear_of_regime`
    (Step 3, assuming `β` is constant along the fixed `uIndexSet` residue progression),
    `sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_of_rankOneShear_of_regime`
    (Step 4, assuming `α` is constant along the fixed `vIndexSet` residue progression).
  These are the first concrete “assumption → proof” extractions for the new
  `..._on_zSet...`/`..._on_zSetV...` interfaces.
- Added residue-index bridge lemmas so progression representatives can be used directly without
  repeating filter/membership boilerplate:
  - `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean`:
    `uFromIndex_mem_uSet_of_mem_uIndexSet`,
    `vResidue_uFromIndex_eq_of_mem_uIndexSet`,
    `vFromIndex_mem_vSet_of_mem_vIndexSet`,
    `uResidue_vFromIndex_eq_of_mem_vIndexSet`.
- Added BG-geometry corollaries specialized to progression representatives:
  - `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean`:
    `zSet_eq_uFromIndex_of_mem_uIndexSet_of_regime`,
    `zSetV_eq_vFromIndex_of_mem_vIndexSet_of_regime`.
  These are the direct forms needed when applying MV on `uIndexSet` / `vIndexSet`.
- Wired the new “equal-on-common-domain” const-coefficient interfaces into the residue-index MV
  wrappers:
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean` now includes
    `step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_on_zSet_finiteLargeSieve`
    and
    `step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_sum_fiberVZ_vFromIndex_eq_ref_on_zSetV_finiteLargeSieve`.
  These remove the stronger “equality on every translated `zBox` index” requirement in favor of:
  (i) domain equality along a residue progression, and
  (ii) fiber-sum equality only on the common domain.
- Promoted the “extra fibers are empty” support facts to **public** deterministic lemmas, and
  removed duplicate private copies:
  - Step 3: `SSU/Engines/LargeSieve/TypeIISumDecompose.lean` (`sum_fiberUZ_eq_zero_of_not_mem_zSet`)
  - Step 4: `SSU/Engines/LargeSieve/TypeIISumDecomposeV.lean` (`sum_fiberVZ_eq_zero_of_not_mem_zSetV`)
  This unblocks cleaner rewrites where we enlarge `zSet`/`zSetV` to uniform supersets (`zBox`/`zBoxV`)
  without re-proving the same emptiness argument in each file.
- Refactored the uniform-box rewrite and TT*/energy plumbing to reuse the new public lemmas:
  `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean`, `SSU/Engines/LargeSieve/TypeIIConstCoeffMV.lean`.
- Proved a fully *geometric* membership characterization of the centered BG tube shear image
  (no assumptions like “shear image = box”): `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:170`
  (`mem_image_shearMap_iff_exists_dn_ofBG`). This is the clean starting point for later
  surjectivity/fullness lemmas once we add parameter-regime inequalities.
- Proved fully *geometric* membership characterizations of the Step 3/4 progression-index sets
  `zSet` / `zSetV` for the centered BG tube, expanded to explicit dyadic-box witnesses `(d,n)`:
  `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:46` (`mem_zSet_iff_exists_dn`),
  `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:202` (`mem_zSetV_iff_exists_dn`).
  These are the exact starting point for the next “prove as geometry” step: show the `n`-range
  constraints are automatically satisfied in the intended parameter regime, so the `z`-ranges
  become uniform/constant across residue classes (the TeX Step 3/4 bottleneck).
- Proved **uniqueness** of the Step 3/4 `n`-witness once `(u,z)` (resp. `(v,z)`) is fixed, purely by
  cancellation using `q ≠ 0`:
  `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:149` (`existsUnique_n_of_mem_zSet`),
  `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:281` (`existsUnique_n_of_mem_zSetV`).
  This is a prerequisite for turning the “there exists some `(d,n)`” geometry into **counting**
  statements about `card(zSet)` / `card(zSetV)` without assuming fullness.
- Forced-witness + counting layer:
  - Repackaged Step 3 membership so the `d`-witness is *forced* to be `vResidue(u)+z*q`:
    `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:216` (`mem_zSet_iff_exists_n_forcedD`).
  - Made the **forced `n`** explicit (pure congruence/Bezout geometry):
    - Step 3: `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:272`
      (`mem_zSet_iff_forcedDn`) where `n = (u + a*d)/q` with `d = vResidue(u)+z*q`.
    - Step 4: `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:481`
      (`mem_zSetV_iff_forcedUn`) where `u = uResidue(v)+z*q` and `n = (u + a*v)/q`.
    These isolate the **only** remaining obstruction to TeX-strength “fullness”: proving that the
    forced `n` automatically lies in `nRange` in the intended parameter regime (so the `z`-ranges
    become uniform across fibers).
  - Added explicit **regime** lemmas (TeX margin inequalities) that *prove* `n ∈ nRange` is
    automatic for the centered BG tube’s forced witnesses:
    - Step 3 (outer `u`): `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:441`
      (`mem_zSet_iff_forcedD_of_regime`)
    - Step 4 (outer `v`): `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:664`
      (`mem_zSetV_iff_forcedU_of_regime`)
    This is the “geometry → regime” milestone needed before we can turn the Step 3/4 MV hypotheses
    into *proved* large-sieve bounds for the actual BG tube decomposition.
  - Added *use-site* corollaries that eliminate the redundant bounds on `uSet` / `vSet` (so later
    proofs can treat the `z`-domains as purely box-controlled):
    - Step 3 on `uSet`: `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:763`
      (`mem_zSet_iff_forcedD_of_regime_of_mem_uSet`)
    - Step 4 on `vSet`: `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:789`
      (`mem_zSetV_iff_forcedU_of_regime_of_mem_vSet`)
  - Proved the TeX Step 3/4 “constant domain on a residue class” lemmas (under the same regime):
    `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:822` (`mem_zSet_iff_dRange_of_eq_vResidue_of_regime`),
    `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:842` (`zSet_eq_of_eq_vResidue_of_regime`),
    `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:866` (`mem_zSetV_iff_uBound_of_eq_uResidue_of_regime`),
    `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:885` (`zSetV_eq_of_eq_uResidue_of_regime`).
  - Derived geometry-only cardinality bounds (no regime assumptions):
    `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:251` (`card_zSet_le_card_dRange`),
    `SSU/Engines/LargeSieve/BGTubeZSetGeometry.lean:373` (`card_zSetV_le_card_nRange`).
- Generalized the weighted Toeplitzization lemma to accept the **torus-side** product sum
  `prodSumTorusByProd` directly (so applications don’t need to re-prove the `e(ξk/X) = fourier k (ξ/X)`
  bridge each time): `SSU/Engines/BGTypeIIArrayWeightedToeplitz.lean:64`.
- Refactored the Fejér-banked extraction lemma to use the new domain-general engine lemma:
  `SSU/Instances/FejerBankedTypeIIToeplitzExtraction.lean:1`.
- Added a TeX-friendly “prove Step34 only for `ξ ≠ 0`” interface `Step34ProdSumNe0` and an adapter
  `Step34ProdSum.of_ne0` that patches `ξ = 0` by deterministic Cauchy–Schwarz, so future proofs can
  follow the TeX (which always states large-sieve bounds for `ξ ≠ 0`) without rewriting the whole
  TT* layer (`SSU/Engines/TypeIIToeplitz.lean:70`).

## Status rubric (what moves the bar)

This project has lots of “micro-steps”, but the *status bar* is meant to track only the major
TeX-facing deliverables that convert hypothesis-plumbing into proved analytic machinery.

Practical rule of thumb:
- The bar moves **materially** when we replace a hypothesis/interface used by the TeX wrappers
  (Step 3/4/5, heart instantiation, etc.) by a proved theorem for the *actual extracted signal*.
- Geometry-only lemmas (membership rewrites, uniqueness, finiteness) are necessary prerequisites,
  but they typically move the bar only **slightly** until they combine into a proved Step 3/4 bound.

Legend:
- ✅ proved (Lean theorem, TeX-strength)
- ✅* proved (Lean theorem, **weak fallback** / CS+geometry; useful for plumbing but not the final TeX bound)
- 🧩 wired (interfaces + deterministic reductions exist; still hypotheses)
- ⏳ not started

| Milestone (TeX-facing) | Weight | Current | What “done” means |
|---|---:|:---:|---|
| Plumbing: packets/TT*/Toeplitz/bridges compile end-to-end | 40% | ✅ | Deterministic reductions exist; bridges produce SSU contracts assuming analytic hypotheses |
| Additive Dirichlet-kernel bound (1D exponential sums) | 0% | ✅ | Foundational lemmas for the MV large sieve are proved (`‖∑ e(n t)‖ ≤ min N (1/(2|t|))` under `|t|≤1/2`) |
| MV large sieve proved (rank-one shear “box model”) | 10% | ✅ | `RankOneShearBoxLargeSieveTeX` gives TeX-style polylog MV bounds for `shearSum` on `J × Icc(a,a+N-1)` and the Step 5 geometric mean |
| Step 3 MV (outer-`u`) proved (usable for SSU heart) | 10% | ⏳ | A theorem produces `Step3LargeSieveOuterU td` (or a provably-equivalent replacement) for the **actual** extracted Type–II signal used in SSU, not just the “box model” |
| Step 3 MV (outer-`u`) weak fallback (geometry-only) | 0% | ✅* | Cauchy–Schwarz + `card(zSet)` bounds produce a usable `Step3MontgomeryVaughan` instance |
| Step 4 MV (outer-`v`) proved (usable for SSU heart) | 10% | ⏳ | A theorem produces `Step4LargeSieveOuterV td` (or a provably-equivalent replacement) for the **actual** extracted Type–II signal used in SSU |
| Step 4 MV (outer-`v`) weak fallback (geometry-only) | 0% | ✅* | Cauchy–Schwarz + `card(zSetV)` bounds produce a usable `Step4MontgomeryVaughan` instance (prefactor inserted by monotonicity on the ξ-band) |
| Step 3–5 large sieve fully proved (TeX Step 5 derived from proved Step 3/4) | 5% | 🧩 (box model ✅; weak Type–II ✅*) | Box-model Step 5 is proved; Type–II packaging exists as weak `Step34LargeSieveTeX` instances; the remaining work is to replace the weak Step 3/4 inputs by proved ones for the extracted signal |
| `balanced-xi` for the chosen admissible kernel discharged | 5% | ✅ | `BalancedXiClaimInv X H (Khat H)` proved for the concrete `K̂_H` (possibly crude constants) |
| SSU Type–II “heart” instantiated for Fejér-banked packets | 20% | 🧩 | For the *actual* Fejér-banked packet family, the proved Step 3–5 input feeds the SSU ledger machinery and yields the advertised Gram/ledger bounds |
| Remaining instance hypotheses discharged (TT*/reindexing identities, etc.) | 10% | ⏳ | No application-facing fields like `tubeForm_eq` / `ReductionToTubeForm` remain assumptions for the flagship instance |

Interpretation of the current ~60%:
- We are “done with plumbing” (and even discharged `balanced-xi` for the admissible kernel), but
  we have not yet proved the large-sieve/MV steps in the **full tube** form (the first truly
  analytic bottleneck).
- However, we now have the core 1D exponential-sum estimates in place; the next work is the
  *actual* Montgomery–Vaughan inequality (spacing + row-sums + polylog), and then specializing it
  to the `05b_SSU.tex` Step 3/4 interfaces.

What would move the **TeX-strength** bar materially (the next big “ticks”):
- Tick 1 (≈ +10%): prove Step 3 MV (LS-outer-u) at TeX strength (not just CS+cardinality).
- Tick 2 (≈ +10%): prove Step 4 MV (LS-outer-v) at TeX strength (same).
- Tick 3 (≈ +5%): package Step 3+4 into the exact TeX Step 5 interface and feed it into the
  Fejér-banked SSU heart wiring (this is mostly “apply existing wrappers” once Tick 1+2 exist).

So: the next time the status bar should “move” in a noticeable way is when we land either the
TeX-strength Step 3 proof or the TeX-strength Step 4 proof.

Where the bar is “sticky” right now:
- We already have MV-on-`ℤ` machinery and several TeX-shaped specializations proved for rank-one “models”.
- The remaining work is the *application-facing specialization*: show that the **actual** extracted
  Type–II signal in the SSU pipeline satisfies the hypotheses of those MV bounds (or prove new bounds
  that match the `Step3LargeSieveOuterU` / `Step4LargeSieveOuterV` interfaces directly).
- Concretely, this is the “extracted coefficients → progression/fiber hypotheses → Step 3/4 bounds”
  bridge; once that exists, Step 5 and the TT* integration wrappers become straightforward applications.

## What’s done (Lean proved, builds)

- Multiplier Gram expansion (inner product → integral) is proved and reusable:
  - Canonical (arbitrary measured space): `SSU/Analysis/Multipliers.lean:120`
    (`SSU.Analysis.inner_mulL2Op_eq_integral`)
  - Torus specialization is a thin re-export: `SSU/Torus/Multipliers.lean:92`
  - Fejér-banked specialization: `SSU/Instances/FejerBankedPartition.lean:118`
  - “Packet family as multipliers” wrapper (torus instance of the domain-general API):
    `SSU/Torus/Multipliers.lean:137` (`Packets.MultiplierPacketFamily.inner_packetOp_eq_integral`)
- TeX normalization “band ↔ small arc” bridge is now project-neutral (usable outside Fejér-banked):
  - No-wrap band map + arc set: `SSU/Torus/BandMap.lean:1`
  - Arc-indicator Haar integral ↔ real `Icc` integral: `SSU/Torus/ArcBridge.lean:1`
  - `x = ξ/X` substitution with `1/X` Jacobian: `SSU/Torus/BandToArc.lean:1`
- Fejér-banked Gram expansion is now expanded down to internal tube sums (still on the torus side):
  - `(ψ_i)^* ψ_j = (shellSum i)*(shellSum j)*|Φ|^2`: `SSU/Instances/FejerBankedPartition.lean:136`
  - `shellSum` expanded as a double tube-index sum inside the integral:
    `SSU/Instances/FejerBankedPartition.lean:161`
  - Full “swap sum with integral” (tube-pair double sum of integrals):
    `SSU/Instances/FejerBankedPartition.lean:175`
  - Same statement for the canonical unnormalized packet operators
    `(D.toMultiplierModel).packetOpUnnormalized`:
    `SSU/Instances/FejerBankedPartition.lean:524`
- TeX-faithful Toeplitz “group by product” regrouping (05_BG.tex, Eq. (5.2)/(5.3) → line-37 form):
  - Core deterministic lemma grouping `tubeFormProd` by product: `SSU/Engines/TypeII.lean:951`
  - BG-facing wrappers (including TeX ordering under even kernel): `SSU/Engines/BGToeplitz.lean:80`,
    `SSU/Engines/BGToeplitz.lean:87`
  - TeX-facing reduction interface exposes the TeX `k,k'` form and proves equivalence to
    `tubeFormProd` under kernel evenness: `SSU/Engines/BGToeplitzReduction.lean:76`,
    `SSU/Engines/BGToeplitzReduction.lean:89`
- Admissible Toeplitz kernel evenness (needed for TeX ordering): `SSU/Engines/TypeII.lean:1685`
- TeX-facing reduction works end-to-end in the singleton-tube toy (regression target):
  `SSU/Instances/FejerBankedPlatinumTypeIIToeplitzToyTeX.lean:1`
- Legacy non-TeX toy name is now a thin wrapper around the TeX toy + the generic bridge:
  `SSU/Instances/FejerBankedPlatinumTypeIIToeplitzToy.lean:1`
- `lake build SSU` succeeds (warnings only).
- Deterministic large-sieve plumbing for TeX Step 3/4 is formalized:
  - Outer `u`-fiber decomposition and `v = v₀(u) + z*q` progression split:
    `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:1`
  - Finite Cauchy–Schwarz helper for outer sums:
    `SSU/Engines/LargeSieve/FinsetCS.lean:1`
  - Outer-`u` Cauchy–Schwarz reduction (TeX Step 3) from a “fiber large sieve” hypothesis:
    `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:1`
  - Symmetric `v`-fiber decomposition (`u = u₀(v) + z*q`) and the corresponding outer-`v` reduction
    (TeX Step 4):
    `SSU/Engines/LargeSieve/TypeIISumDecomposeV.lean:1`,
    `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:1`
  - Auxiliary deterministic inequality used in the TeX “geometric mean” bookkeeping:
    `U/q + x ≤ max(U/(qD),1) * (D + x)` and its square-root form:
    `SSU/Engines/LargeSieve/Step34Aux.lean:1`
  - Added an abstract Montgomery–Vaughan-style “finite large sieve” hypothesis interface to plug in
    later analytic proofs cleanly:
    `SSU/Engines/LargeSieve/MontgomeryVaughanHypothesis.lean:1`
  - Rank-one shear MV wrapper with TeX-style explicit constant
    `N + (1/|t|)*(1+log R)` (replaces the opaque `LS.C`):
    `SSU/Engines/LargeSieve/RankOneShearLargeSieveTeX.lean:28`
  - Type–II rank-one large sieve bridge: any proved rank-one decomposition of `typeIISum`
    immediately yields the TeX-style polylog bound (no CS/card inflation):
    `SSU/Engines/LargeSieve/TypeIIRankOneLargeSieveBridgeTeX.lean:39`
  - Toy “identity shear” (a=0,q=1) rank-one extraction for `typeIISum` on a product set, plus the
    resulting explicit MV/one-add-log bound (interval-indexed version):
    `SSU/Engines/LargeSieve/TypeIIRankOneProductToyTeX.lean:39`
  - Box-first rank-one Type–II coefficient model on the dyadic box now has a directly-usable
    MV/one-add-log bound stated on the **product-phase sum** (`prodSum`) itself (via the identity
    `prodSum = typeIISum` when `(a,q)=(0,1)`), so downstream Toeplitz code can consume it without
    rerunning the toy algebra:
    `SSU/Engines/BGTypeIIRankOneToyMV.lean:1` (`Input.norm_prodSum_sq_le_one_add_log_box_rankOne`)
  - Step 3 MV application lemma: applies the TeX-style MV bound to the *actual* Step 3 decomposition
    `typeIISum_eq_outer_u_innerUZ`, assuming only a rank-one hypothesis for `innerSumUZ` (this is
    the exact interface the residue-class extraction step must discharge next):
    `SSU/Engines/LargeSieve/TypeIIStep3RankOneApplyMVTeX.lean:38`
  - Step 4 MV application lemma: same as Step 3 but for the TeX Step 4 decomposition
    `typeIISum_eq_outer_v_innerVZ`, assuming a rank-one hypothesis for `innerSumVZ`:
    `SSU/Engines/LargeSieve/TypeIIStep4RankOneApplyMVTeX.lean:33`
  - Deterministic algebra for rank-one (separated) Type–II coefficients in shear coordinates
    `F(d,n) = α(d) * β(qn - ad)`: rewrites the Step 3/4 inner sums as sampled progressions:
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:53` (`innerSumUZ_eq_rankOne`),
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:120` (`innerSumVZ_eq_rankOne`).
    Fiber-sum collapse lemmas extracted for reuse:
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:61` (`sum_fiberUZ_coeff_eq`),
    `SSU/Engines/LargeSieve/TypeIIRankOneShearCoeffs.lean:89` (`sum_fiberVZ_coeff_eq`).
  - Added “fixed-interval” (`Icc`) versions of the uniform-box rewrites for Step 3/4 inner sums:
    `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:162` (`innerSumUZ_eq_sum_Icc_zBox`),
    `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:192` (`innerSumVZ_eq_sum_Icc_zBoxV`).
  - Added the fiber-factorization → MV-hypothesis bridge (plumbing): if the fiber coefficient sums
    factor as `β(u)*α(z)` (resp. `β(v)*α(z)`) on the uniform `zBox` interval, then the TeX-facing MV
    application lemmas apply *verbatim*:
    - Step 3: `SSU/Engines/LargeSieve/TypeIIRankOneFiberBridgeTeX.lean:109`
      (`norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBox`)
    - Step 4: `SSU/Engines/LargeSieve/TypeIIRankOneFiberBridgeTeX.lean:190`
      (`norm_typeIISum_sq_le_one_add_log_of_fiberFactor_zBoxV`)
  - Added TeX Step 3/4 “progressions” rewrites for the *rank-one shear* coefficient model, matching
    the displayed expansions in `05b_SSU.tex` (lines 535–557):
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:35`
    (`typeIISum_eq_outer_u_rankOne_progression`),
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:55`
    (`typeIISum_eq_outer_v_rankOne_progression`).
  - Proved the TeX Step 3/4 MV bounds and Step 5 geometric-mean bound for `shearSum` on the
    symmetric dyadic box (rank-one shear model):
    `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:302`
    (`norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic`),
    `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:476`
    (`norm_shearSum_sq_le_one_add_log_boxEnergy_symmDyadic_outerV`),
    `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:646`
    (`norm_shearSum_sq_le_geomMean_boxEnergy_symmDyadic`).
  - Wired the *geometry-only* CS+cardinality surrogates into the TeX Step 3/4/5 interfaces
    (`Step3LargeSieveOuterU`, `Step4LargeSieveOuterV`, `Step34LargeSieveTeX`), so the TeX TT*
    wrappers can be run end-to-end without assuming those interfaces as axioms:
    `SSU/Engines/LargeSieve/TypeIIWeakLargeSieveTeX.lean:20`.
  - Added “use-site” MV helper lemmas: if a later extraction layer proves the translated `Fin`
    coefficient arrays `coeffUZFin` / `coeffVZFin` are *constant* in the outer index, then MV
    yields a clean `‖typeIISum‖² ≤ C * tubeEnergy` bound without extra cardinality loss:
    `SSU/Engines/LargeSieve/TypeIIConstCoeffMV.lean:1`
    (`norm_typeIISum_sq_le_uSet_finiteLargeSieve_C_mul_tubeEnergy_of_constCoeffUZFin`,
     `norm_typeIISum_sq_le_vSet_finiteLargeSieve_C_mul_tubeEnergy_of_constCoeffVZFin`).
  - Upgraded the above “use-site” const-coeff MV bounds into **TeX-shaped Step 3/4 inequalities**
    (still conditional on the same constancy hypotheses, but now in the exact `05b_SSU.tex` Step 3/4
    prefactor format):
    `SSU/Engines/LargeSieve/TypeIIConstCoeffTeXBounds.lean:1`
    (`norm_typeIISum_sq_le_step3_teX_of_constCoeffUZFin`,
     `norm_typeIISum_sq_le_step4_teX_of_constCoeffVZFin`,
     `norm_typeIISum_sq_le_step5_teX_of_constCoeffUZFin_of_constCoeffVZFin`).
- TeX-faithful BG tube geometry layer is in place (dyadic box, shear tubes, `S_{a/q}` range):
  `SSU/Engines/BGTubeGeometry.lean:1`
- Deterministic BG→TypeII shear-box containment plus an `ℓ²` energy comparison (tube ≤ ambient box):
  `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:126` (`image_shearMap_subset_rankOneShearBox`),
  `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:253`
  (`tubeEnergy_le_sum_norm_sq_on_rankOneShearBox_ofBG`),
  `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:293`
  (`tubeEnergy_le_boxEnergy_on_rankOneShearBox_ofBG`)
- Added a TeX-faithful “box as tube” helper (represents the dyadic box as a trivial tube when
  `U ≥ 2N`), so the tube-based Type–II/Toeplitz infrastructure can be reused for the 05_BG Toeplitz
  block without committing to a shear constraint:
  - `SSU/Engines/BGTubeGeometry.lean:1` (`tubeFinset_eq_box_of_U_ge_twoN`)
  - `SSU/Engines/BGTypeIIData.lean:1` (`TubeParams.boxTube`, `tubeFinset_boxTube_eq_box`)
- TeX-faithful TFA cutoff interface is stubbed as properties (no closed form committed yet):
  `SSU/Engines/TFAWeight.lean:1`
- Added an explicit “separable weight” variant (product of 1D bumps), matching the standard
  dyadic-cutoff convention needed for exact Toeplitz regrouping steps:
  `SSU/Engines/TFAWeight.lean:39`
- Added a concrete default separable dyadic cutoff (piecewise-linear tent, supported on `[1/2,2]`
  and equal to `1` on `[1,2]`, then multiplied in 2D):
  `SSU/Engines/TFAWeightTent.lean:1`
- 03_TFA “balanced bank mask” (Eq. `balanced-bank`) is now *defined* at the discrete/finite-sum level
  and the alias-suppression cancellation lemmas (TeX Lemma `alias-delta2`) are proved:
  - `SSU/Engines/TFAWeight.lean:1` (`BalancedBank.mask`)
  - `SSU/Engines/TFAWeightAliasSuppression.lean:1`
    (`BalancedBank.sum_mask_right`, `BalancedBank.sum_mask_left`,
     `BalancedBank.sum_sum_mul_mask_eq_zero_left`, `BalancedBank.sum_sum_mul_mask_eq_zero_right`)
- Added a TeX-faithful “BG Type–II data” wiring layer:
  tube geometry + TFA cutoff → coefficient-factorization object used by the BG Toeplitz reduction:
  `SSU/Engines/BGTypeIIData.lean:1`
- Added a “separable cutoff pulled back to lattice points” helper:
  `SSU/Engines/BGTypeIIData.lean:54`
- Added a navigation index mapping TeX → Lean:
  `SSU/INDEX.md:1`
- Added a deterministic “BG bilinear vs `tubeFormProd`” normalization lemma (swap + kernel evenness):
  `SSU/Engines/BGBilinear.lean:1`
- Defined the TeX coefficient-array map `F(d,n)` and its aggregation `A_k := ∑_{dn=k} F(d,n)`,
  plus the deterministic regrouping of the corresponding torus product sum:
  `SSU/Engines/BGTypeIIArray.lean:1`
- Added the real-frequency regrouping lemma (TeX-normalized `S(ξ) = ∑ A_k e(ξk/X)`) and a
  deterministic corollary relating `e(ξk/X)` to `fourier k ((ξ/X):𝕋)`:
  `SSU/Engines/BGTypeIIArray.lean:87`
- Added the deterministic “Toeplitz kernel extraction” step on real frequency:
  `∫_{|ξ|≤1/H} w(ξ) |∑_{k∈S} A_k e(ξk/X)|^2 dξ` becomes a `k,k'` Toeplitz form with kernel
  `K_w(h) := ∫ w(ξ) e(ξh/X) dξ`:
  `SSU/Engines/BGTypeIIWeightedToeplitz.lean:1`
- Specialized the weighted Toeplitz kernel extraction to the TeX product sum
  `prodSumRealByProd` built from `A_k` on `tube.image prod`:
  `SSU/Engines/BGTypeIIArrayWeightedToeplitz.lean:1`
- Defined the TeX-faithful packet-overlap weight `w_{i,j}(ξ) := K̂_H(ξ) ψ_i(ξ/X) conj(ψ_j(ξ/X))`
  and the induced complex Toeplitz kernel `K_{i,j}(h)`; proved the resulting `k,k'` Toeplitz form
  for `prodSumRealByProd` with this pair-dependent kernel:
  `SSU/Instances/FejerBankedTypeIIToeplitzKernel.lean:1`
- Added the Lean-facing conjugated weight `wLean := star(w)` so Toeplitz kernels line up with
  Mathlib’s `inner` convention (conjugate-linear in the first argument):
  `SSU/Instances/FejerBankedTypeIIToeplitzKernel.lean:78`
- Made the ξ-band integrability of the packet-overlap weight *automatic*:
  - Added measurability fields to the Fejér-banked data (`P_{U_{j,k}}`, `Φ_H`) so the real-frequency
    evaluation map is Lean-usable.
  - Proved `Weight.integrableOn_w` and added `_auto` wrappers so downstream theorems no longer take
    an explicit `hw : IntegrableOn w (band H)` argument:
    `SSU/Instances/FejerBankedTypeIIToeplitzKernel.lean:1`
- Added the deterministic extraction lemma rewriting the weighted band integral in *torus evaluation*
  form (`S((ξ/X):𝕋)`) into the same TeX `k,k'` Toeplitz form with the packet-overlap weight:
  `SSU/Instances/FejerBankedTypeIIToeplitzExtraction.lean:1`
- Added a TeX-faithful interface for the remaining TT*/kernel-representation step (as a hypothesis),
  together with the deterministic consequence that it yields an `inner = toeplitzFormTeXC` identity
  with the induced complex kernel `K_{i,j}`:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarHypothesis.lean:1`
- Added the equivalent TeX-narrative interface where TT* is stated directly as the *Toeplitz form*
  (physical-side short-shift quadratic form), and the ξ-band weighted-integral statement is derived
  deterministically:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.lean:1`
- Recorded the `1/X` Jacobian factor (TeX normalization) for the substitution `x = ξ / X` as a
  deterministic interval-integral lemma:
  `SSU/Engines/RealChangeOfVariables.lean:1`
- Added a set-integral (`Icc`) variant of the same change-of-variables lemma, so we can work with
  TeX’s closed bands directly (and still use `intervalIntegral` substitution internally):
  `SSU/Engines/RealChangeOfVariables.lean:147`
- Made the pointwise admissible-kernel moment bounds public (`0 ≤ K̂_H ≤ 1`, etc.), so instance
  files can use them without copying proofs:
  `SSU/Engines/TypeII.lean:1689`
- Added a generic (measure-space) `L²` multiplier operator package + Gram expansion lemma (so we can
  reuse the “inner = integral” reduction outside the torus):
  `SSU/Engines/L2Multipliers.lean:1`
- Added deterministic diameter/distance bounds for the Step 3/4 index sets (`uSet`, `vSet`), so MV
  large-sieve lemmas that assume `∀ i,j∈J, distZ i j ≤ R` can be applied with an explicit `R`:
  `SSU/Engines/LargeSieve/TypeIIIndexBounds.lean:1`
- Added residue-class partitions needed for the TeX Step 3/4 progression bookkeeping, plus a
  Step 3 LHS rewrite that splits the outer `u`-sum into the `r ∈ [0,q)` classes, and the
  pointwise phase-split on each class (`u = u₀(r) + uIndex(r,u)*q`):
  - partition: `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:1`
  - phase split lemma: `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:35`
  - rewrite lemma: `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:58`
  - Step 4 phase split lemma (the `v`-analogue): `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:37`
  - Step 4 rewrite lemma (the `v`-analogue): `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:58`
- Strengthened the residue partitions with explicit “arithmetic progression” structure:
  on each class you can rewrite elements as `u = uResidue(r) + z*q` / `v = vResidue(r) + z*q`,
  and the resulting index maps are injective on each class:
  `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:1`
- Added deterministic “reindex by progression parameter” lemmas so sums over residue classes can be
  rewritten as sums over the `uIndex`/`vIndex` images (the exact TeX progression index):
  - `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:187` (`uFromIndex`, `sum_uClass_eq_sum_uIndexSet`)
  - `SSU/Engines/LargeSieve/TypeIIResiduePartition.lean:362` (`vFromIndex`, `sum_vClass_eq_sum_vIndexSet`)
  - convenience rewrites for `‖innerSum‖²` sums:
    `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:75`,
    `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:69`
- Added the “index-specialized” phase-split lemmas (same content as TeX’s AP rewrite, but with
  the variable *already* renamed to the progression parameter `m`):
  - `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:56` (`innerSumUZ_uFromIndex_eq_phaseSplit`)
  - `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:56` (`innerSumVZ_vFromIndex_eq_phaseSplit`)
- Built MV `FiniteLargeSieve` instances directly on the progression-index sets `uIndexSet td r` and
  `vIndexSet td r` (this matches the TeX Step 3/4 “1D progression” lens), including explicit
  diameter bounds and a ξ-band “small phase” wrapper for `t = ξ*q/X`:
  `SSU/Engines/LargeSieve/TypeIIResidueIndexLargeSieve.lean:1`
- Added TeX-friendly `(1+log)` bounds on the MV constants `C` for those progression-index instances
  (so downstream can use a single explicit polylog expression instead of unfolding MV internals):
  `SSU/Engines/LargeSieve/TypeIIResidueIndexLargeSieve.lean:118`
- Combined (Step 3/4) residue-class partitions with the `uIndex`/`vIndex` reindexing so the outer
  sums are literally over `r ∈ [0,q)` and the progression parameter `m`:
  - `SSU/Engines/LargeSieve/TypeIIStep3Reduce.lean:103`
  - `SSU/Engines/LargeSieve/TypeIIStep4Reduce.lean:110`
- Repackaged the Step 3/4 MV hypotheses in a TeX-faithful “per residue class” form and proved the
  deterministic summation lemma from the per-residue interface back to the global interface:
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:1`
- Packaged those diameter bounds + the ξ-band “small phase” condition into ready-to-use MV
  `FiniteLargeSieve` instances on `uSet td` / `vSet td`:
  `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:1`
- Added “phase-unfold” helper lemmas for those MV `FiniteLargeSieve` instances, so downstream code
  can match TeX phases without unfolding the record:
  `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:127`
- Added TeX-friendly `(1+log)` bounds on the MV constants `C` for those instances (rewriting
  `1/|t|` as `X/|ξ|` for `t = ξ/X`):
  - `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:204` (`uSet_finiteLargeSieve_C_le_one_add_log`)
  - `SSU/Engines/LargeSieve/TypeIIIndexLargeSieve.lean:288` (`vSet_finiteLargeSieve_C_le_one_add_log`)
- Added uniform “z-box” supersets `zBox td` / `zBoxV td` that contain every per-fiber index set
  `zSet td u` / `zSetV td v`, removing residue-class dependence at the deterministic level:
  `SSU/Engines/LargeSieve/TypeIIZSetBox.lean:1`
- Added rewrites that (i) enlarge `innerSumUZ` / `innerSumVZ` to sums over the uniform boxes and
  (ii) reindex `Ioc`/`Icc` interval sums as translated `range` sums (to match MV’s `Fin N` shape):
  `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:1`
- Added deterministic “base-point phase factoring” for those translated `range` sums, plus
  `‖innerSum‖ = ‖translated sum‖` corollaries (unimodular phase drops in norms):
  `SSU/Engines/LargeSieve/TypeIIZBoxRewrite.lean:183`
- Added deterministic `range`→`Fin N` rewrites for the translated `zBox` sums, so MV/`FiniteLargeSieve`
  can be applied without manual coercion gymnastics:
  `SSU/Engines/LargeSieve/TypeIIZBoxToFin.lean:1`
- Added a small “glue” lemma layer to apply a `FiniteLargeSieve` bound to the Step 3/4 fiber sums,
  under an explicit coefficient-constancy hypothesis (used later by the rank-one extraction):
  `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:1`
- Specialized that glue layer to the MV `FiniteLargeSieve` instances on `uSet td` / `vSet td`,
  discharging the phase side-conditions automatically by evaluating MV at `-ξ` (so the built-in
  `-t*i*n` phase matches TeX’s `+ξ*i*n/X`):
  `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:196`
- Added residue-class variants that apply MV on the progression parameter `m` over
  `uIndexSet td r` / `vIndexSet td r` (TeX’s “1D progression” lens), absorbing the residue-phase
  into the coefficient array and using `‖e(·)‖ = 1` to keep the same energy:
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:281`
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:391`
- Added the matching per-residue `(1+log)` corollaries (replace `LS.C` by an explicit polylog):
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:509`
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:558`
- Added TeX-friendly corollaries of those specializations where the MV constant is replaced by an
  explicit `(1+log)` expression (still conditional on coefficient-constancy):
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:273`
    (`step3_sum_u_norm_innerSumUZ_sq_le_of_constCoeff_uSet_one_add_log`)
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:351`
    (`step4_sum_v_norm_innerSumVZ_sq_le_of_constCoeff_vSet_one_add_log`)
- Proved (optional) harmonic/log simplifications for the MV Crow sum, so MV constants can be stated
  with explicit polylog losses:
  - `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:244` (`sum_aMV_Icc_le_harmonic`)
  - `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:325` (`sum_aMV_Icc_le_one_add_log`)
- Packaged the corresponding bound on the MV `FiniteLargeSieve` constant `C`:
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZInterface.lean:127`
- Added an explicit ℤ-indexed “dual large sieve” inequality from the exponential Gram bound:
  - weight `aMV(d)` (Dirichlet-kernel `min(N, 1/(|t|d))`) and
  - a finite Crow constant in `Icc 1 R` form,
  yielding `‖∑ c_i • expVec(i)‖² ≤ Crow * ∑ ‖c_i‖²` (optional harmonic/log simplification still
  TODO):
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:1`
- Proved the TT*/kernel-representation identity in a canonical *real-frequency* model:
  on the ξ-band with measure `(1/X)dξ`, packets are multipliers by `√K̂_H(ξ) ψ_j(ξ/X)`, so
  the Gram is exactly the TeX-weighted band integral with weight
  `wLean(ξ)=K̂_H(ξ) conj(ψ_i(ξ/X)) ψ_j(ξ/X)`:
  `SSU/Instances/FejerBankedTypeIIToeplitzRealTTStar.lean:1`
- Proved a first non-toy *end-to-end* Toeplitz Type–II reduction in that real-frequency TT* model:
  starting from the rank-one Type–II product signal `S(ξ)=∑_k A_k e(ξk/X)`, the packet Gram equals
  the TeX `k,k'` Toeplitz quadratic form with induced kernel `K_{i,j}`:
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:1`
- Isolated the deterministic “rank-one band integral → TeX Toeplitz form” lemma (no TT* / torus
  operator content, just Toeplitz kernel extraction with the frozen Type–II signal):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusRankOneTTStar.lean:1`
- Made the rank-one Type–II “signal” faithful to TeX’s **double-sum** presentation and connected it
  deterministically to the grouped-by-product form:
  - `signalTorusDN`, `signalRealDN`, and `*_eq_*ByProd` regrouping:
    `SSU/Engines/BGTypeIIRankOneSignal.lean:1`
- Wired the rank-one Type–II input into the generic `BGTypeIIArray.Data` packaging on the **full
  dyadic box** (box-as-tube), so downstream Toeplitz kernel extraction can use a uniform API:
  - `boxData` + `tube/F/A` compatibility lemmas:
    `SSU/Engines/BGTypeIIRankOneSignal.lean:1`
- Added “boxData-form” corollaries for the deterministic Toeplitzization statements:
  - band-integral Toeplitzization:
    `SSU/Instances/FejerBankedTypeIIToeplitzTorusRankOneTTStar.lean:1`
  - full TT* inner-product milestone:
    `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:1`
- Strengthened the “boxData” packaging so it is ambient-type-generic (no torus dependency in the
  Engines layer) and added a `mkBox`-style TT* Toeplitz identity whose RHS is written directly in
  terms of a `BGTypeIIArray.Data` object:
  - generic `Input.boxData` API: `SSU/Engines/BGTypeIIRankOneSignal.lean:195`
  - `inner_eq_toeplitzFormTeXC_rankOne_mkBoxData`:
    `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:1`
- Added the first deterministic “no wrap-around” lemma for the TeX substitution `x = ξ/X`:
  if `(1/H)/X < 1/2`, then `ξ ↦ ((ξ/X):𝕋)` is injective on `|ξ| ≤ 1/H`:
  `SSU/Instances/FejerBankedTypeIIToeplitzBandMap.lean:1`
- Added the corresponding small-arc integral bridge on `𝕋`:
  for endpoints inside the fundamental domain, the Haar integral of an arc-indicator equals the
  real set-integral on the representative interval:
  `SSU/Instances/FejerBankedTypeIIToeplitzArcBridge.lean:1`
- Combined the two into a single TeX-facing “band → arc” bridge:
  `(1/X) ∫_{|ξ|≤1/H} g((ξ/X):𝕋) dξ = ∫_{𝕋} 1_{arc} g` under the smallness assumption
  `(1/H)/X < 1/2`:
  `SSU/Instances/FejerBankedTypeIIToeplitzBandToArc.lean:1`
- Added a TeX-faithful “TT* as an arc statement” interface, plus a deterministic conversion
  `arc-form TT* ⇒ ξ-band TT*` (so future proofs can avoid carrying the real variable `ξ`):
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcHypothesis.lean:1`
- Exported the deterministic “no wrap-around” evaluation lemma for the lifted kernel weight:
  `KhatTorus(X,H)((ξ/X):𝕋) = Khat(H) ξ` on `|ξ|≤1/H` under `(1/H)/X<1/2`:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcHypothesis.lean:67`
- Strengthened the rank-one real-frequency TT* milestone with a TeX-faithful arc-form corollary:
  the same Gram entry equals a Haar integral over the small arc `|x|≤1/(HX)` with integrand
  `KhatTorus * packetOverlap * |signal|^2`:
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneReal.lean:447`
- Added a thin “arc proof” wrapper that re-exports the two key rank-one Type–II milestones under a
  TeX-aligned filename:
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcProof.lean:1`
- Proved the foundational 1D exponential-sum bounds needed for the MV large sieve:
  - `norm_e_sub_one_lower_of_abs_le_half` and the Dirichlet kernel bound
    `norm_sum_range_e_mul_le_min`:
    `SSU/Engines/LargeSieve/AdditiveMV.lean:1`
- Added the generic “row-sum Gram bound ⇒ dual large sieve” bridge (Schur/Cotlar–Stein glue):
  `SSU/Engines/LargeSieve/DualSieveFromInterzoneZ.lean:1`
- Added the deterministic “interval sum ⇒ Dirichlet-kernel min bound” lemma for exponentials
  on `Icc a b`, which is the core ingredient to bound Gram entries in the MV proof:
  `SSU/Engines/LargeSieve/MVExponentialGram.lean:1`
- Added `…_onJ` variants of the two rank-one identities (same statements, but with `i,j ∈ D.J`
  arguments to match downstream “SSU heart” APIs):
  `SSU/Instances/FejerBankedTypeIIToeplitzTTStarArcProof.lean:59`
- Added a TeX-narrative entry point for the **rank-one-only** “inner = Toeplitz form” statement:
  `SSU/Instances/FejerBankedTypeIIToeplitzReductionRankOne.lean:1`
- Added a first “ledger inequality actually runs” lemma for the TT* band model packets, evaluated
  on the rank-one Type–II signal `S(ξ)` (analytic-trivial: uses only Cauchy–Schwarz, `a ≡ 1`):
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneLedger.lean:1`
- Proved the first genuinely analytic bridge: Step 3–4 (`Step34ProdSum`) ⇒ a uniform TT* Gram bound
  for the Fejér-banked ξ-band packets evaluated on the rank-one Type–II signal:
  `SSU/Instances/FejerBankedTypeIIToeplitzRankOneStep34.lean:115`
- Combined the Step 3–4 Gram bound with the deterministic band→arc identity, yielding a
  TeX-shaped **small-arc** inequality (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzStep34ArcProof.lean:1`
- Packaged the TeX “arc integral = Toeplitz form” identity (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzArcToeplitzRankOne.lean:1`
- Repackaged Step 3–4 as a direct bound on the **normalized** Toeplitz form
  `‖(1/X) * toeplitzFormTeXC‖` (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzStep34ToeplitzBound.lean:1`
- Finished the torus-side TT* bridge for the **actual Fejér-banked torus packet operators**
  (rank-one Type–II input), with the `1/X` Jacobian and packet overlap
  `ψ_i(ξ/X) * conj(ψ_j(ξ/X))` built into the weight:
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOne.lean:270`
- Generalized the same torus-side bridge from the fixed rank-one signal to an *arbitrary*
  BG Type–II coefficient-array package `BGTypeIIArray.Data` (still deterministic/algebraic;
  no “SSU heart” analytic work):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPackets.lean:425`
- Factored the common `AddCircle.equivIoc` / `AddCircle.liftIoc` measurability lemmas into a reusable
  torus module (used by both the rank-one and general torus Toeplitz bridges):
  `SSU/Torus/AddCircleMeasurability.lean:1`
- Wrapped the Step 3–4 Toeplitz bound into a direct bound for the torus packet Gram
  `‖⟪T_i fTT, T_j fTT⟫‖` (rank-one Type–II input):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsRankOneBound.lean:1`
- Wrapped the Step 3–4 hypothesis into a direct bound for the **torus packet Gram** for an
  *arbitrary* `BGTypeIIArray.Data` package (general Type–II array, still assuming `Step34ProdSum`):
  `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.lean:44`
- Added TeX-faithful *statement interfaces* for the Step 3/4 large-sieve bounds (and their
  geometric-mean combination) in the SSU single-tube proof:
  `SSU/Engines/TypeIILargeSieveTeX.lean:1`
- Added “use-site” (per extracted signal `F`) wrappers so later extraction lemmas can supply a
  Step 5 bound without constructing global `∀ F` interfaces:
  `SSU/Engines/TypeIILargeSieveTeXFor.lean:1`
- Added a TeX-faithful *statement interface* for Lemma `balanced-xi` (moment hypotheses on `K̂_H`
  and the resulting ξ-integration bound):
  `SSU/Engines/TypeIIBalancedXiTeX.lean:1`
- Discharged the `balanced-xi` *Inv* interface for the concrete admissible kernel
  `AdmissibleKernel.Khat` (crude but explicit, `C = 2`; assumes `0 ≤ X` and `1 < H`):
  `SSU/Engines/TypeIIBalancedXiAdmissibleKernel.lean:1`
- Added TeX-faithful TT* wrappers replacing the uniform-in-ξ surrogate; wrappers accept either
  `Step34LargeSieveTeX` directly or `(Step3LargeSieveOuterU, Step4LargeSieveOuterV)` via the
  geometric-mean combiner:
  `SSU/Engines/TypeIITTStarWrappersTeX.lean:1`
- Added the corresponding Fejér-banked bridge wiring the TeX-shaped Type-II hypotheses into a
  Fejér-banked SSU contract:
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Added `HypothesisKhat` variant that removes the `balanced-xi` hypothesis by instantiating it
  for the concrete admissible kernel `K̂_H := AdmissibleKernel.Khat`:
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Started the Step 3–4 large-sieve proof effort by adding deterministic residue-class bookkeeping
  for the TeX congruence `u ≡ -a v (mod q)` in shear coordinates:
  `SSU/Engines/LargeSieve/TypeIISetup.lean:1`
- Completed the next deterministic TeX Step 3/4 rewrite: partition `typeIISum` by shear fibers
  `u = qn - ad`, split `v = v₀(u) + z*q`, and factor out the `v₀(u)` phase:
  `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:1` (`typeIISum_eq_sum_u`)
- Added the secondary deterministic rewrite used immediately before the large-sieve inequality:
  for each fixed `u`, group the fiber sum by the progression parameter `z` and extract the
  exponential `e(ξ*u*z/X)`:
  `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:55` (`sum_fiberU_eq_sum_z`, `zSet`, `fiberUZ`)
- Combined these two deterministic rewrites into a single TeX-shaped `(u,z)` double-sum expansion
  of `typeIISum`:
  `SSU/Engines/LargeSieve/TypeIISumDecompose.lean:337` (`typeIISum_eq_sum_u_sum_z`)
- Added deterministic fiber-energy bookkeeping, using the fact that each `(u,z)` (and each `(v,z)`)
  fiber corresponds to at most one lattice point in shear coordinates:
  - inequality form (fallback): `SSU/Engines/LargeSieve/TypeIIFiberEnergy.lean:64`
    (`sum_u_z_norm_fiberUZ_sum_sq_le_tubeEnergy`, `sum_v_z_norm_fiberVZ_sum_sq_le_tubeEnergy`)
  - exact form (preferred for later constant-tracking): `SSU/Engines/LargeSieve/TypeIIFiberEnergy.lean:173`
    (`sum_u_z_norm_fiberUZ_sum_sq_eq_tubeEnergy`, `sum_v_z_norm_fiberVZ_sum_sq_eq_tubeEnergy`)
- Added TeX-facing “shear-image” rewrites so `typeIISum` and `tubeEnergy` can be treated as sums over
  `T' := (shearMap td.a td.q) '' td.T ⊂ ℤ×ℤ` (this matches the TeX `S(ξ)` viewpoint):
  - general change-of-variables (`typeIISum` ↔ `shearSum` over the image):
    `SSU/Engines/LargeSieve/TypeIIShearSumTeX.lean:91`
  - no-classical-inverse specialization when coefficients factor through shear coordinates:
    `SSU/Engines/LargeSieve/TypeIIShearSumTeX.lean:147`
  - matching energy rewrite (`tubeEnergy` ↔ shear-image ℓ² energy):
    `SSU/Engines/LargeSieve/TypeIIShearSumTeX.lean:177`
  - rank-one shear coefficients specialized to the TeX `F(u,v)=β(u)α(v)` convention:
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:124`
    `SSU/Engines/LargeSieve/TypeIIProgressionSignalTeX.lean:136`
- Added Montgomery–Vaughan hypothesis interfaces specialized to the TeX Step 3/4 fiber sums,
  together with adapter lemmas that turn them into `Step3FiberLargeSieve` / `Step4FiberLargeSieve`:
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:1`
- Added a deterministic helper that upgrades a *cardinality bound* on the `z`-progressions into a
  TeX-shaped Step 3 (MV) hypothesis via a single Cauchy–Schwarz inequality (useful as a proof
  scaffold while the full MV large sieve is being formalized):
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:52`
- Added deterministic geometry bounding the Step 3 progression parameter `z` by a floor/ceil
  interval using only the dyadic box constraint `D < d ≤ 2D` (this is the input needed to produce
  `zSet` cardinality bounds of size `O(1 + D/q)`):
  `SSU/Engines/LargeSieve/TypeIIZSetCard.lean:1`
- Added a sharp finite “analysis from synthesis” helper (Bessel duality) so we can turn the
  synthesis/dual large sieve into the analysis/primal form without losing constants:
  `SSU/Engines/LargeSieve/AnalysisFromSynthesis.lean:40`
- Completed a TeX-aligned “finite MV large sieve on ℤ” package (dual + primal forms) using
  `Real.toNNReal` (this repo’s mathlib snapshot does not provide `NNReal.ofReal`):
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZ.lean:1`
- Added a small bridge packaging the proved MV finite large sieve into the generic
  `FiniteLargeSieve` hypothesis interface (phase `-t*i*n`):
  `SSU/Engines/LargeSieve/MVFiniteLargeSieveZInterface.lean:1`
- Upgraded that geometric bound into a directly-usable estimate
  `((zSet td u).card : ℝ) ≤ 3 * (D/q)` under the mild regime assumption `1 ≤ D/q`, and used it to
  build a concrete (still analytic-trivial) Step 3 MV hypothesis from pure box geometry:
  `SSU/Engines/LargeSieve/TypeIIZSetCard.lean:133`,
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:196`
- Added the Step 4 analogue: `zSetV` (the progression parameter in `u = u₀(v) + z*q`) is bounded
  deterministically using only the tube constraint `|u| ≤ U`, yielding
  `card(zSetV) = O(U/q + 1)`:
  `SSU/Engines/LargeSieve/TypeIIZSetVCard.lean:1`
- Used that `zSetV` bound to build a concrete (still analytic-trivial) Step 4 MV hypothesis from
  pure geometry + a single Cauchy–Schwarz inequality; the TeX prefactor
  `D * (U/q + X/|ξ|)` is inserted by monotonicity on the ξ-band under the mild regime assumptions
  `1 ≤ D` and `1 ≤ X*H`:
  `SSU/Engines/LargeSieve/MontgomeryVaughanTypeII.lean:256`
- Added the TeX Step 5 “geometric mean” combiner: Step 3 + Step 4 ⇒ `Step34LargeSieveTeX` (with the
  deterministic `max(U/(qD),1)` inflation absorbed into the constant):
  `SSU/Engines/LargeSieve/TypeIIStep34CombineTeX.lean:1`
- Wired the TeX bridge so you can assume Step 3 + Step 4 (Montgomery–Vaughan) and automatically
  derive Step 5 and the downstream Fejér-banked SSU contract (`HypothesisMV`):
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Added a convenience constructor that builds the *full* TeX-facing `Hypothesis` from the
  geometry-only weak large-sieve bound (and discharges `balanced-xi` for `K̂_H`):
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:175`
- Added `HypothesisMVKhat` variant that (i) assumes Step 3 + Step 4 (MV), (ii) derives Step 5, and
  (iii) discharges `balanced-xi` for the concrete admissible kernel:
  `SSU/Instances/FejerBankedTypeIIBridgeTeX.lean:1`
- Added a convenience wrapper that builds the full TeX-facing contract using the geometry-only
  Step 3/4 fallbacks (to reduce boilerplate while the real MV large sieve proofs are pending):
  `SSU/Instances/FejerBankedTypeIIBridgeTeXBoxFallback.lean:1`
- Added rank-one shear “outer weight + MV on an interval” plumbing lemmas (this is the core
  building block for a first *proved* Step 3/4 in the rank-one model):
  - interval → `Fin N` rewrite: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:44`
  - MV applied to interval sums: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:169`
  - Cauchy–Schwarz outer-weight wrapper: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:244`
  - combined rank-one signal bound: `SSU/Engines/LargeSieve/RankOneShearLargeSieve.lean:328`
- Added the first TeX-facing, **non-toy** MV application lemma in shear coordinates: for a rank-one
  coefficient array on the product box `J × Icc(a,a+N-1)`, `shearSum` is exactly the MV-ready
  “rank-one signal”, and hence satisfies the polylog MV bound with RHS written as 2D energy
  `boxEnergy`:
  `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:45`
- Added a TeX-faithful dyadic-box convenience wrapper (`u ∈ [-U,U]`, `v ∈ (D,2D]` as `Icc(D+1,2D)`):
  `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:148`
- Added the deterministic “tube by restriction” corollary: shrink `u`-support by replacing `β` with
  `β' := 1_{J'}·β` on a larger box, without breaking rank-one:
  `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:251`
- Added variants of the same MV bounds with the TeX-literal RHS energy
  `∑_{(u,v)∈box} ‖β(u)α(v)‖²` (instead of the packaged `boxEnergy`):
  - `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:416`
    (`norm_shearSum_sq_le_one_add_log_sum_norm_sq_on_box`)
  - `SSU/Engines/LargeSieve/RankOneShearBoxLargeSieveTeX.lean:437`
    (`norm_shearSum_sq_le_one_add_log_sum_norm_sq_on_box_of_left_restrict`)
- Added a deterministic interval diameter bound to discharge `distZ ≤ R` goals on `Finset.Icc A B`:
  `SSU/Hilbert/DistZ.lean:39`
- Wired the shear-image change-of-variables into the rank-one shear-box MV bound: if you can
  identify `td.T.image (shearMap a q)` with a product box, then you get a TeX-friendly bound for
  `typeIISum` immediately:
  `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:1`
  - plus the “tube by restriction” variant using `βrestrict` (shrink `u`-support without breaking
    rank-one):
    `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:131`
  - plus symmetric-dyadic convenience wrappers (match the TeX dyadic box convention
    `u ∈ [-U,U]`, `v ∈ (D,2D]`) transporting the proved `shearSum` bounds to `typeIISum`:
    - outer-`u` constant: `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:318`
    - outer-`v` constant: `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:356`
    - Step 5 geom mean: `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:391`
  - plus TeX-literal RHS energy variants:
    - `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:127`
      (`norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc`)
    - `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:188`
      (`norm_typeIISum_sq_le_one_add_log_sum_norm_sq_on_box_of_image_eq_box_Icc_left_restrict`)
  - plus tube-energy restatements of those TeX-literal variants (same bound, but RHS is
    `tubeEnergy td.T`):
    - `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:153`
      (`norm_typeIISum_sq_le_one_add_log_tubeEnergy_of_image_eq_box_Icc'`)
    - `SSU/Engines/LargeSieve/TypeIIShearBoxRankOneTeX.lean:257`
      (`norm_typeIISum_sq_le_one_add_log_tubeEnergy_of_image_eq_box_Icc_left_restrict'`)
- Added deterministic plumbing from the explicit BG tube `tubeFinset` (05_BG “def-tube”) to the
  Type–II large-sieve `TubeData` record (centered tube `s=0`), plus the first two “real geometry”
  facts about the shear image:
  - `TubeData` builder: `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:76`
    (`BGTubeBridge.tubeDataOfBGTube`)
  - shear-image containment in the TeX shear box `[-U,U]×(D,2D]`: `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:123`
    (`BGTubeBridge.image_shearMap_subset_rankOneShearBox`)
  - shear congruence `u ≡ -a*v (mod q)`: `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:179`
    (`BGTubeBridge.shearMap_fst_modEq_neg_a_mul_snd_of_mem_image`)
  - convenient explicit index-range bounds (remove `ceil` from later MV plumbing):
    - `uSet ⊆ Icc(-U,U)`: `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:201`
      (`BGTubeBridge.uSet_subset_Icc_negU_U_ofBG`)
    - `vSet ⊆ Icc(D+1,2D)`: `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:229`
      (`BGTubeBridge.vSet_subset_Icc_Dp1_twoD_ofBG`)
  - corresponding `distZ` diameter bounds on those index sets (usable as MV `R`):
    - `distZ i j ≤ 2U` on `uSet`: `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:377`
      (`BGTubeBridge.distZ_le_two_mul_U_on_uSet_ofBG`)
    - `distZ i j ≤ 4D` on `vSet`: `SSU/Engines/LargeSieve/BGTubeToTubeData.lean:397`
      (`BGTubeBridge.distZ_le_two_mul_twoD_on_vSet_ofBG`)
  - import hub (so downstream files can just `import SSU.Engines.LargeSieve.BG`):
    `SSU/Engines/LargeSieve/BG.lean:1`
- Added “use-site” TeX Step 3/4 wrapper interfaces and a Step 5 geometric-mean combiner (so
  downstream packet/TT* wrappers can consume *either* proved Step 3/4 hypotheses or weak fallback
  ones without touching the global interfaces):
  `SSU/Engines/TypeIILargeSieveTeXFor.lean:1`
  Also added constructors that build the use-site Step 3/4 objects directly from the proved
  **const-coefficient** TeX bounds:
  - `SSU/Engines/TypeIILargeSieveTeXFor.lean:124` (`Step3LargeSieveOuterUFor.of_constCoeffUZFin`)
  - `SSU/Engines/TypeIILargeSieveTeXFor.lean:177` (`Step4LargeSieveOuterVFor.of_constCoeffVZFin`)
- Added a per-signal TeX TT* wrapper: given `Step2ToTubeForm`, a **use-site** Step 5 bound
  (`Step34LargeSieveTeXFor td F`), and `BalancedXiClaimInv`, derive the final tube-form bound for
  that particular extracted coefficient array `F`:
  `SSU/Engines/TypeIITTStarWrappersTeXFor.lean:1`
  Also added the “two-interface” convenience wrapper: use-site Step 3 + Step 4 ⇒ use-site Step 5
  ⇒ TT* for a fixed `F`:
  `SSU/Engines/TypeIITTStarWrappersTeXFor.lean:321`
  And a “constCoeff ⇒ (Step 3 + Step 4) ⇒ TT*” wiring lemma (so we’re no longer forced to go
  through the Step 5 interface at the call-site):
  `SSU/Engines/TypeIITTStarWrappersTeXFor.lean:354`
  Also added the next “plug into reduction” lemma: combine the per-signal TT* bound with a
  `ReductionToTubeForm` to obtain an immediate **use-site Gram estimate** for one pair `(i,j)`:
  `SSU/Engines/TypeIITTStarWrappersTeXFor.lean:359`
  Also added and compiled a BG one-add-log reduction-level bridge that wires
  `of_bgTubeRankOne_modEq_oneAddLog` through Step 5 to TT* at the reduction layer (with the
  Step-5 constant packaged via a local `h34` binding to avoid dependent-cast bottlenecks):
  `SSU/Engines/TypeIITTStarWrappersTeXFor.lean:786`
  Verified downstream import wiring still compiles:
  `lake build SSU.Instances.FejerBankedTypeIIBridgeTeX` (pass).
- Added a deterministic helper that reduces the “const-coefficient” hypotheses needed by the TeX
  Step 3/4 interfaces to a fiber-sum invariance statement:
  `SSU/Engines/LargeSieve/TypeIIConstCoeffFromFiber.lean:1`
  Extended this helper to the **residue-index** setting (`uIndexSet` / `vIndexSet`) used by the
  more TeX-faithful “progression parameter” large sieve variants:
  - `SSU/Engines/LargeSieve/TypeIIConstCoeffFromFiber.lean:67`
    (`exists_constCoeffUZFin_of_sum_fiberUZ_uFromIndex_eq_ref`)
  - `SSU/Engines/LargeSieve/TypeIIConstCoeffFromFiber.lean:105`
    (`exists_constCoeffVZFin_of_sum_fiberVZ_vFromIndex_eq_ref`)
  Also added direct bridge lemmas that turn fiber-sum invariance into the Step 3/4 progression-index
  MV inequalities without separately packaging a `constCoeff` hypothesis:
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:390`
    (`step3_sum_uFromIndex_norm_innerSumUZ_sq_le_of_sum_fiberUZ_uFromIndex_eq_ref_finiteLargeSieve`)
  - `SSU/Engines/LargeSieve/TypeIIFiberLargeSieveFromFiniteLargeSieve.lean:535`
    (`step4_sum_vFromIndex_norm_innerSumVZ_sq_le_of_sum_fiberVZ_vFromIndex_eq_ref_finiteLargeSieve`)

## Optional post-platinum sharpenings

1. Tighten constants on broad non-box extracted families (optional quality improvement).
2. Add stronger residue/tube-class analytic bounds where mathematically available.
3. Continue lint/cleanup-only passes (`simp`/unused-variable warnings) without API changes.

## Note on TeX faithfulness (current bottleneck)

- The TeX SSU proof uses Step 3–5 large-sieve bounds with an `X/|ξ|` singular term and then
  handles ξ-integration using moment hypotheses (Lemma `balanced-xi`). We now have TeX-faithful
  TT* wrappers (`Step34LargeSieveTeX` + `BalancedXiClaimInv`) and Fejér-banked bridges that consume
  them, but the older uniform surrogate (`Step34LargeSieve` / `Step34ProdSum`) remains in parallel
  for legacy/toy paths.

## Known remaining hypothesis-style interfaces

- Any instance-level `inner_eq_toeplitzForm` still present as a field/hypothesis (to be proved).
- Any instance-level Type–II SSU bound (large sieve / Sawyer testing) still present as a field/hypothesis.
