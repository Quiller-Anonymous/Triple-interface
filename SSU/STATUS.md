# SSU status (rolling)

Last updated: 2026-02-18

Estimated “status bar” (**TeX-strength**, end-to-end SSU as in TeX): ~64%

Internal micro-bar (Type–II large sieve stage): ~92%

Secondary bar (**plumbing + weak fallbacks**, end-to-end objects exist but with crude CS/geometry
surrogates standing in for real large-sieve input): ~79%

## What’s next (major remaining steps)

Step-3 status (split):
- ✅ Engine/use-site proved: non-fallback `Step3LargeSieveOuterUFor` route exists for the extracted
  Type–II signal shape (BG rank-one/modEq pathway in
  `FejerBankedTypeIIBridgeTeXBGRankOne`).
- ✅ `hF`-plumbing improved: new coefficient-form constructors can now discharge `hF`
  definitionally once inner/energy reduction identities are supplied in rank-one coefficient form.
- ⏳ Flagship-instance discharge pending: we still need extraction-side proofs that the concrete
  flagship extracted coefficients satisfy the required input hypotheses (`hF`/constancy/modEq
  family), so Step 3 is not yet “assumption-free” at the final instance layer.

1) Discharge extraction-side constancy inputs used by the proved Step-3/Step-4 routes.
- Target output: replace application-facing `hαconst`/`hβconst` and residue-index constancy
  assumptions with proved lemmas from the flagship extraction map.

2) Finish the non-toy extraction bridge to Toeplitz form for the frozen Fejér-banked packets.
- Target output: production `inner_eq_toeplitzForm` path used by the main instance.

3) Discharge flagship instance assumptions (especially `tubeForm_eq` + reduction plumbing) by proof.
- Target output: bridge constructors for the flagship instance require no application-facing
  hypothesis placeholders.

4) Close the SSU heart for the flagship packet family and expose the final contract.
- Target output: proved `GramHypothesis`/ledger contract from the full proved chain above.

These four steps are the main remaining path from current ~64% TeX-strength to an end-to-end
proved SSU apparatus for the flagship instance.

Latest microstep:
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

## What’s next (highest priority)

1. Plumbing milestone (Type–II extraction) is complete:
   - deterministic bridge from torus packet Gram → TeX Toeplitz form for a general Type–II array:
     `SSU/Instances/FejerBankedTypeIIToeplitzTorusPackets.lean:425`
   - Step 3–4 (`Step34ProdSum`) ⇒ torus packet Gram bound (general Type–II array):
     `SSU/Instances/FejerBankedTypeIIToeplitzTorusPacketsStep34Bound.lean:44`
- TeX-faithful rank-one Type–II input (`α⊗β`) on the dyadic box is now a *definitionally frozen*
  object (independent of packets), with the TeX-ordered Toeplitz regrouping lemma proved:
  `SSU/Engines/BGTypeIIRankOne.lean:1`
- The corresponding torus-side Type–II signal `f(x) = ∑ A_k fourier k x` (and real-frequency
  normalization `f(ξ/X) = ∑ A_k e(ξk/X)`) is now defined and bridged deterministically:
  `SSU/Engines/BGTypeIIRankOneSignal.lean:1`
2. Prove (i.e. *discharge*) `Step34ProdSum` for the first meaningful class of Type–II arrays
   (start with the rank-one `α⊗β` box model; then the shear-tube restriction), matching the TeX
   “square-root gain” with the right scale `(H/X)^{1/2}` (polylog losses OK).
3. Use (2) inside the Fejér-banked torus packet Gram bound, then wire the resulting Gram control
   into the SSU interzone hypotheses for the already-summed shell packets and run the SSU ledger.

## Note on TeX faithfulness (current bottleneck)

- The TeX SSU proof uses Step 3–5 large-sieve bounds with an `X/|ξ|` singular term and then
  handles ξ-integration using moment hypotheses (Lemma `balanced-xi`). We now have TeX-faithful
  TT* wrappers (`Step34LargeSieveTeX` + `BalancedXiClaimInv`) and Fejér-banked bridges that consume
  them, but the older uniform surrogate (`Step34LargeSieve` / `Step34ProdSum`) remains in parallel
  for legacy/toy paths.

## Known remaining hypothesis-style interfaces

- Any instance-level `inner_eq_toeplitzForm` still present as a field/hypothesis (to be proved).
- Any instance-level Type–II SSU bound (large sieve / Sawyer testing) still present as a field/hypothesis.
- 03_TFA “alias suppression” (`δ=2`) cancellation for the balanced mask (currently TODO in
  `SSU/Engines/TFAWeight.lean:1`).
