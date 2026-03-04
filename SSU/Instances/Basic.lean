import SSU.Basic
import SSU.Instances.FejerBankedTypeIIBridgeTeXBGRankOne
import SSU.Instances.FejerBankedTypeIIToeplitzBridge

namespace SSU
namespace Instances

namespace Flagship

open SSU.Instances.FejerBankedTypeIIBridgeTeX.BGRankOne

namespace FixedSignalRankOne

/-- Public alias for the fixed-signal flagship input record using the proved rank-one Toeplitz route. -/
abbrev Input (κ : Type*) [DecidableEq κ] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.RankOne.FixedSignalInput (κ := κ)

end FixedSignalRankOne

/-- Public alias for the reduction-free operator-global Toeplitz-first bridge surface.

This is the non-extracted companion to the extracted TT*-native route: it replaces the old
operator-global `ReductionToTubeFormProd` seam by a Toeplitz TT* identity plus a separate
energy comparison. -/
abbrev ToeplitzOperatorInput (κ ι : Type*) [DecidableEq κ] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.ToeplitzOperatorInput (κ := κ) (ι := ι)

/-- Public wrapper: torus-side packet Gram bound from the reduction-free operator-global
Toeplitz-first bridge surface. -/
noncomputable abbrev toeplitzOperatorNormInnerPacketOpUnnormalizedLe :=
  fun {κ ι} [DecidableEq κ] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.ToeplitzOperatorInput.norm_inner_packetOpUnnormalized_le
      (κ := κ) (ι := ι)

/-- Public wrapper: core-facing Gram hypothesis from the reduction-free operator-global
Toeplitz-first bridge surface. -/
noncomputable abbrev toeplitzOperatorGramHypothesis :=
  fun {κ ι} [DecidableEq κ] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.ToeplitzOperatorInput.gramHypothesis
      (κ := κ) (ι := ι)

/-- Public wrapper: SSU contract from the reduction-free operator-global
Toeplitz-first bridge surface. -/
noncomputable abbrev toeplitzOperatorContract :=
  fun {κ ι} [DecidableEq κ] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.ToeplitzOperatorInput.contract
      (κ := κ) (ι := ι)

namespace OperatorGlobal

/-- Canonical non-extracted operator-global flagship input surface. -/
abbrev Input (κ ι : Type*) [DecidableEq κ] :=
  ToeplitzOperatorInput (κ := κ) (ι := ι)

/-- Canonical non-extracted operator-global flagship torus-side packet Gram bound. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLe :=
  fun {κ ι} [DecidableEq κ] =>
    toeplitzOperatorNormInnerPacketOpUnnormalizedLe (κ := κ) (ι := ι)

/-- Canonical non-extracted operator-global flagship core-facing Gram hypothesis. -/
noncomputable abbrev gramHypothesis :=
  fun {κ ι} [DecidableEq κ] =>
    toeplitzOperatorGramHypothesis (κ := κ) (ι := ι)

/-- Canonical non-extracted operator-global flagship core-facing contract. -/
noncomputable abbrev contract :=
  fun {κ ι} [DecidableEq κ] =>
    toeplitzOperatorContract (κ := κ) (ι := ι)

end OperatorGlobal

namespace Extracted

/-- Primary public alias for the TT*-native pair-dependent extracted-signal flagship record. -/
abbrev Input (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TTStarInput (κ := κ) (H0 := H0)

/-- Compatibility alias for the canonical constructor record that builds `Input`. -/
abbrev LegacyInput (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.Input (κ := κ) (H0 := H0)

/-- Public alias for the TT*-native pair-dependent extracted-signal flagship record. -/
abbrev TTStarInput (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TTStarInput (κ := κ) (H0 := H0)

/-- Public alias for the TT*-native use-site extracted-signal flagship record. -/
abbrev TTStarInputFor (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TTStarInputFor (κ := κ) (H0 := H0)

/-- Public alias for the canonical Step-2 Toeplitz-form extraction package on the frozen
Fejér-banked packet family. -/
abbrev ToeplitzPairHypothesis (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzTTStarToeplitzHypothesis.PairHypothesis
    (κ := κ) H0

/-- Public alias for the Toeplitz-first extracted higher-bridge input (Step 2 packaged as a
canonical Toeplitz-form object, then Step 3–4 added). -/
abbrev ToeplitzInput (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.ToeplitzInput (κ := κ) (H0 := H0)

/-- Public alias for the Toeplitz-first extracted higher-bridge input with a genuine use-site
Step 3–4 family. -/
abbrev ToeplitzInputFor (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.ToeplitzInputFor (κ := κ) (H0 := H0)

/-- Compatibility alias for the frozen-packet extracted use-site input record. -/
abbrev InputFor (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor (κ := κ) (H0 := H0)

/-- Public alias for the extracted physical-side TeX base surface. This is the honest non-box
extracted bridge when the available Step 3–4 theorem is stated in the skew/type-II form rather
than as a product-side `Step34ProdSumFor`. -/
abbrev TubeFormBase (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TubeFormBase (κ := κ) (H0 := H0)

/-- Public alias for the extracted physical-side TeX use-site input record. -/
abbrev TubeFormInputFor (κ : Type*) [DecidableEq κ]
    (H0 : Type*) [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] :=
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TubeFormInputFor
    (κ := κ) (H0 := H0)

/-- Public constructor: lift a global extracted Step 3–4 package to the use-site extracted
family. -/
noncomputable abbrev inputForOfInput :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.ofInput (κ := κ) (H0 := H0)

/-- Public constructor: global extracted Step 3–4 package from a product-fiber multiplicity bound
on the extracted tube. This is the current broadest deterministic non-box product-side route. -/
noncomputable abbrev inputOfProdFiberCardBound :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.ofProdFiberCardBound
      (κ := κ) (H0 := H0)

/-- Public constructor: global extracted Step 3–4 package on the full dyadic box using the proved
product-fiber cardinality bound `|{(d,n) ∈ box : dn = k}| ≤ min(|dRange|, |nRange|)`. This is the
first concrete extracted class for the product-fiber global route. -/
noncomputable abbrev boxInputOfProdFiberCardBound :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.ofBoxProdFiberCardBound
      (κ := κ) (H0 := H0)

/-- Public constructor: global extracted Step 3–4 package for a single exact BG shear level on a
dyadic box. This uses the arithmetic product-fiber bound `≤ 2` on each fiber `dn = k`. -/
noncomputable abbrev constShearInputOfProdFiberCardBound :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.ofConstShearProdFiberCardBound
      (κ := κ) (H0 := H0)

/-- Public constructor: global extracted Step 3–4 package for a bounded union of BG shear levels
inside a dyadic box. This yields the arithmetic product-fiber bound `≤ 2 * levels.card`.
Prefer `tubeWindowInputOfProdFiberCardBound` when the support hypothesis is already
`Dtype.tube ⊆ BGTube.tubeFinset P a q s`. -/
noncomputable abbrev shearLevelSetInputOfProdFiberCardBound :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.ofShearLevelSetProdFiberCardBound
      (κ := κ) (H0 := H0)

/-- Public constructor: global extracted Step 3–4 package for the canonical BG tube window.
If the extracted support lies inside `tubeFinset P a q s`, the shear-level set is derived
automatically as the interval `[-U,U]`, eliminating an explicit `levels` parameter. -/
noncomputable abbrev tubeWindowInputOfProdFiberCardBound :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.ofTubeWindowProdFiberCardBound
      (κ := κ) (H0 := H0)

/-- Public theorem: direct extracted packet bound from any global extracted Step 3–4 package.

This is the broadest currently available nontrivial extracted endpoint: prefer it whenever a
global extracted `Input` is available. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeOfInput :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.norm_inner_packetOpUnnormalized_le_ofInput
      (κ := κ) (H0 := H0)

/-- Public fallback constructor: the first honest non-rank-one extracted use-site family, given
by the deterministic trivial Step 3–4 bound on the extracted coefficient arrays. Prefer
`boxGeometryOneAddLogInputFor` when the box hypotheses are available. -/
noncomputable abbrev trivialInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.trivial (κ := κ) (H0 := H0)

/-- Public fallback theorem: direct non-rank-one extracted packet bound from the trivial use-site
family. Prefer `normInnerPacketOpUnnormalizedLeBoxGeometryOneAddLog` when the box hypotheses are
available. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTrivial :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.norm_inner_packetOpUnnormalized_le_trivial
      (κ := κ) (H0 := H0)

/-- Public constructor: the first nontrivial extracted use-site family on the flagship path.

The name is kept for compatibility, but this now routes through the product-side
`tubeWindowInputOfProdFiberCardBound` geometry (`P.box` as the canonical tube window), so this
entrypoint is no longer tied to the skew-side TeX one-add-log wrapper. -/
noncomputable abbrev boxGeometryOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.boxGeometryOneAddLog
      (κ := κ) (H0 := H0)

/-- Public theorem: direct non-rank-one extracted packet bound from the first nontrivial
box-geometry use-site family (compatibility name preserved as `...OneAddLog`). This is the
preferred extracted endpoint whenever the full-box tube-window hypotheses are available. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeBoxGeometryOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.norm_inner_packetOpUnnormalized_le_boxGeometryOneAddLog
      (κ := κ) (H0 := H0)

/-- Public constructor: build a non-box extracted one-add-log TeX Step 3–4 family from
common-domain residue witnesses on the skew/type-II side. Use this when the available theorem is a
`Step34LargeSieveTeXFor` family and the product-side `Step34ProdSum` interface is too strong. -/
noncomputable abbrev tubeFormInputForOfSumFiberRefOnZSetOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TubeFormInputFor.of_sumFiber_ref_on_zSet_oneAddLog
      (κ := κ) (H0 := H0)

/-- Public theorem: direct non-box extracted packet bound on the physical-side TeX route. This is
the honest endpoint for extracted one-add-log families that do not admit a product-side
`Step34ProdSumFor` package. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeForm :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TubeFormInputFor.norm_inner_packetOpUnnormalized_le
      (κ := κ) (H0 := H0)

end Extracted

/-- Canonical route selector for flagship index-witness APIs. -/
abbrev Route := FlagshipIndexRoute

/-- Canonical default route (`.nonFallback`) for selector-first flagship APIs. -/
abbrev defaultRoute : Route := flagshipSelectorDefaultRoute

/-- Canonical fallback route: proved Step 3 + fallback Step 4. -/
abbrev step3FallbackStep4Route : Route := .step3FallbackStep4

/-- Canonical fallback route: proved Step 4 + fallback Step 3. -/
abbrev step4FallbackStep3Route : Route := .step4FallbackStep3

namespace Extracted

/-- Route selector for the Toeplitz-first extracted higher-layer flagship input family. -/
noncomputable abbrev toeplitzInputSelect (route : Route) :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    toeplitzInput_flagship_select_ofIndexWitness_extracted
      (κ := κ) (H0 := H0) route

/-- Route selector for the TT*-native extracted higher-layer flagship input family. -/
noncomputable abbrev inputSelect (route : Route) :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    ttStarInput_flagship_select_ofIndexWitness_extracted
      (κ := κ) (H0 := H0) route

/-- Route selector for the TT*-native extracted higher-layer packet Gram bound. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeSelect (route : Route) :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    norm_inner_packetOpUnnormalized_le_flagship_select_ofIndexWitness_extracted
      (κ := κ) (H0 := H0) route

/-- Canonical default-route (`.nonFallback`) TT*-native extracted higher-layer input family. -/
noncomputable abbrev input :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    inputSelect defaultRoute (κ := κ) (H0 := H0)

/-- Canonical default-route (`.nonFallback`) Toeplitz-first extracted higher-layer input family. -/
noncomputable abbrev toeplitzInput :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    toeplitzInputSelect defaultRoute (κ := κ) (H0 := H0)

/-- Canonical default-route (`.nonFallback`) TT*-native extracted higher-layer packet Gram bound. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLe :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    normInnerPacketOpUnnormalizedLeSelect defaultRoute (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 3 proved, Step 4 fallback) for the TT*-native extracted
higher-layer packet Gram bound. Currently equal to `normInnerPacketOpUnnormalizedLe`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeStep3FallbackStep4 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    normInnerPacketOpUnnormalizedLeSelect step3FallbackStep4Route (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 4 proved, Step 3 fallback) for the TT*-native extracted
higher-layer packet Gram bound. Currently equal to `normInnerPacketOpUnnormalizedLe`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeStep4FallbackStep3 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    normInnerPacketOpUnnormalizedLeSelect step4FallbackStep3Route (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 3 proved, Step 4 fallback) for the TT*-native extracted
higher-layer input family. Currently equal to `input`. -/
noncomputable abbrev inputStep3FallbackStep4 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    inputSelect step3FallbackStep4Route (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 3 proved, Step 4 fallback) for the Toeplitz-first extracted
higher-layer input family. Currently equal to `toeplitzInput`. -/
noncomputable abbrev toeplitzInputStep3FallbackStep4 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    toeplitzInputSelect step3FallbackStep4Route (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 4 proved, Step 3 fallback) for the TT*-native extracted
higher-layer input family. Currently equal to `input`. -/
noncomputable abbrev inputStep4FallbackStep3 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    inputSelect step4FallbackStep3Route (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 4 proved, Step 3 fallback) for the Toeplitz-first extracted
higher-layer input family. Currently equal to `toeplitzInput`. -/
noncomputable abbrev toeplitzInputStep4FallbackStep3 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    toeplitzInputSelect step4FallbackStep3Route (κ := κ) (H0 := H0)

end Extracted

/-- Route selector: `from_hF` flagship endpoint family. -/
noncomputable abbrev hypothesisStep34ForUniform_select_ofIndexWitness_from_hF
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_select_ofIndexWitness_from_hF
      (κ := κ) (ι := ι) route

/-- Route selector: `from_hF` flagship endpoint family. -/
noncomputable abbrev gramHypothesis_select_ofIndexWitness_from_hF
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_select_ofIndexWitness_from_hF
      (κ := κ) (ι := ι) route

/-- Route selector: `from_hF` flagship endpoint family. -/
noncomputable abbrev contract_select_ofIndexWitness_from_hF
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_select_ofIndexWitness_from_hF
      (κ := κ) (ι := ι) route

/-- Route selector: extracted-constancy flagship endpoint family. -/
noncomputable abbrev hypothesisStep34ForUniform_select_ofIndexWitness
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_select_ofIndexWitness
      (κ := κ) (ι := ι) route

/-- Route selector: extracted-constancy flagship endpoint family. -/
noncomputable abbrev gramHypothesis_select_ofIndexWitness
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_select_ofIndexWitness
      (κ := κ) (ι := ι) route

/-- Route selector: extracted-constancy flagship endpoint family. -/
noncomputable abbrev contract_select_ofIndexWitness
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_select_ofIndexWitness
      (κ := κ) (ι := ι) route

/-- Route selector: auto-Step-2 flagship endpoint family. -/
noncomputable abbrev hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_select_ofIndexWitness_autoTubeForm
      (κ := κ) (ι := ι) route

/-- Route selector: auto-Step-2 flagship endpoint family. -/
noncomputable abbrev gramHypothesis_select_ofIndexWitness_autoTubeForm
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_select_ofIndexWitness_autoTubeForm
      (κ := κ) (ι := ι) route

/-- Route selector: auto-Step-2 flagship endpoint family. -/
noncomputable abbrev contract_select_ofIndexWitness_autoTubeForm
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_select_ofIndexWitness_autoTubeForm
      (κ := κ) (ι := ι) route

/-- Compatibility route selector: legacy reduction-based auto-Step-2 flagship endpoint family. -/
noncomputable abbrev hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionLegacy
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_select_ofIndexWitness_autoTubeForm_fromReduction
      (κ := κ) (ι := ι) route

/-- Compatibility route selector: legacy reduction-based auto-Step-2 flagship endpoint family. -/
noncomputable abbrev gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionLegacy
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_select_ofIndexWitness_autoTubeForm_fromReduction
      (κ := κ) (ι := ι) route

/-- Compatibility route selector: legacy reduction-based auto-Step-2 flagship endpoint family. -/
noncomputable abbrev contract_select_ofIndexWitness_autoTubeForm_fromReductionLegacy
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_select_ofIndexWitness_autoTubeForm_fromReduction
      (κ := κ) (ι := ι) route

/-- Compatibility alias for the legacy reduction-based auto-Step-2 route selector. -/
noncomputable abbrev hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReduction
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionLegacy route
      (κ := κ) (ι := ι)

/-- Compatibility alias for the legacy reduction-based auto-Step-2 route selector. -/
noncomputable abbrev gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReduction
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionLegacy route
      (κ := κ) (ι := ι)

/-- Compatibility alias for the legacy reduction-based auto-Step-2 route selector. -/
noncomputable abbrev contract_select_ofIndexWitness_autoTubeForm_fromReduction
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm_fromReductionLegacy route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_from_hF defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_from_hF defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_from_hF defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionLegacy defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionLegacy defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm_fromReductionLegacy defaultRoute
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    contract_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_from_hF step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step3FallbackStep4_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_from_hF step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step3FallbackStep4_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_from_hF step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step3FallbackStep4_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step3FallbackStep4_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step3FallbackStep4_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step3FallbackStep4_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionLegacy step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionLegacy step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm_fromReductionLegacy step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    contract_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_from_hF step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step4FallbackStep3_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_from_hF step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step4FallbackStep3_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_from_hF step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step4FallbackStep3_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step4FallbackStep3_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step4FallbackStep3_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step4FallbackStep3_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionLegacy step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionLegacy step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm_fromReductionLegacy step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    contract_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionLegacy
      (κ := κ) (ι := ι)

end Flagship

/-!
Concrete SSU instances.

This folder is intended to combine packet definitions (zones, projectors, kernels) with one or more
engine lemmas to produce a ready-to-use SSU bound in the library’s public API.

`SSU.Instances.Basic` re-exports the canonical flagship endpoint families from
`FejerBankedTypeIIBridgeTeXBGRankOne`, including non-fallback and fallback
index-witness wrappers, plus the reduction-based auto-Step-2 variants.

It also re-exports the fixed-signal rank-one Toeplitz bridge route from
`FejerBankedTypeIIToeplitzBridge`, which is the current highest fully proved
higher-layer flagship path with production Step-2 extraction and non-fallback Step 3–4.
-/

end SSU.Instances
