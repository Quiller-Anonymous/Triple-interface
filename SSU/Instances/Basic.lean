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

/- Canonical SSU-heart closure on the reduction-free operator-global flagship route:
torus TT* bound → core-facing Gram hypothesis → SSU ledger contract. -/
namespace HeartOperatorGlobal

/-- Canonical non-extracted operator-global flagship input surface. -/
abbrev Input (κ ι : Type*) [DecidableEq κ] :=
  Flagship.OperatorGlobal.Input (κ := κ) (ι := ι)

/-- Canonical non-extracted operator-global flagship packet Gram bound. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLe :=
  fun {κ ι} [DecidableEq κ] =>
    Flagship.OperatorGlobal.normInnerPacketOpUnnormalizedLe (κ := κ) (ι := ι)

/-- Canonical non-extracted operator-global flagship core-facing Gram hypothesis. -/
noncomputable abbrev gramHypothesis :=
  fun {κ ι} [DecidableEq κ] =>
    Flagship.OperatorGlobal.gramHypothesis (κ := κ) (ι := ι)

/-- Canonical non-extracted operator-global flagship SSU ledger contract. -/
noncomputable abbrev contract :=
  fun {κ ι} [DecidableEq κ] =>
    Flagship.OperatorGlobal.contract (κ := κ) (ι := ι)

end HeartOperatorGlobal

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
  SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.ToeplitzInputFor (κ := κ) (H0 := H0)

/-- Compatibility alias for the legacy global Toeplitz-first extracted input. -/
abbrev LegacyToeplitzInput (κ : Type*) [DecidableEq κ]
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

/-- Public constructor: non-fallback Step-3/Step-4 route on the broader non-BG-compatible
extracted class given by box support plus finite shear-level control. -/
noncomputable abbrev shearLevelSetOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.shearLevelSetOneAddLog
      (κ := κ) (H0 := H0)

/-- Public constructor: non-fallback Step-3/Step-4 route on the broad box-support extracted class.
Shear levels are extracted automatically as the finite image of `shear` on `Dtype.tube`. -/
noncomputable abbrev boxSupportOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.boxSupportOneAddLog
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
`tubeWindowOneAddLogInputFor` when tube-window geometry is available. -/
noncomputable abbrev trivialInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.trivial (κ := κ) (H0 := H0)

/-- Public fallback theorem: direct non-rank-one extracted packet bound from the trivial use-site
family. Prefer `normInnerPacketOpUnnormalizedLeTubeWindowOneAddLog` when tube-window geometry is
available. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTrivial :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.norm_inner_packetOpUnnormalized_le_trivial
      (κ := κ) (H0 := H0)

/-- Public constructor: canonical non-box extracted use-site family on the product-side route.
Assumes extracted support inside a BG tube window `tubeFinset P a q s`; cardinality/level bounds
are derived directly from tube geometry. This canonical default endpoint promotes to the
centered-unit proved Step-3/Step-4-for + `Step34ProdSumFor` chain whenever its compatibility
conditions hold. -/
noncomputable abbrev tubeWindowOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.tubeWindowOneAddLog
      (κ := κ) (H0 := H0)

/-- Public theorem: direct non-rank-one extracted packet bound from the canonical non-box
tube-window product-side use-site family (with centered-unit promotion to the explicit Step-3/4
proved chain when applicable). -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (f : H0) (i j : ℤ) => by
    let h0 :=
      SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.tubeWindowOneAddLog
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a s q hq hX hH hsmall hsubTube
    simpa [h0] using (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Public centered-unit compatibility constructor, now routed through the canonical default
endpoint `tubeWindowOneAddLogInputFor`. -/
noncomputable abbrev tubeWindowCenteredUnitOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    fun Dpacket Dtype P hX hH hsmall hsubTube =>
      tubeWindowOneAddLogInputFor (κ := κ) (H0 := H0)
        Dpacket Dtype P 0 0 1 (by decide) hX hH hsmall hsubTube

/-- Public centered-unit compatibility theorem, now routed through the canonical default
endpoint `normInnerPacketOpUnnormalizedLeTubeWindowOneAddLog`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowCenteredUnitOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    fun Dpacket Dtype P hX hH hsmall hsubTube f i j =>
      normInnerPacketOpUnnormalizedLeTubeWindowOneAddLog (κ := κ) (H0 := H0)
        Dpacket Dtype P 0 0 1 (by decide) hX hH hsmall hsubTube f i j

/-- Public constructor: canonical scale-agnostic extracted one-add-log route for centered
general slope (`s = 0`). -/
noncomputable abbrev tubeWindowGeneralSlopeOneAddLogDefaultInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0) =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.tubeWindowGeneralSlopeOneAddLogDefault
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a q hq hX hH hsmall hsubTube

/-- Public constructor (compatibility signature): centered general-slope extracted one-add-log.
This now delegates to `tubeWindowGeneralSlopeOneAddLogDefaultInputFor`; legacy parameters
`hcop`, `q ≤ D`, and explicit scale witnesses are retained only for call-site compatibility. -/
noncomputable abbrev tubeWindowGeneralSlopeOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (_hcop : Nat.Coprime a.natAbs q)
    (_hXeq : Dpacket.X = (P.X : ℝ))
    (_hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (_hD1 : 1 ≤ P.D) (_hU1 : 1 ≤ P.U)
    (_hqD : q ≤ P.D)
    (_hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0) =>
    tubeWindowGeneralSlopeOneAddLogDefaultInputFor (κ := κ) (H0 := H0)
      Dpacket Dtype P a q hq hX hH hsmall hsubTube

/-- Public constructor: canonical scale-agnostic extracted one-add-log route for shifted
general slope (`a/q`, arbitrary `s`). -/
noncomputable abbrev tubeWindowShiftedGeneralSlopeOneAddLogDefaultInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.tubeWindowShiftedGeneralSlopeOneAddLogDefault
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq hX hH hsmall hsubTube

/-- Public constructor (compatibility signature): shifted general-slope extracted one-add-log.
This now delegates to `tubeWindowShiftedGeneralSlopeOneAddLogDefaultInputFor`; legacy parameters
`hcop`, `q ≤ D`, and explicit scale witnesses are retained only for call-site compatibility. -/
noncomputable abbrev tubeWindowShiftedGeneralSlopeOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (_hcop : Nat.Coprime a.natAbs q)
    (_hXeq : Dpacket.X = (P.X : ℝ))
    (_hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (_hD1 : 1 ≤ P.D) (_hU1 : 1 ≤ P.U)
    (_hqD : q ≤ P.D)
    (_hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s) =>
    tubeWindowShiftedGeneralSlopeOneAddLogDefaultInputFor (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq hX hH hsmall hsubTube

/-- Public theorem: direct extracted packet bound from
`tubeWindowGeneralSlopeOneAddLogDefaultInputFor`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowGeneralSlopeOneAddLogDefault :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0)
    (f : H0) (i j : ℤ) => by
    let h0 := tubeWindowGeneralSlopeOneAddLogDefaultInputFor (κ := κ) (H0 := H0)
      Dpacket Dtype P a q hq hX hH hsmall hsubTube
    simpa [h0] using (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Public theorem (compatibility signature): direct extracted packet bound from
`tubeWindowGeneralSlopeOneAddLogInputFor`. Legacy parameters are retained only for call-site
compatibility and are ignored by the canonical default route. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowGeneralSlopeOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (_hcop : Nat.Coprime a.natAbs q)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hqD : q ≤ P.D)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q 0)
    (f : H0) (i j : ℤ) => by
    exact
      normInnerPacketOpUnnormalizedLeTubeWindowGeneralSlopeOneAddLogDefault
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a q hq hX hH hsmall hsubTube f i j

/-- Public theorem: direct extracted packet bound from
`tubeWindowShiftedGeneralSlopeOneAddLogDefaultInputFor`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowShiftedGeneralSlopeOneAddLogDefault :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (f : H0) (i j : ℤ) => by
    let h0 := tubeWindowShiftedGeneralSlopeOneAddLogDefaultInputFor (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq hX hH hsmall hsubTube
    simpa [h0] using (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Public theorem (compatibility signature): direct extracted packet bound from
`tubeWindowShiftedGeneralSlopeOneAddLogInputFor`. Legacy parameters are retained only for call-site
compatibility and are ignored by the canonical default route. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowShiftedGeneralSlopeOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (_hcop : Nat.Coprime a.natAbs q)
    (hXeq : Dpacket.X = (P.X : ℝ))
    (hHeq : Dpacket.H = (P.H : ℝ))
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hD1 : 1 ≤ P.D) (hU1 : 1 ≤ P.U)
    (hqD : q ≤ P.D)
    (hXH1 : 1 ≤ (P.X : ℝ) * (P.H : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (f : H0) (i j : ℤ) => by
    exact
      normInnerPacketOpUnnormalizedLeTubeWindowShiftedGeneralSlopeOneAddLogDefault
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a s q hq hX hH hsmall hsubTube f i j

/-- Canonical extracted one-add-log constructor on non-box classes (tube-window route). -/
noncomputable abbrev oneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    tubeWindowOneAddLogInputFor (κ := κ) (H0 := H0)

/-- Canonical extracted one-add-log packet bound on non-box classes (tube-window route). -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    normInnerPacketOpUnnormalizedLeTubeWindowOneAddLog (κ := κ) (H0 := H0)

/-- Public constructor: residue-union non-box extracted use-site family on the product-side
route. Assumes tube-window support and that each shear value lands in one of finitely many
congruence classes modulo `m`; cardinality control is derived with explicit modulus dependence. -/
noncomputable abbrev tubeWindowResidueSetOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.tubeWindowResidueSetOneAddLog
      (κ := κ) (H0 := H0)

/-- Public theorem: direct non-rank-one extracted packet bound from the residue-union
non-box tube-window product-side use-site family. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowResidueSetOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m : ℤ)
    (residueReps : Finset ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidueSet :
      ∀ p ∈ Dtype.tube, ∃ r ∈ residueReps,
        SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m])
    (f : H0) (i j : ℤ) => by
    let h0 :=
      SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.tubeWindowResidueSetOneAddLog
        (κ := κ) (H0 := H0)
        Dpacket Dtype P a s q hq m residueReps hX hH hsmall hsubTube hresidueSet
    simpa [h0] using (h0.norm_inner_packetOpUnnormalized_le (f := f) (i := i) (j := j))

/-- Public constructor: residue-structured non-box extracted use-site family on the product-side
route. This is a compatibility wrapper over the residue-union endpoint with singleton
`residueReps = {r}`. -/
noncomputable abbrev tubeWindowResidueOneAddLogInputFor :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m r : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidue :
      ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m]) =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.InputFor.tubeWindowResidueOneAddLogDefault
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq m r hX hH hsmall hsubTube hresidue

/-- Public theorem: direct non-rank-one extracted packet bound from the residue-structured
non-box tube-window product-side use-site family. This is a compatibility wrapper over the
residue-union theorem with singleton `residueReps = {r}`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeTubeWindowResidueOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0]
    (Dpacket : SSU.Instances.FejerBankedPartition.Data κ)
    (Dtype : SSU.Engines.BGTypeIIArray.Data H0)
    (P : SSU.Engines.BGTube.Params)
    (a s : ℤ) (q : ℕ)
    (hq : 1 ≤ q)
    (m r : ℤ)
    (hX : 0 < Dpacket.X) (hH : 0 < Dpacket.H)
    (hsmall : (1 / Dpacket.H) / Dpacket.X < (1 / 2 : ℝ))
    (hsubTube : Dtype.tube ⊆ SSU.Engines.BGTube.tubeFinset P a q s)
    (hresidue :
      ∀ p ∈ Dtype.tube, SSU.Engines.BGTube.shear a q s p ≡ r [ZMOD m])
    (f : H0) (i j : ℤ) =>
    normInnerPacketOpUnnormalizedLeTubeWindowResidueSetOneAddLog
      (κ := κ) (H0 := H0)
      Dpacket Dtype P a s q hq m ({r} : Finset ℤ) hX hH hsmall hsubTube
      (by
        intro p hp
        exact ⟨r, by simp, hresidue p hp⟩)
      f i j

/-- Public constructor: the first nontrivial extracted use-site family on the flagship path.

The name is kept for compatibility, but this now routes through the product-side
`tubeWindowInputOfProdFiberCardBound` geometry (`P.box` as the canonical tube window), so this
entrypoint is no longer tied to the skew-side TeX one-add-log wrapper. Prefer
`tubeWindowOneAddLogInputFor` / `tubeWindowResidueOneAddLogInputFor` on non-box extracted
classes. -/
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

/-- Public constructor (preferred when available): non-box extracted one-add-log TeX Step 3–4
family routed through the sharpened by-residue MV constructors, using common-domain residue
witnesses uniform in `F`. -/
noncomputable abbrev tubeFormInputForOfSumFiberRefOnZSetOneAddLogUniformMV :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TubeFormInputFor.of_sumFiber_ref_on_zSet_oneAddLog_uniformMV
      (κ := κ) (H0 := H0)

/-- Public constructor: non-fallback Step-3/Step-4 (and resulting Step-34) on the genuine
non-centered/non-box extracted BG rank-one/modEq family, via the proved geometry-first TeX route.
This avoids product-fiber fallback packaging on this extracted family. -/
noncomputable abbrev tubeFormInputForOfBGTubeRankOneModEqOneAddLog :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    SSU.Instances.FejerBankedTypeIIToeplitzBridge.Extracted.TubeFormInputFor.of_bgTubeRankOne_modEq_oneAddLog_ofBGGeometry
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
    ttStarInput_flagship_default_ofIndexWitness_extracted (κ := κ) (H0 := H0)

/-- Canonical default-route (`.nonFallback`) Toeplitz-first extracted higher-layer input family. -/
noncomputable abbrev toeplitzInput :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    toeplitzInput_flagship_select_ofIndexWitness_extracted
      (κ := κ) (H0 := H0) .nonFallback

/-- Canonical default-route (`.nonFallback`) TT*-native extracted higher-layer packet Gram bound. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLe :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    norm_inner_packetOpUnnormalized_le_flagship_default_ofIndexWitness_extracted
      (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 3 proved, Step 4 fallback) for the TT*-native extracted
higher-layer packet Gram bound. Currently equal to `normInnerPacketOpUnnormalizedLe`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeStep3FallbackStep4 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    normInnerPacketOpUnnormalizedLe (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 4 proved, Step 3 fallback) for the TT*-native extracted
higher-layer packet Gram bound. Currently equal to `normInnerPacketOpUnnormalizedLe`. -/
noncomputable abbrev normInnerPacketOpUnnormalizedLeStep4FallbackStep3 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    normInnerPacketOpUnnormalizedLe (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 3 proved, Step 4 fallback) for the TT*-native extracted
higher-layer input family. Currently equal to `input`. -/
noncomputable abbrev inputStep3FallbackStep4 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    input (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 3 proved, Step 4 fallback) for the Toeplitz-first extracted
higher-layer input family. Currently equal to `toeplitzInput`. -/
noncomputable abbrev toeplitzInputStep3FallbackStep4 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    toeplitzInput (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 4 proved, Step 3 fallback) for the TT*-native extracted
higher-layer input family. Currently equal to `input`. -/
noncomputable abbrev inputStep4FallbackStep3 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    input (κ := κ) (H0 := H0)

/-- Fallback selector alias (Step 4 proved, Step 3 fallback) for the Toeplitz-first extracted
higher-layer input family. Currently equal to `toeplitzInput`. -/
noncomputable abbrev toeplitzInputStep4FallbackStep3 :=
  fun {κ} [DecidableEq κ] {H0} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] =>
    toeplitzInput (κ := κ) (H0 := H0)

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

/-- Route selector: proof-driven reduction-data auto-Step-2 flagship endpoint family. -/
noncomputable abbrev hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionData
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_select_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι) route

/-- Route selector: proof-driven reduction-data auto-Step-2 flagship endpoint family. -/
noncomputable abbrev gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionData
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_select_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι) route

/-- Route selector: proof-driven reduction-data auto-Step-2 flagship endpoint family. -/
noncomputable abbrev contract_select_ofIndexWitness_autoTubeForm_fromReductionData
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_select_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι) route

/-- Canonical alias for the proof-driven reduction-data auto-Step-2 route selector.
Legacy reduction-witness route remains available via the `...fromReductionLegacy` names. -/
noncomputable abbrev hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReduction
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionData route
      (κ := κ) (ι := ι)

/-- Canonical alias for the proof-driven reduction-data auto-Step-2 route selector.
Legacy reduction-witness route remains available via the `...fromReductionLegacy` names. -/
noncomputable abbrev gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReduction
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionData route
      (κ := κ) (ι := ι)

/-- Canonical alias for the proof-driven reduction-data auto-Step-2 route selector.
Legacy reduction-witness route remains available via the `...fromReductionLegacy` names. -/
noncomputable abbrev contract_select_ofIndexWitness_autoTubeForm_fromReduction
    (route : Route) :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm_fromReductionData route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_default_ofIndexWitness_from_hF
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_default_ofIndexWitness_from_hF
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_from_hF :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_default_ofIndexWitness_from_hF
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_default_ofIndexWitness
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_default_ofIndexWitness
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_default_ofIndexWitness
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_default_ofIndexWitness_autoTubeForm
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_default_ofIndexWitness_autoTubeForm
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_autoTubeForm :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_default_ofIndexWitness_autoTubeForm
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_default_ofIndexWitness_autoTubeForm_fromReduction
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_default_ofIndexWitness_autoTubeForm_fromReduction
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_autoTubeForm_fromReductionLegacy :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_default_ofIndexWitness_autoTubeForm_fromReduction
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_flagship_default_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_flagship_default_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    contract_flagship_default_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

/- Canonical flagship SSU-heart closure on the proof-driven auto-Step-2 + reduction-data route:
uniform Step-5 packaging → core-facing Gram hypothesis → SSU ledger contract. -/
namespace Heart

/-- Canonical flagship uniform Step-5 package on the proof-driven reduction-data route. -/
noncomputable abbrev hypothesisStep34ForUniform :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

/-- Canonical flagship core-facing Gram hypothesis on the proof-driven reduction-data route. -/
noncomputable abbrev gramHypothesis :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

/-- Canonical flagship SSU ledger contract on the proof-driven reduction-data route. -/
noncomputable abbrev contract :=
  fun {κ ι} [DecidableEq κ] =>
    contract_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

end Heart

noncomputable abbrev hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev contract_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    contract_ofIndexWitness_autoTubeForm_fromReductionData
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

noncomputable abbrev hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionData step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionData step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm_fromReductionData step3FallbackStep4Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    contract_step3FallbackStep4_ofIndexWitness_autoTubeForm_fromReductionData
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

noncomputable abbrev hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_select_ofIndexWitness_autoTubeForm_fromReductionData step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_select_ofIndexWitness_autoTubeForm_fromReductionData step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionData :=
  fun {κ ι} [DecidableEq κ] =>
    contract_select_ofIndexWitness_autoTubeForm_fromReductionData step4FallbackStep3Route
      (κ := κ) (ι := ι)

noncomputable abbrev hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    hypothesisStep34ForUniform_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev gramHypothesis_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    gramHypothesis_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionData
      (κ := κ) (ι := ι)

noncomputable abbrev contract_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReduction :=
  fun {κ ι} [DecidableEq κ] =>
    contract_step4FallbackStep3_ofIndexWitness_autoTubeForm_fromReductionData
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
