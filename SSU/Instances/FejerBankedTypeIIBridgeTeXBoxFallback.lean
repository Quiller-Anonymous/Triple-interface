import SSU.Instances.FejerBankedTypeIIBridgeTeX

/-!
Convenience wrapper: build the TeX-facing Type-II SSU contract using the geometry-only Step 3/4
fallbacks (Cauchy–Schwarz + progression cardinality).

This does **not** prove the Montgomery–Vaughan large sieve. It just reduces boilerplate when one
wants to run the end-to-end pipeline assuming only the remaining application-facing fields:

* `tubeForm_eq` (TT*/reindexing identity: tube quadratic form = `Khat`-weighted ξ-integral);
* `reduction` (packet Gram entries → tube quadratic form + energy comparison).
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIBridgeTeX

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

namespace BoxFallback

variable {κ ι : Type*} [DecidableEq κ]

/--
Build the most-wired TeX bridge hypothesis (`HypothesisMVKhat`) using only box-geometry fallbacks
for Step 3 and Step 4 (no MV large sieve yet).
-/
noncomputable def hypothesisMVKhat
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    HypothesisMVKhat κ ι :=
  HypothesisMVKhat.mk_of_box_geometry
    (κ := κ) (ι := ι)
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq := tubeForm_eq) (reduction := reduction)

/-- `hypothesisMVKhat`, but deriving `tubeForm_eq` from a packaged `Step2ToTubeForm` witness. -/
noncomputable def hypothesisMVKhat_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    HypothesisMVKhat κ ι :=
  hypothesisMVKhat
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.tubeForm_eq_of_step2ToTubeForm
        (td := td) h2 hKhat)
    (reduction := reduction)

/-- `hypothesisMVKhat_autoStep2` with reduction assembled from explicit fields. -/
noncomputable def hypothesisMVKhat_autoStep2_ofReductionData
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (F : SSU.Global.Signal → ℤ → ℤ → TubePoint → ℂ)
    (inner_eq :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K td) td.T (F f i j))
    (energy_le :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy td.T (F f i j) ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    HypothesisMVKhat κ ι :=
  hypothesisMVKhat_autoStep2
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (h2 := h2) (hKhat := hKhat)
    (reduction :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.reduction_of_data
        (FB := FB) (td := td)
        (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
        (F := F) (inner_eq := inner_eq) (energy_le := energy_le))

/-- The same fallback packaged in the global-Step-5 `HypothesisKhat` format. -/
noncomputable def hypothesisKhat
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    HypothesisKhat κ ι :=
  { FB := FB
    td := td
    hX := hX
    hH1 := hH1
    hU := hU
    hD := hD
    step34 := (hypothesisMVKhat
      (FB := FB) (td := td)
      (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
      (hDq := hDq) (hXH1 := hXH1)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)).step34
    tubeForm_eq := tubeForm_eq
    reduction := reduction }

/-- `hypothesisKhat`, but deriving `tubeForm_eq` from a packaged `Step2ToTubeForm` witness. -/
noncomputable def hypothesisKhat_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    HypothesisKhat κ ι :=
  hypothesisKhat
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.tubeForm_eq_of_step2ToTubeForm
        (td := td) h2 hKhat)
    (reduction := reduction)

/-- The fallback packaged directly as the legacy global-Step-5 `Hypothesis` bundle. -/
noncomputable def hypothesis
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    Hypothesis κ ι :=
  (hypothesisKhat
      (FB := FB) (td := td)
      (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
      (hDq := hDq) (hXH1 := hXH1)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)).toHypothesis

/-- `hypothesis`, but deriving `tubeForm_eq` from a packaged `Step2ToTubeForm` witness. -/
noncomputable def hypothesis_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    Hypothesis κ ι :=
  hypothesis
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.tubeForm_eq_of_step2ToTubeForm
        (td := td) h2 hKhat)
    (reduction := reduction)

/-- The fallback packaged as the uniform use-site Step-5 bridge bundle. -/
noncomputable def hypothesisStep34ForUniform
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    HypothesisStep34ForUniform κ ι :=
  (hypothesisMVKhat
      (FB := FB) (td := td)
      (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
      (hDq := hDq) (hXH1 := hXH1)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)).toHypothesisStep34ForUniform

/-- `hypothesisStep34ForUniform`, but deriving `tubeForm_eq` from `Step2ToTubeForm`. -/
noncomputable def hypothesisStep34ForUniform_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    HypothesisStep34ForUniform κ ι :=
  hypothesisStep34ForUniform
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.tubeForm_eq_of_step2ToTubeForm
        (td := td) h2 hKhat)
    (reduction := reduction)

/-- The resulting Gram hypothesis through the uniform use-site Step-5 route. -/
noncomputable def gramHypothesis_uniform
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) :=
  SSU.Instances.FejerBankedTypeIIBridgeTeX.gramHypothesis_of_box_geometry
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq := tubeForm_eq) (reduction := reduction)

/-- `gramHypothesis_uniform`, but deriving `tubeForm_eq` from `Step2ToTubeForm`. -/
noncomputable def gramHypothesis_uniform_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) :=
  SSU.Instances.FejerBankedTypeIIBridgeTeX.gramHypothesis_of_box_geometry_autoStep2
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (h2 := h2) (hKhat := hKhat) (reduction := reduction)

/-- `gramHypothesis_uniform_autoStep2` with reduction assembled from explicit fields. -/
noncomputable def gramHypothesis_uniform_autoStep2_ofReductionData
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (F : SSU.Global.Signal → ℤ → ℤ → TubePoint → ℂ)
    (inner_eq :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K td) td.T (F f i j))
    (energy_le :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy td.T (F f i j) ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) :=
  SSU.Instances.FejerBankedTypeIIBridgeTeX.gramHypothesis_of_box_geometry_autoStep2_ofReductionData
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (h2 := h2) (hKhat := hKhat)
    (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
    (F := F) (inner_eq := inner_eq) (energy_le := energy_le)

/-- The resulting SSU contract for the Fejér-banked packet family (still assuming `tubeForm_eq` and
`reduction`). -/
noncomputable def contract
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  (hypothesisMVKhat
      (FB := FB) (td := td)
      (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
      (hDq := hDq) (hXH1 := hXH1)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)).contract

/-- `contract`, but deriving `tubeForm_eq` from a packaged `Step2ToTubeForm` witness. -/
noncomputable def contract_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  contract
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.tubeForm_eq_of_step2ToTubeForm
        (td := td) h2 hKhat)
    (reduction := reduction)

/-- Gram hypothesis through the legacy global-Step-5 `Hypothesis` route. -/
noncomputable def gramHypothesis
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) :=
  (hypothesis
      (FB := FB) (td := td)
      (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
      (hDq := hDq) (hXH1 := hXH1)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)).gramHypothesis

/-- `gramHypothesis`, but deriving `tubeForm_eq` from `Step2ToTubeForm`. -/
noncomputable def gramHypothesis_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (FB.data).J
      ((FB.data).corePacketFamily.T) :=
  gramHypothesis
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.tubeForm_eq_of_step2ToTubeForm
        (td := td) h2 hKhat)
    (reduction := reduction)

/-- SSU contract through the legacy global-Step-5 `Hypothesis` route. -/
noncomputable def contract_legacy
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  (hypothesis
      (FB := FB) (td := td)
      (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
      (hDq := hDq) (hXH1 := hXH1)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction)).contract

/-- `contract_legacy`, but deriving `tubeForm_eq` from `Step2ToTubeForm`. -/
noncomputable def contract_legacy_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  contract_legacy
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq :=
      SSU.Instances.FejerBankedTypeIIBridgeTeX.tubeForm_eq_of_step2ToTubeForm
        (td := td) h2 hKhat)
    (reduction := reduction)

/-- Same as `contract`, but through the uniform use-site Step-5 bridge route. -/
noncomputable def contract_uniform
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (tubeForm_eq :
      ∀ F : TubePoint → ℂ,
        tubeForm (K td) td.T F =
          ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
                (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ))
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  SSU.Instances.FejerBankedTypeIIBridgeTeX.contract_of_box_geometry
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (tubeForm_eq := tubeForm_eq) (reduction := reduction)

/-- `contract_uniform`, but deriving `tubeForm_eq` from `Step2ToTubeForm`. -/
noncomputable def contract_uniform_autoStep2
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (reduction :
      ReductionToTubeForm
        (H := SSU.Global.Signal)
        (J := (FB.data).J)
        (T := ((FB.data).corePacketFamily.T))
        td
        (K td)) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  SSU.Instances.FejerBankedTypeIIBridgeTeX.contract_of_box_geometry_autoStep2
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (h2 := h2) (hKhat := hKhat) (reduction := reduction)

/-- `contract_uniform_autoStep2` with reduction assembled from explicit fields. -/
noncomputable def contract_uniform_autoStep2_ofReductionData
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH1 : 1 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (hDq : 1 ≤ td.D / (td.q : ℝ))
    (hXH1 : 1 ≤ td.X * td.H)
    (h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td))
    (hKhat : h2.Khat = Khat td)
    (Cenergy : ℝ) (Cenergy_nonneg : 0 ≤ Cenergy)
    (F : SSU.Global.Signal → ℤ → ℤ → TubePoint → ℂ)
    (inner_eq :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        inner ℂ (((FB.data).corePacketFamily.T i) f) (((FB.data).corePacketFamily.T j) f) =
          tubeForm (K td) td.T (F f i j))
    (energy_le :
      ∀ f : SSU.Global.Signal, ∀ i ∈ (FB.data).J, ∀ j ∈ (FB.data).J,
        tubeEnergy td.T (F f i j) ≤
          Cenergy * ‖((FB.data).corePacketFamily.T i) f‖ * ‖((FB.data).corePacketFamily.T j) f‖) :
    SSU.Global.SSUContract (FB.data).corePacketFamily :=
  SSU.Instances.FejerBankedTypeIIBridgeTeX.contract_of_box_geometry_autoStep2_ofReductionData
    (FB := FB) (td := td)
    (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
    (hDq := hDq) (hXH1 := hXH1)
    (h2 := h2) (hKhat := hKhat)
    (Cenergy := Cenergy) (Cenergy_nonneg := Cenergy_nonneg)
    (F := F) (inner_eq := inner_eq) (energy_le := energy_le)

end BoxFallback

end

end FejerBankedTypeIIBridgeTeX
end Instances
end SSU
