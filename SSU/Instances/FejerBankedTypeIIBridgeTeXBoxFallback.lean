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

end BoxFallback

end

end FejerBankedTypeIIBridgeTeX
end Instances
end SSU
