import SSU.Instances.FejerBankedTeX
import SSU.Engines.TypeII

/-!
Bridge: Type-II tube inequality → Fejér-banked SSU contract.

This file does *not* prove the Type-II heart. Instead it wires together the existing interfaces:

* a Fejér-banked packet family (`FejerBankedTeX.Hypothesis`),
* a Type-II tube package (`TubeData`, `Step34LargeSieve`, and a TT*/reindexing identity),
* a reduction of packet Grams to the Type-II tube quadratic form (`ReductionToTubeForm`).

From these hypotheses, we produce an `SSU.Interzone.GramHypothesis` for the Fejér-banked packet
operators, and hence an `SSU.Global.SSUContract`.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIBridge

open scoped BigOperators

noncomputable section

open SSU.Engines.TypeII

abbrev K (td : TubeData) : ℤ → ℝ :=
  SSU.Engines.TypeII.AdmissibleKernel.K td.X td.H

abbrev Khat (td : TubeData) : ℝ → ℝ :=
  SSU.Engines.TypeII.AdmissibleKernel.Khat td.H

structure Hypothesis (κ ι : Type*) [DecidableEq κ] where
  /-- TeX-facing Fejér-banked partition package, producing the packet operators. -/
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  /-- Type-II tube parameters. -/
  td : TubeData
  /-- Positivity of the short-shift scale `H` (needed for kernel integrability). -/
  hH : 0 < td.H
  /-- Steps 3–4 (large sieve) estimate. -/
  step34 : Step34LargeSieve td
  /--
  The TT*/reindexing identity that turns the tube quadratic form into a `Khat`-weighted ξ-integral
  of `|S(ξ)|²` (TeX Step 2, abstracted as `Step2ToTubeForm.tubeForm_eq`).
  -/
  tubeForm_eq :
    ∀ F : TubePoint → ℂ,
      tubeForm (K td) td.T F =
        ((∫ ξ in Set.Icc (-(1 / td.H)) (1 / td.H),
              (Khat td ξ) * (‖typeIISum td.a td.q td.X ξ td.T F‖ ^ 2)) : ℂ)
  /--
  Reduction from packet Gram entries to the Type-II tube quadratic form, plus an energy comparison.

  This is the “application-specific” bookkeeping: it depends on how the packet operators are built.
  -/
  reduction :
    ReductionToTubeForm
      (H := SSU.Global.Signal)
      (J := (FB.data).J)
      (T := ((FB.data).corePacketFamily.T))
      td
      (K td)

def mk_trivialStep34
    {κ ι : Type*} [DecidableEq κ]
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH : 0 < td.H)
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
  { FB := FB
    td := td
    hH := hH
    step34 := Step34LargeSieve.trivial td hX hH
    tubeForm_eq := tubeForm_eq
    reduction := reduction }

namespace Hypothesis

variable {κ ι : Type*} [DecidableEq κ] (h : Hypothesis κ ι)

noncomputable def step2 : Step2ToTubeForm h.td (K h.td) :=
  SSU.Engines.TypeII.AdmissibleKernel.step2ToTubeForm
    (td := h.td) (hH := h.hH) (htube := h.tubeForm_eq)

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
by
  classical
  exact
    SSU.Engines.TypeII.gramHypothesis_of_step2ToTubeForm
      (td := h.td) (K := K h.td) (h2 := h.step2) (h34 := h.step34) (R := h.reduction)

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis)

end Hypothesis

end

end FejerBankedTypeIIBridge
end Instances
end SSU
