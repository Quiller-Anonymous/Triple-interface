import SSU.Instances.FejerBankedTeX
import SSU.Engines.TypeIITTStarWrappersTeX
import SSU.Engines.TypeIIBalancedXiAdmissibleKernel
import SSU.Engines.LargeSieve.MontgomeryVaughanTypeII
import SSU.Engines.LargeSieve.TypeIIStep34CombineTeX

/-!
Bridge (TeX-faithful): Type-II tube inequality → Fejér-banked SSU contract.

This is the TeX-shaped version of `SSU/Instances/FejerBankedTypeIIBridge.lean`.

Differences:
* Steps 3–5 are supplied in the TeX large-sieve form (`Step34LargeSieveTeX`), with the `X/|ξ|`
  singular term (valid for `ξ ≠ 0`).
* ξ-integration is handled via the TeX moment lemma interface (`BalancedXiClaimInv`), rather than
  the uniform surrogate `Step34LargeSieve`.

No analytic number theory is proved here; we only wire the hypotheses into the SSU contract.
-/

namespace SSU
namespace Instances
namespace FejerBankedTypeIIBridgeTeX

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
  /-- Positivity of the global scale `X`. -/
  hX : 0 < td.X
  /-- Positivity of the short-shift scale `H` (needed for kernel integrability). -/
  hH : 0 < td.H
  /-- Lower bound `U ≥ 1` for the TeX ξ-integration lemma. -/
  hU : 1 ≤ td.U
  /-- Lower bound `D ≥ 1` for the TeX ξ-integration lemma. -/
  hD : 1 ≤ td.D
  /-- Steps 3–5 (large sieve) estimate in TeX form. -/
  step34 : Step34LargeSieveTeX td
  /-- TeX Lemma `balanced-xi` (moment hypothesis) for `K̂_H`. -/
  balancedXi : BalancedXiClaimInv td.X td.H (Khat td)
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

/-!
## Stronger wiring: supply Step 3 and Step 4 (Montgomery–Vaughan) and derive Step 5

This is the “fully wired” TeX path:

`MV (fiber) → Step 3/4 outer bounds → Step 5 (geometric mean) → TT* wrappers`.
-/

structure HypothesisMV (κ ι : Type*) [DecidableEq κ] where
  /-- TeX-facing Fejér-banked partition package, producing the packet operators. -/
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  /-- Type-II tube parameters. -/
  td : TubeData
  /-- Positivity of the global scale `X`. -/
  hX : 0 < td.X
  /-- Positivity of the short-shift scale `H` (needed for kernel integrability). -/
  hH : 0 < td.H
  /-- Lower bound `U ≥ 1` for the TeX ξ-integration lemma. -/
  hU : 1 ≤ td.U
  /-- Lower bound `D ≥ 1` for the TeX ξ-integration lemma. -/
  hD : 1 ≤ td.D
  /-- Step 3 (Montgomery–Vaughan) hypothesis in the TeX fiber shape. -/
  step3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td
  /-- Step 4 (Montgomery–Vaughan) hypothesis in the TeX fiber shape. -/
  step4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td
  /-- TeX Lemma `balanced-xi` (moment hypothesis) for `K̂_H`. -/
  balancedXi : BalancedXiClaimInv td.X td.H (Khat td)
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
  -- The new TeX-faithful TT* wrapper lives in `SSU.Engines.TypeIITTStarWrappersTeX`.
  have hbal' : BalancedXiClaimInv h.td.X h.td.H (step2 (h := h)).Khat := by
    -- `step2.Khat` is definitionally the admissible `Khat td`.
    simpa [step2, Khat] using h.balancedXi
  exact
    SSU.Engines.TypeII.gramHypothesis_of_step2ToTubeForm_teX
      (h2 := h.step2)
      (h34 := h.step34)
      (hbal := hbal')
      (hX := h.hX) (hH := h.hH) (hU := h.hU) (hD := h.hD)
      (R := h.reduction)

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis)

end Hypothesis

namespace HypothesisMV

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisMV κ ι)

theorem hUpos : 0 < h.td.U :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hU

theorem hDpos : 0 < h.td.D :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hD

noncomputable def step34 : Step34LargeSieveTeX h.td :=
by
  classical
  -- Step 3/4: MV → fiber-large-sieve → outer-large-sieve.
  have hD0 : 0 ≤ h.td.D := le_of_lt h.hDpos
  have hU0 : 0 ≤ h.td.U := le_of_lt h.hUpos
  have hX0 : 0 ≤ h.td.X := le_of_lt h.hX
  have h3fiber :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := h.td) h.step3MV hD0 hU0 hX0
  have h4fiber :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := h.td) h.step4MV hD0 hU0 hX0
  have h3outer :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := h.td) h3fiber
  have h4outer :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := h.td) h4fiber
  -- Step 5: geometric mean.
  exact
    SSU.Engines.TypeII.LargeSieve.step34LargeSieveTeX_of_step3_step4
      (td := h.td) h3outer h4outer h.hDpos h.hUpos hX0

noncomputable def toHypothesis : Hypothesis κ ι where
  FB := h.FB
  td := h.td
  hX := h.hX
  hH := h.hH
  hU := h.hU
  hD := h.hD
  step34 := h.step34
  balancedXi := h.balancedXi
  tubeForm_eq := h.tubeForm_eq
  reduction := h.reduction

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  (h.toHypothesis).contract

end HypothesisMV

/-!
## Variant: remove the `balanced-xi` hypothesis *and* derive Step 5 from Step 3/4 (MV)

This is the “most wired” TeX path for the current concrete admissible kernel:

* assume Step 3 and Step 4 as Montgomery–Vaughan hypotheses (fiber form),
* derive Step 5 (geometric mean) as `Step34LargeSieveTeX`,
* discharge `BalancedXiClaimInv` for `K̂_H = AdmissibleKernel.Khat`.
-/

structure HypothesisMVKhat (κ ι : Type*) [DecidableEq κ] where
  /-- TeX-facing Fejér-banked partition package, producing the packet operators. -/
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  /-- Type-II tube parameters. -/
  td : TubeData
  /-- Positivity of the global scale `X`. -/
  hX : 0 < td.X
  /-- `H > 1`, sufficient for the crude `balanced-xi` proof for `K̂_H`. -/
  hH1 : 1 < td.H
  /-- Lower bound `U ≥ 1` for the TeX ξ-integration lemma. -/
  hU : 1 ≤ td.U
  /-- Lower bound `D ≥ 1` for the TeX ξ-integration lemma. -/
  hD : 1 ≤ td.D
  /-- Step 3 (Montgomery–Vaughan) hypothesis in the TeX fiber shape. -/
  step3MV : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan td
  /-- Step 4 (Montgomery–Vaughan) hypothesis in the TeX fiber shape. -/
  step4MV : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan td
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

namespace HypothesisMVKhat

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisMVKhat κ ι)

theorem hH : 0 < h.td.H :=
  lt_trans (by norm_num) h.hH1

theorem hUpos : 0 < h.td.U :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hU

theorem hDpos : 0 < h.td.D :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hD

noncomputable def step34 : Step34LargeSieveTeX h.td :=
by
  classical
  have hD0 : 0 ≤ h.td.D := le_of_lt h.hDpos
  have hU0 : 0 ≤ h.td.U := le_of_lt h.hUpos
  have hX0 : 0 ≤ h.td.X := le_of_lt h.hX
  have h3fiber :=
    SSU.Engines.TypeII.LargeSieve.step3FiberLargeSieve_of_montgomeryVaughan
      (td := h.td) h.step3MV hD0 hU0 hX0
  have h4fiber :=
    SSU.Engines.TypeII.LargeSieve.step4FiberLargeSieve_of_montgomeryVaughan
      (td := h.td) h.step4MV hD0 hU0 hX0
  have h3outer :=
    SSU.Engines.TypeII.LargeSieve.step3OuterU_of_fiberLargeSieve (td := h.td) h3fiber
  have h4outer :=
    SSU.Engines.TypeII.LargeSieve.step4OuterV_of_fiberLargeSieve (td := h.td) h4fiber
  exact
    SSU.Engines.TypeII.LargeSieve.step34LargeSieveTeX_of_step3_step4
      (td := h.td) h3outer h4outer h.hDpos h.hUpos hX0

noncomputable def balancedXi :
    BalancedXiClaimInv h.td.X h.td.H (Khat h.td) :=
  SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat
    h.td.X h.td.H (le_of_lt h.hX) h.hH1

noncomputable def toHypothesisMV : HypothesisMV κ ι where
  FB := h.FB
  td := h.td
  hX := h.hX
  hH := h.hH
  hU := h.hU
  hD := h.hD
  step3MV := h.step3MV
  step4MV := h.step4MV
  balancedXi := h.balancedXi
  tubeForm_eq := h.tubeForm_eq
  reduction := h.reduction

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  (h.toHypothesisMV).contract

end HypothesisMVKhat

namespace HypothesisMVKhat

/-!
## Weak fallback constructor: geometry-only Step 3/4 (Cauchy–Schwarz + progression cardinality)

This is *not* the TeX-strength Montgomery–Vaughan large sieve. It is a deterministic scaffold:
it builds `step3MV` and `step4MV` from the already-proved `zSet` / `zSetV` cardinality bounds.
-/

variable {κ ι : Type*} [DecidableEq κ]

noncomputable def mk_of_box_geometry
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
by
  classical
  have hD0 : 0 ≤ td.D := le_trans (by norm_num) hD
  have hU0 : 0 ≤ td.U := le_trans (by norm_num) hU
  have hX0 : 0 ≤ td.X := le_of_lt hX
  refine
    { FB := FB
      td := td
      hX := hX
      hH1 := hH1
      hU := hU
      hD := hD
      step3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_box_geometry
        (td := td) hDq hD0 hU hX0
      step4MV := SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_box_geometry
        (td := td) hU0 hX0 hD hXH1
      tubeForm_eq := tubeForm_eq
      reduction := reduction }

end HypothesisMVKhat

/-!
## Variant: remove the `balanced-xi` hypothesis for the concrete admissible kernel

For the project’s current concrete choice `K̂_H = AdmissibleKernel.Khat`, we can discharge
`BalancedXiClaimInv` (crudely but explicitly). This lets instance-level bridges avoid carrying
`balancedXi` as an assumption.

We keep the original `Hypothesis` (hypothesis-style) version intact.
-/

structure HypothesisKhat (κ ι : Type*) [DecidableEq κ] where
  /-- TeX-facing Fejér-banked partition package, producing the packet operators. -/
  FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι
  /-- Type-II tube parameters. -/
  td : TubeData
  /-- Positivity of the global scale `X`. -/
  hX : 0 < td.X
  /-- `H > 1`, sufficient for the crude `balanced-xi` proof for `K̂_H`. -/
  hH1 : 1 < td.H
  /-- Lower bound `U ≥ 1` for the TeX ξ-integration lemma. -/
  hU : 1 ≤ td.U
  /-- Lower bound `D ≥ 1` for the TeX ξ-integration lemma. -/
  hD : 1 ≤ td.D
  /-- Steps 3–5 (large sieve) estimate in TeX form. -/
  step34 : Step34LargeSieveTeX td
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

namespace HypothesisKhat

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisKhat κ ι)

theorem hH : 0 < h.td.H :=
  lt_trans (by norm_num) h.hH1

noncomputable def balancedXi :
    BalancedXiClaimInv h.td.X h.td.H (Khat h.td) :=
  SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat
    h.td.X h.td.H (le_of_lt h.hX) h.hH1

noncomputable def toHypothesis : Hypothesis κ ι where
  FB := h.FB
  td := h.td
  hX := h.hX
  hH := h.hH
  hU := h.hU
  hD := h.hD
  step34 := h.step34
  balancedXi := h.balancedXi
  tubeForm_eq := h.tubeForm_eq
  reduction := h.reduction

noncomputable def step2 : Step2ToTubeForm h.td (K h.td) :=
  (h.toHypothesis).step2

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesis).gramHypothesis

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  (h.toHypothesis).contract

end HypothesisKhat

end

end FejerBankedTypeIIBridgeTeX
end Instances
end SSU
