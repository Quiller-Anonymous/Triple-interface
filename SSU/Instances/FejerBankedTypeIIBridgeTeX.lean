import SSU.Instances.FejerBankedTeX
import SSU.Engines.TypeIITTStarWrappersTeX
import SSU.Engines.TypeIITTStarWrappersTeXFor
import SSU.Engines.TypeIIBalancedXiAdmissibleKernel
import SSU.Engines.LargeSieve.MontgomeryVaughanTypeII
import SSU.Engines.LargeSieve.TypeIIWeakLargeSieveTeX
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

/-!
## Variant: Step 3/4 hypotheses supplied per residue class

This keeps callers in the TeX Step 3/4 “fixed residue class” presentation and only collapses to
global MV internally via deterministic `of_byResidue` adapters.
-/

structure HypothesisMVByResidue (κ ι : Type*) [DecidableEq κ] where
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
  /-- Step 3 (Montgomery–Vaughan) hypothesis in residue-class form. -/
  step3MVByResidue : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td
  /-- Step 4 (Montgomery–Vaughan) hypothesis in residue-class form. -/
  step4MVByResidue : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td
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

namespace Hypothesis

/-!
## Convenience constructor: geometry-only large sieve (weak fallback)

This builds a full TeX-facing `Hypothesis` using:
- the deterministic Step 2 identity (`tubeForm_eq`),
- the deterministic packet-to-tube reduction (`reduction`),
- the geometry-only (Cauchy–Schwarz + cardinality) weak large-sieve bound, and
- the crude but explicit `balanced-xi` witness for the concrete admissible kernel `K̂_H`.

This is intended as a low-friction “plumbing complete” constructor while the TeX-strength
Step 3/4 large sieve is being proved.
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
    Hypothesis κ ι :=
by
  classical
  have hD0 : 0 ≤ td.D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD
  have hU0 : 0 ≤ td.U := le_trans (by norm_num : (0 : ℝ) ≤ 1) hU
  have hX0 : 0 ≤ td.X := le_of_lt hX
  have hH : 0 < td.H := lt_trans (by norm_num : (0 : ℝ) < 1) hH1
  -- Geometry-only Step 3/4/5 (TeX-shaped) large sieve.
  let step34 : Step34LargeSieveTeX td :=
    SSU.Engines.TypeII.LargeSieve.step34LargeSieveTeX_of_box_geometry
      (td := td) (hDq := hDq) (hD := hD0) (hU1 := hU) (hX := hX0)
      (hU0 := hU0) (hD1 := hD) (hXH1 := hXH1)
  -- Crude but explicit `balanced-xi` witness for `K̂_H`.
  let balancedXi :
      BalancedXiClaimInv td.X td.H (Khat td) :=
    SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat td.X td.H hX0 hH1
  exact
    { FB := FB
      td := td
      hX := hX
      hH := hH
      hU := hU
      hD := hD
      step34 := step34
      balancedXi := balancedXi
      tubeForm_eq := tubeForm_eq
      reduction := reduction }

end Hypothesis

namespace HypothesisMV

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisMV κ ι)

theorem hUpos : 0 < h.td.U :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hU

theorem hDpos : 0 < h.td.D :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hD

noncomputable def step2 : Step2ToTubeForm h.td (K h.td) :=
  SSU.Engines.TypeII.AdmissibleKernel.step2ToTubeForm
    (td := h.td) (hH := h.hH) (htube := h.tubeForm_eq)

/-- Use-site TeX Step 3 bound specialized to the extracted array `reduction.F f i j`. -/
noncomputable def step3For (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor h.td (h.reduction.F f i j) :=
  SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_montgomeryVaughan
    (td := h.td) (h3MV := h.step3MV)
    (hD := le_of_lt h.hDpos) (hU := le_of_lt h.hUpos) (hX := le_of_lt h.hX)
    (h.reduction.F f i j)

/-- Use-site TeX Step 4 bound specialized to the extracted array `reduction.F f i j`. -/
noncomputable def step4For (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor h.td (h.reduction.F f i j) :=
  SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_montgomeryVaughan
    (td := h.td) (h4MV := h.step4MV)
    (hD := le_of_lt h.hDpos) (hU := le_of_lt h.hUpos) (hX := le_of_lt h.hX)
    (h.reduction.F f i j)

/-- Use-site TeX Step 5 bound specialized to the extracted array `reduction.F f i j`. -/
noncomputable def step34For (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step34LargeSieveTeXFor h.td (h.reduction.F f i j) :=
  SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
    (td := h.td) (F := h.reduction.F f i j)
    (h3 := h.step3For f i j) (h4 := h.step4For f i j)
    (hD := h.hDpos) (hU := h.hUpos) (hX := le_of_lt h.hX)

/--
One-shot reduction-level TeX TT* bound (MV route):
`Step 3 (MV) + Step 4 (MV) + balanced-ξ + reduction → packet Gram bound`.

This is the use-site entrypoint for downstream code that wants a direct bound for a fixed
`(f,i,j)` without manually assembling an intermediate Step 5 object.
-/
theorem norm_inner_le_step3MV_step4MV
    (f : SSU.Global.Signal) (i : ℤ) (hi : i ∈ (h.FB.data).J)
    (j : ℤ) (hj : j ∈ (h.FB.data).J) :
    ‖inner ℂ (((h.FB.data).corePacketFamily.T i) f) (((h.FB.data).corePacketFamily.T j) f)‖ ≤
      (((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MV_step4MV
            (td := h.td) (F := h.reduction.F f i j) (h3MV := h.step3MV) (h4MV := h.step4MV)
            (hD0 := le_of_lt h.hDpos) (hU0 := le_of_lt h.hUpos) (hX0 := le_of_lt h.hX)
            (hD := h.hDpos) (hU := h.hUpos)).C *
          Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
            h.balancedXi.C *
              ((h.td.U * h.td.D) / h.td.H
                + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                    Real.sqrt (h.td.H * Real.log h.td.H)
                + h.td.X)) *
          h.reduction.Cenergy) *
        ‖((h.FB.data).corePacketFamily.T i) f‖ * ‖((h.FB.data).corePacketFamily.T j) f‖ := by
  simpa [step2, Khat, K] using
    (SSU.Engines.TypeII.norm_inner_le_of_reduction_step2ToTubeForm_step3MV_step4MV
      (R := h.reduction) (h2 := h.step2)
      (h3MV := h.step3MV) (h4MV := h.step4MV)
      (hbal := by simpa [step2, Khat] using h.balancedXi)
      (hD0 := le_of_lt h.hDpos) (hU0 := le_of_lt h.hUpos)
      (hX0 := le_of_lt h.hX) (hH0 := h.hH)
      (hU := h.hU) (hD := h.hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj))

/-- Same bound as `norm_inner_le_step3MV_step4MV`, with Step 5 packaged as `step34For`. -/
theorem norm_inner_le_step34For
    (f : SSU.Global.Signal) (i : ℤ) (hi : i ∈ (h.FB.data).J)
    (j : ℤ) (hj : j ∈ (h.FB.data).J) :
    ‖inner ℂ (((h.FB.data).corePacketFamily.T i) f) (((h.FB.data).corePacketFamily.T j) f)‖ ≤
      ((h.step34For f i j).C *
          Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
            h.balancedXi.C *
              ((h.td.U * h.td.D) / h.td.H
                + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                    Real.sqrt (h.td.H * Real.log h.td.H)
                + h.td.X)) *
          h.reduction.Cenergy *
        ‖((h.FB.data).corePacketFamily.T i) f‖ * ‖((h.FB.data).corePacketFamily.T j) f‖ := by
  simpa [step2, Khat, K] using
    (SSU.Engines.TypeII.norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
      (R := h.reduction) (h2 := h.step2)
      (hbal := by simpa [step2, Khat] using h.balancedXi)
      (h34 := h.step34For f i j)
      (hX0 := le_of_lt h.hX) (hH0 := h.hH)
      (hU := h.hU) (hD := h.hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj))

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
by
  have hbal' : BalancedXiClaimInv h.td.X h.td.H (step2 (h := h)).Khat := by
    simpa [step2, Khat] using h.balancedXi
  exact
    SSU.Engines.TypeII.gramHypothesis_of_reduction_step2ToTubeForm_step3MV_step4MV
      (R := h.reduction) (h2 := h.step2)
      (h3MV := h.step3MV) (h4MV := h.step4MV)
      (hbal := hbal')
      (hD0 := le_of_lt h.hDpos) (hU0 := le_of_lt h.hUpos)
      (hX0 := le_of_lt h.hX) (hX := h.hX) (hH0 := h.hH)
      (hU := h.hU) (hD := h.hD)

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
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis)

end HypothesisMV

namespace HypothesisMVByResidue

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisMVByResidue κ ι)

theorem hUpos : 0 < h.td.U :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hU

theorem hDpos : 0 < h.td.D :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h.hD

noncomputable def step2 : Step2ToTubeForm h.td (K h.td) :=
  SSU.Engines.TypeII.AdmissibleKernel.step2ToTubeForm
    (td := h.td) (hH := h.hH) (htube := h.tubeForm_eq)

/-- Use-site TeX Step 3 bound specialized to the extracted array `reduction.F f i j`. -/
noncomputable def step3For (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step3LargeSieveOuterUFor h.td (h.reduction.F f i j) :=
  SSU.Engines.TypeII.Step3LargeSieveOuterUFor.of_montgomeryVaughan_byResidue
    (td := h.td) (h3MV := h.step3MVByResidue)
    (hD := le_of_lt h.hDpos) (hU := le_of_lt h.hUpos) (hX := le_of_lt h.hX)
    (h.reduction.F f i j)

/-- Use-site TeX Step 4 bound specialized to the extracted array `reduction.F f i j`. -/
noncomputable def step4For (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step4LargeSieveOuterVFor h.td (h.reduction.F f i j) :=
  SSU.Engines.TypeII.Step4LargeSieveOuterVFor.of_montgomeryVaughan_byResidue
    (td := h.td) (h4MV := h.step4MVByResidue)
    (hD := le_of_lt h.hDpos) (hU := le_of_lt h.hUpos) (hX := le_of_lt h.hX)
    (h.reduction.F f i j)

/-- Use-site TeX Step 5 bound specialized to the extracted array `reduction.F f i j`. -/
noncomputable def step34For (f : SSU.Global.Signal) (i j : ℤ) :
    SSU.Engines.TypeII.Step34LargeSieveTeXFor h.td (h.reduction.F f i j) :=
  SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3_step4
    (td := h.td) (F := h.reduction.F f i j)
    (h3 := h.step3For f i j) (h4 := h.step4For f i j)
    (hD := h.hDpos) (hU := h.hUpos) (hX := le_of_lt h.hX)

theorem norm_inner_le_step3MVByResidue_step4MVByResidue
    (f : SSU.Global.Signal) (i : ℤ) (hi : i ∈ (h.FB.data).J)
    (j : ℤ) (hj : j ∈ (h.FB.data).J) :
    ‖inner ℂ (((h.FB.data).corePacketFamily.T i) f) (((h.FB.data).corePacketFamily.T j) f)‖ ≤
      (((SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_step3MVByResidue_step4MVByResidue
            (td := h.td) (F := h.reduction.F f i j)
            (h3MV := h.step3MVByResidue) (h4MV := h.step4MVByResidue)
            (hD0 := le_of_lt h.hDpos) (hU0 := le_of_lt h.hUpos) (hX0 := le_of_lt h.hX)
            (hD := h.hDpos) (hU := h.hUpos)).C *
          Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
            h.balancedXi.C *
              ((h.td.U * h.td.D) / h.td.H
                + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                    Real.sqrt (h.td.H * Real.log h.td.H)
                + h.td.X)) *
          h.reduction.Cenergy) *
        ‖((h.FB.data).corePacketFamily.T i) f‖ * ‖((h.FB.data).corePacketFamily.T j) f‖ := by
  simpa [step2, Khat, K] using
    (SSU.Engines.TypeII.norm_inner_le_of_reduction_step2ToTubeForm_step3MVByResidue_step4MVByResidue
      (R := h.reduction) (h2 := h.step2)
      (h3MV := h.step3MVByResidue) (h4MV := h.step4MVByResidue)
      (hbal := by simpa [step2, Khat] using h.balancedXi)
      (hD0 := le_of_lt h.hDpos) (hU0 := le_of_lt h.hUpos)
      (hX0 := le_of_lt h.hX) (hH0 := h.hH)
      (hU := h.hU) (hD := h.hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj))

/-- Same bound as `norm_inner_le_step3MVByResidue_step4MVByResidue`, with Step 5 packaged as
`step34For`. -/
theorem norm_inner_le_step34For
    (f : SSU.Global.Signal) (i : ℤ) (hi : i ∈ (h.FB.data).J)
    (j : ℤ) (hj : j ∈ (h.FB.data).J) :
    ‖inner ℂ (((h.FB.data).corePacketFamily.T i) f) (((h.FB.data).corePacketFamily.T j) f)‖ ≤
      ((h.step34For f i j).C *
          Real.sqrt ((h.td.D * h.td.U) / (h.td.q : ℝ)) *
            h.balancedXi.C *
              ((h.td.U * h.td.D) / h.td.H
                + Real.sqrt h.td.X * (Real.sqrt h.td.U + Real.sqrt h.td.D) *
                    Real.sqrt (h.td.H * Real.log h.td.H)
                + h.td.X)) *
          h.reduction.Cenergy *
        ‖((h.FB.data).corePacketFamily.T i) f‖ * ‖((h.FB.data).corePacketFamily.T j) f‖ := by
  simpa [step2, Khat, K] using
    (SSU.Engines.TypeII.norm_inner_le_of_reduction_step2ToTubeForm_step34TeXFor
      (R := h.reduction) (h2 := h.step2)
      (hbal := by simpa [step2, Khat] using h.balancedXi)
      (h34 := h.step34For f i j)
      (hX0 := le_of_lt h.hX) (hH0 := h.hH)
      (hU := h.hU) (hD := h.hD)
      (f := f) (i := i) (hi := hi) (j := j) (hj := hj))

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
by
  have hbal' : BalancedXiClaimInv h.td.X h.td.H (step2 (h := h)).Khat := by
    simpa [step2, Khat] using h.balancedXi
  exact
    SSU.Engines.TypeII.gramHypothesis_of_reduction_step2ToTubeForm_step3MVByResidue_step4MVByResidue
      (R := h.reduction) (h2 := h.step2)
      (h3MV := h.step3MVByResidue) (h4MV := h.step4MVByResidue)
      (hbal := hbal')
      (hD0 := le_of_lt h.hDpos) (hU0 := le_of_lt h.hUpos)
      (hX0 := le_of_lt h.hX) (hX := h.hX) (hH0 := h.hH)
      (hU := h.hU) (hD := h.hD)

noncomputable def toHypothesisMV : HypothesisMV κ ι where
  FB := h.FB
  td := h.td
  hX := h.hX
  hH := h.hH
  hU := h.hU
  hD := h.hD
  step3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue
    h.td h.step3MVByResidue
  step4MV := SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue
    h.td h.step4MVByResidue
  balancedXi := h.balancedXi
  tubeForm_eq := h.tubeForm_eq
  reduction := h.reduction

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis)

end HypothesisMVByResidue

/-!
## Variant: use-site Step 5 family with a uniform constant envelope

This route is useful once Step 3/4 has been proved at the extracted-array level and packaged as
`step34For f i j`, but before introducing a global Step 3/4 interface object.
-/

structure HypothesisStep34ForUniform (κ ι : Type*) [DecidableEq κ] where
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
  -/
  reduction :
    ReductionToTubeForm
      (H := SSU.Global.Signal)
      (J := (FB.data).J)
      (T := ((FB.data).corePacketFamily.T))
      td
      (K td)
  /-- Uniform envelope for the use-site Step 5 constants. -/
  C34 : ℝ
  C34_nonneg : 0 ≤ C34
  /-- Use-site Step 5 bound for each extracted array. -/
  step34For :
    ∀ f : SSU.Global.Signal, ∀ i j : ℤ,
      SSU.Engines.TypeII.Step34LargeSieveTeXFor td (reduction.F f i j)
  /-- Uniform control of Step 5 constants across `(f,i,j)`. -/
  C34_le :
    ∀ f : SSU.Global.Signal, ∀ i j : ℤ, (step34For f i j).C ≤ C34

namespace HypothesisStep34ForUniform

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisStep34ForUniform κ ι)

noncomputable def step2 : Step2ToTubeForm h.td (K h.td) :=
  SSU.Engines.TypeII.AdmissibleKernel.step2ToTubeForm
    (td := h.td) (hH := h.hH) (htube := h.tubeForm_eq)

/-- Build the uniform use-site Step-5 bridge object from a user-provided family
`step34For f i j` and a uniform constant envelope `C34`. -/
noncomputable def of_step34For
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH : 0 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (balancedXi : BalancedXiClaimInv td.X td.H (Khat td))
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
        (K td))
    (C34 : ℝ)
    (C34_nonneg : 0 ≤ C34)
    (step34For :
      ∀ f : SSU.Global.Signal, ∀ i j : ℤ,
        SSU.Engines.TypeII.Step34LargeSieveTeXFor td (reduction.F f i j))
    (C34_le :
      ∀ f : SSU.Global.Signal, ∀ i j : ℤ, (step34For f i j).C ≤ C34) :
    HypothesisStep34ForUniform κ ι where
  FB := FB
  td := td
  hX := hX
  hH := hH
  hU := hU
  hD := hD
  balancedXi := balancedXi
  tubeForm_eq := tubeForm_eq
  reduction := reduction
  C34 := C34
  C34_nonneg := C34_nonneg
  step34For := step34For
  C34_le := C34_le

/-- Build the uniform use-site Step-5 bridge object from a global `Step34LargeSieveTeX` package. -/
noncomputable def of_globalStep34
    (FB : SSU.Instances.FejerBankedTeX.Hypothesis κ ι)
    (td : TubeData)
    (hX : 0 < td.X)
    (hH : 0 < td.H)
    (hU : 1 ≤ td.U)
    (hD : 1 ≤ td.D)
    (balancedXi : BalancedXiClaimInv td.X td.H (Khat td))
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
        (K td))
    (step34 : Step34LargeSieveTeX td) :
    HypothesisStep34ForUniform κ ι :=
  of_step34For
    (FB := FB) (td := td)
    (hX := hX) (hH := hH) (hU := hU) (hD := hD)
    (balancedXi := balancedXi)
    (tubeForm_eq := tubeForm_eq)
    (reduction := reduction)
    (C34 := step34.C)
    (C34_nonneg := step34.C_nonneg)
    (step34For := fun f i j =>
      SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_global
        td step34 (reduction.F f i j))
    (C34_le := by
      intro f i j
      simp [SSU.Engines.TypeII.Step34LargeSieveTeXFor.of_global])

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
by
  have hbal' : BalancedXiClaimInv h.td.X h.td.H (step2 (h := h)).Khat := by
    simpa [step2, Khat] using h.balancedXi
  exact
    SSU.Engines.TypeII.gramHypothesis_of_reduction_step2ToTubeForm_step34TeXFor_uniform
      (R := h.reduction) (h2 := h.step2) (hbal := hbal')
      (hX0 := le_of_lt h.hX) (hH0 := h.hH) (hU := h.hU) (hD := h.hD)
      (C34 := h.C34) (hC34_nonneg := h.C34_nonneg)
      (h34For := h.step34For) (hC34 := h.C34_le)

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis)

end HypothesisStep34ForUniform

/-!
## Direct geometry-only Gram/contract constructors (box fallback path)

These constructors consume the new direct engine route
`gramHypothesis_of_reduction_step2ToTubeForm_box_geometry` without first packaging a global or
uniform Step-5 hypothesis object.
-/

variable {κ ι : Type*} [DecidableEq κ]

/-- Build the SSU Gram hypothesis directly from box-geometry assumptions plus Step 2/reduction. -/
noncomputable def gramHypothesis_of_box_geometry
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
      ((FB.data).corePacketFamily.T) := by
  have hH : 0 < td.H := lt_trans (by norm_num : (0 : ℝ) < 1) hH1
  have hX0 : 0 ≤ td.X := le_of_lt hX
  have hU0 : 0 ≤ td.U := le_trans (by norm_num : (0 : ℝ) ≤ 1) hU
  have hD0 : 0 ≤ td.D := le_trans (by norm_num : (0 : ℝ) ≤ 1) hD
  let h2 : SSU.Engines.TypeII.Step2ToTubeForm td (K td) :=
    SSU.Engines.TypeII.AdmissibleKernel.step2ToTubeForm
      (td := td) (hH := hH) (htube := tubeForm_eq)
  have hbal : SSU.Engines.TypeII.BalancedXiClaimInv td.X td.H h2.Khat := by
    simpa [h2, Khat] using
      (SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat
        td.X td.H hX0 hH1)
  exact
    SSU.Engines.TypeII.gramHypothesis_of_reduction_step2ToTubeForm_box_geometry
      (R := reduction)
      (h2 := h2)
      (hbal := hbal)
      (hDq := hDq)
      (hD0 := hD0) (hU0 := hU0) (hX0 := hX0)
      (hX := hX) (hH0 := hH)
      (hU := hU) (hD := hD)
      (hXH1 := hXH1)

/-- Build the SSU contract directly from the geometry-only Gram constructor above. -/
noncomputable def contract_of_box_geometry
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
  FB.contract_of_gramHypothesis
    (h := gramHypothesis_of_box_geometry
      (FB := FB) (td := td)
      (hX := hX) (hH1 := hH1) (hU := hU) (hD := hD)
      (hDq := hDq) (hXH1 := hXH1)
      (tubeForm_eq := tubeForm_eq) (reduction := reduction))

namespace Hypothesis

variable {κ ι : Type*} [DecidableEq κ] (h : Hypothesis κ ι)

/-- Route global Step-5 hypotheses through the uniform use-site Step-5 bridge format. -/
noncomputable def toHypothesisStep34ForUniform : HypothesisStep34ForUniform κ ι :=
  HypothesisStep34ForUniform.of_globalStep34
    (FB := h.FB) (td := h.td)
    (hX := h.hX) (hH := h.hH) (hU := h.hU) (hD := h.hD)
    (balancedXi := h.balancedXi)
    (tubeForm_eq := h.tubeForm_eq)
    (reduction := h.reduction)
    (step34 := h.step34)

noncomputable def gramHypothesis_uniform :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract_uniform : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis_uniform)

end Hypothesis

namespace HypothesisMV

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisMV κ ι)

/-- Convert MV-input hypotheses into the uniform use-site Step 5 bridge format. -/
noncomputable def toHypothesisStep34ForUniform : HypothesisStep34ForUniform κ ι :=
  HypothesisStep34ForUniform.of_globalStep34
    (FB := h.FB) (td := h.td)
    (hX := h.hX) (hH := h.hH) (hU := h.hU) (hD := h.hD)
    (balancedXi := h.balancedXi)
    (tubeForm_eq := h.tubeForm_eq)
    (reduction := h.reduction)
    (step34 := h.step34)

noncomputable def gramHypothesis_uniform :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract_uniform : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis_uniform)

end HypothesisMV

namespace HypothesisMVByResidue

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisMVByResidue κ ι)

/-- Route residue-class MV inputs through the uniform use-site Step 5 bridge format. -/
noncomputable def toHypothesisStep34ForUniform : HypothesisStep34ForUniform κ ι :=
  (h.toHypothesisMV).toHypothesisStep34ForUniform

noncomputable def gramHypothesis_uniform :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract_uniform : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis_uniform)

end HypothesisMVByResidue

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

/-- Same as `HypothesisMVKhat`, but with Step 3/4 supplied in per-residue form. -/
structure HypothesisMVKhatByResidue (κ ι : Type*) [DecidableEq κ] where
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
  /-- Step 3 (Montgomery–Vaughan) hypothesis in residue-class form. -/
  step3MVByResidue : SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughanByResidue td
  /-- Step 4 (Montgomery–Vaughan) hypothesis in residue-class form. -/
  step4MVByResidue : SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughanByResidue td
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

/-- Route `HypothesisMVKhat` through the uniform use-site Step 5 bridge format. -/
noncomputable def toHypothesisStep34ForUniform : HypothesisStep34ForUniform κ ι :=
  (h.toHypothesisMV).toHypothesisStep34ForUniform

noncomputable def gramHypothesis_uniform :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis_uniform)

end HypothesisMVKhat

namespace HypothesisMVKhatByResidue

variable {κ ι : Type*} [DecidableEq κ] (h : HypothesisMVKhatByResidue κ ι)

theorem hH : 0 < h.td.H :=
  lt_trans (by norm_num) h.hH1

noncomputable def balancedXi :
    BalancedXiClaimInv h.td.X h.td.H (Khat h.td) :=
  SSU.Engines.TypeII.AdmissibleKernel.balancedXiClaimInv_Khat
    h.td.X h.td.H (le_of_lt h.hX) h.hH1

noncomputable def toHypothesisMVByResidue : HypothesisMVByResidue κ ι where
  FB := h.FB
  td := h.td
  hX := h.hX
  hH := h.hH
  hU := h.hU
  hD := h.hD
  step3MVByResidue := h.step3MVByResidue
  step4MVByResidue := h.step4MVByResidue
  balancedXi := h.balancedXi
  tubeForm_eq := h.tubeForm_eq
  reduction := h.reduction

noncomputable def toHypothesisMVKhat : HypothesisMVKhat κ ι where
  FB := h.FB
  td := h.td
  hX := h.hX
  hH1 := h.hH1
  hU := h.hU
  hD := h.hD
  step3MV := SSU.Engines.TypeII.LargeSieve.Step3MontgomeryVaughan.of_byResidue
    h.td h.step3MVByResidue
  step4MV := SSU.Engines.TypeII.LargeSieve.Step4MontgomeryVaughan.of_byResidue
    h.td h.step4MVByResidue
  tubeForm_eq := h.tubeForm_eq
  reduction := h.reduction

/-- Route `HypothesisMVKhatByResidue` through the uniform use-site Step 5 bridge format. -/
noncomputable def toHypothesisStep34ForUniform : HypothesisStep34ForUniform κ ι :=
  (h.toHypothesisMVByResidue).toHypothesisStep34ForUniform

noncomputable def gramHypothesis_uniform :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def gramHypothesis :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisMVByResidue).gramHypothesis

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis_uniform)

end HypothesisMVKhatByResidue

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

/-- Route `HypothesisKhat` through the uniform use-site Step-5 bridge format. -/
noncomputable def toHypothesisStep34ForUniform : HypothesisStep34ForUniform κ ι :=
  HypothesisStep34ForUniform.of_globalStep34
    (FB := h.FB) (td := h.td)
    (hX := h.hX) (hH := h.hH) (hU := h.hU) (hD := h.hD)
    (balancedXi := h.balancedXi)
    (tubeForm_eq := h.tubeForm_eq)
    (reduction := h.reduction)
    (step34 := h.step34)

noncomputable def gramHypothesis_uniform :
    SSU.Interzone.GramHypothesis
      (H := SSU.Global.Signal)
      (h.FB.data).J
      ((h.FB.data).corePacketFamily.T) :=
  (h.toHypothesisStep34ForUniform).gramHypothesis

noncomputable def contract : SSU.Global.SSUContract (h.FB.data).corePacketFamily :=
  h.FB.contract_of_gramHypothesis (h := h.gramHypothesis_uniform)

end HypothesisKhat

end

end FejerBankedTypeIIBridgeTeX
end Instances
end SSU
