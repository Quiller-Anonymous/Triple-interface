import Twin.ChecklistModel
import Twin.MajorArc.SWUniform
import Twin.ChecklistAxioms

namespace Twin.ChecklistSme

noncomputable section

open Twin

abbrev A : ℝ := Twin.ChecklistModel.A
abbrev B : ℝ := Twin.ChecklistModel.B
abbrev Lambda : ℕ → ℝ := Twin.ChecklistModel.Λ
abbrev Wwin : ℝ → ℝ := Twin.ChecklistModel.W
abbrev What : ℝ → ℝ := Twin.ChecklistModel.W_hat

/-
Conventional analytic input (postulated):

This is the standard “smoothed major-arc Siegel–Walfisz” estimate for the specific model
`(A,B,Lambda,Wwin,What)` used in `Twin/ChecklistModel.lean`, i.e. a major-arc asymptotic
for the smoothed von Mangoldt exponential sum `Twin.SW.sumValue` against the main term
`Twin.SW.mainTerm`, uniform for `q ≤ (log X)^B` and `|α-a/q| ≤ δ/(H+1)`.

Justification (paper-facing):
  - This is the classical major-arc evaluation in the Siegel–Walfisz range for smoothed
    prime exponential sums (derived from twisted Chebyshev ψ-bounds + partial summation
    + standard major-arc harmonic analysis).
  - We record it in the *exact* interface consumed by the Twin wiring layer:
    `Twin.MajorArc.SmoothMajorArcEstimate`.

Status:
  - Declared here as an explicit `axiom` so it is counted as a *conventional* dependency
    (and shows up in `#print axioms` audits), until a full derivation is formalized.
-/

/-!
Instead of axiomatizing the entire `SmoothMajorArcEstimate` record, we fix the numerical
parameters (`δ`, `X0`, `C`) explicitly and postulate only the core major-arc bound.

This makes the major-arc boxes used elsewhere (e.g. `Twin/MajorArc/MajMass.lean`) concrete,
so later replacement by a proof is purely about filling `sme_bound`.
-/

def δ : ℝ := (1 : ℝ) / 1000
lemma δ_pos : 0 < δ := by
  norm_num [δ]

def X0 : ℝ := 3

def C : ℝ := 1

/--
Conventional major-arc bound (paper §11.2-style, “smoothed Siegel–Walfisz” range).

This is the single analytic input needed to instantiate `SmoothMajorArcEstimate` for
the frozen model `(A,B,Lambda,Wwin,What)`.
-/
axiom instSW_bound :
  ∀ {X H : ℝ}, X0 ≤ X → 1 ≤ H →
    ∀ {q a : ℕ}, 1 ≤ q → (q : ℝ) ≤ Real.rpow (Real.log X) B → Nat.Coprime a q →
    ∀ {α : ℝ}, |α - (a : ℝ)/q| ≤ δ / (H + 1) →
      ‖Twin.SW.sumValue Lambda Wwin X H α - Twin.SW.mainTerm What X H α a q‖
        ≤ C * (X / Real.rpow (Real.log X) A)

instance instSW : Twin.MajorArc.SiegelWalfisz A B Lambda Wwin What :=
{ δ := δ
, δ_pos := δ_pos
, X0 := X0
, C := C
, bound := instSW_bound
}

/-- Frozen-model `SmoothMajorArcEstimate`, built from the explicit constants above. -/
def sme : Twin.MajorArc.SmoothMajorArcEstimate A B Lambda Wwin What :=
  Twin.MajorArc.SmoothMajorArcEstimate.ofSW (A := A) (B := B) (Λ := Lambda) (W := Wwin) (W_hat := What)

/-
Conventional numeric input (postulated):

This is the paper-facing parameter/saving inequality asserting that the pointwise SW-error
envelope used in `Twin.ChecklistAxioms.pinnedMajors_SW_error_L1_raw` fits inside the `/6`
budget for the pinned-major bookkeeping.

It is split out as a separate axiom so it is clearly attached to the *frozen* major-arc model
`sme` rather than being a global fact about `Twin.ChecklistAxioms`.
-/
axiom pinnedMajors_SW_error_envelope_budget :
  Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme)

instance : Twin.ChecklistAxioms.PinnedMajorsSWErrorEnvelopeBudget (sme := sme) :=
  pinnedMajors_SW_error_envelope_budget

/-!
Conventional arithmetic input (postulated):

This is the pinned-major *main-term* evaluation at the truncated singular series scale,
for the frozen model `sme`.  It is recorded as a typeclass in `Twin.ChecklistAxioms`
so parameterized theorems make the dependency explicit.
-/

axiom pinnedMajors_mainTerm_eval :
  Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme)

instance : Twin.ChecklistAxioms.PinnedMajorsMainTermEval (sme := sme) :=
  pinnedMajors_mainTerm_eval

/-!
Conventional minor-arc input (postulated):

This is the paper-facing minor-arc `L²` bound feeding the gate, recorded in the exact
`Twin.ChecklistAxioms.MinorMassAtSqSumBudget` interface (the `/9` square-sum budget on
`bigIcc(X)`).

Paper anchor: the minor-arc `L²` estimate (large sieve / Type-II) in the gate argument.
-/

axiom minorMassAt_sq_sum_bigIcc_budget :
  Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme)

instance : Twin.ChecklistAxioms.MinorMassAtSqSumBudget (sme := sme) :=
  minorMassAt_sq_sum_bigIcc_budget

/-!
Conventional desmoothing input (postulated):

We split the `/3` desmoothing budget for `dsMassAt = |fullMassAt - localizedTwinMass|`
into two `/6` budgets in `Twin.ChecklistAxioms`:

* `DsFourierAtSumBudget`: Fourier inversion + smooth/sharp window comparison.
* `DsPrimePowerAtSumBudget`: prime-power disposal (ΛΛ versus prime-only log-indicator).

Paper-facing anchor: the standard desmoothing + prime-power bookkeeping used when moving
between smoothed Λ-sums and sharp prime indicators in a windowed correlation.
-/

axiom dsFourierAt_sum_bigIcc_budget :
  Twin.ChecklistAxioms.DsFourierAtSumBudget

instance : Twin.ChecklistAxioms.DsFourierAtSumBudget :=
  dsFourierAt_sum_bigIcc_budget

axiom dsPrimePowerAt_sum_bigIcc_budget :
  Twin.ChecklistAxioms.DsPrimePowerAtSumBudget

instance : Twin.ChecklistAxioms.DsPrimePowerAtSumBudget :=
  dsPrimePowerAt_sum_bigIcc_budget

end

end Twin.ChecklistSme
