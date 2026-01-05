import Mathlib
import Twin.GoalAPI
import Twin.AnalyticCore
import Twin.Bridge
import Twin.Ledger
import Twin.MajorArc.Pin
import Twin.MajorArc.PaperChecklist

noncomputable section
open scoped BigOperators

namespace Twin.MajorArc

open Twin
open Twin.GoalAPI

/-
Appendix-A adapter (PDF → Lean)
===============================

In `Twin_primes macho.pdf`, Appendix A describes a simple decomposition:

  TwinWeight_k = W_k + e_k

where `W_k` is the model major-arc contribution and `e_k` is the total error.
Summing over `k=0..H` yields a “pinned gate” criterion: if the windowed `L¹` error is small,
the total mass is positive, hence a twin exists in the window.

In our Lean wiring, the major-arc side is isolated as a `PaperMajorArcChecklist`:
we need an auxiliary windowed major-arc quantity `majMass X` together with

* `MajorArcLower`    (pinned majors lower bound, windowed)
* `MajorArcTransfer` (routing/transfer to localized twin mass + explicit error channels)

This file provides a minimal record matching the Appendix-A spine and a lemma producing
the checklist record used by the paper-facing route.
-/

/-- Minimal Appendix-A-style assumptions for producing the major-arc checklist.

`Wmaj` is the “model major-arc weight per integer” (paper: the pinned major arcs’ contribution).
The assumptions ask for:

* a windowed lower bound on `∑ Wmaj(X+k)` (pinned majors), in the Lean-normalized form of
  `MajorArcLower` for `majMass X := windowSum X H Wmaj`, and
* a pointwise routing inequality `Wmaj(X+k) ≤ J_H(k)*twinIndicator(X+k) + emin + eds`,
  which implies the windowed `MajorArcTransfer` inequality by summation.

This is intentionally “shape-only”: it does not commit to how `Wmaj` is constructed from SW,
nor how the lower bound is proved. -/
structure AppendixAInputs
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  (P : Params)
  (emin eds : ℕ → ℝ)
  (sme  : SmoothMajorArcEstimate A B Λ W W_hat)
  (spec : GateSpec P) where
  /-- Model major-arc contribution as a per-integer weight. -/
  Wmaj : ℕ → ℝ
  /-- Pinned majors lower bound, expressed directly as `MajorArcLower` for
  `majMass X := windowSum X H Wmaj`. -/
  lower :
    MajorArcLower P (fun X => Twin.Ledger.windowSum X P.H Wmaj)
  /-- Pointwise routing inequality (paper: `TwinWeight = W + e`), uniform in `X ≥ X0`. -/
  route_pointwise :
    ∀ ⦃X k⦄, P.X0 ≤ X → k ≤ P.H →
      Wmaj (X + k)
        ≤ Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
          + emin (X + k) + eds (X + k)

/-- From Appendix-A-style inputs, build the paper checklist record. -/
def AppendixAInputs.toPaperMajorArcChecklist
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  {P : Params} {emin eds : ℕ → ℝ}
  {sme : SmoothMajorArcEstimate A B Λ W W_hat}
  {spec : GateSpec P}
  (I : AppendixAInputs (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec)) :
  PaperMajorArcChecklist (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec) :=
by
  classical
  refine
    { majMass := fun X => Twin.Ledger.windowSum X P.H I.Wmaj
    , lower := I.lower
    , transfer := ?_ }
  refine ⟨?_⟩
  intro X hX
  -- Sum the pointwise routing inequality over the window `k=0..H`.
  set S : Finset ℕ := Finset.range (P.H + 1)
  have hsum :
      S.sum (fun k => I.Wmaj (X + k))
        ≤ S.sum (fun k =>
            Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
              + emin (X + k) + eds (X + k)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hk_le : k ≤ P.H := by
      have : k < P.H + 1 := Finset.mem_range.mp hk
      exact Nat.lt_succ_iff.mp this
    simpa [add_assoc, add_comm, add_left_comm] using I.route_pointwise (X := X) (k := k) hX hk_le
  -- Rewrite both sides into the `MajorArcTransfer` form.
  have hL :
      S.sum (fun k => I.Wmaj (X + k)) = Twin.Ledger.windowSum X P.H I.Wmaj := by
    simp [Twin.Ledger.windowSum, Twin.Ledger.windowSumN, S]
  have hMass :
      S.sum (fun k => Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k))
        = Twin.Bridge.localizedTwinMass X P.H := by
    simp [Twin.Bridge.localizedTwinMass, S]
  have hEmin :
      S.sum (fun k => emin (X + k)) = Twin.Ledger.windowSum X P.H emin := by
    simp [Twin.Ledger.windowSum, Twin.Ledger.windowSumN, S]
  have hEds :
      S.sum (fun k => eds (X + k)) = Twin.Ledger.windowSum X P.H eds := by
    simp [Twin.Ledger.windowSum, Twin.Ledger.windowSumN, S]
  have hR :
      S.sum (fun k =>
          Twin.Kernel.J P.H k * Twin.Bridge.twinIndicator (X + k)
            + emin (X + k) + eds (X + k))
        =
        Twin.Bridge.localizedTwinMass X P.H
          + Twin.Ledger.windowSum X P.H emin
          + Twin.Ledger.windowSum X P.H eds := by
    simp [S, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm, hMass, hEmin, hEds]
  -- combine
  simpa [hL, hR] using hsum

/-- Convenience: immediately obtain the `MajorArcPackage` used by `Twin.Main.windows_largeX_of_errorData`
by passing through the checklist. -/
def AppendixAInputs.toMajorArcPackage
  {A B : ℝ} {Λ : ℕ → ℝ} {W W_hat : ℝ → ℝ}
  {P : Params} {emin eds : ℕ → ℝ}
  {sme : SmoothMajorArcEstimate A B Λ W W_hat}
  {spec : GateSpec P}
  (I : AppendixAInputs (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec)) :
  MajorArcPackage (P := P) (emin := emin) (eds := eds) (sme := sme) (spec := spec) :=
  (I.toPaperMajorArcChecklist).toMajorArcPackage

end Twin.MajorArc

