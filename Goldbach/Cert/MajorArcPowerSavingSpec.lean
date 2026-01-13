import Goldbach.Cert.MajorArcAxiomsFunX

/-!
Major arcs: conventional “power saving” axiom boundary (FunX track).

This file is intentionally **not** imported by the main `Goldbach.GoldFunX` entry point.
It exists to:
- record the intended orthodox analytic statement in a theorem-shaped form, and
- provide a clean place for an eventual proof or checkable certificate.

Downstream pipeline code should depend only on the definitional interfaces in
`Goldbach/Cert/MajorArcAxiomsFunX.lean`.
-/

namespace Goldbach.Cert.MajorArcPowerSavingSpec

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Cert.MajorArcAxiomsFunX

noncomputable section

/--
Textbook-facing major-arc input: power saving in `log X` on the canonical window.

This is the orthodox analytic shape the project ultimately aims to prove from standard inputs
(e.g. Siegel–Walfisz + major-arc analysis).
-/
axiom majorArc_powerSaving : MajorArcPowerSaving

theorem major_arc_eval_on_window :
  ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ {X N : ℕ},
      X0 ≤ X → N ∈ EvenIn X H →
        |RΛ_smooth X N - RΛ_model X N| ≤ C / (Real.log (X : ℝ)) ^ A := by
  simpa [MajorArcPowerSaving, MajorArcBound] using majorArc_powerSaving

lemma majorArcPowerSaving_of_axiom : MajorArcPowerSaving :=
  majorArc_powerSaving

end

end Goldbach.Cert.MajorArcPowerSavingSpec
