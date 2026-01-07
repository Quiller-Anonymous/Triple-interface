import Goldbach.Cert.MajorArcAxiomsFunX

/-!
Goldbach/Cert/MajorArcCanonCert.lean
====================================

Project-specific major-arc certificate boundary (FunX track).

The canonical Goldbach pipeline currently needs a *pinned*, numeric major-arc cap on the canonical
window.  This is not “conventional-math-invariant” under the strict README definition, so it is
kept in its own `Cert/` module.

Long-term goal:
* derive this from textbook-facing major-arc inputs (e.g. `MajorArcPowerSaving`) plus a numerical
  calibration argument, and eventually eliminate this axiom.
-/

namespace Goldbach.Cert.MajorArcAxiomsFunX

/--
Pinned major-arc evaluation on the canonical window with the canonical numeric cap `δ_major_canon`.

This is exactly the form consumed by `Goldbach/AO_MajorSwapTenorAxiomsFunX.lean`.
-/
axiom major_arc_eval_on_window_canon :
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ Goldbach.Windows.EvenIn X H →
      |RΛ_smooth X N - RΛ_model X N|
        ≤ δ_major_canon

end Goldbach.Cert.MajorArcAxiomsFunX
