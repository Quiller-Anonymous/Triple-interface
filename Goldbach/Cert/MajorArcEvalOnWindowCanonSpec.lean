import Goldbach.Cert.MajorArcAxiomsFunX

/-!
Major arcs: canonical on-window evaluation axiom (Strategy 2 / Option B).

This is the “orthodox but still high-level” boundary suggested in
`SupportingDocs/FunX_major_arc_strategy2.txt`:

* state the major-arc evaluation directly on the *project’s* smoothed correlation functional
  `RΛ_smooth` and its σ-model `RΛ_model`, and
* avoid any pinned calibration (`A_canon`, `C_canon`, cutoff inequality at `X0`, …).

Downstream code can consume this in the exact shape it needs:
`|RΛ_smooth - RΛ_model| ≤ δ_major_canon` uniformly on the canonical window.
-/

namespace Goldbach.Cert.MajorArcEvalOnWindowCanonSpec

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.Cert.MajorArcAxiomsFunX

noncomputable section

/--
Conventional (textbook) major-arc input, specialized to the project’s canonical cap
`δ_major_canon`.

This is the Strategy-2 replacement for the pinned calibration datum in
`Goldbach/Cert/MajorArcCanonCalibrationFromPinned.lean`.
-/
axiom major_arc_eval_on_window_canon :
  ∀ {X N : ℕ},
    X0 ≤ X → N ∈ EvenIn X H →
      |RΛ_smooth X N - RΛ_model X N| ≤ δ_major_canon

end

end Goldbach.Cert.MajorArcEvalOnWindowCanonSpec

