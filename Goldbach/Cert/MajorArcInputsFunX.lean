import Goldbach.Cert.MajorArcAxiomsFunX
import Goldbach.Cert.SiegelWalfiszAxioms

/-!
Textbook-facing major-arc input interfaces (FunX track).

This file is part of the “hard step” refactor plan: we want the major-arc assumptions feeding the
FunX track to be expressible as orthodox, textbook-style analytic statements, and to keep all
project-specific bookkeeping as proved lemmas.

The *current* pipeline still consumes the pinned canonical bound
`Goldbach.Cert.MajorArcAxiomsFunX.major_arc_eval_on_window_canon`. This file is preparatory: it
packages the more orthodox assumptions we aim to use to *derive* that pinned bound (after a
separate numerical calibration step).

No project-specific numerical constants are introduced here.
-/

namespace Goldbach.Cert.MajorArcInputsFunX

open Goldbach.Cert

/--
Core major-arc input for the FunX track: a power-saving major-arc evaluation for the smoothed
Goldbach correlation functional `RΛ_smooth(X,N)` versus the singular-series model.

This is the canonical “textbook-shaped” statement we want to rely on long-term.
-/
structure MajorArcCore : Prop where
  majorArc_powerSaving : MajorArcAxiomsFunX.MajorArcPowerSaving

/--
Optional strengthening: include an orthodox Siegel–Walfisz/PNT-in-AP input on `ψ(x; q, a)`.

This does not (yet) imply `majorArc_powerSaving` inside the codebase; the point is to pin the
*intended* analytic foundation in a conventional, reusable form.
-/
structure MajorArcWithSW : Prop extends MajorArcCore where
  sw_psi :
    ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ⦃x q a : ℕ⦄,
        3 ≤ x →
        1 ≤ q →
        Nat.Coprime a q →
        (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A →
        |SiegelWalfisz.psi x q a - (x : ℝ) / (Nat.totient q : ℝ)|
          ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A

theorem majorArcPowerSaving_of_core (h : MajorArcCore) :
    MajorArcAxiomsFunX.MajorArcPowerSaving :=
  h.majorArc_powerSaving

theorem majorArcPowerSaving_of_sw (h : MajorArcWithSW) :
    MajorArcAxiomsFunX.MajorArcPowerSaving :=
  h.majorArc_powerSaving

theorem swPsi_of_sw (h : MajorArcWithSW) :
    ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ⦃x q a : ℕ⦄,
        3 ≤ x →
        1 ≤ q →
        Nat.Coprime a q →
        (q : ℝ) ≤ (Real.log (x : ℝ)) ^ A →
        |SiegelWalfisz.psi x q a - (x : ℝ) / (Nat.totient q : ℝ)|
          ≤ C * (x : ℝ) / (Real.log (x : ℝ)) ^ A :=
  h.sw_psi

end Goldbach.Cert.MajorArcInputsFunX
