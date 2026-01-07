import Goldbach.Cert.SigmaTailAxiomsFun

/-!
Calibration scaffolding for the Fun-track σ-tail bound.

Goal (hard step): replace the axiom
`Goldbach.Cert.SigmaTailAxiomsFun.sigmaTail_bound_on_window`
by a derived theorem from:

1) an axiom-free analytic bound producing an explicit constant `K_tail`, and
2) a project-specific calibration inequality `K_tail ≤ K_tail_canon` (numeric/cert work).

This file only packages the calibration interface and the one-line specialization lemma.
-/

namespace Goldbach.Cert.SigmaTailCalibrationFun

open Goldbach.BankParams
open Goldbach.Cert.SigmaTailAxiomsFun

/--
A σ-tail bound on a window with an explicit constant `K_tail`.

This is the “math-shaped” input we ultimately want to prove from the off-diagonal analysis.
-/
structure TailBound (X0 H : ℕ) (Q : ℕ → ℕ) where
  K_tail : ℝ
  K_tail_nonneg : 0 ≤ K_tail
  bound : SigmaTailBoundOnWindow X0 H Q K_tail

/--
Canonical calibration interface: the explicit bound constant is dominated by the pinned canonical
constant `K_tail_canon`.

This is the only step expected to require project-specific numeric work (proof or certificate).
-/
structure CanonicalCalibration (Q : ℕ → ℕ) extends TailBound X0 H Q where
  cal : K_tail ≤ K_tail_canon

/--
Once a calibration is provided, we can specialize the σ-tail bound to the canonical constant
`K_tail_canon` uniformly on the window.
-/
theorem sigmaTailBoundOnWindow_canon_of_calibration
    {Q : ℕ → ℕ} (h : CanonicalCalibration Q) :
    SigmaTailBoundOnWindow X0 H Q K_tail_canon := by
  intro X N hX hN hQ
  have hQ0 : 0 ≤ (Q X : ℝ) := by positivity
  have h0 := h.bound (X := X) (N := N) hX hN hQ
  have h1 : h.K_tail / (Q X : ℝ) ≤ K_tail_canon / (Q X : ℝ) :=
    div_le_div_of_nonneg_right h.cal hQ0
  exact le_trans h0 h1

end Goldbach.Cert.SigmaTailCalibrationFun

