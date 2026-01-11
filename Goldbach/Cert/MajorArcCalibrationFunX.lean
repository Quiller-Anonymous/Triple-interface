import Goldbach.Cert.MajorArcAxiomsFunX

/-!
Calibration scaffolding for the FunX major-arc bound.

Goal (hard step): eventually replace the pinned major-arc cap by a derived theorem from orthodox
major-arc inputs (e.g. a power-saving statement) plus a *numerical calibration* that turns the
asymptotic bound into the canonical constant `δ_major_canon` on the pinned window.

This file only packages the *project-specific* calibration interface and the one-line
specialization lemma. It does not introduce any new analytic axioms.
-/

namespace Goldbach.Cert.MajorArcCalibrationFunX

open Goldbach.Cert.MajorArcAxiomsFunX
open Goldbach.BankParams

/-- On the canonical window, `log X` is positive. -/
private lemma log_pos_of_X0_le {X : ℕ} (hX : X0 ≤ X) : 0 < Real.log (X : ℝ) := by
  have hX0' : (1 : ℝ) < (X0 : ℝ) := by
    norm_num [Goldbach.BankParams.X0, X0]
  have hX' : (1 : ℝ) < (X : ℝ) := lt_of_lt_of_le hX0' (by exact_mod_cast hX)
  exact Real.log_pos hX'

/--
Calibration monotonicity: to bound `C/(log X)^A` by a fixed constant for all `X ≥ X0`,
it suffices to prove the inequality at `X = X0`.
-/
theorem cal_from_X0
    {A : ℕ} {C δ : ℝ}
    (hC : 0 ≤ C)
    (hX0 : C / (Real.log (X0 : ℝ)) ^ A ≤ δ) :
    ∀ {X : ℕ}, X0 ≤ X → C / (Real.log (X : ℝ)) ^ A ≤ δ := by
  intro X hX
  have hlogX0 : 0 < Real.log (X0 : ℝ) := log_pos_of_X0_le (X := X0) (le_rfl)
  have hlog_le : Real.log (X0 : ℝ) ≤ Real.log (X : ℝ) := by
    have hX0pos : 0 < (X0 : ℝ) := by
      norm_num [Goldbach.BankParams.X0, X0]
    have hX0leX : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    exact Real.log_le_log hX0pos hX0leX
  have hpow_le : (Real.log (X0 : ℝ)) ^ A ≤ (Real.log (X : ℝ)) ^ A := by
    exact pow_le_pow_left₀ (le_of_lt hlogX0) hlog_le A
  have hmono :
      C / (Real.log (X : ℝ)) ^ A ≤ C / (Real.log (X0 : ℝ)) ^ A := by
    exact div_le_div_of_nonneg_left hC (pow_pos hlogX0 _) hpow_le
  exact le_trans hmono hX0

/--
A single power-saving major-arc bound at a fixed exponent `A`, together with an explicit constant
`C` and the corresponding windowed bound.

This is “textbook-shaped” (no pinned numeric cap yet).
-/
structure PowerSavingBound where
  A : ℕ
  C : ℝ
  C_nonneg : 0 ≤ C
  bound : MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A)

/--
Calibration interface for the canonical pinned window:
the chosen power-saving bound is *numerically dominated* by `δ_major_canon` for all `X ≥ X0`.

This is the only step that should require project-specific numeric work (proof or certificate).
-/
structure CanonicalCalibration extends PowerSavingBound where
  cal : ∀ {X : ℕ}, X0 ≤ X → C / (Real.log (X : ℝ)) ^ A ≤ δ_major_canon

/--
Build a `CanonicalCalibration` datum from:
- an explicit single-exponent power-saving bound, and
- a single numeric inequality at the cutoff `X0`.

This isolates the “pinned numeric work” to proving the inequality at `X0`.
-/
noncomputable def mkCanonicalCalibration
    (A : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hmajor : MajorArcBound (fun X => C / (Real.log (X : ℝ)) ^ A))
    (hX0 : C / (Real.log (X0 : ℝ)) ^ A ≤ δ_major_canon) :
    CanonicalCalibration :=
  { A := A
    C := C
    C_nonneg := hC
    bound := hmajor
    cal := cal_from_X0 (A := A) (C := C) (δ := δ_major_canon) hC hX0 }

/--
Once a calibration is provided, we can specialize the power-saving major-arc estimate to the
canonical constant cap `δ_major_canon` uniformly on the window.

This is pure order reasoning; it does not use any analytic facts beyond the `bound` field.
-/
theorem majorArcBound_canon_of_calibration (h : CanonicalCalibration) :
    MajorArcBound (fun _X => δ_major_canon) :=
  Goldbach.Cert.MajorArcAxiomsFunX.majorArcBound_canon_of_calibration
    (A := h.A) (C := h.C) (hmajor := h.bound) (hcal := h.cal)

theorem major_arc_eval_on_window_canon_of_calibration (h : CanonicalCalibration) :
    ∀ {X N : ℕ},
      Goldbach.BankParams.X0 ≤ X →
      N ∈ Goldbach.Windows.EvenIn X Goldbach.BankParams.H →
        |Goldbach.Cert.MajorArcAxiomsFunX.RΛ_smooth X N
            - Goldbach.Cert.MajorArcAxiomsFunX.RΛ_model X N|
          ≤ Goldbach.Cert.MajorArcAxiomsFunX.δ_major_canon := by
  intro X N hX hN
  -- This is just the specialization of the power-saving bound using the calibration inequality.
  exact (majorArcBound_canon_of_calibration h) hX hN

end Goldbach.Cert.MajorArcCalibrationFunX
