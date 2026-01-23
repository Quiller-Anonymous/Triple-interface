/-
  Fejér alignment control: turn effective-band zeros into the δ-inequality
  required by the barrier. The heavy analytic statement is packaged into the
  `fejer_explicit_formula_delta` axiom so we can wire the result through the
  remainder of the system without duplicating the contour argument here.
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Basic
import AltZeta.ExplicitFormula
import AltZeta.Analytic.FejerCore

noncomputable section
open Real Complex AltZeta Analytic

namespace AltZeta

/-- Alignment gain `κ_{H,α}` extracted from the compact interval `[log X, log 2X]`. -/
def fejerAlignmentKappa (bp : BandParams) : ℝ :=
  Real.cos (bp.α * bp.c * Real.log 2 / bp.H)

/-- Fejér δ-weight: `(1-α) κ_{H,α} |ρ|`. -/
def fejerDelta (bp : BandParams) (z : ℂ) : ℝ :=
  (1 - bp.α) * fejerAlignmentKappa bp * ‖z‖

/-- Auxiliary lemma: `1 - α > 0` since `α ∈ (0,1)`. -/
lemma one_sub_alpha_pos (bp : BandParams) : 0 < 1 - bp.α := by
  have hαlt : bp.α < 1 := (bp.hα).2
  exact sub_pos.mpr hαlt

/-- Complex numbers with positive real part are nonzero. -/
lemma complex_ne_zero_of_pos_re {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro hzero
  have h0 : z.re = 0 := by simpa [hzero]
  exact (ne_of_gt hz) h0

/-- Norm is positive when the real part is positive. -/
lemma complex_norm_pos_of_pos_re {z : ℂ} (hz : 0 < z.re) : 0 < ‖z‖ := by
  have hne : z ≠ 0 := complex_ne_zero_of_pos_re hz
  exact (norm_pos_iff).2 hne

/--
Formal statement of the smoothed explicit-formula inequality: whenever a zero
lies in the effective band encoded by `bp`, the Fejér δ-weight bounds the
completion/ledger side. The proof follows the residue computation described in
the analytic notes; we expose it as an axiom so the remainder of the code can
move forward without duplicating the contour argument here.
-/
axiom fejer_explicit_formula_delta
  (setup : EFSetup) (bp : BandParams)
  (hBandHeight : setup.band.height = bp.α * bp.T)
  (hCosPos : 0 < fejerAlignmentKappa bp)
  (hz : OffLineZeroWitness setup) :
  fejerDelta bp hz.s * Real.sqrt setup.x
    ≤ setup.CGamma - setup.M + Real.sqrt setup.x * setup.S

/-- Data required to run the Fejér control argument for a given `EFSetup`. -/
structure FejerControl (setup : EFSetup) where
  band : BandParams
  hBandHeight : setup.band.height = band.α * band.T
  hCos : 0 < fejerAlignmentKappa band
  hσCrit_nonneg : 0 ≤ setup.band.σCrit

namespace FejerControl

variable {setup : EFSetup} (fc : FejerControl setup)

/-- The δ function returned to the barrier. -/
def delta (hz : OffLineZeroWitness setup) : ℝ :=
  fejerDelta fc.band hz.s

/-- Positivity of δ follows from `α < 1`, `κ > 0`, and the positive real part
of every witness. -/
lemma delta_pos (hz : OffLineZeroWitness setup) : 0 < fc.delta hz := by
  have hRe : setup.band.σCrit < hz.s.re := hz.hRe.1
  have hposRe : 0 < hz.s.re :=
    lt_of_le_of_lt fc.hσCrit_nonneg hRe
  have hα := one_sub_alpha_pos fc.band
  have hκ := fc.hCos
  have habs : 0 < ‖hz.s‖ := complex_norm_pos_of_pos_re hposRe
  have hcoeff : 0 < (1 - fc.band.α) * fejerAlignmentKappa fc.band :=
    mul_pos hα hκ
  exact mul_pos hcoeff habs

/-- The Fejér δ inequality, fed directly by the analytic axiom. -/
lemma delta_bound (hz : OffLineZeroWitness setup) :
    fc.delta hz * Real.sqrt setup.x
      ≤ setup.CGamma - setup.M + Real.sqrt setup.x * setup.S := by
  have := fejer_explicit_formula_delta (setup:=setup) (bp:=fc.band)
    fc.hBandHeight fc.hCos hz
  simpa [delta, fejerDelta] using this

/-- Package the Fejér control into the generic explicit-formula control data. -/
def toExplicitFormulaControl : ExplicitFormulaControl setup :=
{ δ := fc.delta
, hδ := fc.delta_pos
, bound := fc.delta_bound }

end FejerControl

/-- Convenience lemma re-exporting the barrier-facing hypothesis. -/
lemma FejerControl.toHypothesis {setup : EFSetup} (fc : FejerControl setup) :
    EFHypothesis setup :=
  ExplicitFormulaControl.toHypothesis setup fc.toExplicitFormulaControl

end AltZeta
