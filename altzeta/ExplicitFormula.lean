/-
  EF interface: concrete data records for the off-line zero event together with
  a helper lemma that packages the explicit-formula inequality needed by the
  barrier.
-/
import Mathlib.Data.Complex.Basic
import AltZeta.Core

noncomputable section
open scoped Real
open Complex AltZeta

namespace AltZeta

/-- Abstract handle for the analytic kernel used by Alt-Zeta.  We only need the
evaluation map; the analytic properties are supplied by the external theory. -/
structure AltZetaKernel where
  eval : ℂ → ℂ

/-- A rectangular spectral band that traps candidate off-line zeros.  The line
`σ = σCrit` sits strictly inside the band to encode the “off-line” condition. -/
structure SpectralBand where
  σCrit : ℝ
  σMax : ℝ
  hσ : σCrit < σMax
  height : ℝ
  hheight : 0 ≤ height

/-- Data tying together the dyadic window, the barrier ledger, and the analytic
kernel/band used on the explicit-formula side. -/
structure EFSetup where
  W : Window
  x : ℝ
  hx : ValidX W x
  CGamma : ℝ
  M : ℝ
  S : ℝ
  kernel : AltZetaKernel
  band : SpectralBand

/-- A concrete witness that the Alt-Zeta kernel has a zero in the effective
band (off the baseline line). -/
structure OffLineZeroWitness (setup : EFSetup) where
  s : ℂ
  hzero : setup.kernel.eval s = 0
  hRe : setup.band.σCrit < s.re ∧ s.re ≤ setup.band.σMax
  hIm : |s.im| ≤ setup.band.height

/-- “There exists an off-line zero in the effective band” for the chosen setup. -/
def OffLineZeroInBand (setup : EFSetup) : Prop :=
  Nonempty (OffLineZeroWitness setup)

/-- The documented EF hypothesis: any off-line zero forces the barrier-side
inequality at the same `x`. -/
def EFHypothesis (setup : EFSetup) : Prop :=
  OffLineZeroInBand setup →
    ∃ δ : ℝ, 0 < δ ∧
      δ * Real.sqrt setup.x ≤
        setup.CGamma - setup.M + Real.sqrt setup.x * setup.S

/-- Explicit-formula control data: it produces the required `δ` witness for
every off-line zero in the prescribed band. -/
structure ExplicitFormulaControl (setup : EFSetup) where
  δ : OffLineZeroWitness setup → ℝ
  hδ : ∀ hz, 0 < δ hz
  bound :
    ∀ hz,
      δ hz * Real.sqrt setup.x ≤
        setup.CGamma - setup.M + Real.sqrt setup.x * setup.S

/-- Control data automatically supplies the EF hypothesis expected by the
barrier theorem. -/
lemma ExplicitFormulaControl.toHypothesis
    (setup : EFSetup) (ctrl : ExplicitFormulaControl setup) :
    EFHypothesis setup := by
  intro hz
  classical
  rcases hz with ⟨w⟩
  refine ⟨ctrl.δ w, ctrl.hδ w, ctrl.bound w⟩

end AltZeta
