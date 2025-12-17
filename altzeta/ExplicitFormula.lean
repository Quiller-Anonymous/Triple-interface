/-
  EF interface: a documented hypothesis shape you will provide from the
  sign/weights + alignment argument. The barrier theorem only needs:

    OffLineZeroInBand → ∃ δ>0, δ*sqrt x ≤ CGamma - M + sqrt x * S

  for the *same* x used in the margin inequality.
-/
import AltZeta.Core

noncomputable section
open AltZeta

namespace AltZeta

/-- Abstract predicate: “there exists an off-line zero in the effective band.” -/
abbrev OffLineZeroInBand : Prop := Prop

/-- The (documented) EF hypothesis type we will eventually construct. -/
def EFHypothesis
  (CGamma M S x : ℝ) : Prop :=
  OffLineZeroInBand → ∃ δ : ℝ, 0 < δ ∧ δ * Real.sqrt x ≤ CGamma - M + Real.sqrt x * S

end AltZeta
