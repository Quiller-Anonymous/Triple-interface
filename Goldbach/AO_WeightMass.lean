import Mathlib
import Goldbach.BG_Bank

namespace Goldbach.AO_WeightMass

/-!
AO weight mass.

This is kept separate from `Goldbach.AO_Core` so that off-diagonal modules can depend on
`weight_mass` without importing `AO_Core` (which is useful when refactoring AOI to make
`Mcanon` definitionally match a staged term).
-/

noncomputable section

/--
Major-arc weight mass.

With the current windowed/scaled bank weight `wX`, the (kernel-localized) main term in the major-arc
correlation functional scales like `wScale(X)^2`, since on the bank band both inputs see the same
constant weight factor.
-/
@[simp] def weight_mass (X : ℕ) : ℝ :=
  (Goldbach.BG_Bank.wScale X) ^ 2

end

end Goldbach.AO_WeightMass
