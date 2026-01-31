import Mathlib.Analysis.Fourier.AddCircle

/-!
SSU standard torus conventions.

We standardize SSU’s Fourier-side model on the additive circle `AddCircle 1` and its Haar measure,
as in Mathlib’s `Analysis.Fourier.AddCircle`.

Downstream instantiations (Goldbach/Twin/Alt-Zeta) may provide compatibility lemmas showing their
local `e(x)` / Fourier wrappers agree with these definitions.
-/

namespace SSU
namespace Torus

open MeasureTheory AddCircle

noncomputable section

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The unit circle group `𝕋` as `AddCircle 1`. -/
abbrev UC : Type := AddCircle (1 : ℝ)

/-- Haar measure on `AddCircle 1`. -/
abbrev μ : Measure UC := AddCircle.haarAddCircle (T := (1 : ℝ))

end

end Torus
end SSU

