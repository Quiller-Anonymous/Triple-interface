import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Int.Basic

/-!
Convenience aliases for the SSU ambient Hilbert spaces.

SSU’s “global” formulation lives on the sequence space `ℓ²(ℤ, ℂ)`.

This is intentionally independent of measure theory / Fourier normalization conventions. Any
Fourier-side instantiation should pass through a dedicated bridge module.
-/

namespace SSU
namespace Spaces

noncomputable section

/-- The ambient complex Hilbert space `ℓ²(ℤ)` (counting measure). -/
abbrev L2Z : Type :=
  ℓ²(ℤ, ℂ)

/-- Optional: `ℓ²(ℕ)` (counting measure). -/
abbrev L2N : Type :=
  ℓ²(ℕ, ℂ)

end

end Spaces
end SSU
