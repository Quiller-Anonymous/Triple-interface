/-
  Goldbach/BG_KernelAPI.lean

  Minimal interface for an admissible short-shift kernel on integers.
  This isolates the properties used by BG_Identity and allows swapping
  the concrete model (triangular tent vs. band-limited kernel) later
  without refactoring downstream code.
-/
import Mathlib

namespace Goldbach
namespace BG

/-- Interface for a short–shift kernel indexed by integer offsets,
    restricted to a symmetric band `[-U, U]`.

    Notes:
    - We keep the interface minimal and binder‑free.
    - Frequency‑side properties (band‑limited support, L¹/log‑moment bounds)
      can be added later as additional fields when needed by SSU.
 -/
structure AdmissibleKernel (U : ℕ) where
  /-- The kernel values on integer offsets. -/
  K : ℤ → ℝ
  /-- Evenness: `K(-k) = K(k)`. -/
  even : ∀ k, K (-k) = K k
  /-- Pointwise nonnegativity. -/
  nonneg : ∀ k, 0 ≤ K k
  /-- Mass on the working band `[-U, U]`. Normalize to `1` for convenience. -/
  mass_on_band :
    Finset.sum (Finset.Icc (-(U : ℤ)) (U : ℤ)) (fun k => K k) = 1
  /-- Positivity at zero ensures inner-band mass is nonzero. -/
  pos_at_zero : 0 < K 0

end BG
end Goldbach
