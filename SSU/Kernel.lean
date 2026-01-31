import SSU.Basic

namespace SSU

open scoped BigOperators

/-!
Kernel hypotheses used throughout the SSU section of the notes.

The `Goldbach over.pdf` presentation mixes “time pin” properties (support/positivity in the time
variable) and “band-limited multiplier” properties (support/moment bounds in frequency).

This file starts with *containers* for those hypotheses. The goal is to keep statements usable even
before committing to a specific Fourier-analytic formalization.
-/

/-- A nonnegative “time pin” kernel on integer shifts, with an explicit width parameter `H`. -/
structure TimePin (H : ℝ) where
  K : ℤ → ℝ
  nonneg : ∀ t : ℤ, 0 ≤ K t
  /-- Optional support control (often `supp K ⊆ [-2H,2H]`). -/
  support : ∀ t : ℤ, K t ≠ 0 → |(t : ℝ)| ≤ 2 * H

/-- A nonnegative frequency-side kernel (multiplier) with bandwidth `1/H`. -/
structure BandLimitedMultiplier (H : ℝ) where
  Khat : ℝ → ℝ
  nonneg : ∀ ξ : ℝ, 0 ≤ Khat ξ
  /-- Band-limitation: `Khat` vanishes off `|ξ| ≤ 1/H`. -/
  support : ∀ ξ : ℝ, Khat ξ ≠ 0 → |ξ| ≤ (1 / H)

end SSU

