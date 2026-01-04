-- Twin/SW/NewUniform.lean
import Twin.SW.Defs

noncomputable section
open scoped BigOperators

namespace Twin.SW

/-!
Compatibility shim.

This file historically contained standalone definitions of `sumValue` and the
major-arc `mainTerm`. We now source these definitions from `Twin.SW.Defs` so
the entire project uses a single normalization. -/

/-- Additive character `e(t) = exp(2π i t)`. -/
@[simp] abbrev e (t : ℝ) : ℂ := χ_add t

end Twin.SW
