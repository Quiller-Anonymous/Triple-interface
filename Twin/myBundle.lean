/-
  Twin/MyBundle.lean
  Thin wrapper: from any analytic Bundle to the final large-X twin existence.
-/
import Twin.Pipeline
import Twin.AssembleFromGates
import Twin.PinnedLower
import Twin.SpectralNull
import Twin.CrossLevel

namespace Twin.MyBundle

/-- If you supply a bundle of gates `b`, you get twins in every large window. -/
theorem twins_large_windows (b : Twin.AssembleFromGates.Bundle) :
    ∀ {X : ℕ}, b.i.X0 ≤ X → Twin.ExistsTwinInWindow X b.i.H :=
  Twin.Pipeline.twins_in_all_large_windows b

end Twin.MyBundle
