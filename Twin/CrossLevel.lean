/-
  Twin/CrossLevel.lean
  Interface to "lift" the raw spectral-null error `e0` up to the final window error `E`.
-/
import Mathlib
import Twin.SpectralNull

noncomputable section

namespace Twin.CrossLevel

/-- A refinement that bounds the raw error `e0` by a chosen final error `E`. -/
structure Refinement (sn : Twin.SpectralNull.Proof) where
  E    : ℕ → ℝ
  le_E : ∀ n : ℕ, sn.e0 n ≤ E n

end Twin.CrossLevel
