/-
  Twin/SpectralNull.lean
  Interface for a pointwise spectral-null lower bound:
    c * L n - e0 n ≤ J_H (n - X) * twinIndicator n
  for every X ≥ X0 and every n.
-/
import Mathlib
import Twin.Kernel
import Twin.Bridge

noncomputable section

namespace Twin.SpectralNull

/-- Pointwise spectral-null statement (interface only). -/
structure Proof where
  H     : ℕ
  X0    : ℕ
  c     : ℝ
  c_pos : 0 < c
  L     : ℕ → ℝ
  e0    : ℕ → ℝ
  /-- The pointwise lower bound available for every window start `X ≥ X0`. -/
  pointwise :
    ∀ {X : ℕ}, X0 ≤ X →
      ∀ n : ℕ,
        c * L n - e0 n
          ≤ Twin.Kernel.J H (n - X) * Twin.Bridge.twinIndicator n

end Twin.SpectralNull
