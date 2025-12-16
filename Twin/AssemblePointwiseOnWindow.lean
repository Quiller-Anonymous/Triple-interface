/-
  Twin/AssemblePointwiseOnWindow.lean
  On-window pointwise PSB gate.
-/
import Mathlib
import Twin.Kernel
import Twin.Bridge
import Twin.PinnedLower

noncomputable section

namespace Twin.AssemblePointwiseOnWindow

structure Proof where
  i  : Twin.PinnedLower.Inputs
  assemble_onWindow :
    ∀ {X : ℕ}, i.X0 ≤ X →
      ∀ k : ℕ, k ≤ i.H →
        (Twin.PinnedLower.Inputs.c i) * (Twin.PinnedLower.Inputs.L i) (X + k)
          - i.err (X + k)
        ≤ Twin.Kernel.J i.H k * Twin.Bridge.twinIndicator (X + k)

end Twin.AssemblePointwiseOnWindow
