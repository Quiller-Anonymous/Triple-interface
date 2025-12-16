/-
  Twin/AssemblePointwise.lean
  Thin API: you provide the analytic pointwise PSB inequality here.
  Everything else (PinnedLower → Gates → BuildWitness) is deterministic.
-/
import Mathlib
import Twin.Kernel
import Twin.Bridge
import Twin.PinnedLower
import Twin.BuildWitness

noncomputable section

namespace Twin.AssemblePointwise

/-- You will *construct* one of these later, proving `assemble_pointwise`. -/
structure Proof where
  i  : Twin.PinnedLower.Inputs
  assemble_pointwise :
    ∀ {X : ℕ}, i.X0 ≤ X →
      ∀ n : ℕ, (Twin.PinnedLower.Inputs.c i) * (Twin.PinnedLower.Inputs.L i) n - i.err n
              ≤ Twin.Kernel.J i.H (n - X) * Twin.Bridge.twinIndicator n

/-- Turn your pointwise proof + pinned lower into full Gates. -/
def toGates (p : Proof) : Twin.BuildWitness.Gates :=
  Twin.PinnedLower.toGates p.i (assemble_pointwise := p.assemble_pointwise)

/-- Once you have `Proof`, you immediately get a TwinWitness. -/
def toWitness (p : Proof) : Twin.Analytic.TwinWitness :=
  Twin.BuildWitness.build (toGates p)

end Twin.AssemblePointwise
