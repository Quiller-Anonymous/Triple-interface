/-
  Twin/AssembleFromGates.lean
  Glue: (PinnedLower Inputs) + (SpectralNull) + (CrossLevel Refinement)
  ⇒ assemble_pointwise (the gate used by BuildWitness).
-/
import Mathlib
import Twin.Kernel
import Twin.Bridge
import Twin.PinnedLower
import Twin.SpectralNull
import Twin.CrossLevel
import Twin.AssemblePointwise  -- provides the final Proof wrapper

noncomputable section

namespace Twin.AssembleFromGates

/-- All ingredients needed to derive the `assemble_pointwise` inequality. -/
structure Bundle where
  i   : Twin.PinnedLower.Inputs
  sn  : Twin.SpectralNull.Proof
  cr  : Twin.CrossLevel.Refinement sn
  -- Parameter compatibility
  H_match  : sn.H  = i.H
  X0_match : sn.X0 = i.X0
  c_match  : sn.c  = i.c
  L_match  : sn.L  = i.L
  -- Choose the final error to be the PinnedLower error:
  E_match  : cr.E  = i.err

/-- The derived pointwise assembly inequality, ready for BuildWitness. -/
lemma assemble_pointwise (b : Bundle) :
  ∀ {X : ℕ}, b.i.X0 ≤ X →
    ∀ n : ℕ,
      (Twin.PinnedLower.Inputs.c b.i) * (Twin.PinnedLower.Inputs.L b.i) n
        - b.i.err n
      ≤ Twin.Kernel.J b.i.H (n - X) * Twin.Bridge.twinIndicator n := by
  classical
  intro X hX n
  -- Rewrite the cutoff in terms of the spectral-null bundle
  have hX' : b.sn.X0 ≤ X := by simpa [b.X0_match] using hX
  -- Start from the spectral-null pointwise lower bound
  have base :
      b.sn.c * b.sn.L n - b.sn.e0 n
        ≤ Twin.Kernel.J b.sn.H (n - X) * Twin.Bridge.twinIndicator n :=
    b.sn.pointwise (X := X) hX' n
  -- Align parameters (c, L, H) with PinnedLower inputs
  have base' :
      (Twin.PinnedLower.Inputs.c b.i) * (Twin.PinnedLower.Inputs.L b.i) n
        - b.sn.e0 n
      ≤ Twin.Kernel.J b.i.H (n - X) * Twin.Bridge.twinIndicator n := by
    simpa [b.c_match, b.L_match, b.H_match] using base
  -- Strengthen the LHS by replacing e0 with the (larger) final error E = i.err
  have e0_le_E : b.sn.e0 n ≤ b.cr.E n := b.cr.le_E n
  have sub_le :
      (Twin.PinnedLower.Inputs.c b.i) * (Twin.PinnedLower.Inputs.L b.i) n
        - b.cr.E n
      ≤ (Twin.PinnedLower.Inputs.c b.i) * (Twin.PinnedLower.Inputs.L b.i) n
        - b.sn.e0 n := by
    -- if e0 ≤ E then  cL - E ≤ cL - e0
    have := neg_le_neg e0_le_E
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (add_le_add_left this ((Twin.PinnedLower.Inputs.c b.i) * (Twin.PinnedLower.Inputs.L b.i) n))
  -- Chain the inequalities and rewrite E as i.err
  have :
      (Twin.PinnedLower.Inputs.c b.i) * (Twin.PinnedLower.Inputs.L b.i) n
        - b.cr.E n
      ≤ Twin.Kernel.J b.i.H (n - X) * Twin.Bridge.twinIndicator n :=
    le_trans sub_le base'
  simpa [b.E_match] using this

/-- Package the derived inequality as an `AssemblePointwise.Proof`. -/
def toAssemble (b : Bundle) : Twin.AssemblePointwise.Proof :=
{ i := b.i
, assemble_pointwise := by
    intro X hX n
    exact assemble_pointwise b (X := X) hX n
}

end Twin.AssembleFromGates
