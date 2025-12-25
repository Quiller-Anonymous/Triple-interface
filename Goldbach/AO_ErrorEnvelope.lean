import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_ErrorCore

namespace Goldbach.AO_ErrorEnvelope

open Goldbach
open Goldbach.AO_AssembleEnvelope

noncomputable abbrev δAO (K : Caps) : ℝ := AO_AssembleEnvelope.δAO K
abbrev δAO_nonneg (K : Caps) : 0 ≤ δAO K := AO_AssembleEnvelope.δAO_nonneg K

lemma errAO_bound
    (C : Channels) (K : Caps) [Decomposition C] [Bounds C K]
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
    |Goldbach.AO_Major.errAO X N| ≤ δAO K :=
  AO_AssembleEnvelope.errAO_bound (C:=C) (K:=K) hX hN

/-- Canonical channels (telescoping wiring), from `AO_Instantiate`. -/
abbrev channels : Goldbach.AO_AssembleEnvelope.Channels :=
  Goldbach.AO_Instantiate.channels

/-- Canonical caps, from `AO_Instantiate`. -/
noncomputable abbrev caps : Goldbach.AO_AssembleEnvelope.Caps :=
  Goldbach.AO_Instantiate.caps

/-- Total AO error cap as a plain number (simple envelope API). -/
noncomputable abbrev δAO : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO caps

/-- Simple on-window bound in the shape `AO_Major` expects. -/
lemma errAO_bound {X N : ℕ} (hX : X0 ≤ X) (hN : N ∈ EvenIn X H) :
    |Goldbach.AO_Major.errAO X N| ≤ δAO := by
  -- Use the general 4-channel bound with the canonical instances from `AO_Instantiate`.
  simpa [δAO, caps] using
    (Goldbach.AO_AssembleEnvelope.errAO_bound (C:=channels) (K:=caps) hX hN)

/-- Nonnegativity of the simple cap. -/
lemma δAO_nonneg : 0 ≤ δAO := by
  simpa [δAO, caps] using (Goldbach.AO_AssembleEnvelope.δAO_nonneg caps)

end Goldbach.AO_ErrorEnvelope
