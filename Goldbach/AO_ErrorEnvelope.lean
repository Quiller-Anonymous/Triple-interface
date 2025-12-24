import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Major
import Goldbach.AO_AssembleEnvelope

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

end Goldbach.AO_ErrorEnvelope
