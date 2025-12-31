import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_Major

namespace Goldbach.AO_ErrorEnvelope

open Goldbach
open Goldbach.AO_AssembleEnvelope

/-- Total AO cap associated to a choice of caps `K`. -/
noncomputable abbrev δAO (K : Caps) : ℝ :=
  Goldbach.AO_AssembleEnvelope.δAO K

lemma δAO_nonneg (K : Caps) : 0 ≤ δAO K :=
  Goldbach.AO_AssembleEnvelope.δAO_nonneg K

/-- Generic 4-channel envelope bound: provided `C` decomposes `AO_Major.errAO` and `K` caps
the channels on the canonical window, we get `|errAO| ≤ δAO K`. -/
lemma errAO_bound
    (C : Channels) (K : Caps) [Decomposition C] [Bounds C K]
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
    |Goldbach.AO_Major.errAO X N| ≤ δAO K := by
  simpa [δAO] using
    (Goldbach.AO_AssembleEnvelope.errAO_bound (C := C) (K := K) hX hN)

end Goldbach.AO_ErrorEnvelope
