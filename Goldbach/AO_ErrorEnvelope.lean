/-
  Goldbach/AO_ErrorEnvelope.lean  — axiom-free shim

  Re-exports:
    • δAO, δAO_nonneg
    • errAO_bound : |errAO X N| ≤ δAO  (on canonical window)

  You instantiate `Channels` and `Caps` (numbers + proofs) in your
  analytic files and register them below (`instance` blocks).
-/
import Mathlib
import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_Core
import Goldbach.AO_AssembleEnvelope

/-!
  Hook points:
  Provide these in your analytic files (KernelTail, MellinTrunc, SmoothLoss, BG_Bank):

  * a concrete `channels : Goldbach.AO_AssembleEnvelope.Channels` with
      E_kernel, E_mellin, E_smooth, E_off

  * a concrete `caps : Goldbach.AO_AssembleEnvelope.Caps` with
      δ_kernel, δ_mellin, δ_smooth, δ_off and their nonnegativity

  * instances:
      instance : Goldbach.AO_AssembleEnvelope.Decomposition channels := ...
      instance : Goldbach.AO_AssembleEnvelope.Bounds channels caps := ...

  For now you can keep these instances in those files; this file stays agnostic.
-/

namespace Goldbach.AO_ErrorEnvelope

open Goldbach
open Goldbach.AO_AssembleEnvelope

/-- Export δAO and its nonnegativity from the assembled version. -/
noncomputable abbrev δAO (K : Caps) : ℝ := AO_AssembleEnvelope.δAO K
abbrev δAO_nonneg (K : Caps) : 0 ≤ δAO K := AO_AssembleEnvelope.δAO_nonneg K

/-- Export the pointwise bound using the registered channels/caps. -/
lemma errAO_bound
    (C : Channels) (K : Caps) [Decomposition C] [Bounds C K]
    {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ Windows.EvenIn X BankParams.H) :
    |Goldbach.AO_Core.errAO X N| ≤ δAO K :=
  AO_AssembleEnvelope.errAO_bound (C:=C) (K:=K) hX hN

end Goldbach.AO_ErrorEnvelope
