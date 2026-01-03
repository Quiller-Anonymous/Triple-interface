import Goldbach.AO_AssembleEnvelope
import Goldbach.AO_Core
import Goldbach.AO_Stages
import Goldbach.BankParams
import Goldbach.Windows

/-!
`AO_McanonWiring` isolates the bespoke “wiring” obligation needed to turn the AO channel bounds
into a bound on the core AO remainder `AO_Core.errAO`.

This keeps the rest of the pipeline (bounds, telescoping decomposition, etc.) structural.

Gold-standard intent: eventually replace any instances of `McanonEqMOffOnWindow` by proofs.
-/

namespace Goldbach
namespace AO_McanonWiring

open Goldbach
open Goldbach.BankParams
open Goldbach.Windows
open Goldbach.AO_AssembleEnvelope

/-- Identification hook: on the canonical window, `AO_Core.Mcanon` agrees with the fully staged term. -/
class McanonEqMOffOnWindow (C : Channels) : Prop where
  mcanon_eq_moff :
    ∀ {X N : ℕ}, X0 ≤ X → N ∈ EvenIn X H →
      Goldbach.AO_Core.Mcanon N = Goldbach.AO_Stages.M_off C X N

/-- Once `McanonEqMOffOnWindow` is supplied, the AO decomposition is purely algebraic. -/
instance (C : Channels) [McanonEqMOffOnWindow C] : Decomposition C := by
  refine ⟨by
    intro X N hX hN
    have hM :
        Goldbach.AO_Core.Mcanon N = Goldbach.AO_Stages.M_off C X N :=
      (McanonEqMOffOnWindow.mcanon_eq_moff (C := C)) hX hN
    simpa using
      (Goldbach.AO_Stages.errAO_decomp_window_of_Mcanon_eq (C := C) (X := X) (N := N) hM)⟩

end AO_McanonWiring
end Goldbach

