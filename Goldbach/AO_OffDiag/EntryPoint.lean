
import Mathlib
import Goldbach.AO_Core
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailEuler
import Goldbach.AO_OffDiag.SigmaTailReindex

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows
open TailBlock

/--
AO_OffDiag entry point: package the off-diagonal tail machinery as a `TailBlock.Model`
using `AO_Core.sigma` as the “true” σ.
-/
noncomputable def offDiagModel : TailBlock.Model where
  sigma := Goldbach.AO_Core.sigma
  F := TailBlock.F_block
  F_bound_on_window := by
    intro X N hX hN
    -- This is exactly the lemma currently living (as `sorry`) in `SigmaTailEuler`.
    simpa using (Goldbach.AO_OffDiag.SigmaTailEuler.F_block_bound_on_window (X:=X) (N:=N) hX hN)
  sigma_tail_block := by
    intro X N hX hN
    -- This is where the reindex/Euler tail analysis should go.
    -- For now it is not proved: wiring it here makes the dependency explicit.
    -- You will ultimately prove it using `SigmaTailReindex.tail_reindex_bound` + Euler bounds.
    sorry

/-- The numeric tail bound on the canonical window, for `AO_Core.sigma`. -/
theorem offDiag_tail_bound_on_window
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
  |Goldbach.AO_Core.sigma N - TailBlock.sigma_trunc_Q0 N| ≤ (3e-4 : ℝ) :=
by
  simpa [offDiagModel] using TailBlock.tail_bound_on_window (M := offDiagModel) hX hN

end AO_OffDiag
end Goldbach
