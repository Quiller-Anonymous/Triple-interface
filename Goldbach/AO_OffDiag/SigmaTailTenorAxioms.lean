import Goldbach.BankParams
import Goldbach.Windows
import Goldbach.AO_OffDiag.TailBlock
import Goldbach.AO_OffDiag.SigmaTailReindex

/-!
This file is the **transparency boundary** for the off-diagonal σ-tail truncation input.

Gold-standard intent:
- Only *conventional math* is axiomatized here (facts intended to be available from the literature).
- All bespoke arithmetic/combinatorial work should be proved elsewhere in the pipeline.

In the Tenor writeup, the relevant claim is a truncation estimate for the singular series tail.
We currently record it directly as a bound on our definition `SigmaTailReindex.sigmaTail`.
-/

namespace Goldbach
namespace AO_OffDiag

open Goldbach.Windows
open TailBlock

/-- Conventional input: a tail bound for the σ-series reindexed tail on the canonical window. -/
axiom sigmaTail_bound_on_window
  {X N : ℕ} (hX : BankParams.X0 ≤ X) (hN : N ∈ EvenIn X BankParams.H) :
    |SigmaTailReindex.sigmaTail N| ≤ (1.02 : ℝ) / (TailBlock.Q0 : ℝ)

end AO_OffDiag
end Goldbach

